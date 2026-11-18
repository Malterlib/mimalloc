/* ----------------------------------------------------------------------------
Copyright (c) 2018-2026, Microsoft Research, Daan Leijen
This is free software; you can redistribute it and/or modify it under the
terms of the MIT license. A copy of the license can be found in the file
"LICENSE" at the root of this distribution.
-----------------------------------------------------------------------------*/

#include "mimalloc.h"
#include "mimalloc/prim/prim-tls.h"
#include "mimalloc/util/stats.h"
#include "mimalloc/util/memid.h"
#include "mimalloc/arena/arena-alloc.h"
#include "mimalloc/arena/arena.h"
#include "mimalloc/heap/page-map.h"
#include "mimalloc/profile/sample-profile.h"
#include "mimalloc/heap/subproc.h"
#include "mimalloc/heap/process.h"
#include "mimalloc/alloc/page.h"
#include "mimalloc/util/threadlocal.h"

// the list of sub-processes is in the sealed `subprocs` (and the main subprocess is allocated in the process meta data)

/* -----------------------------------------------------------
  Meta-data allocation
  We allocate thread local data and theaps through a dedicated
  theap `subproc.theap_meta` which uses a detached tld with
  a detached thread id. The initial theap_meta is statically
  allocated and can thus be used to allocate on an as yet
  uninitialized thread or process.
  We need to take a lock though to allocate safely on the
  detached `theap_meta`.
----------------------------------------------------------- */

void* _mi_meta_zalloc( mi_subproc_t* subproc, size_t size, mi_memid_t* memid ) {
  mi_assert_internal(subproc->theap_meta != NULL);
  void* p = NULL;
  mi_lock(&subproc->theap_meta_lock) {
    p = mi_theap_zalloc(subproc->theap_meta, size);
    if (memid != NULL) { *memid = (p==NULL ? _mi_memid_none() : _mi_memid_create_malloc(p,size,true) ); }
  }
  return p;
}

void* _mi_meta_zalloc_aligned( mi_subproc_t* subproc, size_t size, size_t aligned, mi_memid_t* memid ) {
  mi_assert_internal(subproc->theap_meta != NULL);
  void* p = NULL;
  mi_lock(&subproc->theap_meta_lock) {
    p = mi_theap_zalloc_aligned(subproc->theap_meta, size, aligned);
    if (memid != NULL) { *memid = (p==NULL ? _mi_memid_none() : _mi_memid_create_malloc(p,size,true) ); }
  }
  return p;
}

void* _mi_meta_rezalloc( mi_subproc_t* subproc, void* oldp, size_t newsize, mi_memid_t* memid ) {
  mi_assert_internal(subproc->theap_meta != NULL);
  // note: since we take a meta lock we cannot use `mi_theap_rezalloc` as that could call `mi_free` which
  // can call `mi_stat_free` which would try to take the meta lock again. See issue #1358.
  void* p = NULL;
  mi_lock(&subproc->theap_meta_lock) {
    p = mi_theap_zalloc(subproc->theap_meta, newsize);
  }
  if (p!=NULL) {
    if (oldp!=NULL) {
      const size_t oldsize  = mi_usable_size(oldp);
      const size_t copysize = (newsize < oldsize ? newsize : oldsize);
      mi_memcpy(p,oldp,copysize);
      if (memid!=NULL) { _mi_meta_free(subproc,oldp,*memid); }
                  else { mi_free(oldp); }
    }
    if (memid!=NULL) { *memid = _mi_memid_create_malloc(p,newsize,true); }
  }
  else {
    if (memid!=NULL) { *memid = _mi_memid_none(); }
  }
  return p;
}

void _mi_meta_free(mi_subproc_t* subproc, void* p, mi_memid_t memid) {
  if (p==NULL || mi_memid_needs_no_free(memid)) return;
  if (memid.memkind == MI_MEM_MALLOC) {
    mi_free(p);
  }
  else {
    mi_assert_internal(subproc!=NULL);
    _mi_arenas_free(subproc, p, _mi_memid_size(memid), memid);
  }
}

bool _mi_meta_is_meta_page(const mi_subproc_t* subproc, const mi_page_t* page) {
  if (page==NULL) return false;
  mi_theap_t* theap = page->theap;
  return (theap != NULL && theap == subproc->theap_meta);
}


/* -----------------------------------------------------------
  Sub process helpers
----------------------------------------------------------- */

mi_subproc_t* _mi_subproc_main(void) {
  return mi_process_metadata_field(mi_subproc_t, subproc_main);
}

bool _mi_subproc_is_main(mi_subproc_t* subproc) {
  const mi_process_metadata_t* const metadata = mi_process_get_sealed_once()->metadata;
  return (metadata != NULL && mi_addr(subproc) == mi_addr(&metadata->subproc_main));  // `metadata` has no memory tag
}

mi_subproc_t* _mi_subproc(void) {
  mi_theap_t* theap = _mi_theap_default();
  if (theap == NULL || theap->tld == NULL || theap->tld->subproc == NULL) {  // see issue #1289 and #1391
    return _mi_subproc_main();
  }
  else {
    return theap->tld->subproc;
  }
}

mi_heap_t* mi_heap_main(void) {
  return _mi_subproc_heap_main(_mi_subproc()); // don't use mi_theap_main_init_get() so this call works during process_init
}


mi_subproc_t* _mi_subproc_from_id(mi_subproc_id_t subproc_id) {
  return (mi_subproc_t*)(subproc_id._mi_subproc_id);
}

mi_subproc_id_t _mi_subproc_to_id(mi_subproc_t* subproc) {
  mi_subproc_id_t id = { subproc };
  return id;
}

mi_subproc_id_t mi_subproc_main(void) {
  return _mi_subproc_to_id(_mi_subproc_main());
}

mi_subproc_id_t mi_subproc_current(void) {
  return _mi_subproc_to_id(_mi_subproc());
}


/* -----------------------------------------------------------
  Sub process creation
----------------------------------------------------------- */


static mi_subproc_t* mi_subproc_init(mi_subproc_t* subproc) {
  subproc->subproc_seq = mi_atomic_increment_relaxed(&_mi_process.subprocs_created_count);
  mi_stats_header_init(&subproc->stats);
  mi_lock_init(&subproc->arena_reserve_lock);
  mi_lock_init(&subproc->heaps_lock);
  mi_lock_init(&subproc->theap_meta_lock);
  mi_lock(&_mi_process.subprocs_lock) {
    // push on subproc list (the list head is sealed and stored without memory tag)
    mi_subproc_t* const head = (mi_subproc_t*)mi_meta_load_maybe(mi_process_get_sealed()->subprocs);
    subproc->next = head;
    if (head!=NULL) { head->prev = subproc; }
    mi_process_sealed_t* const sealed = _mi_process_unseal();
    sealed->subprocs = (mi_subproc_t*)mi_ptr_memtag_meta(subproc);
    _mi_process_seal();
  }
  return subproc;
}

mi_subproc_id_t mi_subproc_new(void) {
  mi_thread_init();
  // sub-process meta data is allocated in the main subprocess as that outlives all other subprocesses
  mi_subproc_t* const subproc_main = _mi_subproc_main();
  mi_memid_t memid;
  mi_subproc_t* const subproc = (mi_subproc_t*)_mi_meta_zalloc(subproc_main, sizeof(mi_subproc_t), &memid);
  if (subproc == NULL) { return _mi_subproc_to_id(NULL); }
  subproc->memid  = memid;

  mi_memid_t theap_memid;
  mi_theap_t* const theap_meta = (mi_theap_t*)_mi_meta_zalloc(subproc_main, sizeof(mi_theap_t), &theap_memid);
  if (theap_meta==NULL) {
    _mi_meta_free(subproc_main, subproc, memid);
    return _mi_subproc_to_id(NULL);
  }
  theap_meta->memid = theap_memid;

  // init subproc
  mi_subproc_init(subproc);

  // init main heap
  mi_heap_t* heap_main = _mi_heap_new_for_subproc(subproc,0,true,false);
  if (heap_main==NULL) {
    _mi_meta_free(subproc_main, theap_meta, theap_meta->memid);
    mi_subproc_destroy(_mi_subproc_to_id(subproc));
    return _mi_subproc_to_id(NULL);
  }
  mi_assert_internal(subproc->heap_main == heap_main);

  // init meta theap
  mi_assert_internal(subproc_main->theap_meta!=NULL);
  mi_assert_internal(subproc_main->theap_meta->tld!=NULL);
  mi_assert_internal(subproc_main->theap_meta->tld->thread_id == MI_THREAD_ID_DETACHED);
  _mi_theap_meta_init(theap_meta,heap_main,subproc_main->theap_meta->tld /* detached tld */);
  subproc->theap_meta = theap_meta;

  return _mi_subproc_to_id(subproc);
}


/* -----------------------------------------------------------
  Sub process destruction
----------------------------------------------------------- */

// destroy all subproc resources including arena's, heap's etc.
static void mi_subproc_unsafe_destroy(mi_subproc_t* subproc, bool acquire_subprocs_lock)
{
  if (subproc==NULL) return;

  // remove from the subproc list
  mi_lock_maybe(&_mi_process.subprocs_lock, acquire_subprocs_lock) {
    mi_list_unlink_check(subproc, prev, next, mi_process_get_sealed()->subprocs, NULL);
    if (subproc->next!=NULL) { subproc->next->prev = subproc->prev;  }
    if (subproc->prev!=NULL) { subproc->prev->next = subproc->next;  }
    else {
      mi_process_sealed_t* const sealed = _mi_process_unseal();
      mi_assert_internal(mi_addr(sealed->subprocs)==mi_addr(subproc));
      sealed->subprocs = (mi_subproc_t*)mi_ptr_memtag_meta(subproc->next);
      _mi_process_seal();
    }
  }

  // destroy all subproc heaps
  mi_lock(&subproc->heaps_lock) {
    mi_heap_t* heap = subproc->heaps;
    while (heap != NULL) {
      mi_heap_t* next = heap->next;
      if (heap!=subproc->heap_main) { _mi_heap_force_destroy(heap, false /* don't re-acquire the heaps_lock */); }
      heap = next;
    }
    mi_assert_internal(subproc->heap_main==NULL || subproc->heaps == subproc->heap_main);
    if (subproc->heap_main!=NULL) {
      if (_mi_subproc_is_main(subproc)) {
        _mi_thread_locals_thread_done(); // release thread locals of the current thread (at process exit)
        _mi_thread_locals_done();
      }
      _mi_heap_force_destroy(subproc->heap_main, false /* don't re-acquire the heaps_lock */);  // no warning if destroying the main heap
    }
  }

  subproc->theap_meta = NULL;     // theap meta stats are merged during heap_destroy of the main heap

  if (!_mi_subproc_is_main(subproc)) {
    // merge stats back into the main subproc
    _mi_stats_merge_into(&_mi_subproc_main()->stats, &subproc->stats);
  }

  // remove associated arenas
  _mi_arenas_unsafe_destroy_all(subproc);

  // show stats of the main process (at process end) before releasing the heaps lock
  if (_mi_subproc_is_main(subproc)) {
    if (mi_option_is_enabled(mi_option_show_stats) || mi_option_is_enabled(mi_option_verbose)) {
      mi_subproc_stats_print_out(mi_subproc_main(), NULL, NULL);
    }
  }

  // todo: should we refcount subprocesses?
  mi_lock_done(&subproc->arena_reserve_lock);
  mi_lock_done(&subproc->heaps_lock);
  mi_lock_done(&subproc->theap_meta_lock);
  _mi_meta_free(_mi_subproc_main(), subproc, subproc->memid);
  if (_mi_subproc_is_main(subproc)) {
    // for the main subproc, also release the global page map
    _mi_page_map_unsafe_destroy();
  }
}

void mi_subproc_destroy(mi_subproc_id_t subproc_id) {
  mi_subproc_t* subproc = _mi_subproc_from_id(subproc_id);
  if (subproc==NULL || _mi_subproc_is_main(subproc)) return;
  mi_subproc_unsafe_destroy(subproc, true /* take lock */);
}

void _mi_subprocs_unsafe_destroy_all(void) {
  mi_lock(&_mi_process.subprocs_lock) {
    mi_subproc_t* subproc = (mi_subproc_t*)mi_meta_load_maybe(mi_process_get_sealed()->subprocs);
    while (subproc!=NULL) {
      mi_subproc_t* next = subproc->next;
      if (!_mi_subproc_is_main(subproc)) {
        mi_subproc_unsafe_destroy(subproc, false /* take subprocs lock */);
      }
      subproc = next;
    }
  }
  mi_subproc_unsafe_destroy(_mi_subproc_main(), true /* take subprocs lock */);
}


/* -----------------------------------------------------------
  Sub process various
----------------------------------------------------------- */

void mi_subproc_add_current_thread(mi_subproc_id_t subproc_id) {
  mi_subproc_t* subproc = _mi_subproc_from_id(subproc_id);
  mi_assert_internal(subproc!=NULL);
  if (subproc==NULL) return;
  mi_assert_internal(subproc->heap_main!=NULL);
  if (subproc->heap_main==NULL) return;
  mi_theap_t* theap = _mi_theap_default();
  if (mi_theap_is_initialized(theap)) {
    if (theap->tld!=NULL && theap->tld->subproc != subproc) {
      _mi_warning_message("unable to add thread to the subprocess as it was already in another subprocess (at %p)\n", theap->tld->subproc);
    }
    return;
  }

  // initialize this thread tld & theap
  _mi_thread_init_with_heap(subproc->heap_main);
}


bool mi_subproc_visit_heaps(mi_subproc_id_t subproc_id, mi_heap_visit_fun* visitor, void* arg) {
  mi_subproc_t* subproc = _mi_subproc_from_id(subproc_id);
  if (subproc==NULL) return false;
  bool ok = true;
  mi_lock(&subproc->heaps_lock) {
    for (mi_heap_t* heap = subproc->heaps; heap!=NULL && ok; heap = heap->next) {
      ok = (*visitor)(heap, arg);
    }
  }
  return ok;
}


mi_subproc_t* _mi_subproc_main_init(void) {
  mi_lock_init(&_mi_process.subprocs_lock);
  mi_subproc_t* const subproc = _mi_subproc_main();
  subproc->memid = _mi_memid_create_static(subproc,sizeof(mi_subproc_t));
  mi_subproc_init(subproc);
  _mi_os_stats_bootstrap_merge(subproc);  // account for the OS allocation of the process meta data
  return subproc;
}

void _mi_subproc_main_done(void) {
  mi_lock_done(&_mi_process.subprocs_lock);
}


/* -----------------------------------------------------------
  Fork support

  In a forked child only the forking thread exists, so the theaps of all other
  threads are dead. The fork handler only marks this and the pages of the dead
  theaps are abandoned later on the generic allocation path. This is required as
  other threads may have been inside mimalloc at the time of the fork, leaving their
  data structures inconsistent; a child that only calls `exec` or `_exit` (as POSIX
  requires for multi-threaded programs) then never touches them.
  If a child keeps allocating, it should only fork when all other threads are
  quiesced at a safe point outside mimalloc (as is done for example by CPython's
  stop-the-world). If a dead thread held a lock at the fork, its pages are leaked.

  On macOS, the child can see a torn snapshot of memory that other threads wrote
  concurrently with the fork (across separate mappings). In particular, the thread
  free lists of the pages of the forking thread, and abandoned pages, may be torn.
  libSystem allocates in the child before the pthread child handlers run, so the malloc
  zone `reinit_lock` (which runs before that) drops (and leaks) the thread free lists of
  the forking thread, and suspends reclaiming abandoned pages until the pthread child
  handler. (So on macOS the zone override is required for fork support.)
  It also marks the child as torn, since free arena slices may still have a guard
  page of a page that was allocated concurrently with the fork (see `arena/arena-page-alloc.c`).
----------------------------------------------------------- */


size_t _mi_fork_epoch(void) {
  return _mi_process.fork.epoch;
}

bool _mi_fork_is_torn(void) {
  return _mi_process.fork.torn;
}

bool _mi_fork_keeps_abandoned(void) {
  return _mi_process.fork.keep_abandoned;
}

static bool mi_fork_theap_is_dead(const mi_theap_t* theap) {
  const mi_tld_t* const tld = theap->tld;
  return (tld != NULL && tld->thread_id != MI_THREAD_ID_DETACHED && tld->fork_epoch != _mi_process.fork.epoch);
}

// Abandon the pages of dead theaps in a heap.
// The theap and tld memory itself is not freed as the (dead) thread lists may be inconsistent.
static bool mi_fork_heap_abandon_dead(mi_heap_t* heap) {
  if (!mi_lock_try_acquire(&heap->theaps_lock)) return false;
  mi_theap_t* theap = heap->theaps;
  while (theap != NULL) {
    mi_theap_t* const next = theap->hnext;
    if (mi_fork_theap_is_dead(theap)) {
      mi_list_unlink_check(theap, hprev, hnext, heap->theaps, NULL);
      if (theap->hnext != NULL) { theap->hnext->hprev = theap->hprev; }
      if (theap->hprev != NULL) { theap->hprev->hnext = theap->hnext; }
                           else { heap->theaps = theap->hnext; }
      theap->hnext = NULL;
      theap->hprev = NULL;
      theap->tld = NULL;
      _mi_theap_abandon_owned_pages(theap);
      _mi_stats_merge_into(&heap->stats, &theap->stats);
      mi_atomic_store_ptr_release(mi_heap_t, &theap->heap, NULL);
    }
    theap = next;
  }
  mi_lock_release(&heap->theaps_lock);
  return true;
}

// Called at thread initialization and regularly on the generic allocation path.
// Retried later if a lock is busy.
void _mi_fork_child_try_collect(void) {
  if mi_likely(mi_atomic_load_relaxed(&_mi_process.fork.pending) == 0) return;
  if (mi_atomic_exchange_acq_rel(&_mi_process.fork.pending, 0) == 0) return;
  bool done = false;
  if (mi_lock_try_acquire(&_mi_process.subprocs_lock)) {
    done = true;
    for (mi_subproc_t* subproc = (mi_subproc_t*)mi_meta_load_maybe(mi_process_get_sealed()->subprocs); subproc != NULL; subproc = subproc->next) {
      if (mi_lock_try_acquire(&subproc->heaps_lock)) {
        for (mi_heap_t* heap = subproc->heaps; heap != NULL; heap = heap->next) {
          if (!mi_fork_heap_abandon_dead(heap)) { done = false; }
        }
        mi_lock_release(&subproc->heaps_lock);
      }
      else {
        done = false;
      }
    }
    mi_lock_release(&_mi_process.subprocs_lock);
  }
  if (!done) { mi_atomic_store_release(&_mi_process.fork.pending, 1); }
}

#if defined(__APPLE__)
// Called on macOS in the child from the malloc zone `reinit_lock`.
void _mi_fork_child_zone(void) {
  _mi_process.fork.torn = true;
  mi_theap_t* const theap_default = _mi_theap_default();
  if (!mi_theap_is_initialized(theap_default)) return;

  // suspend reclaiming abandoned pages (by allocation) of the default heap
  mi_heap_t* const heap = mi_theap_heap(theap_default);
  for (size_t bin = 0; bin < MI_BIN_COUNT; bin++) {
    _mi_process.fork.suspended_count[bin] = mi_atomic_exchange_relaxed(&heap->abandoned_count[bin], 0);
  }
  _mi_process.fork.suspended_heap = heap;

  // drop the thread free lists of the pages of the forking thread
  mi_tld_t* const tld = theap_default->tld;
  if (!mi_lock_try_acquire(&tld->theaps_lock)) return;
  for (mi_theap_t* theap = tld->theaps; theap != NULL; theap = theap->tnext) {
    for (size_t bin = 0; bin <= MI_BIN_FULL; bin++) {
      for (mi_page_t* page = theap->pages[bin].first; page != NULL; page = page->next) {
        const mi_thread_free_t tf = mi_atomic_load_relaxed(&page->xthread_free);
        mi_atomic_store_relaxed(&page->xthread_free, mi_tf_create(NULL, mi_tf_is_owned(tf)));
      }
    }
  }
  mi_lock_release(&tld->theaps_lock);
}

// Resume reclaiming abandoned pages (adding as the count may have changed in the meantime)
static void mi_fork_child_resume_reclaim(void) {
  mi_heap_t* const heap = _mi_process.fork.suspended_heap;
  if (heap == NULL) return;
  _mi_process.fork.suspended_heap = NULL;
  for (size_t bin = 0; bin < MI_BIN_COUNT; bin++) {
    mi_atomic_add_relaxed(&heap->abandoned_count[bin], _mi_process.fork.suspended_count[bin]);
  }
}
#endif

// Called in the child process right after a fork.
void _mi_fork_child(void) {
  #if defined(__APPLE__)
  mi_fork_child_resume_reclaim();
  #endif
  _mi_process.fork.epoch++;
  mi_theap_t* const theap = _mi_theap_default();
  if (mi_theap_is_initialized(theap)) { theap->tld->fork_epoch = _mi_process.fork.epoch; }  // the forking thread survives
  mi_atomic_store_release(&_mi_process.fork.pending, 1);
}

// A lock that another thread held when the process forked stays locked in the child, where that
// thread is gone. Threads take locks when they start and end, as for the list of the theaps of a
// heap, so the child takes its locks afresh. What a lock protected can be in the middle of a change.
// The locks of the one-time initializations (`_mi_atomic_once_enter`, `_mi_pthread_key_create`) are
// left as they are.
static void mi_fork_child_reinit_locks(void) {
  mi_lock_init(&_mi_process.subprocs_lock);
  mi_lock_init(&_mi_process.thread_locals_lock);
  _mi_process_sealed_fork_child();
  _mi_page_map_fork_child();
  _mi_options_fork_child();
  for (mi_subproc_t* subproc = (mi_subproc_t*)mi_meta_load_maybe(mi_process_get_sealed()->subprocs); subproc != NULL; subproc = subproc->next) {
    mi_lock_init(&subproc->arena_reserve_lock);
    mi_lock_init(&subproc->heaps_lock);
    mi_lock_init(&subproc->theap_meta_lock);
    for (mi_heap_t* heap = subproc->heaps; heap != NULL; heap = heap->next) {
      mi_lock_init(&heap->theaps_lock);
      mi_lock_init(&heap->os_abandoned_pages_lock);
      mi_lock_init(&heap->arena_pages_lock);
      #if MI_QSBR
      mi_lock_init(&heap->qsbr_delayed_lock);
      #endif
    }
  }
  mi_theap_t* const theap = _mi_theap_default();
  if (mi_theap_is_initialized(theap)) { mi_lock_init(&theap->tld->theaps_lock); }
}

static void mi_fork_child_relink_theap(mi_theap_t* theap) {
  mi_heap_t* const heap = mi_theap_heap_peek(theap);
  if (heap == NULL) return;
  theap->hprev = NULL;
  theap->hnext = heap->theaps;
  if (heap->theaps != NULL) { heap->theaps->hprev = theap; }
  heap->theaps = theap;
}

// The theaps of the threads that are gone leave the lists of the theaps of the heaps, which threads
// change as they start and end: such a list can link a theap that its thread was freeing. The lists
// become those of the theaps that the child has: of the forking thread, and for the meta data.
static void mi_fork_child_reset_theaps(void) {
  for (mi_subproc_t* subproc = (mi_subproc_t*)mi_meta_load_maybe(mi_process_get_sealed()->subprocs); subproc != NULL; subproc = subproc->next) {
    for (mi_heap_t* heap = subproc->heaps; heap != NULL; heap = heap->next) {
      heap->theaps = NULL;
    }
  }
  for (mi_subproc_t* subproc = (mi_subproc_t*)mi_meta_load_maybe(mi_process_get_sealed()->subprocs); subproc != NULL; subproc = subproc->next) {
    if (subproc->theap_meta != NULL) { mi_fork_child_relink_theap(subproc->theap_meta); }
  }
  mi_theap_t* const theap = _mi_theap_default();
  if (mi_theap_is_initialized(theap)) {
    for (mi_theap_t* t = theap->tld->theaps; t != NULL; t = t->tnext) { mi_fork_child_relink_theap(t); }
  }
}

// Malterlib extension: for a host that forwards its own fork handling and builds with
// MI_NO_PTHREAD_ATFORK. It calls this in the child process right after a fork, before the child
// allocates.
// This is best effort, and deliberately no more: a child only has to work as well as with the
// handler of upstream, which supports a child that keeps allocating only when the other threads were
// stopped outside mimalloc. There is no call for before the fork, or for the parent, that takes the
// locks around the fork, so the child can find what a lock protected in the middle of a change, and
// a fork while other threads allocate, start or end is not expected to always give a working child.
// The host does not stop its other threads at a safe point outside mimalloc for the fork,
// and its children keep allocating, so the child must not use what those threads can have been
// changing when the process forked. The handler of upstream (`_mi_fork_child`) abandons the pages of
// those threads, and finds them inconsistent. Here they are not touched: they leak in the child,
// and the theaps of those threads leave their heaps. The fork epoch still marks the threads as gone.
// The child also leaves abandoned pages as they are for as long as it runs, as those threads free
// into them, collect them and reclaim them: it can find one in the middle of that, where a free
// waits for the thread that had it (`mi_bitmap_clear_once_set`), and on macOS with free lists that
// are torn. Allocation doesn't reclaim an abandoned page (`_mi_arenas_page_try_find_abandoned`), a
// free in one only pushes its block (`mi_free_block_mt`), and theaps keep their full pages rather
// than abandon them. So the child reads the free lists only of the pages that the forking thread
// owned, of the pages that it allocates itself, and of the pages for the meta data, which threads
// allocate under a lock. The pages that a thread of the child leaves behind when it ends are not
// reclaimed either.
// On macOS, where the child can see a torn snapshot, the thread free lists of the pages of the
// forking thread are dropped as well, which upstream does from its malloc zone, which is not there
// without MI_OVERRIDE.
void mi_process_forked_child(void) mi_attr_noexcept {
  mi_fork_child_reinit_locks();
  mi_fork_child_reset_theaps();
  #if defined(__APPLE__)
  _mi_fork_child_zone();
  mi_fork_child_resume_reclaim();  // the counts stay those of the abandoned maps, which nothing takes pages from
  #endif
  _mi_process.fork.keep_abandoned = true;
  _mi_process.fork.epoch++;
  mi_theap_t* const theap = _mi_theap_default();
  if (mi_theap_is_initialized(theap)) {
    mi_tld_t* const tld = theap->tld;
    tld->fork_epoch = _mi_process.fork.epoch;  // the forking thread survives
    theap->allow_page_abandon = false;
    for (mi_theap_t* t = tld->theaps; t != NULL; t = t->tnext) { t->allow_page_abandon = false; }
  }
}

// Called at process initialization.
void _mi_fork_init(void) {
  #if defined(MI_USE_PTHREADS) && !defined(__wasi__) && !defined(__EMSCRIPTEN__) && !MI_NO_PTHREAD_ATFORK
  if (pthread_atfork(NULL, NULL, &_mi_fork_child) != 0) {
    _mi_warning_message("unable to register the pthread fork handler\n");
  }
  #endif
}
module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Examples.Recursion

@[expose] public section

/-! # Concurrent data-structure example programs

These programs all surface concurrency / synchronisation patterns and
are currently UNVERIFIED — they exist as targets for future metatheory.
Helper procs (`acquire`, `release`, ticket primitives, channel send/recv,
queue helpers, …) travel with the programs they support.

* `progCounter` — spinlock-protected shared counter.
* `progTicket`  — ticket lock with two contending threads.
* `progTreiber` — lock-free Treiber stack.
* `progMSQueue` — Michael-Scott lock-free queue.
* `progChan`    — single-slot SPSC channel.
-/

namespace Agar
namespace Examples

/-! ## Spinlock-protected counter

The lock is itself just a heap cell holding `0` (free) or `1` (held).
`acquire` spins on `cas`, `release` writes `0` back. Each `incrShared`
takes the lock, does a load/store on the counter, releases.
-/

def acquire : Proc where
  params := ["lk"]
  body := ags(
    done := 0 ;
    while done = 0 do {
      prev := cas lk 0 1 ;
      if prev = 0 then done := 1
    }
  )

def release : Proc where
  params := ["lk"]
  body := ags(store lk 0)

def incrShared : Proc where
  params := ["lk", "c"]
  body := ags(
    tmpA := call acquire(lk) ;
    v    := load c ;
    store c (v + 1) ;
    tmpR := call release(lk)
  )

def progCounter : Program where
  procs := procTable
    [ ("acquire",    acquire)
    , ("release",    release)
    , ("incrShared", incrShared) ]
  main  := ags(
    lk    := alloc 0 ;
    c     := alloc 0 ;
    fork incrShared(lk, c) ;
    fork incrShared(lk, c) ;
    tmpM  := call incrShared(lk, c)
  )

example : progCounter.procs "acquire" = some acquire := rfl

/-! ## Ticket lock

Two shared cells: `next` (next ticket to hand out) and `owner` (currently
served). `ticketAcquire` fetch-and-increments `next` via a `cas` loop,
then spins until `owner == ticket`. `ticketRelease` bumps `owner`.
-/

def ticketAcquire : Proc where
  params := ["next", "owner"]
  body := ags(
    got := 0 ;
    ticket := 0 ;
    while got = 0 do (
      cur  := load next ;
      prev := cas next cur (cur + 1) ;
      if prev = cur then (ticket := cur ; got := 1) else skip
    ) ;
    spin := 0 ;
    while spin = 0 do (
      o := load owner ;
      if o = ticket then spin := 1 else skip
    ) ;
    return ticket
  )

def ticketRelease : Proc where
  params := ["owner"]
  body := ags(
    o := load owner ;
    store owner (o + 1)
  )

def ticketCrit : Proc where
  params := ["next", "owner", "c"]
  body := ags(
    t    := call ticketAcquire(next, owner) ;
    v    := load c ;
    store c (v + 1) ;
    tmpR := call ticketRelease(owner)
  )

def progTicket : Program where
  procs := procTable
    [ ("ticketAcquire", ticketAcquire)
    , ("ticketRelease", ticketRelease)
    , ("ticketCrit",    ticketCrit) ]
  main  := ags(
    next  := alloc 0 ;
    owner := alloc 0 ;
    c     := alloc 0 ;
    fork ticketCrit(next, owner, c) ;
    fork ticketCrit(next, owner, c) ;
    tmpM  := call ticketCrit(next, owner, c)
  )

example : progTicket.procs "ticketAcquire" = some ticketAcquire := rfl
example : progTicket.procs "ticketRelease" = some ticketRelease := rfl

/-! ## Treiber stack

Lock-free stack via CAS on a head pointer.

* `head` holds `0` (empty sentinel — Agar has no null) or a node loc.
* A node is a single cell whose value is the *next* pointer (`0` for
  bottom-of-stack). Payload is `v` at push time; not recovered at pop
  because a Agar cell holds one `Val` and we'd need a second cell whose
  loc we cannot derive from the node loc alone (opaque `Loc`). Pop
  therefore returns the popped node's loc as a token (`0` if empty).
* Nodes are never mutated after publication, so concurrent readers see
  stable `next` links. Only `head` is touched by CAS.
-/

def treiberPush : Proc where
  params := ["head", "v"]
  body := ags(
    node := alloc v ;
    done := 0 ;
    while done = 0 do (
      oh   := load head ;
      store node oh ;
      prev := cas head oh node ;
      if prev = oh then done := 1 else skip
    )
  )

def treiberPop : Proc where
  params := ["head"]
  body := ags(
    done := 0 ;
    result := 0 ;
    while done = 0 do (
      oh := load head ;
      if oh = 0 then (
        result := 0 ; done := 1
      ) else (
        nxt  := load oh ;
        prev := cas head oh nxt ;
        if prev = oh then (result := oh ; done := 1) else skip
      )
    ) ;
    return result
  )

def treiberProducer : Proc where
  params := ["head"]
  body := ags(
    tmp1 := call treiberPush(head, 1) ;
    tmp2 := call treiberPush(head, 2) ;
    tmp3 := call treiberPush(head, 3)
  )

def treiberConsumer : Proc where
  params := ["head"]
  body := ags(
    r1 := call treiberPop(head) ;
    r2 := call treiberPop(head) ;
    r3 := call treiberPop(head)
  )

def progTreiber : Program where
  procs := procTable
    [ ("treiberPush",     treiberPush)
    , ("treiberPop",      treiberPop)
    , ("treiberProducer", treiberProducer)
    , ("treiberConsumer", treiberConsumer) ]
  main  := ags(
    head := alloc 0 ;
    fork treiberProducer(head) ;
    fork treiberConsumer(head) ;
    tmpP := call treiberPush(head, 42) ;
    tmpR := call treiberPop(head)
  )

example : progTreiber.procs "treiberPush" = some treiberPush := rfl
example : progTreiber.procs "treiberPop"  = some treiberPop  := rfl

/-! ## Bounded buffer / message passing (SPSC, capacity 1)

A channel is two heap cells: `data` (slot) and `flag` (0 = empty, 1 = full).
With a single producer and single consumer, only the producer ever writes
`flag := 1` and only the consumer ever writes `flag := 0`, so plain
load/store on `flag` suffices — no thread races another writer. The reads
synchronise because each side spins on the flag value the *other* side
publishes, and Agar's SC semantics makes the matching `data` write/read
observable in order.
-/

def chanSend : Proc where
  params := ["data", "flag", "v"]
  body := ags(
    done := 0 ;
    while done = 0 do (
      f := load flag ;
      if f = 0 then (
        store data v ;
        store flag 1 ;
        done := 1
      ) else skip
    )
  )

def chanRecv : Proc where
  params := ["data", "flag"]
  body := ags(
    done := 0 ;
    result := 0 ;
    while done = 0 do (
      f := load flag ;
      if f = 1 then (
        v := load data ;
        store flag 0 ;
        result := v ;
        done := 1
      ) else skip
    ) ;
    return result
  )

def chanProducer : Proc where
  params := ["data", "flag"]
  body := ags(tmp := call chanSend(data, flag, 42))

def chanConsumer : Proc where
  params := ["data", "flag"]
  body := ags(r := call chanRecv(data, flag))

def progChan : Program where
  procs := procTable
    [ ("chanSend",     chanSend)
    , ("chanRecv",     chanRecv)
    , ("chanProducer", chanProducer)
    , ("chanConsumer", chanConsumer) ]
  main  := ags(
    data := alloc 0 ;
    flag := alloc 0 ;
    fork chanProducer(data, flag) ;
    r    := call chanRecv(data, flag)
  )

example : progChan.procs "chanSend" = some chanSend := rfl
example : progChan.procs "chanRecv" = some chanRecv := rfl

/-! ## Michael-Scott lock-free queue

Two-lock-free FIFO via CAS on `tail.next` (enqueue) and `head` (dequeue).

* `head` and `tail` are heap cells holding node locations.
* A "node" is a single cell holding the *next* pointer (`0` = end of list).
  As with Treiber, payload `v` is not recoverable from the node loc (single
  Agar cell holds one Val; opaque `Loc` admits no sibling derivation), so
  `v` is currently unused. Dequeue returns the unlinked node's loc as a
  token (`0` if empty).
* A sentinel dummy node is allocated at init; `head` and `tail` both point
  at it. Queue is empty iff `head.next = 0`.
* Enqueue: read `t = tail`, read `nxt = *t`. If `nxt = 0`, CAS `t`'s cell
  from `0` to the new node; then help-advance `tail` from `t` to new.
  If `nxt ≠ 0`, tail is lagging — help-advance `tail` from `t` to `nxt`.
* Dequeue: read `h = head`, `t = tail`, `nxt = *h`. If `nxt = 0` queue is
  empty. If `h = t` (lagging tail), help-advance `tail`. Else CAS `head`
  from `h` to `nxt`, return `nxt` on success.
-/

def msqEnqueue : Proc where
  params := ["head", "tail", "v"]
  body := ags(
    node := alloc 0 ;
    done := 0 ;
    while done = 0 do (
      t   := load tail ;
      nxt := load t ;
      if nxt = 0 then (
        prev := cas t 0 node ;
        if prev = 0 then (
          help := cas tail t node ;
          done := 1
        ) else skip
      ) else (
        help := cas tail t nxt
      )
    )
  )

def msqDequeue : Proc where
  params := ["head", "tail"]
  body := ags(
    done := 0 ;
    result := 0 ;
    while done = 0 do (
      h   := load head ;
      t   := load tail ;
      nxt := load h ;
      if nxt = 0 then (
        result := 0 ; done := 1
      ) else (
        if h = t then (
          help := cas tail t nxt
        ) else (
          prev := cas head h nxt ;
          if prev = h then (result := nxt ; done := 1) else skip
        )
      )
    ) ;
    return result
  )

def msqProducer : Proc where
  params := ["head", "tail"]
  body := ags(
    tmp1 := call msqEnqueue(head, tail, 1) ;
    tmp2 := call msqEnqueue(head, tail, 2)
  )

def msqConsumer : Proc where
  params := ["head", "tail"]
  body := ags(
    r1 := call msqDequeue(head, tail) ;
    r2 := call msqDequeue(head, tail)
  )

def progMSQueue : Program where
  procs := procTable
    [ ("msqEnqueue", msqEnqueue)
    , ("msqDequeue", msqDequeue)
    , ("msqProducer", msqProducer)
    , ("msqConsumer", msqConsumer) ]
  main  := ags(
    dummy := alloc 0 ;
    head  := alloc dummy ;
    tail  := alloc dummy ;
    fork msqProducer(head, tail) ;
    fork msqConsumer(head, tail)
  )

example : progMSQueue.procs "msqEnqueue" = some msqEnqueue := rfl
example : progMSQueue.procs "msqDequeue" = some msqDequeue := rfl

end Examples
end Agar

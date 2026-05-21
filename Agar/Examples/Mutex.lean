module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Std.Namespaces
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.TacticsAtomic
public import Agar.Iris.WpSpin
public import Agar.Iris.Algebra.LockRA
public import Agar.Iris.Algebra.CounterRA

@[expose] public section

/-! # `progMiniMutex` — spinlock-style mutex (safety only)

A two-thread CAS-based mutex example. Both forked threads attempt to
acquire a shared lock cell via a single CAS, write a shared counter,
then release. Closed without ghost state for lock ownership, so we
prove **safety + main termination** only — no mutual-exclusion
functional spec. Demonstrates `wp_cas_inv` under two-way fork sharing
of `inv N (∃ v, lk ↦ v)` and `inv N (∃ v, c ↦ v)`.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-! ## Spinlock-style mutex with two contending threads (safety only)

`progMiniMutex` is the smallest faithful encoding of the
acquire-critical-release pattern from `progCounter` (Examples/Counter.lean)
that we can close *without* ghost state for lock ownership.

```
critProc(lk, c) :=
  prev := cas lk 0 1 ;     -- attempt acquire (single CAS, no spin)
  store c 1 ;              -- critical section: write counter
  store lk 0               -- release

main :=
  lk := alloc 0 ;          -- the lock cell, initially 0 = free
  c  := alloc 0 ;          -- the shared counter cell
  fork critProc(lk, c) ;   -- spawn child contender
  fork critProc(lk, c)     -- spawn another child contender
                           -- main then falls through with Val.unit
```

### Realistic scoping

A full functional spec ("counter ends at 2") would require ghost
state tracking *which* thread currently owns the lock — the canonical
Iris locking pattern. That's beyond a single session. We settle for
**safety + main thread termination**: every thread is reducible or
terminated, and a terminated main carries `Val.unit`.

Crucially, this means we make NO claim of mutual exclusion. Both
forked threads execute the entire body unconditionally — the CAS
outcome is irrelevant to safety, and both branches of `wp_cas_inv`
are discharged identically. The invariants `inv N (∃ v, lk ↦ v)` and
`inv N (∃ v, c ↦ v)` (sharing the root namespace, since `E =
CoPset.full` makes `Hsub` trivial regardless) just provide the
"some value lives at this address" reducibility witness needed for
each atomic step.

### What's shared and how

* `HIL` : `inv nroot (∃ v, lk ↦ v)` — the lock invariant, allocated
  before the first fork via `fupd_wp + inv_alloc`. Demoted to the
  intuitionistic context via `ihave #HIL := HIL` so it is duplicated
  by every subsequent `isplitr` (fork split).
* `HIC` : `inv nroot (∃ v, c ↦ v)` — the counter invariant, same
  treatment.

Both are persistent (`inv N P` lives under `□`), so they propagate
freely across the two fork splits and into both forked thread bodies. -/

/-- The critical-section procedure body: acquire (CAS), write counter, release. -/
def critProc : Proc where
  params := ["lk", "c"]
  body := ags(
    prev := cas lk 0 1 ;
    store c 1 ;
    store lk 0
  )

/-- The mini-mutex program: allocate lock + counter, fork two contenders,
fall through. -/
def progMiniMutex : Program where
  procs := fun n => if n = "critProc" then some critProc else none
  main  := ags(
    lk := alloc 0 ;
    c  := alloc 0 ;
    fork critProc(lk, c) ;
    fork critProc(lk, c)
  )

/-- A pointwise discriminator for `Val.int 0`: every value distinct from
`Val.int 0` BEq-tests to `false`. Used to discharge the failure-branch
side condition of `wp_cas_inv`. -/
private theorem val_beq_int0_false :
    ∀ v : Val, v ≠ Val.int 0 → (v == Val.int 0) = false := by
  intro v hne
  cases v with
  | int i =>
      show (i == 0) = false
      have : i ≠ 0 := fun h => hne (by cases h; rfl)
      simp [this]
  | bool _ => rfl
  | loc _ => rfl
  | unit => rfl
  | struct _ => rfl

/-- The single forked-thread proof obligation: starting from
`critProc.body` with `env = bindParams ["lk", "c"] [.loc lkLoc, .loc cLoc]`,
with both invariants in scope persistently, WP closes at `fork_post = emp`. -/
private theorem critProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (lkLoc cLoc : Loc) :
    iprop(inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) lkLoc v) ∗
          inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) cLoc v)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨critProc.body, [],
          bindParams critProc.params [Val.loc lkLoc, Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro ⟨#HIL, #HIC⟩
  unfold critProc
  -- Body: prev := cas lk 0 1 ; store c 1 ; store lk 0
  -- First, peel the outer wp_seq twice to expose `cas` at the head.
  wp_step                        -- wp_seq for the outer (cas; (store c 1; store lk 0))
  iintro !>
  -- Goal: wp ⟨cas "prev" lk 0 1, [store c 1; store lk 0], env, [], none⟩
  iapply wp_cas_inv (GF := GF) (F := F) (N := nroot)
    (vO := Val.int 0) (vN := Val.int 1)
    (Hsub := fun _ _ => CoPset.mem_full)
    (heL := by agar_eval) (heO := by agar_eval) (heN := by agar_eval)
    (heq := by decide)
    (hne_of_ne := val_beq_int0_false)
  iframe HIL
  isplitr
  · -- Success branch: prev bound to 0.
    wp_pures                     -- skip_cons; seq → expose `store c 1`
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIC
    wp_pures                     -- skip_cons → expose `store lk 0`
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIL
    iintro !>
    wp_done
  · -- Failure branch: prev bound to some v ≠ 0. Identical post-CAS sequence.
    iintro !> %v _hvne
    wp_pures                     -- skip_cons; seq → expose `store c 1`
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIC
    wp_pures                     -- skip_cons → expose `store lk 0`
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIL
    iintro !>
    wp_done

theorem progMiniMutex_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progMiniMutex n
            (Machine.initial progMiniMutex) μ') :
    Machine.Adequate progMiniMutex μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progMiniMutex ?_ n μ' htr
  start_closed_proof_with_heap progMiniMutex
  -- main := alloc "lk" 0 ; alloc "c" 0 ; fork critProc(lk,c) ; fork critProc(lk,c)
  wp_pures                                      -- wp_seq
  wp_alloc_intro HPL                            -- HPL : lkLoc ↦ 0
  wp_pures                                      -- skip_cons; seq
  wp_alloc_intro HPC                            -- HPC : cLoc ↦ 0
  wp_pures                                      -- skip_cons; seq exposing first `fork`
  -- Allocate BOTH invariants before the first fork; demote both.
  wp_inv_alloc_pt HPL HIL 0
  wp_inv_alloc_pt HPC HIC 0
  ihave #HIL := HIL
  ihave #HIC := HIC
  -- First fork.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "critProc" [Expr.var "lk", Expr.var "c"] critProc
    [Val.loc _, Val.loc _]
    [Stmt.fork "critProc" [Expr.var "lk", Expr.var "c"]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- First forked thread.
    iintro !>
    iapply critProc_wp_body
    iframe HIL HIC
  · -- Parent continuation: the second `fork`, then fall-through.
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "critProc" [Expr.var "lk", Expr.var "c"] critProc
      [Val.loc _, Val.loc _]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · -- Second forked thread.
      iintro !>
      iapply critProc_wp_body
      iframe HIL HIC
    · -- Final parent continuation: terminal skip at Val.unit.
      iintro !>
      wp_done

/-! ## Strengthened mutual-exclusion proof via `LockRA`

`progMiniMutexExcl` is the variant of `progMiniMutex` whose critical
section is *guarded* by the CAS-acquire result:

```
critProcExcl(lk, c) :=
  prev := cas lk 0 1 ;
  if prev = 0 then (store c 1 ; store lk 0) else skip
```

This is the canonical Iris locking pattern. Only a thread that
*won* the CAS may enter the critical section, and only such a thread
performs the release-store. With the disjunctive lock invariant

```
  inv N ((lk ↦ Val.int 0 ∗ lockOwner γ ∗ ∃ vc, c ↦ vc) ∨ lk ↦ Val.int 1)
```

we now genuinely prove mutual exclusion at the Iris level: only the
holder of `lockOwner γ` may be inside the critical section, and the
two-token exclusivity (`lockOwner_exclusive`) makes it contradictory
for any other thread to simultaneously hold the unlocked-disjunct's
view of the same lock.

### Why the program had to change

In the original `progMiniMutex`, both threads execute `store c 1 ;
store lk 0` unconditionally, including when their CAS failed. A
failing thread has no resources to write `c` or release `lk` under
the lock invariant — both writes would race. The safety-only proof
hides this with a separate `inv N (∃ v, c ↦ v)` whose existential
abstracts away the race. To make the lock pattern's *exclusion* claim
honest, only the CAS-winner enters and releases.

### Proof outline

1. **Acquire** via `wp_cas_atomic`. Open the disjunctive invariant
   body. Since both disjuncts contain `lk ↦ ?` we can present the
   accessor with `vcur = 0` (left disjunct) or `vcur = 1` (right
   disjunct).
   - Left disjunct (`lk ↦ 0 ∗ lockOwner γ ∗ ∃ vc, c ↦ vc`): CAS
     succeeds. Take out `lockOwner γ` and `c ↦ vc` for the thread.
     Close the invariant into the *right* disjunct (`lk ↦ 1`).
   - Right disjunct (`lk ↦ 1`): CAS fails (`vcur = 1 ≠ 0`). Close
     back into the right disjunct unchanged.
2. **Branch on `prev = 0`**.
   - Then-branch (winner): hold `lockOwner γ ∗ c ↦ vc`. Write `c`
     via plain `wp_store`. Then **release** via `wp_store_atomic`.
     Open the disjunctive body; commute later through `∨`; case-split.
     * Left disjunct: the invariant offers a second `lockOwner γ`.
       Combined with our own `lockOwner γ`, `lockOwner_exclusive`
       discharges the impossible case (`False ⊢ anything`).
     * Right disjunct: get `lk ↦ 1`. Store `lk ← 0`. Close into the
       left (unlocked) disjunct using our `lockOwner γ` and `c ↦ 1`.
   - Else-branch (loser): `prev = vcur ≠ 0`, body is `skip`. Done.

The two contending threads use the SAME γ, allocated once in `main`
*before* the first fork, then threaded through both fork branches.
The (persistent) `inv N ...` is duplicated across each `isplitr`.

The closed conclusion is still **safety + Val.unit termination** of
the head (main) thread — adequacy doesn't expose Iris-internal
exclusion claims to the meta-level beyond safety, so the
"mutual-exclusion" strengthening lives entirely inside the proof, in
the shape of the lock invariant and the use of `lockOwner_exclusive`.
-/

/-- The strengthened critical-section procedure: conditional release. -/
def critProcExcl : Proc where
  params := ["lk", "c"]
  body := ags(
    prev := cas lk 0 1 ;
    if prev = 0 then
      (store c 1 ; store lk 0)
    else skip
  )

/-- The strengthened mini-mutex program. -/
def progMiniMutexExcl : Program where
  procs := fun n => if n = "critProcExcl" then some critProcExcl else none
  main  := ags(
    lk := alloc 0 ;
    c  := alloc 0 ;
    fork critProcExcl(lk, c) ;
    fork critProcExcl(lk, c)
  )

/-- The forked-thread proof obligation under the lock invariant. -/
private theorem critProcExcl_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    [LockGpreS GF] {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (lkLoc cLoc : Loc) (γ : GName) :
    iprop(inv (GF := GF) nroot
            iprop(
              (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
                  lockOwner (GF := GF) γ ∗
                  ∃ vc : Val, points_to (GF := GF) (F := F) cLoc vc)
                ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1))) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨critProcExcl.body, [],
          bindParams critProcExcl.params [Val.loc lkLoc, Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold critProcExcl
  -- Body: prev := cas lk 0 1 ; if prev = 0 then (store c 1 ; store lk 0) else skip
  wp_step                                    -- wp_seq exposing `cas`
  iintro !>
  -- Acquire via `wp_cas_atomic_split` (fuses `wp_cas_atomic` + iframe HI +
  -- ▷-commute past ∨ + icases). Disjunctive body P = lockInvBody lk c γ.
  wp_cas_atomic_split HI
    iprop(
      (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
          lockOwner (GF := GF) γ ∗
          ∃ vc : Val, points_to (GF := GF) (F := F) cLoc vc)
        ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1))
    (Val.int 0) (Val.int 1)
    val_beq_int0_false
    with (⟨>HLk, >Hown, %vc, >HC⟩ | >HLk)
  · -- Unlocked: lk↦0, lockOwner γ, c↦vc. CAS will succeed.
    imodintro
    iexists (Val.int 0)
    iframe HLk
    isplitl [Hown HC]
    · -- Success wand: ⌜vcur = 0⌝ -∗ lk↦1 -∗ ={..}=∗ (▷P) ∗ wp ...
      iintro %_ HLk'
      imodintro
      -- Close into the right (locked) disjunct: lk↦1.
      isplitl [HLk']
      · inext; iright; iexact HLk'
      -- Now WP of the critical section. We hold Hown, HC.
      -- Goal: wp ⟨skip, [if ...; ...], env.set "prev" 0, [], none⟩.
      wp_step                              -- wp_skip_cons
      iintro !>
      -- Goal: wp ⟨if prev = 0 then ... else skip, [], env, [], none⟩
      iapply wp_ite_true (heval := by agar_eval)
      iintro !>
      -- Goal: wp ⟨store c 1 ; store lk 0, [], env, [], none⟩
      wp_step                              -- wp_seq
      iintro !>
      -- Goal: wp ⟨store c 1, [store lk 0], env, [], none⟩
      wp_store_keep HC
      wp_step                              -- wp_skip_cons
      iintro !>
      -- Goal: wp ⟨store lk 0, [], env, [], none⟩
      -- Release via wp_store_atomic with the disjunctive body.
      iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
        (P := iprop(
          (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
              lockOwner (GF := GF) γ ∗
              ∃ vc : Val, points_to (GF := GF) (F := F) cLoc vc)
            ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1)))
        (l := lkLoc) (v := Val.int 0)
        (Hsub := fun _ _ => CoPset.mem_full)
        (heL := by agar_eval) (heV := by agar_eval)
      iframe HI
      iintro HP
      inext_or HP
      icases HP with (>⟨_HLk, Hown', %_vc', _HC'⟩ | >HLkR)
      · -- Contradiction: two `lockOwner γ` (mine + invariant's).
        iexfalso
        iapply lockOwner_exclusive γ
        iframe Hown
        iexact Hown'
      · -- Locked branch: lk↦1. Store lk ← 0, close into unlocked disjunct.
        imodintro
        iexists (Val.int 1)
        iframe HLkR
        iintro HLk2
        imodintro
        -- Close into left (unlocked) disjunct using our Hown and HC.
        isplitl [HLk2 Hown HC]
        · inext; ileft
          iframe HLk2
          iframe Hown
          iexists (Val.int 1); iexact HC
        wp_done
    · -- Failure wand: vcur ≠ 0. But we chose vcur = 0; contradiction.
      iintro %hne _
      exfalso; exact hne rfl
  · -- Locked: lk↦1. CAS will fail.
    imodintro
    iexists (Val.int 1)
    iframe HLk
    isplitr
    · -- Success wand: vcur = 0. But vcur = 1; contradiction.
      iintro %heq _
      exfalso; injection heq with h; omega
    · -- Failure wand: vcur ≠ 0 -∗ lk↦1 ={..}=∗ (▷P) ∗ wp ...
      iintro %_hne HLk'
      imodintro
      isplitl [HLk']
      · inext; iright; iexact HLk'
      -- prev is bound to vcur = 1, ≠ 0. Take the else-branch.
      wp_step                              -- wp_skip_cons
      iintro !>
      iapply wp_ite_false (heval := by agar_eval)
      iintro !>
      wp_done

theorem progMiniMutexExcl_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [LockGpreS GF]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progMiniMutexExcl n
            (Machine.initial progMiniMutexExcl) μ') :
    Machine.Adequate progMiniMutexExcl μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progMiniMutexExcl ?_ n μ' htr
  start_closed_proof_with_heap progMiniMutexExcl
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %lkLoc' HPL                         -- HPL : lkLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %cLoc' HPC                          -- HPC : cLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing first `fork`
  iintro !>
  -- Allocate the lock token γ and the disjunctive lock invariant via
  -- the `wp_lock_alloc` combinator (fuses
  -- `fupd_wp + lockOwner_alloc + inv_alloc + imodintro + ihave`).
  wp_lock_alloc γ Hown HI : iprop(
        (points_to (GF := GF) (F := F) lkLoc' (Val.int 0) ∗
            lockOwner (GF := GF) γ ∗
            ∃ vc : Val, points_to (GF := GF) (F := F) cLoc' vc)
          ∨ points_to (GF := GF) (F := F) lkLoc' (Val.int 1))
        := [HPL Hown HPC] by
    inext; ileft
    iframe HPL
    iframe Hown
    iexists (Val.int 0); iexact HPC
  -- First fork.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "critProcExcl" [Expr.var "lk", Expr.var "c"] critProcExcl
    [Val.loc _, Val.loc _]
    [Stmt.fork "critProcExcl" [Expr.var "lk", Expr.var "c"]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- First forked thread.
    iintro !>
    iapply critProcExcl_wp_body
    iexact HI
  · -- Parent continuation: second `fork`, then fall-through.
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "critProcExcl" [Expr.var "lk", Expr.var "c"] critProcExcl
      [Val.loc _, Val.loc _]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · iintro !>
      iapply critProcExcl_wp_body
      iexact HI
    · iintro !>
      wp_done

/-! ## Mutex + counter: combining `LockRA` and `CounterRA`

`progMutexCounter` strengthens `progMiniMutexExcl` by also tracking a
shared *counter* via the `Auth Nat` RA from `CounterRA.lean`. The
critical section now reads the counter, increments it, and writes it
back — exercising both `LockRA` (mutual exclusion of the CS) and
`CounterRA` (ghost increment paired with the heap update).

```
critProcCnt(lk, c) :=
  prev := cas lk 0 1 ;
  if prev = 0 then {
    tmp := load c ;
    store c (tmp + 1) ;
    store lk 0
  }

main :=
  lk := alloc 0 ; c := alloc 0 ;
  fork critProcCnt(lk, c) ;
  fork critProcCnt(lk, c)
```

### Combined invariant

```
inv N ((lk ↦ Val.int 0 ∗ lockOwner γL ∗
          ∃ n : Nat, c ↦ Val.int n ∗
            counter_auth γC n ∗ counter_frag γC n)
        ∨ lk ↦ Val.int 1)
```

The unlocked disjunct ties three pieces of state together:
* the lock cell `lk ↦ 0`,
* the lock-ownership token `lockOwner γL` (kept INSIDE the invariant
  while the lock is free, handed out to the CAS-winner),
* a Σ-tied bundle `c ↦ Val.int n ∗ counter_auth γC n ∗ counter_frag γC n`
  pinning the *heap* counter value to the *ghost* authoritative value
  AND carrying a matching `counter_frag γC n` so a winner can use
  `counter_increment` to atomically bump both `(auth, frag)` from
  `(n, n)` to `(n+1, n+1)` alongside the heap store.

### Realistic scoping

This is the lower bar from the problem statement:

* The proof goes through with `fork_post := emp`. The closed
  conclusion remains safety + `Val.unit` termination of `main`.
* We do NOT thread an extra `counter_frag` resource per thread.
  With a *single* CAS (no spin-retry), only one of the two contenders
  can possibly win — a thread post-condition like `counter_frag γC 1`
  is not provable for the losing thread.
* The *strengthening* over `progMiniMutexExcl_closed` lives entirely
  inside the proof: the invariant now bundles `counter_auth γC n ∗
  counter_frag γC n` with `c ↦ Val.int n`, and the winner branch
  validates the update via `counter_increment`, demonstrating that
  the combined LockRA + CounterRA + heap update is sound.

### Timeless instances

Both `counter_auth` and `counter_frag` are `iOwn`s over `Auth Nat`.
Their underlying CMRA values (`● n` and `◯ n`) are `OFE.DiscreteE`
via `Auth.auth_discrete` / `Auth.frag_discrete`, drawing on the
scoped `DiscreteE` instance for `(_ : Nat)` from `CommMonoidLike`.
This makes both predicates `BI.Timeless` so the `>` modality-strip
pattern works on the invariant body. -/

section MutexCounter

open CMRA UCMRA Auth CommMonoidLike

variable {GF : BundledGFunctors.{0,0,0}} [CounterGpreS GF]

/-- `(● n : Auth ? Nat)` is OFE-discrete. -/
private instance counter_auth_discreteE (n : Nat) :
    OFE.DiscreteE ((● n : Auth PNat Nat)) :=
  Auth.auth_discrete (a := n) (dq := DFrac.own 1) inferInstance inferInstance

/-- `(◯ n : Auth ? Nat)` is OFE-discrete. -/
private instance counter_frag_discreteE (n : Nat) :
    OFE.DiscreteE ((◯ n : Auth PNat Nat)) :=
  Auth.frag_discrete (a := n) inferInstance

/-- `counter_auth γ n` is timeless (its underlying ghost value is
discrete). -/
instance counter_auth_timeless (γ : GName) (n : Nat) :
    BI.Timeless (counter_auth (GF := GF) γ n) := by
  unfold counter_auth
  exact iOwn_timeless

/-- `counter_frag γ n` is timeless. -/
instance counter_frag_timeless (γ : GName) (n : Nat) :
    BI.Timeless (counter_frag (GF := GF) γ n) := by
  unfold counter_frag
  exact iOwn_timeless

end MutexCounter

/-- The counter-tracking critical-section procedure: acquire (CAS),
read + increment counter, release. -/
def critProcCnt : Proc where
  params := ["lk", "c"]
  body := ags(
    prev := cas lk 0 1 ;
    if prev = 0 then {
      tmp := load c ;
      store c (tmp + 1) ;
      store lk 0
    }
  )

/-- The mutex + counter program. -/
def progMutexCounter : Program where
  procs := fun n => if n = "critProcCnt" then some critProcCnt else none
  main  := ags(
    lk := alloc 0 ;
    c  := alloc 0 ;
    fork critProcCnt(lk, c) ;
    fork critProcCnt(lk, c)
  )

/-- The forked-thread proof obligation under the combined lock + counter
invariant. Both threads execute the same body; with `fork_post := emp`
both branches close at `emp`. -/
private theorem critProcCnt_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    [LockGpreS GF] [CounterGpreS GF] {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (lkLoc cLoc : Loc) (γL γC : GName) :
    iprop(inv (GF := GF) nroot
            iprop(
              (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
                  lockOwner (GF := GF) γL ∗
                  ∃ n : Nat,
                    points_to (GF := GF) (F := F) cLoc (Val.int n) ∗
                    counter_auth (GF := GF) γC n ∗
                    counter_frag (GF := GF) γC n)
                ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1))) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨critProcCnt.body, [],
          bindParams critProcCnt.params [Val.loc lkLoc, Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold critProcCnt
  -- Body: prev := cas lk 0 1 ; if prev = 0 then { load; store; store }
  wp_step                                    -- wp_seq exposing `cas`
  iintro !>
  -- Acquire via `wp_cas_atomic_split` over the combined disjunctive body.
  wp_cas_atomic_split HI
    iprop(
      (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
          lockOwner (GF := GF) γL ∗
          ∃ n : Nat,
            points_to (GF := GF) (F := F) cLoc (Val.int n) ∗
            counter_auth (GF := GF) γC n ∗
            counter_frag (GF := GF) γC n)
        ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1))
    (Val.int 0) (Val.int 1)
    val_beq_int0_false
    with (⟨>HLk, >Hown, %n, >HC, >Hauth, >Hfrag⟩ | >HLk)
  · -- Unlocked: lk↦0, lockOwner γL, c↦Val.int n, auth+frag at n.
    imodintro
    iexists (Val.int 0)
    iframe HLk
    isplitl [Hown HC Hauth Hfrag]
    · -- Success wand: close into `lk ↦ 1`, hold Hown/HC/Hauth/Hfrag.
      iintro %_ HLk'
      imodintro
      isplitl [HLk']
      · inext; iright; iexact HLk'
      -- Now perform the CS: load c, store c (tmp+1), store lk 0.
      wp_step                              -- wp_skip_cons (consume post-cas skip)
      iintro !>
      iapply wp_ite_true (heval := by agar_eval)
      iintro !>
      -- Goal: wp ⟨tmp := load c ; store c (tmp+1) ; store lk 0, [], env, [], none⟩
      wp_step                              -- wp_seq exposing `tmp := load c`
      iintro !>
      wp_load_keep HC
      wp_step                              -- wp_skip_cons
      iintro !>
      wp_step                              -- wp_seq exposing `store c (tmp+1)`
      iintro !>
      wp_store_keep HC
      -- Increment auth and frag together: (n,n) ~> (n+1,n+1).
      -- `counter_increment` is a bupd; lift the wp goal to a fupd via
      -- `fupd_wp` so the `ElimModal` for `bupd → fupd` fires.
      iapply fupd_wp
      imod (counter_increment (GF := GF) γC n n) $$ [Hauth Hfrag]
            with ⟨Hauth, Hfrag⟩
      · isplitl [Hauth] <;> iassumption
      imodintro
      wp_step                              -- wp_skip_cons
      iintro !>
      -- Goal: wp ⟨store lk 0, [], env, [], none⟩  (release-store)
      iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
        (P := iprop(
          (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
              lockOwner (GF := GF) γL ∗
              ∃ n : Nat,
                points_to (GF := GF) (F := F) cLoc (Val.int n) ∗
                counter_auth (GF := GF) γC n ∗
                counter_frag (GF := GF) γC n)
            ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1)))
        (l := lkLoc) (v := Val.int 0)
        (Hsub := fun _ _ => CoPset.mem_full)
        (heL := by agar_eval) (heV := by agar_eval)
      iframe HI
      iintro HP2
      inext_or HP2
      icases HP2 with (>⟨_HLk2, Hown', %_n', _HC', _Hauth', _Hfrag'⟩ | >HLkR)
      · -- Contradiction: two `lockOwner γL`.
        iexfalso
        iapply lockOwner_exclusive γL
        iframe Hown
        iexact Hown'
      · -- Locked branch: get lk↦1. Store lk←0; close into unlocked
        -- disjunct using our Hown, HC (now at n+1), Hauth (at n+1),
        -- Hfrag (at n+1).
        imodintro
        iexists (Val.int 1)
        iframe HLkR
        iintro HLk2
        imodintro
        -- Normalize: the heap stored `Val.int (↑n + 1)` but the invariant
        -- existential wants `Val.int ↑(n + 1)`. Equal by `Nat.cast_add`.
        have hcast : Val.int ((n : Int) + 1) = Val.int (((n + 1 : Nat) : Int)) := by
          congr 1
        isplitl [HLk2 Hown HC Hauth Hfrag]
        · inext; ileft
          iframe HLk2
          iframe Hown
          iexists (n + 1)
          isplitl [HC]
          · rw [← hcast]; iexact HC
          iframe Hauth
          iexact Hfrag
        wp_done
    · -- Failure wand: vcur = 0 was our choice → unreachable.
      iintro %hne _
      exfalso; exact hne rfl
  · -- Locked: lk↦1. CAS fails.
    imodintro
    iexists (Val.int 1)
    iframe HLk
    isplitr
    · iintro %heq _
      exfalso; injection heq with h; omega
    · iintro %_hne HLk'
      imodintro
      isplitl [HLk']
      · inext; iright; iexact HLk'
      -- prev = 1 ≠ 0; take the else (skip) branch.
      wp_step                              -- wp_skip_cons
      iintro !>
      iapply wp_ite_false (heval := by agar_eval)
      iintro !>
      wp_done

theorem progMutexCounter_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    [LockGpreS GF] [CounterGpreS GF]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progMutexCounter n
            (Machine.initial progMutexCounter) μ') :
    Machine.Adequate progMutexCounter μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progMutexCounter ?_ n μ' htr
  start_closed_proof_with_heap progMutexCounter
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %lkLoc' HPL                         -- HPL : lkLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %cLoc' HPC                          -- HPC : cLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing first `fork`
  iintro !>
  -- Allocate the counter ghost (auth+frag at 0). The `wp_lock_alloc`
  -- combinator below handles the lock token + disjunctive invariant.
  iapply fupd_wp
  imod counter_alloc with ⟨%γC, Hauth, Hfrag⟩
  imodintro
  wp_lock_alloc γL Hown HI : iprop(
        (points_to (GF := GF) (F := F) lkLoc' (Val.int 0) ∗
            lockOwner (GF := GF) γL ∗
            ∃ n : Nat,
              points_to (GF := GF) (F := F) cLoc' (Val.int n) ∗
              counter_auth (GF := GF) γC n ∗
              counter_frag (GF := GF) γC n)
          ∨ points_to (GF := GF) (F := F) lkLoc' (Val.int 1))
        := [HPL Hown HPC Hauth Hfrag] by
    inext; ileft
    iframe HPL
    iframe Hown
    iexists 0
    iframe HPC
    iframe Hauth
    iexact Hfrag
  -- First fork.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "critProcCnt" [Expr.var "lk", Expr.var "c"] critProcCnt
    [Val.loc _, Val.loc _]
    [Stmt.fork "critProcCnt" [Expr.var "lk", Expr.var "c"]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · iintro !>
    iapply critProcCnt_wp_body
    iexact HI
  · iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "critProcCnt" [Expr.var "lk", Expr.var "c"] critProcCnt
      [Val.loc _, Val.loc _]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · iintro !>
      iapply critProcCnt_wp_body
      iexact HI
    · iintro !>
      wp_done

end Agar.Logic

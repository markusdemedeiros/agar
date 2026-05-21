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
public import Agar.Iris.Algebra.CounterRA

@[expose] public section

/-! # `progCounterCas` — CAS-based shared counter

A two-thread program that bumps a shared counter from `0` to `1` via a
*single inline* CAS each, with no spinlock and no procedure-internal
control flow:

```
casBumpProc(c) := ags( prev := cas c 0 1 )

progCounterCas.main := ags(
  c := alloc 0 ;
  fork casBumpProc(c) ;
  fork casBumpProc(c)
)
```

### Disjunctive invariant

The shared cell is protected by a *two-state* invariant:

```
inv N ((c ↦ Val.int 0 ∗ counter_auth γ 0 ∗ counter_frag γ 0)
       ∨ (c ↦ Val.int 1 ∗ counter_auth γ 1 ∗ counter_frag γ 1))
```

The disjunction matches the two possible heap-values of `c` across the
program's lifetime. The CAS-winner takes the LEFT disjunct (because
the CAS succeeded with `vcur = 0`), drives both `(auth, frag)` from
`(0, 0)` to `(1, 1)` via `counter_increment`, and closes into the
RIGHT disjunct. The CAS-loser takes the RIGHT disjunct (`vcur = 1`),
re-establishes RIGHT unchanged.

### Why the disjunctive shape

`wp_cas_atomic`'s closing-wand pair `(succ-wand) ∗ (fail-wand)` is
joined by **separating** conjunction, so any non-duplicable ghost
state (here `counter_auth γ`) can be placed in at most one wand's
preconditions. Bundling the ghost with the heap value inside a
disjunctive invariant routes the ghost-update entirely through the
success branch and reproduces the disjunct's right side from the heap
value alone in the failure branch — exactly the locking idiom from
`progMiniMutexExcl_closed`, adapted to a counter.

### Closed adequacy

`progCounterCas_closed` discharges
`Machine.Adequate progCounterCas μ' Val.unit` for any reachable `μ'`.
Per-thread safety + main-thread `Val.unit` termination. The internal
Iris invariant additionally guarantees, post-hoc, that the heap value
`c` only ever takes the values `0` or `1` — but adequacy itself does
not expose that meta-fact. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet
open CMRA UCMRA Auth CommMonoidLike

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## Timeless instances for `counter_auth` / `counter_frag` -/

section CounterTimeless

variable {GF : BundledGFunctors.{0,0,0}} [CounterGpreS GF]

private instance counter_auth_discreteE_cas (n : Nat) :
    OFE.DiscreteE ((● n : Auth PNat Nat)) :=
  Auth.auth_discrete (a := n) (dq := DFrac.own 1) inferInstance inferInstance

private instance counter_frag_discreteE_cas (n : Nat) :
    OFE.DiscreteE ((◯ n : Auth PNat Nat)) :=
  Auth.frag_discrete (a := n) inferInstance

private instance counter_auth_timeless_cas (γ : GName) (n : Nat) :
    BI.Timeless (counter_auth (GF := GF) γ n) := by
  unfold counter_auth; exact iOwn_timeless

private instance counter_frag_timeless_cas (γ : GName) (n : Nat) :
    BI.Timeless (counter_frag (GF := GF) γ n) := by
  unfold counter_frag; exact iOwn_timeless

end CounterTimeless

/-- Pointwise discriminator: any value distinct from `Val.int 0`
BEq-tests to `false`. Discharges `wp_cas_atomic`'s failure-side
side condition. -/
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

/-! ## The program -/

/-- The CAS-bump worker procedure: a single inline CAS attempt to bump
the shared counter from `0` to `1`. -/
def casBumpProc : Proc where
  params := ["c"]
  body   := ags( prev := cas c 0 1 )

/-- The full program: allocate the shared counter, fork two contending
workers, fall through to `Val.unit`. -/
def progCounterCas : Program where
  procs := fun n => if n = "casBumpProc" then some casBumpProc else none
  main  := ags(
    c := alloc 0 ;
    fork casBumpProc(c) ;
    fork casBumpProc(c)
  )

/-- The invariant body: a two-state disjunction tying the heap value
to a matching `(counter_auth γ, counter_frag γ)` pair. -/
private abbrev counterInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    [CounterGpreS GF] (cLoc : Loc) (γ : GName) : IProp GF :=
  iprop(
    (points_to (GF := GF) (F := F) cLoc (Val.int 0) ∗
        counter_auth (GF := GF) γ 0 ∗
        counter_frag (GF := GF) γ 0)
      ∨ (points_to (GF := GF) (F := F) cLoc (Val.int 1) ∗
          counter_auth (GF := GF) γ 1 ∗
          counter_frag (GF := GF) γ 1))

/-! ## Worker thread spec

The worker's body, run under `inv N (counterInv cLoc γ)`, closes WP at
`emp`. The disjunctive invariant routes the (non-duplicable) ghost
auth/frag update through the CAS-success branch only. -/

private theorem casBumpProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    [CounterGpreS GF] {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (cLoc : Loc) (γ : GName) :
    iprop(inv (GF := GF) nroot (counterInv GF F cLoc γ)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨casBumpProc.body, [],
          bindParams casBumpProc.params [Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold casBumpProc
  -- Body: `prev := cas c 0 1` (single statement; no `seq`).
  -- Acquire-style CAS over the counter via the disjunctive-body opener.
  wp_cas_atomic_split HI
    (counterInv GF F cLoc γ) (Val.int 0) (Val.int 1)
    val_beq_int0_false
    with (⟨>HC, >Hauth, >Hfrag⟩ | ⟨>HC, >Hauth, >Hfrag⟩)
  · -- Left disjunct: c ↦ 0, auth γ 0, frag γ 0. CAS will succeed.
    imodintro
    iexists (Val.int 0)
    iframe HC
    isplitl [Hauth Hfrag]
    · -- Success wand: vcur = 0, hold c ↦ Val.int 1.
      iintro %_hv0 HC'
      -- Bump (auth, frag): (0, 0) ↝ (1, 1) under `|==>`.
      imod (counter_increment (GF := GF) γ 0 0) $$ [Hauth Hfrag]
            with ⟨Hauth, Hfrag⟩
      · isplitl [Hauth] <;> iassumption
      imodintro
      -- Close into the RIGHT disjunct (c ↦ 1, auth γ 1, frag γ 1).
      isplitl [HC' Hauth Hfrag]
      · inext; iright
        iframe HC'
        iframe Hauth
        iexact Hfrag
      wp_done
    · -- Failure wand: vcur = 0 was our value; vcur ≠ 0 contradiction.
      iintro %hne _
      exfalso; exact hne rfl
  · -- Right disjunct: c ↦ 1, auth γ 1, frag γ 1. CAS will fail.
    imodintro
    iexists (Val.int 1)
    iframe HC
    isplitr
    · -- Success wand: vcur = 0 required; we have vcur = 1; contradiction.
      iintro %heq _
      exfalso; injection heq with h; omega
    · -- Failure wand: vcur ≠ 0, points-to back at Val.int 1.
      iintro %_hne HC'
      imodintro
      -- Close back into the RIGHT disjunct unchanged.
      isplitl [HC' Hauth Hfrag]
      · inext; iright
        iframe HC'
        iframe Hauth
        iexact Hfrag
      wp_done

/-! ## Closed adequacy theorem -/

/-- **Closed adequacy** for `progCounterCas`: under any reachable
machine trace, every thread is terminated or reducible, and a
terminated main thread returns `Val.unit`. -/
theorem progCounterCas_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [CounterGpreS GF]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCounterCas n
            (Machine.initial progCounterCas) μ') :
    Machine.Adequate progCounterCas μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progCounterCas ?_ n μ' htr
  start_closed_proof_with_heap progCounterCas
  -- main := alloc "c" 0 ; fork casBumpProc(c) ; fork casBumpProc(c)
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %cLoc' HPC                          -- HPC : cLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing first `fork`
  iintro !>
  -- Allocate the counter ghost (auth+frag at 0).
  iapply fupd_wp
  imod (counter_alloc (GF := GF)) with ⟨%γ, Hauth, Hfrag⟩
  imodintro
  -- Allocate the disjunctive invariant in the LEFT (c=0) disjunct.
  iapply fupd_wp
  imod (inv_alloc nroot CoPset.full (counterInv GF F cLoc' γ))
        $$ [HPC Hauth Hfrag]
        with HI
  · inext; ileft
    iframe HPC
    iframe Hauth
    iexact Hfrag
  imodintro
  ihave #HI := HI
  -- First fork.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "casBumpProc" [Expr.var "c"] casBumpProc
    [Val.loc _]
    [Stmt.fork "casBumpProc" [Expr.var "c"]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- First forked thread.
    iintro !>
    iapply casBumpProc_wp_body
    iexact HI
  · -- Parent continuation: second `fork`, then fall-through.
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "casBumpProc" [Expr.var "c"] casBumpProc
      [Val.loc _]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · -- Second forked thread.
      iintro !>
      iapply casBumpProc_wp_body
      iexact HI
    · -- Final parent continuation: terminal skip at Val.unit.
      iintro !>
      wp_done

end Agar.Logic

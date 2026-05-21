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

@[expose] public section

/-! # `progReaderCount` — CAS-based reader counter (safety only)

A minimal demo of shared-read counter semantics: a single forked
worker `readerProc` performs `acquireRead` followed by `releaseRead`
against a shared cell `c`, modelled as two inline CAS attempts:

```
readerProc(c) := ags(
  acq := cas c 0 1 ;          -- acquireRead:  bump 0 ↝ 1
  rel := cas c 1 0            -- releaseRead:  drop 1 ↝ 0
)

progReaderCount.main := ags(
  c := alloc 0 ;
  fork readerProc(c)
)
```

### Disjunctive (two-state) invariant

The shared cell is protected by

```
inv N ((c ↦ Val.int 0) ∨ (c ↦ Val.int 1))
```

The disjunction mirrors the only two values `c` can take across the
program's lifetime: idle (`0`, no active reader) or held (`1`, one
reader has acquired). Each CAS opens both branches via
`wp_cas_atomic_split` and re-closes into the other disjunct on
success or the same disjunct on failure.

### Scope: safety only

The disjunctive heap invariant suffices to prove safety; a future
extension can route an `Auth(Nat)` ghost through the success branches
to additionally track the acquire/release balance. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## Boolean discriminators for `wp_cas_atomic_split` (k = 0 and k = 1). -/

private theorem val_beq_int0_false_r :
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

private theorem val_beq_int1_false_r :
    ∀ v : Val, v ≠ Val.int 1 → (v == Val.int 1) = false := by
  intro v hne
  cases v with
  | int i =>
      show (i == 1) = false
      have : i ≠ 1 := fun h => hne (by cases h; rfl)
      simp [this]
  | bool _ => rfl
  | loc _ => rfl
  | unit => rfl
  | struct _ => rfl

/-! ## The program -/

/-- The reader worker procedure: acquireRead (CAS 0↦1), then releaseRead
(CAS 1↦0). -/
def readerCountProc : Proc where
  params := ["c"]
  body   := ags(
    acq := cas c 0 1 ;
    rel := cas c 1 0
  )

/-- The full program: allocate the shared cell idle (`0`), fork one
reader worker, fall through to `Val.unit`. -/
def progReaderCount : Program where
  procs := fun n => if n = "readerCountProc" then some readerCountProc else none
  main  := ags(
    c := alloc 0 ;
    fork readerCountProc(c)
  )

/-! ## The disjunctive heap invariant -/

private abbrev rcInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    (cLoc : Loc) : IProp GF :=
  iprop(points_to (GF := GF) (F := F) cLoc (Val.int 0)
        ∨ points_to (GF := GF) (F := F) cLoc (Val.int 1))

/-! ## Worker thread spec

The worker's body, run under `inv N (rcInv cLoc)`, closes WP at `emp`. -/

private theorem readerCountProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (cLoc : Loc) :
    iprop(inv (GF := GF) nroot (rcInv GF F cLoc)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨readerCountProc.body, [],
          bindParams readerCountProc.params [Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold readerCountProc
  -- Body: `acq := cas c 0 1 ; rel := cas c 1 0`.
  wp_step                                       -- wp_seq
  iintro !>
  -- First CAS: acquireRead — flip `c` from 0 to 1.
  wp_cas_atomic_split HI (rcInv GF F cLoc)
    (Val.int 0) (Val.int 1) val_beq_int0_false_r
    with (>HC0 | >HC1)
  · -- LEFT: c ↦ 0. CAS succeeds; re-close into RIGHT (c ↦ 1).
    imodintro
    iexists (Val.int 0)
    iframe HC0
    isplitl []
    · -- Success wand: receives ⌜0 = 0⌝ and c ↦ 1.
      iintro %_ HC1
      imodintro
      isplitl [HC1]
      · inext; iright; iexact HC1
      -- Continuation after the first CAS: do the second CAS.
      wp_pures                                  -- wp_skip_cons
      wp_cas_atomic_split HI (rcInv GF F cLoc)
        (Val.int 1) (Val.int 0) val_beq_int1_false_r
        with (>HC0 | >HC1)
      · -- LEFT after first CAS succeeded should not arise *causally*,
        -- but logically it might (another opener could have rewritten):
        -- here we simply re-close LEFT unchanged on the failure side.
        imodintro
        iexists (Val.int 0)
        iframe HC0
        isplitl []
        · iintro %heq _
          exact Val.noConfusion heq (fun h => absurd h (by decide))
        · iintro %_ HC0
          imodintro
          isplitl [HC0]
          · inext; ileft; iexact HC0
          wp_done
      · -- RIGHT: c ↦ 1. CAS succeeds; re-close into LEFT.
        imodintro
        iexists (Val.int 1)
        iframe HC1
        isplitl []
        · iintro %_ HC0
          imodintro
          isplitl [HC0]
          · inext; ileft; iexact HC0
          wp_done
        · iintro %hne _
          exact absurd rfl hne
    · -- Failure wand on first CAS at LEFT: requires ⌜0 ≠ 0⌝ — impossible.
      iintro %hne _
      exact absurd rfl hne
  · -- RIGHT: c ↦ 1. First CAS fails; re-close RIGHT.
    imodintro
    iexists (Val.int 1)
    iframe HC1
    isplitl []
    · -- Success wand: requires ⌜1 = 0⌝ — impossible.
      iintro %heq _
      exact Val.noConfusion heq (fun h => absurd h (by decide))
    · -- Failure wand: receives ⌜1 ≠ 0⌝ and c ↦ 1; re-close into RIGHT.
      iintro %_ HC1
      imodintro
      isplitl [HC1]
      · inext; iright; iexact HC1
      -- Continuation after the (failed) first CAS: still do the second CAS.
      wp_pures
      wp_cas_atomic_split HI (rcInv GF F cLoc)
        (Val.int 1) (Val.int 0) val_beq_int1_false_r
        with (>HC0 | >HC1)
      · -- LEFT: CAS fails; re-close LEFT.
        imodintro
        iexists (Val.int 0)
        iframe HC0
        isplitl []
        · iintro %heq _
          exact Val.noConfusion heq (fun h => absurd h (by decide))
        · iintro %_ HC0
          imodintro
          isplitl [HC0]
          · inext; ileft; iexact HC0
          wp_done
      · -- RIGHT: CAS succeeds; re-close into LEFT.
        imodintro
        iexists (Val.int 1)
        iframe HC1
        isplitl []
        · iintro %_ HC0
          imodintro
          isplitl [HC0]
          · inext; ileft; iexact HC0
          wp_done
        · iintro %hne _
          exact absurd rfl hne

/-! ## Closed adequacy theorem -/

/-- **Closed adequacy** for `progReaderCount`: under any reachable
machine trace, every thread is terminated or reducible, and a
terminated main thread returns `Val.unit`. -/
theorem progReaderCount_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progReaderCount n
            (Machine.initial progReaderCount) μ') :
    Machine.Adequate progReaderCount μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progReaderCount ?_ n μ' htr
  start_closed_proof_with_heap progReaderCount
  -- main := alloc "c" 0 ; fork readerProc(c)
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %cLoc' HPC                          -- HPC : cLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  -- Allocate the disjunctive invariant in the LEFT (c ↦ 0) disjunct.
  iapply fupd_wp
  imod (inv_alloc nroot CoPset.full (rcInv GF F cLoc')) $$ [HPC] with HI
  · inext; ileft; iexact HPC
  imodintro
  ihave #HI := HI
  -- Fork the reader worker.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "readerCountProc" [Expr.var "c"] readerCountProc
    [Val.loc _]
    [] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked thread runs the reader body.
    iintro !>
    iapply readerCountProc_wp_body
    iexact HI
  · -- Parent continuation: terminal skip at Val.unit.
    iintro !>
    wp_done

end Agar.Logic

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

/-! # `progProdCon` — single-slot bounded buffer (producer/consumer)

A two-thread *asymmetric* concurrent program: one thread produces a
value into a shared slot, the other consumes it. Synchronisation is
encoded in the slot itself by a sentinel value (`0` = empty, `42` =
full):

```
producerProc(slot) := prev := cas slot 0 42
consumerProc(slot) := prev := cas slot 42 0

progProdCon.main := ags(
  slot := alloc 0 ;
  fork producerProc(slot) ;
  fork consumerProc(slot)
)
```

### Disjunctive two-state invariant

Like `progCounterCas`, the slot is protected by a two-state invariant
matching the two possible heap values:

```
inv N ((slot ↦ Val.int 0)        -- EMPTY
      ∨ (slot ↦ Val.int 42))     -- FULL
```

Unlike `progCounterCas` (where both threads do the same CAS 0→1), here
the threads CAS in *opposite directions*:

* **Producer** does `cas slot 0 42` — transitions EMPTY ↦ FULL.
* **Consumer** does `cas slot 42 0` — transitions FULL ↦ EMPTY.

Each thread's CAS-success branch swaps the disjunct; each CAS-failure
branch re-establishes the disjunct it observed unchanged. The proof
demonstrates that the two asymmetric atomic transitions compose
cleanly through a single disjunctive heap invariant.

### What we do *not* prove

Closed adequacy here yields only safety + `Val.unit` termination of
the head thread. A *functional* spec (the consumer actually witnesses
`42` once the producer fires) would need ghost tokens routing the
consumer's "I read the data" obligation through the producer's
CAS-success branch — the asymmetric-token strengthening discussed in
the Mutex / Counter examples. We deliberately defer that here: at the
safety level, the disjunctive heap invariant alone is sound, and this
file is the reference for the *asymmetric two-direction CAS* idiom.

### Closed adequacy

`progProdCon_closed` discharges `Machine.Adequate progProdCon μ'
Val.unit` for any reachable `μ'`. The Iris invariant additionally
guarantees, post-hoc, that the heap value at `slot` only ever takes
the values `0` or `42` — adequacy itself does not expose that
meta-fact. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## CAS-failure-branch discriminators

Two pointwise lemmas closing the failure side of `wp_cas_atomic`: any
value distinct from the expected CAS-old reads as `false` under
`Val.beq`. -/

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

private theorem val_beq_int42_false :
    ∀ v : Val, v ≠ Val.int 42 → (v == Val.int 42) = false := by
  intro v hne
  cases v with
  | int i =>
      show (i == 42) = false
      have : i ≠ 42 := fun h => hne (by cases h; rfl)
      simp [this]
  | bool _ => rfl
  | loc _ => rfl
  | unit => rfl
  | struct _ => rfl

/-! ## The program -/

/-- Producer: a single inline CAS attempting EMPTY ↦ FULL. -/
def producerProc : Proc where
  params := ["slot"]
  body   := ags( prev := cas slot 0 42 )

/-- Consumer: a single inline CAS attempting FULL ↦ EMPTY. -/
def consumerProc : Proc where
  params := ["slot"]
  body   := ags( prev := cas slot 42 0 )

/-- The producer-consumer program: allocate the shared slot, fork the
two asymmetric workers, fall through to `Val.unit`. -/
def progProdCon : Program where
  procs := fun n =>
    if n = "producerProc" then some producerProc
    else if n = "consumerProc" then some consumerProc
    else none
  main  := ags(
    slot := alloc 0 ;
    fork producerProc(slot) ;
    fork consumerProc(slot)
  )

/-- The shared two-state invariant: the slot is either EMPTY (`0`) or
FULL (`42`). -/
private abbrev slotInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    (sLoc : Loc) : IProp GF :=
  iprop(
    points_to (GF := GF) (F := F) sLoc (Val.int 0)
      ∨ points_to (GF := GF) (F := F) sLoc (Val.int 42))

/-! ## Producer-thread WP body

Single-CAS EMPTY → FULL under the disjunctive invariant. -/

private theorem producerProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (sLoc : Loc) :
    iprop(inv (GF := GF) nroot (slotInv GF F sLoc)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨producerProc.body, [],
          bindParams producerProc.params [Val.loc sLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold producerProc
  -- Body: `prev := cas slot 0 42` (single statement; no `seq`).
  wp_cas_atomic_split HI
    (slotInv GF F sLoc) (Val.int 0) (Val.int 42)
    val_beq_int0_false
    with (>HS | >HS)
  · -- LEFT disjunct: slot ↦ 0. CAS succeeds.
    imodintro
    iexists (Val.int 0)
    iframe HS
    isplitl []
    · -- Success wand: close into RIGHT (slot ↦ 42).
      iintro %_hv0 HS'
      imodintro
      isplitl [HS']
      · inext; iright; iexact HS'
      wp_done
    · -- Failure wand: vcur = 0 was our choice → unreachable.
      iintro %hne _
      exfalso; exact hne rfl
  · -- RIGHT disjunct: slot ↦ 42. CAS fails (42 ≠ 0).
    imodintro
    iexists (Val.int 42)
    iframe HS
    isplitr
    · -- Success wand: vcur = 0 required; we have vcur = 42; contradiction.
      iintro %heq _
      exfalso; injection heq with h; omega
    · -- Failure wand: close back into RIGHT unchanged.
      iintro %_hne HS'
      imodintro
      isplitl [HS']
      · inext; iright; iexact HS'
      wp_done

/-! ## Consumer-thread WP body

Single-CAS FULL → EMPTY under the same disjunctive invariant. The
case-split is *symmetric* to the producer's: success is now possible
in the RIGHT disjunct (slot ↦ 42), failure in the LEFT (slot ↦ 0). -/

private theorem consumerProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (sLoc : Loc) :
    iprop(inv (GF := GF) nroot (slotInv GF F sLoc)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨consumerProc.body, [],
          bindParams consumerProc.params [Val.loc sLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold consumerProc
  -- Body: `prev := cas slot 42 0`.
  wp_cas_atomic_split HI
    (slotInv GF F sLoc) (Val.int 42) (Val.int 0)
    val_beq_int42_false
    with (>HS | >HS)
  · -- LEFT disjunct: slot ↦ 0. CAS fails (0 ≠ 42).
    imodintro
    iexists (Val.int 0)
    iframe HS
    isplitr
    · -- Success wand: vcur = 42 required; we have vcur = 0; contradiction.
      iintro %heq _
      exfalso; injection heq with h; omega
    · -- Failure wand: close back into LEFT unchanged.
      iintro %_hne HS'
      imodintro
      isplitl [HS']
      · inext; ileft; iexact HS'
      wp_done
  · -- RIGHT disjunct: slot ↦ 42. CAS succeeds.
    imodintro
    iexists (Val.int 42)
    iframe HS
    isplitl []
    · -- Success wand: close into LEFT (slot ↦ 0).
      iintro %_hv42 HS'
      imodintro
      isplitl [HS']
      · inext; ileft; iexact HS'
      wp_done
    · -- Failure wand: vcur = 42 was our choice → unreachable.
      iintro %hne _
      exfalso; exact hne rfl

/-! ## Closed adequacy theorem -/

/-- **Closed adequacy** for `progProdCon`: under any reachable machine
trace, every thread is terminated or reducible, and a terminated main
thread returns `Val.unit`. -/
theorem progProdCon_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progProdCon n
            (Machine.initial progProdCon) μ') :
    Machine.Adequate progProdCon μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progProdCon ?_ n μ' htr
  start_closed_proof_with_heap progProdCon
  -- main := alloc "slot" 0 ; fork producerProc(slot) ; fork consumerProc(slot)
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc
  iintro !> %sLoc' HPS                          -- HPS : sLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing first `fork`
  iintro !>
  -- Allocate the disjunctive invariant in the LEFT (empty) disjunct.
  iapply fupd_wp
  imod (inv_alloc nroot CoPset.full (slotInv GF F sLoc'))
        $$ [HPS]
        with HI
  · inext; ileft; iexact HPS
  imodintro
  ihave #HI := HI
  -- First fork (producer).
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "producerProc" [Expr.var "slot"] producerProc
    [Val.loc _]
    [Stmt.fork "consumerProc" [Expr.var "slot"]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Producer thread.
    iintro !>
    iapply producerProc_wp_body
    iexact HI
  · -- Parent continuation: second `fork` (consumer), then fall-through.
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "consumerProc" [Expr.var "slot"] consumerProc
      [Val.loc _]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · -- Consumer thread.
      iintro !>
      iapply consumerProc_wp_body
      iexact HI
    · -- Final parent continuation: terminal skip at Val.unit.
      iintro !>
      wp_done

end Agar.Logic

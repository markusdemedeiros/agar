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

Asymmetric pair: producer CAS `slot 0 42` (EMPTY → FULL), consumer
CAS `slot 42 0` (FULL → EMPTY). The disjunctive invariant `slotInv` is
the canonical two-state shape; `progProdCon_closed` proves the safety-
only spec at `Val.unit`. `progProdConRace_closedP` extends to the
predicate-form spec `result ∈ {0, 42}` via the same invariant — no
extra ghost tokens needed. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

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

/-! ## Producer-thread WP body (single CAS `0 → 42`, EMPTY → FULL) -/

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
  wp_cas_atomic_split HI
    (slotInv GF F sLoc) (Val.int 0) (Val.int 42)
    (val_beq_int_false 0)
    with (>HS | >HS)
  · -- Open under LEFT (EMPTY). CAS succeeds.
    cas_succeed_with (Val.int 0) HS
    · inv_close_right HS'; wp_done   -- post-CAS slot ↦ 42; close into FULL
    · cas_dead
  · -- Open under RIGHT (FULL). CAS fails (42 ≠ 0).
    cas_fail_with (Val.int 42) HS
    · cas_dead
    · inv_close_right HS'; wp_done   -- re-close FULL with heap we read

/-! ## Consumer-thread WP body (mirror: CAS `42 → 0`, FULL → EMPTY) -/

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
  wp_cas_atomic_split HI
    (slotInv GF F sLoc) (Val.int 42) (Val.int 0)
    (val_beq_int_false 42)
    with (>HS | >HS)
  · -- Open under LEFT (EMPTY). CAS fails (0 ≠ 42).
    cas_fail_with (Val.int 0) HS
    · cas_dead
    · inv_close_left HS'; wp_done    -- re-close EMPTY with heap we read
  · -- Open under RIGHT (FULL). CAS succeeds.
    cas_succeed_with (Val.int 42) HS
    · inv_close_left HS'; wp_done    -- post-CAS slot ↦ 0; close into EMPTY
    · cas_dead

/-! ## Closed adequacy theorem -/

/-- **Closed adequacy** for `progProdCon`: under any reachable machine
trace, every thread is terminated or reducible, and a terminated main
thread returns `Val.unit`. -/
theorem progProdCon_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progProdCon (· = Val.unit) := by
  adequacy_with_heap_intro progProdCon Val.unit
  wp_pures
  wp_alloc_intro sLoc' HPS                      -- HPS : sLoc' ↦ 0
  wp_pures
  inv_alloc_left (slotInv GF F sLoc') HPS
  wp_fork_emp "producerProc" [Expr.var "slot"] producerProc [Val.loc _]
    [Stmt.fork "consumerProc" [Expr.var "slot"]]
  isplitr
  · -- Producer thread.
    iintro !>
    iapply producerProc_wp_body
    iexact HI
  · -- Parent continuation: second `fork` (consumer), then fall-through.
    iintro !>
    wp_pures
    wp_fork_emp "consumerProc" [Expr.var "slot"] consumerProc [Val.loc _] []
    isplitr
    · -- Consumer thread.
      iintro !>
      iapply consumerProc_wp_body
      iexact HI
    · -- Final parent continuation: terminal skip at Val.unit.
      iintro !>
      wp_done

/-! ## `progProdConRace` — predicate-form adequacy: `result ∈ {0, 42}`

Same producer/consumer pair, but main loads the slot once and returns
the observed value. The slot's two-state invariant feeds directly into
the postcondition without any extra ghost machinery — the predicate
form lets the spec match the invariant's natural shape. -/

def progProdConRace : Program where
  procs := fun n =>
    if n = "producerProc" then some producerProc
    else if n = "consumerProc" then some consumerProc
    else none
  main  := ags(
    slot := alloc 0 ;
    fork producerProc(slot) ;
    fork consumerProc(slot) ;
    v := load slot ;
    return v
  )

theorem progProdConRace_closedP
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progProdConRace
      (fun v => v = Val.int 0 ∨ v = Val.int 42) := by
  adequacy_with_heap_intro_P progProdConRace
    (fun v => v = Val.int 0 ∨ v = Val.int 42)
  wp_pures
  wp_alloc_intro sLoc' HPS
  wp_pures
  inv_alloc_left (slotInv GF F sLoc') HPS
  wp_fork_emp "producerProc" [Expr.var "slot"] producerProc [Val.loc _]
    [ags(fork consumerProc(slot) ; v := load slot ; return v)]
  isplitr
  · iintro !>
    iapply producerProc_wp_body
    iexact HI
  · iintro !>
    wp_pures
    wp_fork_emp "consumerProc" [Expr.var "slot"] consumerProc [Val.loc _]
      [ags(v := load slot ; return v)]
    isplitr
    · iintro !>
      iapply consumerProc_wp_body
      iexact HI
    · iintro !>
      wp_pures
      iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
        (P := slotInv GF F sLoc')
        (Hsub := by rw [nclose_root])
        (heL := by agar_eval)
      iframe HI
      iintro HP
      ihave HP := BI.later_or.mp $$ HP
      icases HP with (>HC | >HC)
      · imodintro
        iexists (Val.int 0)
        isplitl [HC]
        · iexact HC
        iintro HC
        imodintro
        isplitl [HC]
        · inext; ileft; iexact HC
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "v") (Val.int 0) [] _ _
          (heval := by agar_eval))
        ipure_intro; left; rfl
      · imodintro
        iexists (Val.int 42)
        isplitl [HC]
        · iexact HC
        iintro HC
        imodintro
        isplitl [HC]
        · inext; iright; iexact HC
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "v") (Val.int 42) [] _ _
          (heval := by agar_eval))
        ipure_intro; right; rfl

end Agar.Logic

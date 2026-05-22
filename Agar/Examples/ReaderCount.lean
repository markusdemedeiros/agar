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

A single forked worker does `acquireRead` (`cas c 0 1`) then
`releaseRead` (`cas c 1 0`) against a binary-semaphore invariant `rcInv`
(`c ↦ 0 ∨ c ↦ 1`). Safety only; an Auth(Nat) ghost could later track
the acquire/release balance. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

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

/-! ## Worker thread spec — acquire then release, 2×2 case analysis on
the open disjunct vs which CAS direction will succeed. No ghost; both
CASes can fail under interleaving, the failure side re-closes from heap. -/

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
  wp_pures
  -- Acquire (CAS 0→1).
  wp_cas_atomic_split HI (rcInv GF F cLoc)
    (Val.int 0) (Val.int 1) (val_beq_int_false 0)
    with (>HC0 | >HC1)
  · cas_succeed_with (Val.int 0) HC0
    · inv_close_right HC1
      -- Release (CAS 1→0). Another thread may have toggled `c` between
      -- acquire and release, so this open can land in either disjunct.
      wp_pures
      wp_cas_atomic_split HI (rcInv GF F cLoc)
        (Val.int 1) (Val.int 0) (val_beq_int_false 1)
        with (>HC0 | >HC1)
      · cas_fail_with (Val.int 0) HC0
        · cas_dead
        · inv_close_left HC0; wp_done
      · cas_succeed_with (Val.int 1) HC1
        · inv_close_left HC0; wp_done
        · cas_dead
    · cas_dead
  · cas_fail_with (Val.int 1) HC1
    · cas_dead
    · inv_close_right HC1
      wp_pures
      wp_cas_atomic_split HI (rcInv GF F cLoc)
        (Val.int 1) (Val.int 0) (val_beq_int_false 1)
        with (>HC0 | >HC1)
      · cas_fail_with (Val.int 0) HC0
        · cas_dead
        · inv_close_left HC0; wp_done
      · cas_succeed_with (Val.int 1) HC1
        · inv_close_left HC0; wp_done
        · cas_dead

theorem progReaderCount_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progReaderCount (· = Val.unit) := by
  adequacy_with_heap_intro progReaderCount Val.unit
  wp_pures
  wp_alloc_intro cLoc' HPC
  wp_pures
  inv_alloc_left (rcInv GF F cLoc') HPC
  wp_fork_emp "readerCountProc" [Expr.var "c"] readerCountProc [Val.loc _] []
  isplitr
  · iintro !>
    iapply readerCountProc_wp_body
    iexact HI
  · iintro !>
    wp_done

end Agar.Logic

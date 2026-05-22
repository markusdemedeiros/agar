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

@[expose] public section

/-! # Invariant examples: `inv N P` for shared-heap reasoning

Four closed adequacy proofs that exercise Iris invariants of shape
`inv N (∃ v, l ↦ v)` and its disjunctive variants:

* `progInvLoad` — single thread, single invariant-mediated load.
* `progSharedFlag` — parent + forked writer share an invariant on `l`.
* `progSharedRead` — parent + forked reader, both consume the invariant
  via `wp_load_inv`.
* `progCasFlip` — CAS over a two-state disjunctive invariant.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-! ## `progInvLoad` — single-thread invariant-mediated load -/

def progInvLoad : Program where
  procs := fun _ => none
  main  := ags(
    x := alloc 42 ;
    v := load x
  )

theorem progInvLoad_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progInvLoad n
            (Machine.initial progInvLoad) μ') :
    Machine.Adequate progInvLoad μ' Val.unit := by
  adequacy_with_heap_intro progInvLoad Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_steps
  wp_inv_alloc_pt HP HI 42
  iapply wp_load_inv (GF := GF) (F := F) (N := nroot)
    (Hsub := by rw [nclose_root])
    (heval := by agar_eval)
  iframe HI
  iintro !> %v HP
  iframe HP
  wp_done

/-! ## `progSharedFlag` — main + forked writer through `inv N (∃ v, l↦v)` -/

def writeOne : Proc where
  params := ["l"]
  body   := ags( store l 1 )

def progSharedFlag : Program where
  procs := fun n => if n = "writeOne" then some writeOne else none
  main  := ags(
    x := alloc 0 ;
    fork writeOne(x)
  )

theorem progSharedFlag_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSharedFlag n
            (Machine.initial progSharedFlag) μ') :
    Machine.Adequate progSharedFlag μ' Val.unit := by
  adequacy_with_heap_intro progSharedFlag Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_pures
  wp_inv_alloc_pt HP HI 0
  wp_fork_emp "writeOne" [Expr.var "x"] writeOne [Val.loc _] []
  isplitr
  · iintro !>
    unfold writeOne
    iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
      (P := iprop(∃ v : Val, points_to (GF := GF) (F := F) _ v))
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    iintro HP
    icases HP with ⟨%vcur, >HLk⟩
    imodintro
    iexists vcur
    iframe HLk
    iintro HLk
    imodintro
    isplitl [HLk]
    · inext; iexists (Val.int 1); iexact HLk
    wp_done
  · iintro !>
    wp_done

/-! ## `progSharedRead` — both threads `wp_load_inv` through one invariant -/

def readerProc : Proc where
  params := ["l"]
  body   := ags( v := load l )

def progSharedRead : Program where
  procs := fun n => if n = "readerProc" then some readerProc else none
  main  := ags(
    x := alloc 42 ;
    fork readerProc(x) ;
    w := load x
  )

theorem progSharedRead_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSharedRead n
            (Machine.initial progSharedRead) μ') :
    Machine.Adequate progSharedRead μ' Val.unit := by
  adequacy_with_heap_intro progSharedRead Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_pures
  wp_inv_alloc_pt HP HI 42
  wp_fork_emp "readerProc" [Expr.var "x"] readerProc [Val.loc _]
    [Stmt.load "w" (Expr.var "x")]
  isplitr
  · iintro !>
    unfold readerProc
    iapply wp_load_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heval := by agar_eval)
    iframe HI
    iintro !> %v HP
    iframe HP
    wp_done
  · wp_pures
    iapply wp_load_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heval := by agar_eval)
    iframe HI
    iintro !> %v HP
    iframe HP
    wp_done

/-! ## `progCasFlip` — single CAS over `(x↦0) ∨ (x↦1)` -/

def progCasFlip : Program where
  procs := fun _ => none
  main  := ags(
    x := alloc 0 ;
    r := cas x 0 1
  )

theorem progCasFlip_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCasFlip n
            (Machine.initial progCasFlip) μ') :
    Machine.Adequate progCasFlip μ' Val.unit := by
  adequacy_with_heap_intro progCasFlip Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_steps
  inv_alloc_left
    iprop(points_to (GF := GF) (F := F) l (Val.int 0)
          ∨ points_to (GF := GF) (F := F) l (Val.int 1)) HP
  wp_cas_atomic_split HI
    iprop(points_to (GF := GF) (F := F) l (Val.int 0)
          ∨ points_to (GF := GF) (F := F) l (Val.int 1))
    (Val.int 0) (Val.int 1)
    (val_beq_int_false 0)
    with (>HLk0 | >HLk1)
  · cas_succeed_with (Val.int 0) HLk0
    · inv_close_right HLk1'; wp_done
    · cas_dead
  · -- Disjunct 2: l ↦ 1. CAS fails.
    cas_fail_with (Val.int 1) HLk1
    · cas_dead
    · inv_close_right HLk1'; wp_done   -- re-close RIGHT with heap we read

end Agar.Logic

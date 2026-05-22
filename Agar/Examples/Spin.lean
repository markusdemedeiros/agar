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

/-! # `progSpinFlag` — `wp_load_atomic` + a degenerate `whileDo`

Parent loads a shared flag through `wp_load_atomic`, then sets `done := 1`
to force a static loop exit. The loop is statically known to exit on the
first iteration, so we route through `wp_spin_fixed_env` rather than
`wp_spin` (whose `∀ env` quantifier can't match the fixed post-loop env).
Adequacy at `Val.unit`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

def setterProc : Proc where
  params := ["flag"]
  body   := ags( store flag 1 )

def progSpinFlag : Program where
  procs := fun n => if n = "setterProc" then some setterProc else none
  main  := ags(
    flag := alloc 0 ;
    fork setterProc(flag) ;
    v    := load flag ;
    done := 1 ;
    while done = 0 do skip
  )

theorem progSpinFlag_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSpinFlag n
            (Machine.initial progSpinFlag) μ') :
    Machine.Adequate progSpinFlag μ' Val.unit := by
  adequacy_with_heap_intro progSpinFlag Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_pures
  wp_inv_alloc_pt HP HI 0
  wp_fork_emp "setterProc" [Expr.var "flag"] setterProc [Val.loc _]
    [ags(v := load flag ; done := 1 ; while done = 0 do skip)]
  isplitr
  · iintro !>
    unfold setterProc
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    iintro !>
    wp_done
  · wp_pures
    wp_load_atomic_open HI (by agar_eval)
    wp_pures_no_loop
    -- `done = 1` makes the guard statically false: instantiate J := emp
    -- and route through `wp_spin_fixed_env`.
    iapply (wp_spin_fixed_env _ _ _ _ _ _ _ iprop(emp : IProp GF) _
      (HSpec := ?Hspec))
    case Hspec =>
      iintro ⟨_HIH, _Hemp⟩
      inext
      iapply wp_ite_false (heval := by agar_eval)
      iintro !>
      wp_done
    · iemp_intro

/-! ## `progChanSpin` — genuinely spinning recv on a shared flag

A setter writes `1` to a shared flag; the parent spins
`while done = 0 do (f := load flag ; if f = 1 then done := 1 else skip)`
through `wp_spin` with `J env := ∃ b, eval env (done = 0) = some (.bool b)`
— witnesses the guard's Boolean value at any env, which makes the
post-body re-establishment decidable. Adequacy at `Val.unit`. -/

def chanSpinSetterProc : Proc where
  params := ["flag"]
  body   := ags( store flag 1 )

def progChanSpin : Program where
  procs := fun n => if n = "chanSpinSetterProc" then some chanSpinSetterProc else none
  main  := ags(
    flag := alloc 0 ;
    fork chanSpinSetterProc(flag) ;
    done := 0 ;
    while done = 0 do (
      f := load flag ;
      if f = 1 then done := 1 else skip
    )
  )

theorem progChanSpin_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progChanSpin n
            (Machine.initial progChanSpin) μ') :
    Machine.Adequate progChanSpin μ' Val.unit := by
  adequacy_with_heap_intro progChanSpin Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_pures
  wp_inv_alloc_pt HP HI 0
  wp_fork_emp "chanSpinSetterProc" [Expr.var "flag"] chanSpinSetterProc [Val.loc _]
    [ags(done := 0 ; while done = 0 do (
        f := load flag ;
        if f = 1 then done := 1 else skip
      ))]
  isplitr
  · iintro !>
    unfold chanSpinSetterProc
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    iintro !>
    wp_done
  · iintro !>
    wp_pures_no_loop
    iapply (wp_spin (GF := GF) _ _ _ _ _ _ _
      (J := fun env =>
        iprop(inv nroot (∃ v : Val, points_to (GF := GF) (F := F) l v) ∗
          ∃ b : Bool,
          ⌜Expr.eval env
            (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
            = some (.bool b) ∧
            Expr.eval env (Expr.var "flag") = some (.loc l)⌝)) _
      (HSpec := fun env => ?Hspec))
    case Hspec =>
      iintro ⟨HIH, ⟨#HI, HJ⟩⟩
      inext
      icases HJ with ⟨%b, %hpure⟩
      obtain ⟨hev, hflag⟩ := hpure
      cases b with
      | false =>
        iapply wp_ite_false (heval := hev)
        iintro !>
        wp_done
      | true =>
        iapply wp_ite_true (heval := hev)
        wp_pures
        wp_load_atomic_open HI hflag
        wp_lstep
        by_cases hvcur : vcur = Val.int 1
        · iapply wp_ite_true (heval := by subst hvcur; agar_eval)
          iintro !>
          iapply wp_assign (heval := by agar_eval)
          iintro !>
          wp_lstep
          ihave HIH := HIH $$ %((env.set "f" vcur).set "done" (Val.int 1))
          iapply HIH
          isplitl []
          · iexact HI
          iexists false
          ipure_intro
          refine ⟨?_, ?_⟩
          · agar_eval
          · simpa [agar_eval] using hflag
        · iapply wp_ite_false
            (heval := by
              have hbeq := val_beq_int_false 1 vcur hvcur
              simp [agar_eval, hbeq])
          iintro !>
          wp_lstep
          ihave HIH := HIH $$ %(env.set "f" vcur)
          iapply HIH
          isplitl []
          · iexact HI
          iexists true
          ipure_intro
          refine ⟨?_, ?_⟩
          · simpa [agar_eval] using hev
          · simpa [agar_eval] using hflag
    · -- Initial J at env_loop: guard `done = 0` is true, flag points at l.
      isplitl []
      · iexact HI
      iexists true
      ipure_intro
      refine ⟨?_, ?_⟩
      · agar_eval
      · agar_eval

/-! ## `progCasRetry` — single-thread CAS-retry via `wp_spin_invariant`

Single-thread one-shot retry: `while done = 0 do (prev := load c ; done := 1)`.
Body changes the env between iterations (new `prev`, `done`), which `wp_spin`'s
∀-env IH cannot directly thread; `wp_spin_invariant` factors the loop into
HGuard / HBody / HExit specs so each picks up the post-body env. `I` holds
the heap fragment inline (no `inv` — single-threaded) and witnesses the
guard's Boolean value at every env. -/

def progCasRetry : Program where
  procs := fun _ => none
  main  := ags(
    c := alloc 0 ;
    done := 0 ;
    while done = 0 do (
      prev := load c ;
      done := 1
    )
  )

theorem progCasRetry_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCasRetry n
            (Machine.initial progCasRetry) μ') :
    Machine.Adequate progCasRetry μ' Val.unit := by
  adequacy_with_heap_intro progCasRetry Val.unit
  wp_pures
  wp_alloc_intro HP
  wp_pures_no_loop
  iapply (wp_spin_invariant (GF := GF) _ _ _ _ _ _ _
    (I := fun env =>
      iprop(points_to (GF := GF) (F := F) l (Val.int 0) ∗
        ⌜Expr.eval env (Expr.var "c") = some (.loc l) ∧
          ∃ b : Bool, Expr.eval env
            (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
            = some (.bool b)⌝))
    _
    (HGuard := fun env => ?HGuard)
    (HBody := fun env => ?HBody)
    (HExit := fun env => ?HExit))
  case HGuard =>
    istart
    iintro ⟨HP', %hpure⟩
    isplitl [HP']
    · isplitl [HP']
      · iexact HP'
      · ipure_intro; exact hpure
    · ipure_intro; exact hpure.2
  case HBody =>
    iintro ⟨HIH, ⟨%_hgtrue, ⟨HP', %hpure⟩⟩⟩
    have hflag := hpure.1
    wp_pures
    wp_load_direct HP' hflag
    wp_pures_no_loop
    ihave HIH := HIH $$ %((env.set "prev" (Val.int 0)).set "done" (Val.int 1))
    iapply HIH
    isplitl [HP']
    · iexact HP'
    ipure_intro
    refine ⟨?_, false, ?_⟩
    · simpa [agar_eval] using hflag
    · agar_eval
  case HExit =>
    iintro ⟨%_hgfalse, ⟨_HP', %_hpure⟩⟩
    wp_done
  · -- Initial I at env_loop = (env.set "c" l).set "done" 0:
    -- `c` evaluates to l; the guard `done = 0` evaluates to `some (.bool true)`.
    isplitl [HP]
    · iexact HP
    ipure_intro
    refine ⟨?_, true, ?_⟩
    · agar_eval
    · agar_eval

end Agar.Logic

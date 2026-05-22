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

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## Peterson's algorithm — SHAPE-only safety proof

Peterson's classical 2-thread mutex uses three shared cells `flag0`,
`flag1`, `turn`. Thread `i` enters via:
`store flag[i] 1 ; store turn (1-i) ; while flag[1-i]=1 && turn=1-i do skip ;
... CS ... ; store flag[i] 0`.

We prove the **Peterson SHAPE**: two threads concurrently running this
entry-sequence template against shared-cell invariants on all three
locations. Closed adequacy yields safety + main returns `Val.unit`.

We do **not** prove (a) mutual exclusion — that requires ghost state
for CS ownership and a Peterson-specific argument about flag/turn
interleaving, out of session scope; (b) dynamic loop-exit — adequacy
is purely safety; (c) the literal spin guard — the proof's spin body
checks only `flag[1-i] = 0`, not the `&& turn = 1-i` conjunction;
adding the second load is mechanical but balloons env-reasoning.

The Löb invariant `J` carries the two flag invariants plus per-env
pure facts pinning `myF`/`oF` to the right locations and the guard's
Boolean evaluability across the body's env updates. -/

/-- Peterson worker procedure. Parameters: `myF` (my flag cell),
`oF` (other thread's flag cell), `t` (turn cell), `oId` (other id; for
the turn store). The spin body is simplified (see file docstring): it
only checks `oF = 0`, not the full Peterson conjunction. -/
def petersonProc : Proc where
  params := ["myF", "oF", "t", "oId"]
  body := ags(
    store myF 1 ;
    store t oId ;
    done := 0 ;
    { while done = 0 do {
      f := load oF ;
      if f = 0 then done := 1 else skip
    } } ;
    store myF 0
  )

/-- The Peterson program: allocate `flag0`, `flag1`, `turn`, fork two
workers with swapped arguments, fall through. -/
def progPeterson : Program where
  procs := fun n => if n = "petersonProc" then some petersonProc else none
  main  := ags(
    flag0 := alloc 0 ;
    flag1 := alloc 0 ;
    turn  := alloc 0 ;
    fork petersonProc(flag0, flag1, turn, 1) ;
    fork petersonProc(flag1, flag0, turn, 0)
  )

/-- WP for one worker, parametric in `(myFLoc, oFLoc, tLoc, oId)`. The
three invariants `HIm`, `HIo`, `HIt` cover `myF`, `oF`, `t` respectively
(all persistent). Closes at `fork_post := emp`. -/
private theorem petersonProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (myFLoc oFLoc tLoc : Loc) (oId : Int) :
    iprop(inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) myFLoc v) ∗
          inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) oFLoc v) ∗
          inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) tLoc v)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨petersonProc.body, [],
          bindParams petersonProc.params
            [Val.loc myFLoc, Val.loc oFLoc, Val.loc tLoc, Val.int oId],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro ⟨#HIm, #HIo, #HIt⟩
  unfold petersonProc
  -- store myF 1
  wp_pures
  iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
    (Hsub := by rw [nclose_root])
    (heL := by agar_eval) (heV := by agar_eval)
  iframe HIm
  iintro !>
  -- store t oId
  wp_pures
  iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
    (Hsub := by rw [nclose_root])
    (heL := by agar_eval) (heV := by agar_eval)
  iframe HIt
  iintro !>
  -- done := 0, then spin while done = 0 do (load oF, branch).
  wp_pures_no_loop
  iapply (wp_spin (GF := GF) _ _ _ _ _ _ _
    (J := fun env =>
      iprop(inv nroot (∃ v : Val, points_to (GF := GF) (F := F) myFLoc v) ∗
        inv nroot (∃ v : Val, points_to (GF := GF) (F := F) oFLoc v) ∗
        ∃ b : Bool,
        ⌜Expr.eval env
          (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
          = some (.bool b) ∧
          Expr.eval env (Expr.var "oF") = some (.loc oFLoc) ∧
          Expr.eval env (Expr.var "myF") = some (.loc myFLoc)⌝)) _
    (HSpec := fun env => ?Hspec))
  case Hspec =>
    iintro ⟨HIH, ⟨#HImLoop, #HIoLoop, HJ⟩⟩
    inext
    icases HJ with ⟨%b, %hpure⟩
    obtain ⟨hev, hoF, hmyF⟩ := hpure
    cases b with
    | false =>
      -- Exit: clear `myF` (release our interest claim).
      iapply wp_ite_false (heval := hev)
      iintro !>
      wp_pures
      iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
        (Hsub := by rw [nclose_root])
        (heL := hmyF) (heV := by agar_eval)
      iframe HImLoop
      iintro !>
      wp_done
    | true =>
      iapply wp_ite_true (heval := hev)
      iintro !>
      iapply wp_seq
      iintro !>
      iapply wp_seq
      iintro !>
      wp_load_atomic_open HIoLoop hoF
      wp_lstep
      by_cases hvcur : vcur = Val.int 0
      · -- Observed `oF = 0` → exit the spin via `done := 1`.
        iapply wp_ite_true (heval := by subst hvcur; agar_eval)
        iintro !>
        iapply wp_assign (heval := by agar_eval)
        iintro !>
        wp_lstep
        ihave HIH := HIH $$ %((env.set "f" vcur).set "done" (Val.int 1))
        iapply HIH
        isplitl []
        · iexact HImLoop
        isplitl []
        · iexact HIoLoop
        iexists false
        ipure_intro
        refine ⟨?_, ?_, ?_⟩
        · agar_eval
        · simpa [agar_eval] using hoF
        · simpa [agar_eval] using hmyF
      · -- Observed `oF ≠ 0` → keep spinning.
        iapply wp_ite_false
          (heval := by
            have hbeq := val_beq_int_false 0 vcur hvcur
            simp [agar_eval, hbeq])
        iintro !>
        wp_lstep
        ihave HIH := HIH $$ %(env.set "f" vcur)
        iapply HIH
        isplitl []
        · iexact HImLoop
        isplitl []
        · iexact HIoLoop
        iexists true
        ipure_intro
        refine ⟨?_, ?_, ?_⟩
        · -- `f` ≠ `done`, so the guard's evaluation is invariant under the set.
          simpa [agar_eval] using hev
        · simpa [agar_eval] using hoF
        · simpa [agar_eval] using hmyF
  · -- Initial J at loop entry: done = 0, guard true; oF bound to oFLoc; myF to myFLoc.
    isplitl []
    · iexact HIm
    isplitl []
    · iexact HIo
    iexists true
    ipure_intro
    refine ⟨?_, ?_, ?_⟩
    · agar_eval
    · agar_eval
    · agar_eval

theorem progPeterson_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progPeterson (· = Val.unit) := by
  adequacy_with_heap_intro progPeterson Val.unit
  wp_pures                                      -- wp_seq
  wp_alloc_intro HP0                            -- HP0 : f0Loc ↦ 0
  wp_pures                                      -- skip_cons; seq
  wp_alloc_intro HP1                            -- HP1 : f1Loc ↦ 0
  wp_pures                                      -- skip_cons; seq
  wp_alloc_intro HPT                            -- HPT : tLoc ↦ 0
  wp_pures                                      -- skip_cons; seq exposing first fork
  wp_inv_alloc_pt HP0 HI0 0
  wp_inv_alloc_pt HP1 HI1 0
  wp_inv_alloc_pt HPT HIT 0
  wp_fork_emp "petersonProc"
    [Expr.var "flag0", Expr.var "flag1", Expr.var "turn", Expr.val (Val.int 1)]
    petersonProc [Val.loc _, Val.loc _, Val.loc _, Val.int 1]
    [Stmt.fork "petersonProc"
      [Expr.var "flag1", Expr.var "flag0", Expr.var "turn",
        Expr.val (Val.int 0)]]
  isplitr
  · -- Worker 0: myF=flag0, oF=flag1, t=turn.
    iintro !>
    iapply petersonProc_wp_body
    iframe HI0 HI1 HIT
  · iintro !>
    wp_pures
    wp_fork_emp "petersonProc"
      [Expr.var "flag1", Expr.var "flag0", Expr.var "turn", Expr.val (Val.int 0)]
      petersonProc [Val.loc _, Val.loc _, Val.loc _, Val.int 0] []
    isplitr
    · -- Worker 1: myF=flag1, oF=flag0, t=turn.
      iintro !>
      iapply petersonProc_wp_body
      iframe HI1 HI0 HIT
    · iintro !>
      wp_done

end Agar.Logic

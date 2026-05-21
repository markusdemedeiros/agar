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
  -- Body sequencing: store myF 1 ; store t oId ; done := 0 ; while ... ; store myF 0
  -- 1. store myF 1
  wp_step                                       -- wp_seq
  iintro !>
  iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
    (Hsub := by rw [nclose_root])
    (heL := by agar_eval) (heV := by agar_eval)
  iframe HIm
  iintro !>
  -- 2. store t oId
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq
  iintro !>
  iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
    (Hsub := by rw [nclose_root])
    (heL := by agar_eval) (heV := by agar_eval)
  iframe HIt
  iintro !>
  -- 3. done := 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq
  iintro !>
  wp_step                                       -- wp_assign
  iintro !>
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq (expose `while`; cont gets `store myF 0`)
  iintro !>
  -- 4. while done = 0 do (f := load oF ; if f = 0 then done := 1 else skip)
  -- Goal: wp ⟨whileDo (done=0) body, [store myF 0], env_loop, [], none⟩.
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
      -- Guard false: exit; then `store myF 0`.
      iapply wp_ite_false (heval := hev)
      iintro !>
      wp_step                                   -- wp_skip_cons (skip :: [store myF 0])
      iintro !>
      iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
        (Hsub := by rw [nclose_root])
        (heL := hmyF) (heV := by agar_eval)
      iframe HImLoop
      iintro !>
      wp_done
    | true =>
      -- Guard true: unroll body, atomic-load oF, branch.
      iapply wp_ite_true (heval := hev)
      iintro !>
      iapply wp_seq
      iintro !>
      -- body = (f := load oF) ; (if f = 0 then done := 1 else skip)
      iapply wp_seq
      iintro !>
      iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
        (P := iprop(∃ v : Val, points_to (GF := GF) (F := F) _ v))
        (Hsub := by rw [nclose_root])
        (heL := hoF)
      iframe HIoLoop
      iintro >⟨%vcur, HP⟩
      imodintro
      iexists vcur
      isplitl [HP]
      · iexact HP
      iintro HP
      imodintro
      isplitl [HP]
      · inext; iexists vcur; iexact HP
      wp_step                                   -- wp_skip_cons
      iintro !>
      -- Branch on whether vcur = Val.int 0.
      by_cases hvcur : vcur = Val.int 0
      · -- then-branch: done := 1
        iapply wp_ite_true
          (heval := by
            subst hvcur
            show Expr.eval _ _ = _
            simp [agar_eval]
            show (Val.int 0 == Val.int 0) = true
            exact val_beq_refl _)
        iintro !>
        iapply wp_assign (heval := by agar_eval)
        iintro !>
        wp_step                                 -- wp_skip_cons
        iintro !>
        -- Re-enter loop with J at env_new (done := 1, guard false).
        ihave HIH := HIH $$ %((env.set "f" vcur).set "done" (Val.int 1))
        iapply HIH
        isplitl []
        · iexact HImLoop
        isplitl []
        · iexact HIoLoop
        iexists false
        ipure_intro
        refine ⟨?_, ?_, ?_⟩
        · show Expr.eval _ _ = _
          simp [agar_eval]
          show Val.beq (.int 1) (.int 0) = false
          rfl
        · show Expr.eval _ _ = _
          show Env.set _ _ _ "oF" = _
          simp [agar_eval]
          show Expr.eval env (Expr.var "oF") = _
          exact hoF
        · show Expr.eval _ _ = _
          show Env.set _ _ _ "myF" = _
          simp [agar_eval]
          show Env.set env "f" vcur "myF" = _
          simp [agar_eval]
          show Expr.eval env (Expr.var "myF") = _
          exact hmyF
      · -- else-branch: skip
        iapply wp_ite_false
          (heval := by
            show Expr.eval _ _ = _
            simp [Expr.eval, Env.set]
            cases vcur with
            | int i =>
                have hne : i ≠ 0 := fun h => hvcur (by cases h; rfl)
                show BinOp.eval BinOp.eq (Val.int i) (Val.int 0) = some (Val.bool false)
                show some (Val.bool (Val.beq (.int i) (.int 0))) = _
                show some (Val.bool (i == 0)) = _
                have : (i == 0) = false := by simp [hne]
                rw [this]
            | bool _ => rfl
            | loc _ => rfl
            | unit => rfl
            | struct _ => rfl)
        iintro !>
        wp_step                                 -- wp_skip_cons
        iintro !>
        -- Re-enter loop with J at env_new (done unchanged, guard true).
        ihave HIH := HIH $$ %(env.set "f" vcur)
        iapply HIH
        isplitl []
        · iexact HImLoop
        isplitl []
        · iexact HIoLoop
        iexists true
        ipure_intro
        refine ⟨?_, ?_, ?_⟩
        · show Expr.eval _ _ = _
          have h1 : (Env.set env "f" vcur) "done" = env "done" := by
            simp [agar_eval]
          have h2 : Expr.eval (Env.set env "f" vcur)
              (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
              = Expr.eval env
                  (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0))) := by
            show (((Env.set env "f" vcur) "done").bind _) = _
            rw [h1]; rfl
          rw [h2]; exact hev
        · show Expr.eval _ _ = _
          show Env.set _ _ _ "oF" = _
          simp [agar_eval]
          exact hoF
        · show Expr.eval _ _ = _
          show Env.set _ _ _ "myF" = _
          simp [agar_eval]
          exact hmyF
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
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progPeterson n
            (Machine.initial progPeterson) μ') :
    Machine.Adequate progPeterson μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progPeterson ?_ n μ' htr
  start_closed_proof_with_heap progPeterson
  -- main := alloc flag0 0 ; alloc flag1 0 ; alloc turn 0 ; fork worker0 ; fork worker1
  wp_pures                                      -- wp_seq
  wp_alloc_intro HP0                            -- HP0 : f0Loc ↦ 0
  wp_pures                                      -- skip_cons; seq
  wp_alloc_intro HP1                            -- HP1 : f1Loc ↦ 0
  wp_pures                                      -- skip_cons; seq
  wp_alloc_intro HPT                            -- HPT : tLoc ↦ 0
  wp_pures                                      -- skip_cons; seq exposing first fork
  -- Allocate the three invariants before the first fork; demote all.
  wp_inv_alloc_pt HP0 HI0 0
  wp_inv_alloc_pt HP1 HI1 0
  wp_inv_alloc_pt HPT HIT 0
  ihave #HI0 := HI0
  ihave #HI1 := HI1
  ihave #HIT := HIT
  -- First fork: petersonProc(flag0, flag1, turn, 1)
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "petersonProc"
    [Expr.var "flag0", Expr.var "flag1", Expr.var "turn",
      Expr.val (Val.int 1)] petersonProc
    [Val.loc _, Val.loc _, Val.loc _, Val.int 1]
    [Stmt.fork "petersonProc"
      [Expr.var "flag1", Expr.var "flag0", Expr.var "turn",
        Expr.val (Val.int 0)]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Worker 0: myF=flag0, oF=flag1, t=turn.
    iintro !>
    iapply petersonProc_wp_body
    iframe HI0 HI1 HIT
  · iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    -- Second fork: petersonProc(flag1, flag0, turn, 0)
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "petersonProc"
      [Expr.var "flag1", Expr.var "flag0", Expr.var "turn",
        Expr.val (Val.int 0)] petersonProc
      [Val.loc _, Val.loc _, Val.loc _, Val.int 0]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · -- Worker 1: myF=flag1, oF=flag0, t=turn.
      iintro !>
      iapply petersonProc_wp_body
      iframe HI1 HI0 HIT
    · iintro !>
      wp_done

end Agar.Logic

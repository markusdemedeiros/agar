module

public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Adequacy
public import Agar.Iris.Completeness

@[expose] public section

/-! # Callee-frame WP bridge (Route B)

This file provides `wp_callee_of_pure_helper`: the residual obligation
left by `wp_call` (a wp on the helper body running at a non-empty stack
under the *composite*'s `procs`) is dischargeable from the helper's
denotational identity plus the caller's continuation wp at the
post-doReturn state.

The implementation strategy is **B1 (manual stepping)**: we lift the
operational `PureSteps` chain (`BodyTraj.pure_steps_to_near_end`) one
step at a time through `wp_pure_step`, and then `pstep_near_end_pop`
fires the doReturn step.

The key technical lemma is `wp_of_pstep`: a pure step (in the sense
of `pstep`) lifts to a wp-step under *any* `procs`. This is the Iris
analogue of the operational procs-irrelevance `pstep_tstep_procs`. -/

namespace Agar
open Agar.Logic
namespace CalleeBridge

open Iris Iris.BI Iris.OFE

section
variable {GF : BundledGFunctors.{0,0,0}}
variable {F : Type _} [UFraction F]
variable [InvGS_gen false GF]

/-! ## A pstep that succeeds lifts to a `wp_pure_step` under any procs. -/

/-- `pstep` success rules out `.alloc` (which requires a nondeterministic
location, supplied via `chosen = some l`, but pstep uses `chosen = none`). -/
theorem pstep_some_not_alloc {t t' : Thread} (h : pstep t = some t') :
    ∀ x e, t.stmt ≠ .alloc x e := by
  intro x e habs
  unfold pstep at h
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  cases habs
  simp [tstep] at h

/-- Any `pstep` success forces `t.terminated = false`: pstep on a
terminated thread `(.skip, [], _, [], _)` yields `none`. -/
theorem pstep_some_not_terminated {t t' : Thread} (h : pstep t = some t') :
    t.terminated = false := by
  unfold pstep at h
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  cases stmt <;> try (simp [Thread.terminated]; done)
  -- For `.skip`: the terminated case is `cont = [] ∧ stack = []`, but in
  -- that case `tstep noProcs none Mem.empty ... = none`, contradicting `h`.
  cases cont with
  | nil =>
      cases stack with
      | nil =>
          simp [tstep] at h
      | cons _ _ =>
          simp [Thread.terminated]
  | cons _ _ =>
      simp [Thread.terminated]

/-- **Iris-level procs-irrelevance for one pure step.** If `pstep t =
some t'`, then under *any* `procs` the same step lifts via
`wp_pure_step`. The proof handles the `chosen = some _` determinism
case by ruling out `.alloc` (which is what pstep success forbids). -/
theorem wp_of_pstep [AgarG GF F]
    (procs : Name → Option Proc) (fp : IProp GF)
    (t t' : Thread) (Φ : Val → IProp GF)
    (hp : pstep t = some t') :
    ▷ wp procs fp (⊤ : CoPset) t' Φ ⊢ wp procs fp ⊤ t Φ := by
  refine wp_pure_step (procs := procs) (fork_post := fp) (E := ⊤) t t' Φ
    (pstep_some_not_terminated hp) ?_ ?_
  · intro m
    refine ⟨m, none, ?_⟩
    exact ⟨none, BodyTraj.pstep_tstep_procs procs m t t' hp⟩
  · intro m m'' t'' sp hstep
    obtain ⟨chosen, hstep'⟩ := hstep
    cases chosen with
    | some l =>
        -- For `chosen = some l`, `tstep` only succeeds on `.alloc x e`,
        -- but pstep success rules out `.alloc`.
        exfalso
        have hnot_alloc := pstep_some_not_alloc hp
        unfold tstep at hstep'
        obtain ⟨stmt, cont, env, stack, result⟩ := t
        match h_stmt : stmt with
        | .alloc x e => exact hnot_alloc x e rfl
        | .skip => simp [h_stmt] at hstep'
        | .seq _ _ => simp [h_stmt] at hstep'
        | .assign _ _ => simp [h_stmt] at hstep'
        | .ite _ _ _ => simp [h_stmt] at hstep'
        | .whileDo _ _ => simp [h_stmt] at hstep'
        | .load _ _ => simp [h_stmt] at hstep'
        | .store _ _ => simp [h_stmt] at hstep'
        | .free _ => simp [h_stmt] at hstep'
        | .cas _ _ _ _ => simp [h_stmt] at hstep'
        | .call _ _ _ => simp [h_stmt] at hstep'
        | .ret _ => simp [h_stmt] at hstep'
        | .fork _ _ => simp [h_stmt] at hstep'
    | none =>
        have hpdet := BodyTraj.pstep_tstep_procs procs m t t' hp
        rw [hpdet] at hstep'
        cases hstep'
        exact ⟨rfl, rfl, rfl⟩

/-- **Body-pure-chain lift.** A `PureSteps` chain from `t` to `t'`
lifts to a wp implication under any `procs`. We absorb the `▷`s
introduced by `wp_of_pstep` via `BI.later_intro`. -/
theorem wp_of_pure_steps [AgarG GF F]
    (procs : Name → Option Proc) (fp : IProp GF)
    (Φ : Val → IProp GF) :
    ∀ {t t' : Thread}, PureSteps t t' →
      wp procs fp ⊤ t' Φ ⊢ wp procs fp ⊤ t Φ := by
  intro t t' h
  induction h with
  | refl =>
      iintro H; iexact H
  | @step t1 t2 _ hstep _ ih =>
      iintro H
      iapply wp_of_pstep procs fp t1 t2 Φ hstep
      iapply BI.later_intro
      iapply ih
      iexact H

/-! ## The bridge lemma -/

/-- **Callee-frame wp from a pure helper's denotational identity.**

Given:
* The helper proc `h` has structural shape `.seq (embed pureBody) (.ret retExpr)`.
* The pure body converges denotationally to some `ρ_f`, and `retExpr` evaluates
  to `v_h` in `ρ_f`.
* A continuation wp at the post-doReturn state.

Produce a wp at the body-start thread (which is what `wp_call` leaves
as a residual obligation).

The proof: `pure_steps_to_near_end` gives a `PureSteps` chain from the
body-start to the near-end `.ret retExpr` state; `wp_of_pure_steps`
lifts it to a wp implication; `pstep_near_end_pop` plus `wp_of_pstep`
fires the doReturn step into the caller's continuation.

This is the additive Route-B counterpart to Theorem 15: instead of
generalizing the closed-program adequacy, we provide a re-usable lemma
for the *callee-frame* shape that `wp_call` leaves behind. -/
theorem wp_callee_of_pure_helper [AgarG GF F]
    (composite : Program) (h : Proc)
    (pureBody : PureStmt) (retExpr : Expr)
    (h_body_eq : h.body = .seq (embed pureBody) (.ret retExpr))
    (vs : List Val) (x : Name) (cont : List Stmt) (env : Env) (stack : List Frame)
    (fp : IProp GF) (Φ : Val → IProp GF)
    (ρ_f : Env) (v_h : Val)
    (h_denote : denote pureBody (bindParams h.params vs) = (some (), ρ_f))
    (h_ret : Expr.eval ρ_f retExpr = some v_h) :
    wp composite.procs fp ⊤
      (BodyTraj.postDoReturnThread ⟨x, cont, env⟩ stack v_h) Φ
    ⊢ wp composite.procs fp ⊤
      ⟨h.body, [], bindParams h.params vs, ⟨x, cont, env⟩ :: stack, none⟩ Φ := by
  -- The pure body trajectory from body-start to the near-end .ret state.
  have hbody := BodyTraj.pure_steps_to_near_end pureBody retExpr
    (bindParams h.params vs) ρ_f ⟨x, cont, env⟩ stack h_denote
  -- The final .ret-pop step landing at postDoReturnThread.
  have hpop := BodyTraj.pstep_near_end_pop retExpr ρ_f v_h
    ⟨x, cont, env⟩ stack h_ret
  -- Rewire the starting thread shape via h_body_eq.
  rw [h_body_eq]
  -- Chain: body-start ──pure_steps──▶ near-end ──pstep──▶ post-frame.
  iintro Hcont
  iapply wp_of_pure_steps composite.procs fp Φ hbody
  iapply wp_of_pstep composite.procs fp _ _ Φ hpop
  iapply BI.later_intro
  iexact Hcont

end
end CalleeBridge
end Agar

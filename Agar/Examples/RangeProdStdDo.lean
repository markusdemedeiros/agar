module

public import Std.Do.Triple
public import Std.Do.WP
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Agar.Iris.PureHelperBridge
public import Agar.Examples.SimpleRangeProdComposition
public import Agar.Examples.SimpleRangeProdCompositionRouteA

@[expose] public section

/-! # `Std.Do`-style spec for the `rangeProd` helper

This file is the staging ground for the **pretty endpoint** of Route A:
a `Std.Do` Hoare triple over `denote (prodProg n)`, followed by the
chain that turns it into the operational `helper_safeTp` premise.

The triple itself is `sorry`-ed for now; the rest is the connective
tissue. -/

namespace Agar
open Agar.Logic
namespace SimpleRangeProd
open Std.Do

/-! ## The pretty endpoint

`denote (prodProg n)` runs the body of `rangeProd n` starting at an
environment where `"a"` is already bound. The post says it terminates
(`r = some ()`) with `"acc"` holding the closed-form product.

This is the spec a `Std.Do`-aware user would write and discharge with
`mvcgen` (plus a manual `forN` invariant for the loop). -/

theorem rangeProd_spec (n : Nat) (a : Int) :
    ⦃fun ρ : Env => ⌜ρ "a" = some (Val.int a)⌝⦄
    (show StateM Env (Option Unit) from denote (prodProg n))
    ⦃⇓ r => fun ρ' : Env =>
      ⌜r = some () ∧ ρ' "acc" = some (Val.int (rangeProdValue a n))⌝⦄ := by
  sorry

/-! ## Convergence corollary

The triple gives us the convergent-denotation form that the existing
pure-helper bridge consumes. -/

/-- The helper `rangeProd n` packaged as a `PureHelper`. -/
def rangeProdHelper (n : Nat) : PureHelper where
  body := prodProg n
  ret  := .var "acc"

/-- An initial env where `"a"` is bound to `Val.int a`. Matches
`bindParams ["a"] [Val.int a]`. -/
def env_with_a (a : Int) : Env := Env.empty.set "a" (.int a)

theorem env_with_a_eq_bindParams (a : Int) :
    env_with_a a = bindParams ["a"] [Val.int a] := by
  simp [env_with_a, bindParams]

/-- From the `Std.Do` triple, extract a convergent-denotation witness:
`denote (prodProg n) (env_with_a a) = (some (), ρ_f)` for some `ρ_f`
where `Expr.eval ρ_f (.var "acc") = some (.int (rangeProdValue a n))`. -/
theorem rangeProd_denote_converges (n : Nat) (a : Int) :
    ∃ ρ_f, denote (prodProg n) (env_with_a a) = (some (), ρ_f) ∧
      Expr.eval ρ_f (.var "acc") = some (Val.int (rangeProdValue a n)) := by
  -- Apply the spec at our specific initial env. The Std.Do triple
  -- unfolds to a pointwise statement: pre at s → post at (run m s).
  have hpre : (env_with_a a) "a" = some (Val.int a) := by
    simp [env_with_a, Env.set]
  have hpost := rangeProd_spec n a (env_with_a a) hpre
  -- `hpost` should give us `r = some () ∧ ρ' "acc" = some (Val.int ...)`
  -- where (r, ρ') = (denote (prodProg n)) (env_with_a a).
  obtain ⟨hr, hacc⟩ := hpost
  refine ⟨(denote (prodProg n) (env_with_a a)).2, ?_, ?_⟩
  · -- denote = (some (), ρ'_f)
    show denote (prodProg n) (env_with_a a)
      = (some (), (denote (prodProg n) (env_with_a a)).2)
    rw [← hr]
    rfl
  · -- Expr.eval ρ_f (.var "acc") = some (Val.int ...)
    simp [Expr.eval]
    exact hacc

/-- `denoteHelper`-shaped convergence, the precise input shape for
`Machine.safe_of_denoteHelper`. -/
theorem rangeProd_denoteHelper (n : Nat) (a : Int) :
    denoteHelper (rangeProdHelper n) (env_with_a a)
      = some (Val.int (rangeProdValue a n)) := by
  obtain ⟨ρ_f, hd, hv⟩ := rangeProd_denote_converges n a
  simp [denoteHelper, rangeProdHelper, hd]
  exact hv

/-! ## Bridge to `Machine.safe` of the standalone helper program

`Machine.safe_of_denoteHelper_total` consumes a parameterized-by-ρ₀
convergence witness. Specializing to the single-arg case, we feed in
`rangeProd_denote_converges` (after currying through `denoteHelper`). -/

/-- Standalone helper program at fixed `a` (parameters baked into `main`
via `assignAllParams`, not relevant here since we use `programOfHelper`
which starts from `Env.empty` and we have a per-`ρ₀` triple). -/
abbrev helperProg (n : Nat) : Program := programOfHelper (rangeProdHelper n)

/-- `helper_init n a` is a `HelperThread`: the stmt is the helper's
seq-of-embed-and-ret shape, and the cont/stack are empty. -/
theorem helper_init_helperThread (n : Nat) (a : Int) :
    HelperThread (helper_init n a) := by
  refine ⟨?_, ?_, rfl⟩
  · -- HelperShape ((rangeProd n).body)
    change HelperShape (.seq (embed (prodProg n)) (.ret (.var "acc")))
    exact .seq _ _ (embedShape_helperShape (embed_embedShape _)) (.ret _)
  · intro s hmem; cases hmem

/-- The full pure-step trajectory from `helper_init n a` to the
terminated state at value `Val.int (rangeProdValue a n)`. -/
theorem helper_init_reaches_terminal (n : Nat) (a : Int) :
    PureSteps (helper_init n a)
      (helperTerminal
        ((denote (prodProg n) (env_with_a a)).2)
        (Val.int (rangeProdValue a n))) := by
  obtain ⟨ρ_f, hd, hv⟩ := rangeProd_denote_converges n a
  have hρ_f : (denote (prodProg n) (env_with_a a)).2 = ρ_f := by rw [hd]
  rw [hρ_f]
  -- Step 1: seq pop on (rangeProd n).body = .seq (embed prodProg) (.ret _).
  have hstep1 : pstep (helper_init n a) =
      some ⟨embed (prodProg n), [.ret (.var "acc")],
            bindParams ["a"] [Val.int a], [], none⟩ := by
    show pstep ⟨.seq (embed (prodProg n)) (.ret (.var "acc")), [],
                bindParams ["a"] [Val.int a], [], none⟩ = _
    rfl
  -- Step 2: body via denote_sound.
  have hbody : PureSteps
      ⟨embed (prodProg n), [.ret (.var "acc")],
       bindParams ["a"] [Val.int a], [], none⟩
      ⟨.skip, [.ret (.var "acc")], ρ_f, [], none⟩ := by
    have := denote_sound (prodProg n) [.ret (.var "acc")]
      (bindParams ["a"] [Val.int a]) ρ_f
      (env_with_a_eq_bindParams a ▸ hd)
    exact this
  -- Step 3: skip pops the trailing `.ret`.
  have hstep3 : pstep ⟨.skip, [.ret (.var "acc")], ρ_f, [], none⟩ =
      some ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ := rfl
  -- Step 4: ret fires doReturn on the empty stack.
  have hstep4 : pstep ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ =
      some (helperTerminal ρ_f (Val.int (rangeProdValue a n))) := by
    show pstep ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ = _
    simp [pstep, tstep, hv, doReturn, helperTerminal]
  exact .step hstep1 (hbody.trans (.step hstep3 (.single hstep4)))

/-- Multi-step reachability on a singleton helper threadpool: induct
on `Machine.StepStarN` using `machineStep_helper` to extract `pstep`s
into a `PureSteps` chain. Generalised over the starting thread (the
existing `machineStepStarN_helper` pins it to `Thread.initial h.main`
with `Env.empty`). -/
private theorem helperProg_stepStarN_chain (n : Nat) (a : Int) (σ : Mem) :
    ∀ steps t₀ μ', HelperThread t₀ →
      Machine.StepStarN (helperProg n) steps ⟨σ, [t₀]⟩ μ' →
      ∃ t', μ' = ⟨σ, [t']⟩ ∧ PureSteps t₀ t' ∧ HelperThread t' := by
  intro steps
  induction steps with
  | zero =>
      intro t₀ μ' he htraj
      cases htraj
      exact ⟨t₀, rfl, .refl, he⟩
  | succ k ih =>
      intro t₀ μ' he htraj
      cases htraj with
      | step h1 h2 =>
          have ⟨t', hμ_mid, hp, hHt'⟩ := machineStep_helper _ σ _ _ he h1
          rw [hμ_mid] at h2
          have ⟨t'', hμ_end, hps, hHt''⟩ := ih _ _ hHt' h2
          exact ⟨t'', hμ_end, .step hp hps, hHt''⟩

/-- Safety of the standalone helper program starting from the
parameter-bound thread `helper_init n a`. -/
theorem helperProg_safe (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp (helperProg n) ⟨σ, [helper_init n a]⟩
        (fun v => v = Val.int (rangeProdValue a n)) := by
  intro σ steps μ' htraj k t htk
  -- Convergence + reaching-terminal witness from the spec.
  obtain ⟨ρ_f, hd, hv⟩ := rangeProd_denote_converges n a
  have h_reach :=
    helper_init_reaches_terminal n a
  have hρ_f_eq : (denote (prodProg n) (env_with_a a)).2 = ρ_f := by rw [hd]
  rw [hρ_f_eq] at h_reach
  -- Multi-step trajectory pins μ' = ⟨σ, [t']⟩.
  have ⟨t', hμ', hps, hHt'⟩ :=
    helperProg_stepStarN_chain n a σ steps _ μ'
      (helper_init_helperThread n a) htraj
  -- Case on thread index k.
  rcases k with _ | k
  · -- k = 0.
    rw [hμ'] at htk
    simp at htk
    subst htk
    -- Case on pstep t'.
    rcases hp : pstep t' with _ | tn
    · -- t' is stuck: identify with helperTerminal by PureSteps.stuck_unique.
      have hstuck_term :
          pstuck (helperTerminal ρ_f (Val.int (rangeProdValue a n))) :=
        helperTerminal_pstuck _ _
      have hstuck_t' : pstuck t' := hp
      have ht_eq : t' = helperTerminal ρ_f (Val.int (rangeProdValue a n)) :=
        PureSteps.stuck_unique hps hstuck_t' h_reach hstuck_term
      subst ht_eq
      left
      refine ⟨Val.int (rangeProdValue a n),
              helperTerminal_toValue _ _, fun _ => rfl⟩
    · -- t' is reducible.
      right
      rw [hμ']
      refine ⟨σ, tn, none, none, ?_⟩
      show tstep (helperProg n).procs none _ _ = _
      show tstep noProcs none σ t' = _
      exact tstep_helperShape_chosen_none hp σ
  · -- k > 0: μ'.threads = [t'], so [t'][k+1]? = none, vacuous.
    rw [hμ'] at htk
    simp at htk

/-! ## Bridge to `SafeTp` of the composite

`Machine.safe_of_denoteHelper` produces safety of `programOfHelper h`
(procs = noProcs). Our `helper_safeTp` needs safety on
`rangeProdComposite3` (real procs). The bridge is **procs-irrelevance
for HelperShape threads**: any thread satisfying `HelperShape` is
oblivious to the `procs` table provided the table doesn't define
`embed`'s stuck-call placeholders (`"_no_proc_"`). -/

/-- The composite's procs table does not shadow `embed`'s stuck-call
placeholder. This is true by `rfl` since `rangeProdComposite3.procs`
returns `none` for any name other than `"rangeProd"` and
`"rangeProdCaller"`. -/
theorem rangeProdComposite3_no_shadow :
    rangeProdComposite3.procs "_no_proc_" = none := by rfl

/-- **Procs irrelevance for HelperShape threads (gap).** A reachable
state of `programOfHelper h` from a HelperShape thread is also
reachable on the composite, and vice-versa, *as long as the composite's
procs doesn't shadow the embed placeholders*. The existing proofs
`tstep_helperShape_chosen_none`, `pstep_preserves_helperThread`, and
`machineStepStarN_helper` all generalize. -/
theorem SafeTp_of_safeFrom_helperProg (n : Nat) (a : Int)
    (h_no_shadow : rangeProdComposite3.procs "_no_proc_" = none)
    (h_helper_safe : ∀ σ, Machine.SafeTp (helperProg n)
        ⟨σ, [helper_init n a]⟩ (fun v => v = Val.int (rangeProdValue a n))) :
    ∀ σ, Machine.SafeTp rangeProdComposite3
        ⟨σ, [helper_init n a]⟩ (helper_post_at n a) := by
  -- Procs-irrelevance + initial-env adjustment.
  -- This is the gap to fill. The structure:
  --   1. helper_init n a has HelperShape (since rangeProd n's body is
  --      .seq (embed prodProg) (.ret retExpr)).
  --   2. Under composite.procs (no shadow), HelperShape is preserved.
  --   3. Reachability on composite from helper_init matches reachability
  --      on programOfHelper.
  --   4. helper_post_at matches the φ predicate via rangeProdValue equality.
  sorry

/-! ## Closing the loop

Compose the chain: `rangeProd_spec` → `helperProg_safe` → composite-
procs-irrelevance → `helper_safeTp`. Each `sorry` above is a named
follow-up; this final theorem records the assembly. -/

theorem helper_safeTp_via_StdDo (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp rangeProdComposite3
        ⟨σ, [helper_init n a]⟩ (helper_post_at n a) := by
  apply SafeTp_of_safeFrom_helperProg n a rangeProdComposite3_no_shadow
  exact helperProg_safe n a

end SimpleRangeProd
end Agar

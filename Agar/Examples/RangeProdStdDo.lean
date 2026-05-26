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

/-- Safety of the standalone helper program, with the helper's body
preloaded with `"a" ↦ Val.int a` via the `Std.Do` triple's universal
quantifier over `ρ₀`. -/
theorem helperProg_safe (n : Nat) (a : Int) :
    ∀ σ, Machine.safeFrom (helperProg n) σ
        (fun v => v = .int (rangeProdValue a n)) := by
  -- `safe_of_denoteHelper` wants `denoteHelper h Env.empty = some v ∧ φ v`.
  -- But our `Std.Do` triple is for env_with_a a, not Env.empty.
  -- The `_total` wrapper takes `∀ ρ₀, ∃ v, denoteHelper h ρ₀ = some v ∧ φ v`,
  -- which we'd need to prove for arbitrary ρ₀ — but our spec only covers
  -- env_with_a a (the precondition `ρ.lookup "a" = some (.int a)` fails
  -- for ρ₀ = Env.empty).
  --
  -- The cleaner path: use a custom `safe_of_denoteHelper_at_env` that
  -- starts from a specific ρ₀. The existing proof of
  -- `safe_of_denoteHelper` uses `Env.empty` only because `Thread.initial`
  -- has empty env. For our use we want a thread initialised at `env_with_a a`,
  -- which is precisely what `helper_init n a` is.
  --
  -- For now: stub. Plumbing across this gap is the small follow-up.
  sorry

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
    (h_helper_safe : ∀ σ, Machine.safeFrom (helperProg n) σ
        (fun v => v = .int (rangeProdValue a n))) :
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

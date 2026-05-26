module

public import Std.Do.Triple
public import Std.Do.WP
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Agar.Operational.StackExt
public import Agar.Operational.StrictHelper
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.Completeness
public import Agar.Iris.StackPush
public import Agar.Examples.SimpleRangeProdComposition

@[expose] public section

/-! # External Solver: dispatching a pure helper's `Std.Do.Triple`
     down to a closed `Machine.safe` of a composite program (Route A).

This file is the **complete Route A showcase** — previously split
across `SimpleRangeProdHelperSafe`, `SimpleRangeProdCompositionRouteA`,
and `RangeProdStdDo`, now consolidated for ease of reading.

The point: treat Agar as a *client* of an external solver
(`Std.Do`), where the helper's specification arrives as a
`Std.Do.Triple` over its denotation, and the rest of the pipeline
dispatches that triple — through operational adequacy of the pure
fragment, through Iris's open-context completeness theorem, and
through a stack-embedding lemma — into a closed safety statement
about a composite program that calls the helper concurrently.

```
  rangeProd_spec                  -- 1. Std.Do.Triple over `denote`
        │  (direct induction on the forN; pure StateM reasoning)
        ▼
  rangeProd_denote_converges      -- 2. raw denote convergence
        │  (denote_sound — pure-fragment operational adequacy)
        ▼
  helper_init_reaches_terminal    -- 3. PureSteps chain to helperTerminal
        │  (singleton-pool StepStarN_helper folding)
        ▼
  helperProg_safe                 -- 4. Machine.SafeTp under `noProcs`
        │  SafeTp_procs_irrel_of_strict (StrictHelperShape lift)
        ▼
  helper_safeTp                   -- 5. SafeTp under composite.procs
        │  completeness_open      (Theorem 15, open-context variant)
        ▼
  wp at helper_init under composite.procs
        │  wp_wand                (reshape post)
        ▼
  wp at helper_init, post := wp at postDoReturnThread
        │  wp_stack_push          (callee-frame embedding)
        ▼
  wp at the `wp_call` residual (callee-frame shaped)
        │  wp_callee_routeA       (bridges the three above)
        ▼
  wp_call ⟨...rangeProd...⟩ — discharged.
        │  wp_safe_bupd / adequacy
        ▼
  Machine.safe rangeProdComposite3 (fun _ => True)
```

Step (1) is the **only** Std.Do work in the whole pipeline. Once
`rangeProd_spec` is in hand, steps (2)–(4) are direct operational
manipulations — no Iris machinery yet, no procs-table yet, no fork
semantics yet. Steps (5)–(end) are the Iris bridge.

The whole pipeline picks `fork_post := iprop(True : IProp GF)`
uniformly — that's what `completeness_open` produces, so we thread
the same value at `wp_fork`, `wp_call`, and the `wp_safe_bupd`
existential.

See `HYPOTHESIS.md` §8 for the design and §8.13 for the recipe on
how to apply Route A to a new pure helper. -/

namespace Agar
open Agar.Logic
namespace SimpleRangeProd

/-! ## Part I — Std.Do triple → operational safety -/

section PartI
open Std.Do

/-! ### The pretty endpoint — closed by direct induction on `denote`. -/

/-- Generalised invariant for the inner `forN` loop of `prodProg`.
After `n` iterations of `prodBody` starting from an env with
`acc = A` and `i = I`, the env has `acc = A * rangeProdValue I n`
and `i = I + n`. -/
private theorem forN_prodBody_spec (n : Nat) :
    ∀ (A I : Int) (ρ : Env),
      ρ "acc" = some (Val.int A) → ρ "i" = some (Val.int I) →
      ∃ ρ', denote (.forN n prodBody) ρ = (some (), ρ') ∧
            ρ' "acc" = some (Val.int (A * rangeProdValue I n)) ∧
            ρ' "i" = some (Val.int (I + n)) := by
  induction n with
  | zero =>
      intro A I ρ hA hI
      refine ⟨ρ, rfl, ?_, ?_⟩
      · simp [rangeProdValue, hA]
      · simpa using hI
  | succ k ih =>
      intro A I ρ hA hI
      have hmul : Expr.eval ρ (.bin .mul (.var "acc") (.var "i"))
          = some (Val.int (A * I)) := by
        simp [Expr.eval, hA, hI, BinOp.eval]
      let ρ₁ : Env := ρ.set "acc" (.int (A * I))
      have hbody1 : denote (.assign "acc" (.bin .mul (.var "acc") (.var "i"))) ρ
          = (some (), ρ₁) := by
        show (match Expr.eval ρ (.bin .mul (.var "acc") (.var "i")) with
              | none => (none, ρ)
              | some v => (some (), ρ.set "acc" v)) = _
        rw [hmul]
      have hρ₁_i : ρ₁ "i" = some (Val.int I) := by
        show (if "i" = "acc" then some (Val.int (A*I)) else ρ "i") = _
        simp [hI]
      have hadd : Expr.eval ρ₁ (.bin .add (.var "i") (.val (.int 1)))
          = some (Val.int (I + 1)) := by
        simp [Expr.eval, hρ₁_i, BinOp.eval]
      let ρ₂ : Env := ρ₁.set "i" (.int (I + 1))
      have hbody2 : denote (.assign "i" (.bin .add (.var "i") (.val (.int 1)))) ρ₁
          = (some (), ρ₂) := by
        show (match Expr.eval ρ₁ (.bin .add (.var "i") (.val (.int 1))) with
              | none => (none, ρ₁)
              | some v => (some (), ρ₁.set "i" v)) = _
        rw [hadd]
      have hbody : denote prodBody ρ = (some (), ρ₂) := by
        show (match denote (.assign "acc" (.bin .mul (.var "acc") (.var "i"))) ρ with
              | (none, ρ') => (none, ρ')
              | (some _, ρ') =>
                denote (.assign "i" (.bin .add (.var "i") (.val (.int 1)))) ρ') = _
        rw [hbody1]; exact hbody2
      have hρ₂_acc : ρ₂ "acc" = some (Val.int (A * I)) := by
        show (if "acc" = "i" then some (Val.int (I+1)) else ρ₁ "acc") = _
        simp
        show (if "acc" = "acc" then some (Val.int (A*I)) else ρ "acc") = _
        simp
      have hρ₂_i : ρ₂ "i" = some (Val.int (I + 1)) := by
        show (if "i" = "i" then some (Val.int (I+1)) else ρ₁ "i") = _
        simp
      obtain ⟨ρ', hd, hacc, hi⟩ := ih (A * I) (I + 1) ρ₂ hρ₂_acc hρ₂_i
      refine ⟨ρ', ?_, ?_, ?_⟩
      · rw [denote_forN_succ]
        show (match denote prodBody ρ with
              | (none, ρ') => (none, ρ')
              | (some _, ρ') => denote (.forN k prodBody) ρ') = _
        rw [hbody]; exact hd
      · rw [hacc]; congr 1; congr 1
        show A * I * rangeProdValue (I+1) k = A * rangeProdValue I (k+1)
        show A * I * rangeProdValue (I+1) k = A * (I * rangeProdValue (I + 1) k)
        rw [Int.mul_assoc]
      · rw [hi]; congr 1; congr 1
        show I + 1 + (k : Int) = I + ((k + 1 : Nat) : Int)
        push_cast; omega

/-- **The headline Std.Do triple.** Hoare-style spec on the pure
denotation of the helper's body. This is the *only* Std.Do work in
the whole pipeline. -/
theorem rangeProd_spec (n : Nat) (a : Int) :
    ⦃fun ρ : Env => ⌜ρ "a" = some (Val.int a)⌝⦄
    (show StateM Env (Option Unit) from denote (prodProg n))
    ⦃⇓ r => fun ρ' : Env =>
      ⌜r = some () ∧ ρ' "acc" = some (Val.int (rangeProdValue a n))⌝⦄ := by
  intro ρ hpre
  have ha : ρ "a" = some (Val.int a) := hpre
  let ρ₁ : Env := ρ.set "acc" (.int 1)
  let ρ₂ : Env := ρ₁.set "i" (.int a)
  have hρ₂_acc : ρ₂ "acc" = some (Val.int 1) := by
    show (if "acc" = "i" then some (Val.int a) else ρ₁ "acc") = _
    simp
    show (if "acc" = "acc" then some (Val.int 1) else ρ "acc") = _
    simp
  have hρ₂_i : ρ₂ "i" = some (Val.int a) := by
    show (if "i" = "i" then some (Val.int a) else ρ₁ "i") = _
    simp
  obtain ⟨ρ', hd, hacc, _hi⟩ := forN_prodBody_spec n 1 a ρ₂ hρ₂_acc hρ₂_i
  have hprog : denote (prodProg n) ρ = (some (), ρ') := by
    show (match denote (.assign "acc" (.val (.int 1))) ρ with
          | (none, ρ') => (none, ρ')
          | (some _, ρ') =>
              denote (.seq (.assign "i" (.var "a")) (.forN n prodBody)) ρ') = _
    have h1 : denote (.assign "acc" (.val (.int 1))) ρ = (some (), ρ₁) := by
      show (match Expr.eval ρ (.val (.int 1)) with
            | none => (none, ρ)
            | some v => (some (), ρ.set "acc" v)) = _
      rfl
    rw [h1]
    show (match denote (.assign "i" (.var "a")) ρ₁ with
          | (none, ρ') => (none, ρ')
          | (some _, ρ') => denote (.forN n prodBody) ρ') = _
    have hva : Expr.eval ρ₁ (.var "a") = some (Val.int a) := by
      show ρ₁ "a" = _
      show (if "a" = "acc" then some (Val.int 1) else ρ "a") = _
      simp [ha]
    have h2 : denote (.assign "i" (.var "a")) ρ₁ = (some (), ρ₂) := by
      show (match Expr.eval ρ₁ (.var "a") with
            | none => (none, ρ₁)
            | some v => (some (), ρ₁.set "i" v)) = _
      rw [hva]
    rw [h2]; exact hd
  refine ⟨?_, ?_⟩
  · show (denote (prodProg n) ρ).fst = some ()
    rw [hprog]
  · show (denote (prodProg n) ρ).snd "acc" = some (Val.int (rangeProdValue a n))
    rw [hprog]
    show ρ' "acc" = some (Val.int (rangeProdValue a n))
    rw [hacc]; congr 1; congr 1
    exact Int.one_mul _

/-! ### Convergence corollary -/

def rangeProdHelper (n : Nat) : PureHelper where
  body := prodProg n
  ret  := .var "acc"

def env_with_a (a : Int) : Env := Env.empty.set "a" (.int a)

theorem env_with_a_eq_bindParams (a : Int) :
    env_with_a a = bindParams ["a"] [Val.int a] := by
  simp [env_with_a, bindParams]

theorem rangeProd_denote_converges (n : Nat) (a : Int) :
    ∃ ρ_f, denote (prodProg n) (env_with_a a) = (some (), ρ_f) ∧
      Expr.eval ρ_f (.var "acc") = some (Val.int (rangeProdValue a n)) := by
  have hpre : (env_with_a a) "a" = some (Val.int a) := by
    simp [env_with_a, Env.set]
  have hpost := rangeProd_spec n a (env_with_a a) hpre
  obtain ⟨hr, hacc⟩ := hpost
  refine ⟨(denote (prodProg n) (env_with_a a)).2, ?_, ?_⟩
  · show denote (prodProg n) (env_with_a a)
      = (some (), (denote (prodProg n) (env_with_a a)).2)
    rw [← hr]
    rfl
  · simp [Expr.eval]
    exact hacc

theorem rangeProd_denoteHelper (n : Nat) (a : Int) :
    denoteHelper (rangeProdHelper n) (env_with_a a)
      = some (Val.int (rangeProdValue a n)) := by
  obtain ⟨ρ_f, hd, hv⟩ := rangeProd_denote_converges n a
  simp [denoteHelper, rangeProdHelper, hd]
  exact hv

/-! ### Helper program + standalone safety -/

abbrev helperProg (n : Nat) : Program := programOfHelper (rangeProdHelper n)

/-- Standalone helper init thread at argument `a`. -/
def helper_init (n : Nat) (a : Int) : Thread :=
  ⟨(rangeProd n).body, [], bindParams ["a"] [Val.int a], [], none⟩

/-- Helper's value-post (closed form). -/
def helper_post_at (n : Nat) (a : Int) (v : Val) : Prop :=
  v = Val.int (rangeProdValue a n)

theorem helper_init_helperThread (n : Nat) (a : Int) :
    HelperThread (helper_init n a) := by
  refine ⟨?_, ?_, rfl⟩
  · change HelperShape (.seq (embed (prodProg n)) (.ret (.var "acc")))
    exact .seq _ _ (embedShape_helperShape (embed_embedShape _)) (.ret _)
  · intro s hmem; cases hmem

/-- The crucial strict-helper-shape fact for `helper_init`: `prodProg`
contains no `while_`, so the embedded body has `StrictHelperShape`. -/
theorem prodProg_whileFree (n : Nat) : (prodProg n).whileFree := by
  unfold prodProg prodBody PureStmt.whileFree
  exact ⟨trivial, trivial, ⟨trivial, trivial⟩⟩

theorem helper_init_strictHelperThread (n : Nat) (a : Int) :
    StrictHelperThread (helper_init n a) := by
  refine ⟨?_, ?_, rfl⟩
  · change StrictHelperShape (.seq (embed (prodProg n)) (.ret (.var "acc")))
    exact .seq _ _ (embed_strictHelperShape _ (prodProg_whileFree n)) (.ret _)
  · intro s hmem; cases hmem

theorem helper_init_reaches_terminal (n : Nat) (a : Int) :
    PureSteps (helper_init n a)
      (helperTerminal
        ((denote (prodProg n) (env_with_a a)).2)
        (Val.int (rangeProdValue a n))) := by
  obtain ⟨ρ_f, hd, hv⟩ := rangeProd_denote_converges n a
  have hρ_f : (denote (prodProg n) (env_with_a a)).2 = ρ_f := by rw [hd]
  rw [hρ_f]
  have hstep1 : pstep (helper_init n a) =
      some ⟨embed (prodProg n), [.ret (.var "acc")],
            bindParams ["a"] [Val.int a], [], none⟩ := by
    show pstep ⟨.seq (embed (prodProg n)) (.ret (.var "acc")), [],
                bindParams ["a"] [Val.int a], [], none⟩ = _
    rfl
  have hbody : PureSteps
      ⟨embed (prodProg n), [.ret (.var "acc")],
       bindParams ["a"] [Val.int a], [], none⟩
      ⟨.skip, [.ret (.var "acc")], ρ_f, [], none⟩ := by
    have := denote_sound (prodProg n) [.ret (.var "acc")]
      (bindParams ["a"] [Val.int a]) ρ_f
      (env_with_a_eq_bindParams a ▸ hd)
    exact this
  have hstep3 : pstep ⟨.skip, [.ret (.var "acc")], ρ_f, [], none⟩ =
      some ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ := rfl
  have hstep4 : pstep ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ =
      some (helperTerminal ρ_f (Val.int (rangeProdValue a n))) := by
    show pstep ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ = _
    simp [pstep, tstep, hv, doReturn, helperTerminal]
  exact .step hstep1 (hbody.trans (.step hstep3 (.single hstep4)))

private theorem helperProg_stepStarN_chain (n : Nat) (σ : Mem) :
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

/-- **Operational safety of the standalone helper.** The bottom node
of the operational-side pipeline: from the `PureSteps` chain to the
terminal (built on the Std.Do triple via `denote_sound`), conclude
`Machine.SafeTp` of the singleton-thread pool under `noProcs`.

Method: walk any `Machine.StepStarN`-trajectory through
`helperProg_stepStarN_chain` (which folds `Machine.Step` over a
`HelperThread`-shaped thread into a `pstep`-driven `PureSteps`).
Either the reached thread is stuck (and `PureSteps.stuck_unique`
identifies it with `helperTerminal`, firing the value disjunct of
`SafeTp`), or it has a successor `pstep` (which lifts to a `tstep`
under any procs table — the reducibility disjunct).

Consumed by Part II via `SafeTp_procs_irrel_of_strict` to lift onto
the composite's procs table. -/
theorem helperProg_safe (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp (helperProg n) ⟨σ, [helper_init n a]⟩
        (fun v => v = Val.int (rangeProdValue a n)) := by
  intro σ steps μ' htraj k t htk
  obtain ⟨ρ_f, hd, hv⟩ := rangeProd_denote_converges n a
  have h_reach := helper_init_reaches_terminal n a
  have hρ_f_eq : (denote (prodProg n) (env_with_a a)).2 = ρ_f := by rw [hd]
  rw [hρ_f_eq] at h_reach
  have ⟨t', hμ', hps, hHt'⟩ :=
    helperProg_stepStarN_chain n σ steps _ μ'
      (helper_init_helperThread n a) htraj
  rcases k with _ | k
  · rw [hμ'] at htk
    simp at htk
    subst htk
    rcases hp : pstep t' with _ | tn
    · have hstuck_term :
          pstuck (helperTerminal ρ_f (Val.int (rangeProdValue a n))) :=
        helperTerminal_pstuck _ _
      have hstuck_t' : pstuck t' := hp
      have ht_eq : t' = helperTerminal ρ_f (Val.int (rangeProdValue a n)) :=
        PureSteps.stuck_unique hps hstuck_t' h_reach hstuck_term
      subst ht_eq
      left
      refine ⟨Val.int (rangeProdValue a n),
              helperTerminal_toValue _ _, fun _ => rfl⟩
    · right
      rw [hμ']
      refine ⟨σ, tn, none, none, ?_⟩
      show tstep (helperProg n).procs none _ _ = _
      show tstep noProcs none σ t' = _
      exact tstep_helperShape_chosen_none hp σ
  · rw [hμ'] at htk
    simp at htk

end PartI

/-! ## Part II — operational safety → closed `Machine.safe` via Iris -/

section PartII
open Iris Iris.BI Iris.OFE

/-- **Operational obligation (Route A).** The standalone helper run
under the composite's `procs` is safe with the closed-form post.
Discharged via the procs-irrelevance lift `SafeTp_procs_irrel_of_strict`
applied to `helperProg_safe` (whose target program is
`programOfHelper (rangeProdHelper n)`, with `procs := noProcs`). -/
theorem helper_safeTp (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp rangeProdComposite3
        ⟨σ, [helper_init n a]⟩ (helper_post_at n a) := by
  intro σ
  exact
    SafeTp_procs_irrel_of_strict
      (prog1 := helperProg n) (prog2 := rangeProdComposite3)
      (helper_init_strictHelperThread n a)
      (helperProg_safe n a σ)

/-- Heap-freeness of the composite. Both procs (`rangeProd n` and
`rangeProdCaller`) have bodies built from `.seq`, `.assign`, `.call`,
`.fork`, `.ret` — all heap-free. -/
theorem rangeProdComposite3_heapFree : rangeProdComposite3.heapFree := by
  refine ⟨?_, ?_⟩
  · -- main heap-free
    show Stmt.heapFree _
    refine ⟨trivial, ?_, ?_⟩ <;> trivial
  · -- procs heap-free
    intro name proc hproc
    simp [rangeProdComposite3] at hproc
    split at hproc
    · cases hproc
      show Stmt.heapFree _
      refine ⟨?_, trivial⟩
      exact embed_heapFree _
    · split at hproc
      · cases hproc
        show Stmt.heapFree _
        exact ⟨trivial, trivial⟩
      · cases hproc

/-- Heap-freeness of the standalone helper init thread. -/
theorem helper_init_heapFree (n : Nat) (a : Int) :
    (helper_init n a).heapFree := by
  refine ⟨?_, ?_, ?_⟩
  · show Stmt.heapFree _
    exact ⟨embed_heapFree _, trivial⟩
  · intro s hs; cases hs
  · intro f hf; cases hf

/-! ### Route A bridge: `wp_call` residual from a SafeTp witness

The `wp_call` rule leaves a residual of shape
`wp procs fp ⊤ ⟨h.body, [], bindParams h.params vs, ⟨x, cont, env⟩ :: stack, none⟩ Φ`.

Route A discharges it by:
1. `completeness_open` → `|={⊤}=> wp procs True ⊤ (helper_init) (fun v => ⌜φ v⌝)`.
2. `wp_wand` → reshape post to the caller-supplied continuation.
3. `wp_stack_push` → lift to the callee-frame stack.

This bridge has `fork_post = True`, set by `completeness_open`. -/

section Bridge
variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarG GF F] [InvGS_gen false GF]

/-- **Route A bridge: discharge a `.call rangeProd` residual from a
SafeTp witness.**

This is the single Iris-side interface the walkthrough uses to close
each `wp_call`. Given that the standalone helper is operationally safe
(via `helper_safeTp`), and a continuation that says "if the helper
returns `v` matching the spec, the caller's wp closes," produce the wp
at the callee-frame-shaped thread that `wp_call` leaves behind.

**The composition.** Three inputs into one bridge:

1. `completeness_open` (Theorem 15, open-context) consumes the
   SafeTp witness and produces a wp on the helper running standalone.
2. `wp_wand` reshapes the post from the operational spec
   (`⌜helper_post_at n a v⌝`) into the caller-supplied continuation wp.
3. `BodyTraj.wp_stack_push` lifts the standalone wp to a wp on the
   callee-frame-shaped thread (the helper with the caller's frame
   pushed onto its stack).

**Caller obligation.** The premise is exactly: "for every return value
`v` satisfying the helper's spec, the caller's wp at the post-doReturn
thread closes against the caller's `Φ`." This is the wp shape `wp_call`
leaves behind *anyway*, restated so the bridge can hand off cleanly.

**`fork_post := True`.** The whole pipeline picks `iprop(True : IProp GF)`
as the fork post — this is what `completeness_open` produces; threading
the same value at the call site keeps the bridge typechecking. The
walkthrough's adequacy entry-point picks the same `True` at its
`wp_safe_bupd` existential, so the unification works end-to-end. -/
theorem wp_callee_routeA
    (n : Nat) (a : Int) (x : Name) (cont : List Stmt) (env : Env)
    (Φ : Val → IProp GF) :
    (∀ v, iprop(⌜helper_post_at n a v⌝ -∗
        wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
          (BodyTraj.postDoReturnThread ⟨x, cont, env⟩ [] v) Φ))
    ⊢ |={⊤}=> wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
        ⟨(rangeProd n).body, [], bindParams ["a"] [Val.int a],
         [⟨x, cont, env⟩], none⟩ Φ := by
  iintro Hwand
  -- 1. Get standalone wp from completeness_open.
  ihave Hopen :=
    completeness_open (prog := rangeProdComposite3) (GF := GF) (F := F)
      (φ := helper_post_at n a)
      rangeProdComposite3_heapFree
      (helper_init n a)
      (helper_init_heapFree n a)
      (helper_safeTp n a)
  imod Hopen with Hstandalone
  -- Hstandalone : wp procs True ⊤ (helper_init n a) (fun v => ⌜helper_post_at n a v⌝)
  -- 2. Reshape post via wp_wand.
  ihave Hreshaped := wp_wand (GF := GF) rangeProdComposite3.procs
    (iprop(True : IProp GF))
    (Φ := fun v => iprop(⌜helper_post_at n a v⌝ : IProp GF))
    (Ψ := fun v => wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
            (BodyTraj.postDoReturnThread ⟨x, cont, env⟩ [] v) Φ)
    (helper_init n a) $$ [Hstandalone Hwand]
  · isplitl [Hstandalone]
    · iexact Hstandalone
    · iintro %v Hpurev
      iapply Hwand $$ %v
      iexact Hpurev
  -- Hreshaped : wp procs True ⊤ (helper_init n a)
  --                (fun v => wp procs True ⊤ (postDoReturnThread ...) Φ)
  -- 3. Lift via wp_stack_push.
  imodintro
  show _ ⊢ wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
      (BodyTraj.stackExt (helper_init n a) [⟨x, cont, env⟩]) Φ
  iapply (BodyTraj.wp_stack_push rangeProdComposite3.procs
    (iprop(True : IProp GF)) ⟨x, cont, env⟩ [] Φ (helper_init n a))

end Bridge

/-! ### The walkthrough (Route A)

Mirroring `rangeProd_composite_walkthrough` but discharging each
`wp_call` residual via `wp_callee_routeA` instead of
`wp_callee_of_pure_helper`. Since `wp_callee_routeA` threads
`fork_post := True` (via `completeness_open`), we pick `True` as the
existentially-quantified `fork_post` in `wp_safe_bupd` and use that
same value at every `wp_fork` / `wp_call` site. -/

theorem rangeProd_composite_walkthrough_RouteA
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [TpGpreS GF F] :
    Machine.safe rangeProdComposite3 (fun _ => True) := by
  refine wp_safe_bupd (GF := GF) (φ := fun _ => True) rangeProdComposite3 ?_
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(True : IProp GF)
  iframe HA
  unfold Thread.initial rangeProdComposite3
  -- Goal: WP at main = `.seq (.fork ...) (.seq (.call ...) (.ret ...))`.
  iapply wp_seq
  iintro !>
  -- Fire the fork rule with fork_post := True.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(True : IProp GF))
    _ "rangeProdCaller" ([] : List Expr) rangeProdCaller ([] : List Val)
    [Stmt.seq (.call "x" "rangeProd" [.val (.int 1)]) (.ret (.var "x"))]
    _ [] _
    (by show rangeProdComposite3.procs _ = _; rfl)
    (by agar_eval)
    rfl
  isplitr
  · -- Forked thread: WP at `rangeProdCaller.body`.
    iintro !>
    unfold rangeProdCaller
    wp_pures
    -- Discharge `.call "r" "rangeProd" [5]; .ret (.var "r")` via the Route A bridge.
    iapply wp_call (GF := GF) (F := F) (fork_post := iprop(True : IProp GF))
      _ "r" "rangeProd" [.val (.int 5)] (rangeProd 3) [Val.int 5]
      [.ret (.var "r")] _ _ _
      (by show rangeProdComposite3.procs _ = _; rfl)
      (by agar_eval)
      rfl
    iintro !>
    iapply fupd_wp
    refine .trans ?_ (wp_callee_routeA (GF := GF) (F := F) 3 5 "r"
      [.ret (.var "r")] Env.empty _)
    iintro _
    iintro %v Hpv
    icases Hpv with %hv
    subst hv
    show _ ⊢ wp _ _ _ ⟨.ret (.var "r"), [], Env.empty.set "r" (.int 210),
      [], none⟩ _
    iintro _
    iapply wp_ret_top _ _ _ (.int 210) _ _ _ rfl
    ipure_intro; trivial
  · -- Parent: WP at `.seq (.call "x" "rangeProd" [1]) (.ret "x")`.
    iintro !>
    wp_pures
    -- Discharge `.call "x" "rangeProd" [1]; .ret (.var "x")` via the Route A bridge.
    iapply wp_call (GF := GF) (F := F) (fork_post := iprop(True : IProp GF))
      _ "x" "rangeProd" [.val (.int 1)] (rangeProd 3) [Val.int 1]
      [.ret (.var "x")] _ _ _
      (by show rangeProdComposite3.procs _ = _; rfl)
      (by agar_eval)
      rfl
    iintro !>
    iapply fupd_wp
    refine .trans ?_ (wp_callee_routeA (GF := GF) (F := F) 3 1 "x"
      [.ret (.var "x")] Env.empty _)
    iintro _
    iintro %v Hpv
    icases Hpv with %hv
    subst hv
    show _ ⊢ wp _ _ _ ⟨.ret (.var "x"), [], Env.empty.set "x" (.int 6),
      [], none⟩ _
    iintro _
    iapply wp_ret_top _ _ _ (.int 6) _ _ _ rfl
    ipure_intro; trivial

/-! ## Std.Do entry point

The headline composition theorem, expressing that the Iris-side
`helper_safeTp` is exactly what the operational chain delivers. It's
a trivial restatement, kept here so an external consumer looking for
the "Std.Do → SafeTp under composite procs" interface finds it at the
obvious name. -/

/-- **Std.Do triple ⇒ Machine.SafeTp of the standalone helper under the
composite's procs table.** The full chain in one statement: the
`rangeProd_spec` triple folds via `helperProg_safe` and
`SafeTp_procs_irrel_of_strict` (proof in `helper_safeTp`). -/
theorem helper_safeTp_via_StdDo (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp rangeProdComposite3
        ⟨σ, [helper_init n a]⟩ (helper_post_at n a) :=
  helper_safeTp n a

end PartII

end SimpleRangeProd
end Agar

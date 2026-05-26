module

public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Agar.Iris.PureHelperBridge
public import Agar.Iris.Adequacy

@[expose] public section

/-! # `StrictHelperShape` — procs-irrelevant pure-helper threads

`HelperShape` (in `PureHelperBridge`) permits `.call` (the `callStuck`
constructor) and relies on `noProcs` to keep it stuck. As a result, the
machine-step characterisation `machineStep_helper` only applies under
`programOfHelper h` (whose procs table is `noProcs`).

`StrictHelperShape` drops the `callStuck` constructor entirely. Threads
satisfying `StrictHelperShape` step *identically* under any `procs`
table: every reachable `tstep` case is either a pure expression
evaluation, a sequencing/conditional reshuffle, or a doReturn on an
empty stack — none of which consult `procs`.

This gives us a clean procs-irrelevance lift: an operational `SafeTp`
witness obtained against `programOfHelper h` transfers to a `SafeTp`
witness under *any* program, as long as the thread satisfies
`StrictHelperShape`. -/

namespace Agar
open Agar.Logic

inductive StrictHelperShape : Stmt → Prop where
  | skip   : StrictHelperShape .skip
  | assign : ∀ x e, StrictHelperShape (.assign x e)
  | seq    : ∀ s₁ s₂, StrictHelperShape s₁ → StrictHelperShape s₂ →
              StrictHelperShape (.seq s₁ s₂)
  | ite    : ∀ g s₁ s₂, StrictHelperShape s₁ → StrictHelperShape s₂ →
              StrictHelperShape (.ite g s₁ s₂)
  | ret    : ∀ e, StrictHelperShape (.ret e)

/-- `unroll` of a strict-helper-shape body preserves the shape. -/
theorem unroll_strictHelperShape (body : Stmt) (h : StrictHelperShape body) :
    ∀ n, StrictHelperShape (unroll body n)
  | 0     => .skip
  | n + 1 => .seq _ _ h (unroll_strictHelperShape body h n)

/-- A `PureStmt` is *while-free* when it contains no `while_` constructor.
For such statements, `embed` never emits a stuck `.call` and the result
satisfies `StrictHelperShape`. -/
def PureStmt.whileFree : PureStmt → Prop
  | .skip          => True
  | .assign _ _    => True
  | .seq s₁ s₂     => s₁.whileFree ∧ s₂.whileFree
  | .ite _ s₁ s₂   => s₁.whileFree ∧ s₂.whileFree
  | .repeat _ s    => s.whileFree
  | .forN _ s      => s.whileFree
  | .while_ _ _ _  => False

theorem embed_strictHelperShape (s : PureStmt) (hwf : s.whileFree) :
    StrictHelperShape (embed s) := by
  induction s with
  | skip => exact .skip
  | assign x e => exact .assign x e
  | seq s₁ s₂ ih₁ ih₂ =>
      have ⟨h₁, h₂⟩ := hwf
      exact .seq _ _ (ih₁ h₁) (ih₂ h₂)
  | ite e s₁ s₂ ih₁ ih₂ =>
      have ⟨h₁, h₂⟩ := hwf
      exact .ite _ _ _ (ih₁ h₁) (ih₂ h₂)
  | «repeat» n s ih =>
      show StrictHelperShape (unroll (embed s) n)
      exact unroll_strictHelperShape _ (ih hwf) n
  | forN n s ih =>
      show StrictHelperShape (unroll (embed s) n)
      exact unroll_strictHelperShape _ (ih hwf) n
  | while_ n g s _ => exact absurd hwf (by intro h; exact h)

/-- Embed strict into helper: every `StrictHelperShape` is a `HelperShape`. -/
theorem strictHelperShape_helperShape :
    ∀ {s}, StrictHelperShape s → HelperShape s
  | _, .skip => .skip
  | _, .assign x e => .assign x e
  | _, .seq _ _ h₁ h₂ =>
      .seq _ _ (strictHelperShape_helperShape h₁)
               (strictHelperShape_helperShape h₂)
  | _, .ite _ _ _ h₁ h₂ =>
      .ite _ _ _ (strictHelperShape_helperShape h₁)
                 (strictHelperShape_helperShape h₂)
  | _, .ret e => .ret e

structure StrictHelperThread (t : Thread) : Prop where
  stmt  : StrictHelperShape t.stmt
  cont  : ∀ s ∈ t.cont, StrictHelperShape s
  stack : t.stack = []

theorem strictHelperThread_helperThread {t : Thread}
    (h : StrictHelperThread t) : HelperThread t :=
  { stmt := strictHelperShape_helperShape h.stmt,
    cont := fun s hs => strictHelperShape_helperShape (h.cont s hs),
    stack := h.stack }

/-! ## Procs-irrelevance for `tstep` -/

/-- The key property: a `StrictHelperShape` thread's `tstep` ignores
`procs` (and any heap). Phrased as: for any two procs tables, the result
is the same. -/
theorem tstep_strict_procs_irrel {t : Thread}
    (he : StrictHelperThread t)
    (procs1 procs2 : Name → Option Proc)
    (chosen : Option Loc) (m : Mem) :
    tstep procs1 chosen m t = tstep procs2 chosen m t := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  have hst := he.stmt
  have hsk := he.stack
  simp at hsk; subst hsk
  cases hst <;> (cases chosen <;> simp [tstep])

/-! ## `pstep` preservation -/

theorem pstep_preserves_strictHelperThread {t t' : Thread}
    (he : StrictHelperThread t) (h : pstep t = some t') :
    StrictHelperThread t' := by
  unfold pstep at h
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  have hst := he.stmt
  have hco := he.cont
  have hsk := he.stack
  simp at hsk
  subst hsk
  cases hst with
  | skip =>
      cases cont with
      | nil => simp [tstep] at h
      | cons s rest =>
          simp [tstep] at h
          rcases h with ⟨rfl⟩
          refine ⟨?_, ?_, rfl⟩
          · exact hco s (by simp)
          · intro c hc; exact hco c (by simp [hc])
  | assign x e =>
      simp [tstep] at h
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          simp [hev] at h
          rcases h with ⟨rfl⟩
          exact ⟨.skip, hco, rfl⟩
  | seq s₁ s₂ h₁ h₂ =>
      simp [tstep] at h
      rcases h with ⟨rfl⟩
      refine ⟨h₁, ?_, rfl⟩
      intro c hc
      cases hc with
      | head => exact h₂
      | tail _ hc' => exact hco c hc'
  | ite g s₁ s₂ h₁ h₂ =>
      simp [tstep] at h
      cases hev : Expr.eval env g with
      | none => simp [hev] at h
      | some v =>
          cases v <;> simp [hev] at h
          rename_i b; cases b <;> simp at h
          · rcases h with ⟨rfl⟩; exact ⟨h₂, hco, rfl⟩
          · rcases h with ⟨rfl⟩; exact ⟨h₁, hco, rfl⟩
  | ret e =>
      simp [tstep] at h
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          simp [hev, doReturn] at h
          rcases h with ⟨rfl⟩
          refine ⟨.skip, ?_, rfl⟩
          intro c hc; cases hc

/-! ## `Machine.Step` characterisation for strict-helper threads,
parametric in `prog`. -/

theorem machineStep_strictHelper (prog : Program) {σ : Mem} {t : Thread}
    {μ' : Machine} (he : StrictHelperThread t)
    (hs : Machine.Step prog ⟨σ, [t]⟩ μ') :
    ∃ t', μ' = ⟨σ, [t']⟩ ∧ pstep t = some t' ∧ StrictHelperThread t' := by
  obtain ⟨i, chosen, t₀, t₁, sp, m', hi, hstep, hμ'⟩ := hs.invert
  -- index 0 is the only thread.
  have hi0 : i = 0 := by
    rcases i with _ | i'
    · rfl
    · simp at hi
  subst hi0; simp at hi; subst hi
  -- The tstep on this strict thread is procs-irrelevant — convert to noProcs.
  have hstep' :
      tstep noProcs chosen σ t = some (m', t₁, sp) := by
    rw [tstep_strict_procs_irrel he noProcs prog.procs chosen σ]; exact hstep
  -- chosen = none: try cases.
  cases chosen with
  | some l =>
      -- StrictHelperShape rules out `chosen = some _` for noProcs.
      exfalso
      have h_none :=
        tstep_helperShape_chosen_some
          (strictHelperThread_helperThread he) l σ
      rw [h_none] at hstep'
      cases hstep'
  | none =>
      -- Pin down via pstep.
      have hbundle : pstep t = some t₁ ∧ m' = σ ∧ sp = none ∧
                      StrictHelperThread t₁ := by
        match hp : pstep t with
        | some tp =>
            have hts := pstep_machine_indep t tp hp σ
            rw [hts] at hstep'
            have heq : (σ, tp, none) = (m', t₁, sp) :=
              Option.some.inj hstep'
            have hmm : m' = σ := (congrArg Prod.fst heq).symm
            have htp : tp = t₁ := congrArg (Prod.fst ∘ Prod.snd) heq
            have hsp : sp = (none : Option Thread) :=
              (congrArg (Prod.snd ∘ Prod.snd) heq).symm
            refine ⟨?_, hmm, hsp, ?_⟩
            · exact congrArg some htp
            · rw [← htp]; exact pstep_preserves_strictHelperThread he hp
        | none =>
            exfalso
            have hts :=
              tstep_helperShape_chosen_none_stuck
                (strictHelperThread_helperThread he) hp σ
            rw [hts] at hstep'
            cases hstep'
      obtain ⟨hps, hmm, hsp, hHt⟩ := hbundle
      refine ⟨t₁, ?_, hps, hHt⟩
      rw [hμ', hmm, hsp]; simp

theorem machineStepStarN_strictHelper (prog : Program) (σ : Mem) :
    ∀ n t μ', StrictHelperThread t →
      Machine.StepStarN prog n ⟨σ, [t]⟩ μ' →
      ∃ t', μ' = ⟨σ, [t']⟩ ∧ PureSteps t t' ∧ StrictHelperThread t' := by
  intro n
  induction n with
  | zero =>
      intro t μ' he hs
      cases hs
      exact ⟨t, rfl, .refl, he⟩
  | succ n ih =>
      intro t μ' he hs
      cases hs with
      | step h1 h2 =>
          obtain ⟨t', hμ'_mid, hp, hHt'⟩ := machineStep_strictHelper prog he h1
          rw [hμ'_mid] at h2
          have ⟨t'', hμ', hps, hHt''⟩ := ih t' μ' hHt' h2
          refine ⟨t'', hμ', ?_, hHt''⟩
          exact .step hp hps

/-! ## Lifting a `PureSteps` chain to `Machine.StepStarN` (any prog). -/

theorem PureSteps_to_singleton_StepStarN
    (prog : Program) (σ : Mem) :
    ∀ {t t' : Thread}, PureSteps t t' →
      ∃ n, Machine.StepStarN prog n ⟨σ, [t]⟩ ⟨σ, [t']⟩ := by
  intro t t' hps
  induction hps with
  | refl => exact ⟨0, .refl _⟩
  | @step ta tb tc hstep _ ih =>
      obtain ⟨n, htail⟩ := ih
      have hts : tstep prog.procs none σ ta = some (σ, tb, none) :=
        BodyTraj.pstep_tstep_procs prog.procs σ ta tb hstep
      have hone : Machine.Step prog ⟨σ, [ta]⟩ ⟨σ, [tb]⟩ := by
        have h1 := Machine.Step.step (p := prog)
          (i := 0) (chosen := none) (t := ta) (t' := tb) (sp := none)
          (m := σ) (m' := σ) (threads := [ta]) (hi := by rfl) (hstep := hts)
        have heq : ([ta] : List Thread).set 0 tb ++
                    ((none : Option Thread).toList) = [tb] := by simp
        rw [heq] at h1
        exact h1
      exact ⟨n + 1, .step hone htail⟩

/-! ## The procs-irrelevance lift for `SafeTp` -/

/-- **Procs-irrelevance lift for `Machine.SafeTp`.**

Given a `StrictHelperThread t` (no `.call`, no `.fork`, empty stack —
see `StrictHelperShape`), the operational safety of the singleton
thread pool `[t]` is *independent of the program's procs table*. So a
safety witness obtained against the standalone, `noProcs`-built helper
program (`programOfHelper`) transfers verbatim to safety against the
real composite's procs table.

**Why this is the key lift in the Route A showcase.** The Std.Do
triple lives in a procs-free world (it talks about `denote`, which uses
`noProcs` by definition). Without this lemma, we'd be stuck: the Iris
side wants `SafeTp composite.procs ⟨σ, [helper_init]⟩ φ`, but the
denotational chain only gives us `SafeTp noProcs ⟨σ, [helper_init]⟩ φ`.
`StrictHelperShape` bridges the two by observing that for any thread
whose statements never invoke `procs` (no `.call`, no `.fork`),
`tstep procs1 chosen m t = tstep procs2 chosen m t` holds pointwise
(`tstep_strict_procs_irrel`). Lifting that pointwise equality through
`Machine.StepStarN` and the `SafeTp` disjunction gives this lemma.

**Side condition.** `StrictHelperThread t` is closed under `tstep` (by
`pstep_preserves_strictHelperThread` + the fact that no tstep case
introduces `.call` or `.fork`), so the property is preserved along the
trajectory and the lift is sound.

**Usage in the showcase.** `helper_safeTp` in
`SimpleRangeProdCompositionRouteA.lean` reads in full:
```
helper_safeTp n a σ :=
  SafeTp_procs_irrel_of_strict
    (helper_init_strictHelperThread n a)
    (helperProg_safe n a σ)
``` -/
theorem SafeTp_procs_irrel_of_strict
    {prog1 prog2 : Program} {t : Thread} (he : StrictHelperThread t)
    {φ : Val → Prop} {σ : Mem}
    (h_safe : Machine.SafeTp prog1 ⟨σ, [t]⟩ φ) :
    Machine.SafeTp prog2 ⟨σ, [t]⟩ φ := by
  intro n μ' htraj k tk htk
  -- Walk the trajectory through prog2 via machineStepStarN_strictHelper.
  obtain ⟨t', hμ', hps, hHt'⟩ :=
    machineStepStarN_strictHelper prog2 σ n t μ' he htraj
  -- Lift the PureSteps chain to a Machine.StepStarN under prog1.
  obtain ⟨n1, htraj1⟩ :=
    PureSteps_to_singleton_StepStarN prog1 σ hps
  -- Apply h_safe at the prog1-trajectory.
  have h_at := h_safe n1 ⟨σ, [t']⟩ htraj1 k tk
  -- htk : μ'.threads[k]? = some tk; substitute μ'.
  rw [hμ'] at htk
  -- Apply h_at on tk = same thread index k.
  have h_disj := h_at htk
  -- Now reshape: the disjunction has `thread_reducible prog1.procs σ tk`.
  -- We need `thread_reducible prog2.procs μ'.mem tk`. Use procs irrelevance
  -- on the relevant tk (which is in [t'], so either tk = t' or vacuous).
  rcases h_disj with hval | hred
  · left; exact hval
  · right
    -- Identify tk: μ' = ⟨σ, [t']⟩, so threads[k]? = some tk forces
    -- k = 0 and tk = t'.
    rw [hμ']
    have htk_eq : tk = t' ∧ k = 0 := by
      rcases k with _ | k'
      · simp at htk; exact ⟨htk.symm, rfl⟩
      · simp at htk
    obtain ⟨htk_eq, hk0⟩ := htk_eq
    subst htk_eq
    -- hred : thread_reducible prog1.procs σ t'. Convert to prog2.
    obtain ⟨m', t'', sp, chosen, hstep1⟩ := hred
    refine ⟨m', t'', sp, chosen, ?_⟩
    rw [tstep_strict_procs_irrel hHt' prog2.procs prog1.procs chosen σ]
    exact hstep1

end Agar

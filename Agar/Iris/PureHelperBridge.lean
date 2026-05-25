module

public import Agar.Lang.Denotational
public import Agar.Iris.Adequacy
public import Agar.Iris.Completeness

@[expose] public section

/-! # PureHelper → `Machine.safe` bridge

Closes the loop between denotational reasoning on `PureHelper` and the
operational `Machine.safe` premise of completeness:

```
        denoteHelper h ρ₀ = some v ∧ φ v          (denotational, all ρ₀)
            ──────────────────────────────
              ∀ σ, Machine.safeFrom (programOfHelper h) σ φ
                                ↓ completeness
              ⊢ |={⊤}=>  wp_⊤ (Thread.initial h.main) {v. ⌜φ v⌝}
```

The denotational hypothesis is the natural shape for client reasoning
via Lean's `Std.Do` Hoare-triple framework on `StateM Env (Option Unit)`.
The bridge then feeds that hypothesis into completeness to deliver a
closed Iris derivation. -/

namespace Agar
open Agar.Logic

/-! ## Heap-freeness of helper programs -/

theorem unroll_heapFree (body : Stmt) (h : body.heapFree) :
    ∀ n, (unroll body n).heapFree
  | 0     => trivial
  | n + 1 => ⟨h, unroll_heapFree body h n⟩

theorem unrollW_heapFree (g : Expr) (body : Stmt) (h : body.heapFree) :
    ∀ n, (unrollW g body n).heapFree
  | 0     => trivial
  | n + 1 => ⟨⟨h, unrollW_heapFree g body h n⟩, trivial⟩

theorem embed_heapFree : ∀ s : PureStmt, (embed s).heapFree
  | .skip          => trivial
  | .assign _ _    => trivial
  | .seq s₁ s₂     => ⟨embed_heapFree s₁, embed_heapFree s₂⟩
  | .ite _ s₁ s₂   => ⟨embed_heapFree s₁, embed_heapFree s₂⟩
  | .repeat n s    => unroll_heapFree _ (embed_heapFree s) n
  | .forN n s      => unroll_heapFree _ (embed_heapFree s) n
  | .while_ n g s  => unrollW_heapFree g _ (embed_heapFree s) n

theorem PureHelper.main_heapFree (h : PureHelper) : h.main.heapFree :=
  ⟨embed_heapFree _, trivial⟩

theorem programOfHelper_heapFree (h : PureHelper) :
    (programOfHelper h).heapFree :=
  ⟨h.main_heapFree,
   by intro _ _ habs; simp [programOfHelper, noProcs] at habs⟩

/-! ## Helper-thread shape invariant

`HelperShape` covers exactly the statement forms reachable from
`embed body ; .ret e`: everything `embed` produces, plus `.ret`. Crucially
it rules out the operationally non-pure forms (`alloc`, `fork`,
`load/store/cas/free`, `whileDo`), so a `Machine.Step` on a helper thread
is forced to coincide with `pstep`. -/

inductive HelperShape : Stmt → Prop where
  | skip      : HelperShape .skip
  | assign    : ∀ x e, HelperShape (.assign x e)
  | seq       : ∀ s₁ s₂, HelperShape s₁ → HelperShape s₂ →
                  HelperShape (.seq s₁ s₂)
  | ite       : ∀ g s₁ s₂, HelperShape s₁ → HelperShape s₂ →
                  HelperShape (.ite g s₁ s₂)
  | callStuck : ∀ x f args, HelperShape (.call x f args)
  | ret       : ∀ e, HelperShape (.ret e)

theorem embedShape_helperShape : ∀ {s}, EmbedShape s → HelperShape s
  | _, .skip => .skip
  | _, .assign x e => .assign x e
  | _, .seq s₁ s₂ h₁ h₂ =>
      .seq s₁ s₂ (embedShape_helperShape h₁) (embedShape_helperShape h₂)
  | _, .ite e s₁ s₂ h₁ h₂ =>
      .ite e s₁ s₂ (embedShape_helperShape h₁) (embedShape_helperShape h₂)
  | _, .callStuck x f args => .callStuck x f args

structure HelperThread (t : Thread) : Prop where
  stmt   : HelperShape t.stmt
  cont   : ∀ s ∈ t.cont, HelperShape s
  stack  : t.stack = []

theorem helperThread_initial (h : PureHelper) :
    HelperThread (Thread.initial h.main) := by
  refine ⟨?_, ?_, rfl⟩
  · show HelperShape h.main
    exact .seq _ _ (embedShape_helperShape (embed_embedShape h.body)) (.ret _)
  · intro s hmem; cases hmem

/-! ### `pstep` preservation -/

theorem pstep_preserves_helperThread {t t' : Thread}
    (he : HelperThread t) (h : pstep t = some t') :
    HelperThread t' := by
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
  | callStuck x f args =>
      exfalso
      simp [tstep, callFrom, noProcs] at h
  | ret e =>
      -- stack = [] forces the top-level branch of doReturn.
      simp [tstep] at h
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          simp [hev, doReturn] at h
          rcases h with ⟨rfl⟩
          refine ⟨.skip, ?_, rfl⟩
          intro c hc; cases hc

/-! ### `Machine.Step` characterization for helper threads

`HelperShape` rules out `alloc` and `fork`, so any `Machine.Step` on a
singleton helper threadpool is forced to be:
* at thread index 0,
* with `chosen = none`,
* with no spawned thread,
* leaving memory untouched.

Combined with memory-independence of `pstep` (`pstep_machine_indep`),
this means `Machine.Step` and `pstep` are interchangeable on helper
trajectories. -/

theorem tstep_helperShape_chosen_some {t : Thread}
    (he : HelperThread t) (l : Loc) (m : Mem) :
    tstep noProcs (some l) m t = none := by
  unfold tstep
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  have hst := he.stmt
  cases hst <;> simp

/-- The `chosen = none` case is independent of `HelperThread` —
`pstep_machine_indep` already covers it for any thread. Re-exported here
under a uniformly-named helper for the `Machine.Step` lifting. -/
theorem tstep_helperShape_chosen_none {t t' : Thread}
    (h : pstep t = some t') (m : Mem) :
    tstep noProcs none m t = some (m, t', none) :=
  pstep_machine_indep t t' h m

/-- Memory-independent inverse: when `chosen = none` and `pstep t = none`,
`tstep` is also stuck (at any heap `m`). Needed for the "stuck under
`pstep` ⇒ stuck under `Machine.Step`" direction. -/
theorem tstep_helperShape_chosen_none_stuck {t : Thread}
    (he : HelperThread t) (h : pstep t = none) (m : Mem) :
    tstep noProcs none m t = none := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  have hst := he.stmt
  have hsk := he.stack
  simp at hsk; subst hsk
  unfold pstep at h
  cases hst with
  | skip =>
      cases cont with
      | nil =>
          -- terminal: skip, [], [] → tstep returns none.
          simp [tstep]
      | cons s rest =>
          -- skip with non-empty cont: pstep succeeds. Contradiction.
          simp [tstep] at h
  | assign x e =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e with
      | none => simp
      | some v => simp [hev] at h
  | seq s₁ s₂ _ _ =>
      simp [tstep] at h
  | ite g s₁ s₂ _ _ =>
      cases hev : Expr.eval env g with
      | none =>
          simp [tstep, hev] at h
          simp [tstep, hev]
      | some v =>
          cases v <;> (simp [tstep, hev] at h; simp [tstep, hev])
          rename_i b; cases b <;> simp at h
  | callStuck x f args =>
      simp [tstep, callFrom, noProcs]
  | ret e =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e with
      | none => simp
      | some v =>
          simp [hev, doReturn] at h

/-- A `Machine.Step` from a singleton helper threadpool corresponds to a
`pstep`, with memory and threadpool shape preserved. -/
theorem machineStep_helper (h : PureHelper) (σ : Mem) (t : Thread) (μ' : Machine)
    (he : HelperThread t)
    (hs : Machine.Step (programOfHelper h) ⟨σ, [t]⟩ μ') :
    ∃ t', μ' = ⟨σ, [t']⟩ ∧ pstep t = some t' ∧ HelperThread t' := by
  obtain ⟨i, chosen, t₀, t₁, sp, m', hi, hstep, hμ'⟩ := hs.invert
  -- index 0 is the only thread.
  have hi0 : i = 0 := by
    rcases i with _ | i'
    · rfl
    · simp at hi
  subst hi0; simp at hi; subst hi
  -- chosen = none, else HelperShape rules out alloc.
  have hch : chosen = none := by
    cases chosen with
    | none => rfl
    | some l =>
        exfalso
        rw [show (programOfHelper h).procs = noProcs from rfl] at hstep
        rw [tstep_helperShape_chosen_some he l σ] at hstep
        cases hstep
  subst hch
  -- Now hstep is at chosen=none. Pin down its result via pstep.
  -- chosen = none, programOfHelper has noProcs.
  rw [show (programOfHelper h).procs = noProcs from rfl] at hstep
  -- Combined extraction: pstep t = some t₁, m' = σ, sp = none, HelperThread t₁.
  have hbundle : pstep t = some t₁ ∧ m' = σ ∧ sp = none ∧ HelperThread t₁ := by
    match hp : pstep t with
    | some tp =>
        have hts := tstep_helperShape_chosen_none hp σ
        rw [hts] at hstep
        -- hstep : some (σ, tp, none) = some (m', t₁, sp)
        have heq : (σ, tp, none) = (m', t₁, sp) := Option.some.inj hstep
        have hmm : m' = σ := (congrArg Prod.fst heq).symm
        have htp : tp = t₁ := congrArg (Prod.fst ∘ Prod.snd) heq
        have hsp : sp = (none : Option Thread) :=
          (congrArg (Prod.snd ∘ Prod.snd) heq).symm
        refine ⟨?_, hmm, hsp, ?_⟩
        · exact congrArg some htp
        · rw [← htp]; exact pstep_preserves_helperThread he hp
    | none =>
        exfalso
        have hts := tstep_helperShape_chosen_none_stuck he hp σ
        rw [hts] at hstep
        cases hstep
  obtain ⟨hps, hmm, hsp, hHt⟩ := hbundle
  refine ⟨t₁, ?_, hps, hHt⟩
  rw [hμ', hmm, hsp]; simp

/-- Lifting `Machine.StepStarN` over a singleton helper threadpool to a
`PureSteps` chain. Memory and singleton-shape are preserved throughout. -/
theorem machineStepStarN_helper (h : PureHelper) (σ : Mem) :
    ∀ n μ', Machine.StepStarN (programOfHelper h) n ⟨σ, [Thread.initial h.main]⟩ μ' →
      ∃ t', μ' = ⟨σ, [t']⟩ ∧ PureSteps (Thread.initial h.main) t' ∧
            HelperThread t' := by
  intro n μ'
  -- Induct on n, generalising over the start thread.
  suffices H : ∀ n t μ', HelperThread t →
      Machine.StepStarN (programOfHelper h) n ⟨σ, [t]⟩ μ' →
      ∃ t', μ' = ⟨σ, [t']⟩ ∧ PureSteps t t' ∧ HelperThread t' by
    intro hs
    have ⟨t', hμ', hps, hHt⟩ := H n _ μ' (helperThread_initial h) hs
    exact ⟨t', hμ', hps, hHt⟩
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
          obtain ⟨t', hμ'_mid, hp, hHt'⟩ := machineStep_helper h σ t _ he h1
          -- Substitute μ_mid = ⟨σ, [t']⟩ in h2.
          rw [hμ'_mid] at h2
          have ⟨t'', hμ', hps, hHt''⟩ := ih t' μ' hHt' h2
          refine ⟨t'', hμ', ?_, hHt''⟩
          exact .step hp hps

/-! ## Terminal thread and trajectory uniqueness -/

/-- The unique terminated thread of the helper trajectory at final env
`ρf` with returned value `v`. -/
def helperTerminal (ρf : Env) (v : Val) : Thread :=
  { stmt := .skip, cont := [], env := ρf, stack := [], result := some v }

theorem helperTerminal_pstuck (ρf : Env) (v : Val) :
    pstuck (helperTerminal ρf v) := by
  unfold pstuck pstep helperTerminal; simp [tstep]

theorem helperTerminal_toValue (ρf : Env) (v : Val) :
    (helperTerminal ρf v).toValue = some v := rfl

/-- Trajectory from the helper's initial thread to the terminal,
witnessed by a successful body denotation and a defined return
expression. -/
theorem PureHelper.reaches_terminal (h : PureHelper) (ρf : Env) (v : Val)
    (hd : denote h.body Env.empty = (some (), ρf))
    (hv : Expr.eval ρf h.ret = some v) :
    PureSteps (Thread.initial h.main) (helperTerminal ρf v) := by
  -- Step 1: seq pop.
  have hstep1 : pstep (Thread.initial h.main) =
      some (mkT (embed h.body) [.ret h.ret] Env.empty) := by
    show pstep ⟨h.main, [], Env.empty, [], none⟩ = _
    unfold PureHelper.main; rfl
  -- Step 2: body via denote_sound.
  have hbody : PureSteps (mkT (embed h.body) [.ret h.ret] Env.empty)
                         (mkT .skip [.ret h.ret] ρf) :=
    denote_sound h.body [.ret h.ret] Env.empty ρf hd
  -- Step 3: skip pops the trailing `.ret`.
  have hstep3 : pstep (mkT .skip [.ret h.ret] ρf) =
                  some (mkT (.ret h.ret) [] ρf) := rfl
  -- Step 4: ret fires, doReturn on empty stack terminates the thread.
  have hstep4 : pstep (mkT (.ret h.ret) [] ρf) = some (helperTerminal ρf v) := by
    show pstep ⟨.ret h.ret, [], ρf, [], none⟩ = _
    simp [pstep, tstep, hv, doReturn, helperTerminal]
  -- Chain everything.
  exact .step hstep1 (hbody.trans (.step hstep3 (.single hstep4)))

/-! ## The safety bridge -/

/-- **Main bridge.** From a denotational identity at `Env.empty`
witnessing both the helper's success and `φ` at the returned value,
conclude operational `Machine.safe`-from any starting heap. -/
theorem Machine.safe_of_denoteHelper
    {h : PureHelper} {φ : Val → Prop}
    (hφ : ∃ v, denoteHelper h Env.empty = some v ∧ φ v) :
    ∀ σ, Machine.safeFrom (programOfHelper h) σ φ := by
  intro σ n μ' htraj k t htk
  -- Extract the denotation at Env.empty.
  obtain ⟨v_top, hv_top, hφ_top⟩ := hφ
  -- Decompose denoteHelper into (denote body, Expr.eval ret).
  have ⟨ρf, hd, hv⟩ :
      ∃ ρf, denote h.body Env.empty = (some (), ρf) ∧
            Expr.eval ρf h.ret = some v_top := by
    unfold denoteHelper at hv_top
    rcases hdc : denote h.body Env.empty with ⟨o, ρf⟩
    rw [hdc] at hv_top
    cases o with
    | none   => cases hv_top
    | some _ => exact ⟨ρf, rfl, hv_top⟩
  -- Pin down μ' = ⟨σ, [t']⟩ with t' reachable.
  obtain ⟨t', hμ', hps, hHt'⟩ := machineStepStarN_helper h σ n μ' htraj
  -- Case on the thread index k.
  rcases k with _ | k
  · -- k = 0
    rw [hμ'] at htk
    simp at htk
    subst htk
    -- Case on pstep t'.
    rcases hp : pstep t' with _ | tn
    · -- Stuck. Use stuck_unique to identify t' with the terminal.
      have hps_term :
          PureSteps (Thread.initial h.main) (helperTerminal ρf v_top) :=
        PureHelper.reaches_terminal h ρf v_top hd hv
      have hstuck_term : pstuck (helperTerminal ρf v_top) :=
        helperTerminal_pstuck ρf v_top
      have hstuck_t' : pstuck t' := hp
      have ht_eq : t' = helperTerminal ρf v_top :=
        PureSteps.stuck_unique hps hstuck_t' hps_term hstuck_term
      subst ht_eq
      left
      refine ⟨v_top, helperTerminal_toValue ρf v_top, fun _ => hφ_top⟩
    · -- Reducible.
      right
      refine ⟨σ, tn, none, none, ?_⟩
      show tstep (programOfHelper h).procs none _ _ = _
      rw [hμ']
      show tstep noProcs none σ t' = _
      exact tstep_helperShape_chosen_none hp σ
  · -- k > 0: μ'.threads = [t'], so threads[k+1]? = none, vacuous.
    rw [hμ'] at htk
    simp at htk

/-- Closed-heap version, matching `Machine.safe = Machine.safeFrom`
at the empty heap. -/
theorem Machine.safe_of_denoteHelper_closed
    {h : PureHelper} {φ : Val → Prop}
    (hφ : ∃ v, denoteHelper h Env.empty = some v ∧ φ v) :
    Machine.safe (programOfHelper h) φ :=
  Machine.safe_of_denoteHelper hφ Mem.empty

/-- **Total-correctness wrapper.** Aligns with `Std.Do`-style total
specs: any `ρ₀` yields a successful denotation satisfying `φ`. The
bridge specialises to `Env.empty` internally. -/
theorem Machine.safe_of_denoteHelper_total
    {h : PureHelper} {φ : Val → Prop}
    (hφ : ∀ ρ₀, ∃ v, denoteHelper h ρ₀ = some v ∧ φ v) :
    ∀ σ, Machine.safeFrom (programOfHelper h) σ φ :=
  Machine.safe_of_denoteHelper (hφ Env.empty)

/-! ## Composition with completeness

Feed the bridge into `Agar.Logic.completeness` (Theorem 15) to obtain a
closed Iris derivation of `wp_⊤` over freshly-allocated ghost state. The
denotational hypothesis is all the client needs. -/

section Composition
open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF]

/-- **End-to-end pipeline.** From a denotational identity at
`Env.empty`, derive a closed Iris `wp` for the compiled program. The
`fork_post` is `True` (the helper never forks). -/
theorem PureHelper.wp_of_denote
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F]
    [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF]
    {h : PureHelper} {φ : Val → Prop}
    (hφ : ∃ v, denoteHelper h Env.empty = some v ∧ φ v) :
    ∀ [_LC : InvGS_gen false GF],
      ⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
        state_interp (GF := GF) Mem.empty ∗
        wp (programOfHelper h).procs fork_post ⊤
           (Thread.initial (programOfHelper h).main)
           (fun v => iprop(⌜φ v⌝ : IProp GF)) := by
  intro _LC
  exact completeness GF F
    (programOfHelper_heapFree h)
    (Machine.safe_of_denoteHelper hφ)

end Composition

/-! ## Smoke tests

Trivial verifications that the bridge actually fires. The first uses a
constant-returning helper; the second uses the Gauss-sum loop, showing
that real denotational identities (Gauss closed form) discharge `φ`
through the bridge.

These are `example`s, not `theorem`s — their only job is to typecheck. -/

section SmokeTests
open Iris Iris.BI Iris.OFE

/-- Helper that ignores its input and returns a fixed `Val`. -/
def constHelper (v : Val) : PureHelper where
  body := .skip
  ret  := .val v

theorem denoteHelper_const (v : Val) :
    denoteHelper (constHelper v) Env.empty = some v := rfl

example (v : Val) :
    ∀ σ, Machine.safeFrom (programOfHelper (constHelper v)) σ (· = v) :=
  Machine.safe_of_denoteHelper ⟨v, denoteHelper_const v, rfl⟩

/-- Same constant helper, lifted to a closed Iris derivation via
completeness. -/
example (v : Val)
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F]
    [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF] [_LC : InvGS_gen false GF] :
    ⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
      state_interp (GF := GF) Mem.empty ∗
      wp (programOfHelper (constHelper v)).procs fork_post ⊤
         (Thread.initial (programOfHelper (constHelper v)).main)
         (fun w => iprop(⌜w = v⌝ : IProp GF)) :=
  PureHelper.wp_of_denote (φ := (· = v)) GF F
    ⟨v, denoteHelper_const v, rfl⟩

/-- **Gauss-sum helper.** Wrap the existing `sumProg n` body with a
return of `s`. Operationally: the main thread of `programOfHelper` runs
the loop and terminates with `Val.int (gauss n)`. The denotational
hypothesis is discharged by the existing closed-form theorem
`denote_sumProg`. -/
def gaussHelper (n : Nat) : PureHelper where
  body := sumProg n
  ret  := .var "s"

theorem denoteHelper_gauss (n : Nat) :
    denoteHelper (gaussHelper n) Env.empty = some (.int (gauss n)) := by
  unfold denoteHelper gaussHelper
  rw [denote_sumProg n]
  rfl

example (n : Nat) :
    ∀ σ, Machine.safeFrom (programOfHelper (gaussHelper n)) σ
                          (· = Val.int (gauss n)) :=
  Machine.safe_of_denoteHelper ⟨_, denoteHelper_gauss n, rfl⟩

/-- Gauss-sum helper composed all the way to a closed Iris wp. -/
example (n : Nat)
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F]
    [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF] [_LC : InvGS_gen false GF] :
    ⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
      state_interp (GF := GF) Mem.empty ∗
      wp (programOfHelper (gaussHelper n)).procs fork_post ⊤
         (Thread.initial (programOfHelper (gaussHelper n)).main)
         (fun w => iprop(⌜w = Val.int (gauss n)⌝ : IProp GF)) :=
  PureHelper.wp_of_denote (φ := (· = Val.int (gauss n))) GF F
    ⟨_, denoteHelper_gauss n, rfl⟩

end SmokeTests

end Agar



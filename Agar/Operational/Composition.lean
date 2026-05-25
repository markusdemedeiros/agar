module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Adequacy
public import Agar.Iris.Completeness

@[expose] public section

/-! # Operational composition of a pure helper with an abstract composite

This file is **purely operational** — no Iris, no `wp`, no `state_interp`.
Its job is to deliver a *concrete* `Machine.safe composite composite_post`
from:

1. The standalone safety of a pure helper procedure
   (`StandaloneHelperSafe`) — a `Machine.safe` of the helper run as a
   one-shot program with its parameters baked in.
2. The safety of the composite under an *abstract* step relation
   (`Machine.SafeTp_abstract`) — calls to the helper are treated as
   single atomic steps with a known input-output postcondition
   `helper_post : List Val → Val → Prop`.

The output plugs directly into `Agar.Logic.completeness` to yield an
Iris `wp` on the composite without any per-call wp rule or new
completeness variant.

## Outline

* `Stmt.noCall` — recursive predicate ruling out `.call` in a statement.
* `Stmt.forkFree` — recursive predicate ruling out `.fork`.
* `Machine.Step_abstract` — two-constructor abstract step relation
  (regular non-helper-call step, or atomic helper-call collapse).
* `Machine.StepStarN_abstract` and `Machine.SafeTp_abstract` — the
  n-step closure and thread-pool safety against the abstract relation.
* `assignAllParams` / `programOfHelperAtVs` — bake `vs` into a helper's
  main as a sequence of `.assign param_i (.val vs[i])` before its body.
* `StandaloneHelperSafe` — `Machine.safe` of `programOfHelperAtVs h vs`
  against the helper post.
* `Machine.safe_compose` — the composition lemma (statement + proof
  skeleton).

The proof of `Machine.safe_compose` proceeds by *forward simulation*
between the abstract and concrete steppings. The simulation invariant
classifies each thread as either *Matching* (abstract and concrete
states agree thread-wise) or *InBody* (concrete thread is somewhere
inside the helper body, abstract thread has already taken the atomic
step). See `COMPOSITION_DESIGN.md` for the full sketch.
-/

namespace Agar
open Agar.Logic

/-! ## `Stmt.noCall` and `Stmt.forkFree` (auxiliary predicates)

These are recursive structural predicates on `Stmt`. They sit alongside
`Stmt.heapFree` from `Agar.Iris.Completeness`. -/

/-- A statement is *call-free* if no sub-statement is a `.call`. The
helper body is required to be `noCall` so that no nested calls can
appear during its execution — eliminates a class of stack-bookkeeping
bugs. -/
def Stmt.noCall : Stmt → Prop
  | .skip          => True
  | .assign _ _    => True
  | .load _ _      => True
  | .store _ _     => True
  | .alloc _ _     => True
  | .free _        => True
  | .cas _ _ _ _   => True
  | .seq s₁ s₂     => s₁.noCall ∧ s₂.noCall
  | .ite _ s₁ s₂   => s₁.noCall ∧ s₂.noCall
  | .whileDo _ s   => s.noCall
  | .call _ _ _    => False
  | .ret _         => True
  | .fork _ _      => True

/-- A statement is *fork-free* if no sub-statement is a `.fork`. The
helper body is required to be `forkFree` so it never spawns new
threads. -/
def Stmt.forkFree : Stmt → Prop
  | .skip          => True
  | .assign _ _    => True
  | .load _ _      => True
  | .store _ _     => True
  | .alloc _ _     => True
  | .free _        => True
  | .cas _ _ _ _   => True
  | .seq s₁ s₂     => s₁.forkFree ∧ s₂.forkFree
  | .ite _ s₁ s₂   => s₁.forkFree ∧ s₂.forkFree
  | .whileDo _ s   => s.forkFree
  | .call _ _ _    => True
  | .ret _         => True
  | .fork _ _      => False

/-! ## Abstract step relation

`Machine.Step_abstract` is the *abstract* one-step relation that treats
helper calls as a single atomic transition with a known post. It has
two constructors:

* `regular` — any concrete `Machine.Step` *except* a `.call h_pname …`
  on some thread.
* `atomic_call` — replace a `.call h_pname args` on thread `i` with a
  single transition that:
  - evaluates the args to `vs`,
  - existentially picks a `v` satisfying `helper_post vs v`,
  - updates thread `i` to `⟨.skip, cont, env.set x v, stack, none⟩`.

The mem is unchanged in the `atomic_call` case (helper is heap-free).
No spawned thread (helper is fork-free).
-/

inductive Machine.Step_abstract
    (composite : Program) (h_pname : Name) (h : Proc)
    (helper_post : List Val → Val → Prop) :
    Machine → Machine → Prop where
  | regular
      (i : Nat) (chosen : Option Loc)
      (t t' : Thread) (sp : Option Thread) (m m' : Mem)
      (threads : List Thread)
      (hi : threads[i]? = some t)
      (hnot_helper_call :
        ¬ ∃ (x : Name) (args : List Expr) (vs : List Val),
          t.stmt = .call x h_pname args ∧
          evalArgs t.env args = some vs) :
      tstep composite.procs chosen m t = some (m', t', sp) →
      Machine.Step_abstract composite h_pname h helper_post
        ⟨m, threads⟩
        ⟨m', threads.set i t' ++ sp.toList⟩
  | atomic_call
      (i : Nat) (x : Name) (args : List Expr) (vs : List Val) (v : Val)
      (cont : List Stmt) (env : Env) (stack : List Frame)
      (m : Mem) (threads : List Thread)
      (hi : threads[i]? = some
              (⟨.call x h_pname args, cont, env, stack, none⟩ : Thread))
      (hargs : evalArgs env args = some vs)
      (harity : vs.length = h.params.length)
      (hpost : helper_post vs v) :
      Machine.Step_abstract composite h_pname h helper_post
        ⟨m, threads⟩
        ⟨m, threads.set i ⟨.skip, cont, env.set x v, stack, none⟩⟩

/-- n-step closure of the abstract step relation. Analogue of
`Machine.StepStarN`. -/
inductive Machine.StepStarN_abstract
    (composite : Program) (h_pname : Name) (h : Proc)
    (helper_post : List Val → Val → Prop) :
    Nat → Machine → Machine → Prop where
  | refl (μ : Machine) :
      Machine.StepStarN_abstract composite h_pname h helper_post 0 μ μ
  | step {n : Nat} {μ μ' μ'' : Machine}
      (h1 : Machine.Step_abstract composite h_pname h helper_post μ μ')
      (h2 : Machine.StepStarN_abstract composite h_pname h helper_post n μ' μ'') :
      Machine.StepStarN_abstract composite h_pname h helper_post n.succ μ μ''

/-- A thread is *abstract-reducible* in `m` if some abstract step is
available. This is *either* a real concrete step (that is not an
`h_pname` call), *or* a helper-call collapse with some `v` satisfying
`helper_post` *and matching arity*. Mirrors `thread_reducible`. -/
def thread_reducible_abstract
    (composite : Program) (h_pname : Name) (h : Proc)
    (helper_post : List Val → Val → Prop)
    (m : Mem) (t : Thread) : Prop :=
  (∃ m' t' sp, thread_step composite.procs m t m' t' sp ∧
    ¬ ∃ (x : Name) (args : List Expr) (vs : List Val),
        t.stmt = .call x h_pname args ∧ t.result = none ∧
        evalArgs t.env args = some vs)
  ∨
  (∃ (x : Name) (args : List Expr) (vs : List Val) (v : Val),
      t.stmt = .call x h_pname args ∧
      t.result = none ∧
      evalArgs t.env args = some vs ∧
      vs.length = h.params.length ∧
      helper_post vs v)

/-- **Abstract thread-pool safety.** The abstract analogue of
`Machine.SafeTp`: against the abstract step relation, every reachable
configuration has every thread either at a `toValue` (with
`composite_post` at thread 0) or abstract-reducible. -/
def Machine.SafeTp_abstract
    (composite : Program) (h_pname : Name) (h : Proc)
    (helper_post : List Val → Val → Prop)
    (μ : Machine) (post : Val → Prop) : Prop :=
  ∀ n μ', Machine.StepStarN_abstract composite h_pname h helper_post n μ μ' →
    ∀ k t, μ'.threads[k]? = some t →
      (∃ v, t.toValue = some v ∧ (k = 0 → post v)) ∨
      thread_reducible_abstract composite h_pname h helper_post μ'.mem t

/-- Pointwise version at the initial configuration. -/
theorem Machine.SafeTp_abstract.here
    {composite : Program} {h_pname : Name} {h : Proc}
    {helper_post : List Val → Val → Prop}
    {μ : Machine} {post : Val → Prop}
    (hs : Machine.SafeTp_abstract composite h_pname h helper_post μ post)
    {k : Nat} {t : Thread} (hk : μ.threads[k]? = some t) :
    (∃ v, t.toValue = some v ∧ (k = 0 → post v)) ∨
    thread_reducible_abstract composite h_pname h helper_post μ.mem t :=
  hs 0 μ (.refl μ) k t hk

/-- Step closure of abstract safety. -/
theorem Machine.SafeTp_abstract.step_closed
    {composite : Program} {h_pname : Name} {h : Proc}
    {helper_post : List Val → Val → Prop}
    {μ μ₂ : Machine} {post : Val → Prop}
    (hs : Machine.SafeTp_abstract composite h_pname h helper_post μ post)
    (hst : Machine.Step_abstract composite h_pname h helper_post μ μ₂) :
    Machine.SafeTp_abstract composite h_pname h helper_post μ₂ post :=
  fun n μ' htr => hs (n + 1) μ' (.step hst htr)

/-! ## Baking `vs` into a helper's main

`programOfHelperAtVs h vs` is a one-shot program whose `main` first
assigns each parameter the corresponding value from `vs`, then runs the
helper body. The helper body is expected to end with a `.ret`, so the
thread terminates with a value. -/

/-- Build a sequence of `.assign param_i (.val vs[i])` statements,
collapsing to `.skip` when either list is empty. The caller is expected
to supply lists of matching length. -/
def assignAllParams : List Name → List Val → Stmt
  | [],          _          => .skip
  | _ :: _,      []         => .skip
  | n :: [],     v :: _     => .assign n (.val v)
  | n :: m :: ns, v :: vs   => .seq (.assign n (.val v)) (assignAllParams (m :: ns) vs)

/-- The "no procedures" environment for the standalone helper program.
We define this locally to keep this file free of `Agar.Lang.Denotational`
dependency. -/
def noProcsLocal : Name → Option Proc := fun _ => none

/-- `programOfHelperAtVs h vs` packages a helper as a closed program
where its parameters have been bound to `vs` via a leading sequence of
`.assign` statements. `main = assignAllParams h.params vs ; h.body`.
The helper body is expected to itself end with a `.ret`, so the thread
terminates with a value. -/
def programOfHelperAtVs (h : Proc) (vs : List Val) : Program where
  procs := noProcsLocal
  main  := .seq (assignAllParams h.params vs) h.body

/-- **Standalone helper safety.** Bundles `Machine.safe` of the
parameter-bound helper-as-program *with* a termination witness: the
helper's body actually reaches some terminated state with a value
satisfying `helper_post`. The bridge produces both from a denotational
identity (termination is the bridge's content; safety follows). This is
the per-`vs` premise of `Machine.safe_compose`. -/
structure StandaloneHelperSafe (h : Proc) (vs : List Val)
    (helper_post : List Val → Val → Prop) : Prop where
  safe : Machine.safe (programOfHelperAtVs h vs) (helper_post vs)
  reaches : ∃ (n : Nat) (μ' : Machine) (t : Thread) (v : Val),
    Machine.StepStarN (programOfHelperAtVs h vs) n
      (Machine.initial (programOfHelperAtVs h vs)) μ' ∧
    μ'.threads = [t] ∧
    t.toValue = some v ∧
    helper_post vs v

/-! ## The simulation invariant

The simulation invariant relates an *abstract* machine state to a
*concrete* one. The `mem`s coincide; for each thread index, the pair is
either *Matching* (states agree) or *InBody* (concrete thread is inside
the helper body, abstract thread has already taken the atomic step).

We use a `structure` over `inductive` because the per-index relation
needs to be looked up by index and the structure form makes
field-access trivial. -/
structure Sim
    (composite : Program) (h_pname : Name) (h : Proc)
    (helper_post : List Val → Val → Prop)
    (μ_abs μ_concrete : Machine) : Prop where
  mem_eq : μ_abs.mem = μ_concrete.mem
  length_eq : μ_abs.threads.length = μ_concrete.threads.length
  /-- Every concrete thread is heap-free. Established initially when the
  composite is heap-free, and preserved by every step. Used to discharge
  the InBody arm's heap-free obligations and to transport reducibility
  across memory changes from other threads. -/
  threads_heapFree :
    ∀ (i : Nat) (t : Thread), μ_concrete.threads[i]? = some t → t.heapFree
  /-- Every concrete thread has `result = none` unless it has terminated
  (`stmt = .skip ∧ cont = [] ∧ stack = []`). Established initially and
  preserved by every step (since `doReturn` only writes a non-`none`
  result when it also resets `stmt`/`cont`/`stack` to terminated form). -/
  threads_result_wf :
    ∀ (i : Nat) (t : Thread), μ_concrete.threads[i]? = some t →
      t.result = none ∨ (t.stmt = .skip ∧ t.cont = [] ∧ t.stack = [])
  /-- For each index `i`, the per-thread relation. Either the threads
  match exactly (the `inl` arm), or the abstract has already collapsed
  the helper call into its post-call state and the concrete is inside
  the body (the `inr` arm). -/
  thread_sim :
    ∀ (i : Nat), ∀ (t_a t_c : Thread),
      μ_abs.threads[i]? = some t_a →
      μ_concrete.threads[i]? = some t_c →
      -- Matching:
      (t_a = t_c) ∨
      -- InBody: there exist a saved frame and a helper-produced value
      -- `v_h` such that the abstract is post-call and the concrete is
      -- inside the body. We additionally carry:
      --   * `reducible`: the concrete thread can take a step.
      -- The simulation step preserves these because the body never
      -- gets stuck en route to its terminating `.ret` (standalone
      -- helper safety) and never touches the heap. Heap-freeness of
      -- the concrete thread is supplied uniformly by
      -- `Sim.threads_heapFree`.
      (∃ (vs : List Val) (v_h : Val) (cont : List Stmt) (env : Env)
         (rv : Name) (rest : List Frame),
        helper_post vs v_h ∧
        vs.length = h.params.length ∧
        t_a = (⟨.skip, cont, env.set rv v_h, rest, none⟩ : Thread) ∧
        t_c.stack = (⟨rv, cont, env⟩ : Frame) :: rest ∧
        t_c.result = none ∧
        thread_reducible composite.procs μ_concrete.mem t_c)

/-! ## Auxiliary lemmas (left as `sorry` — see design notes)

The full proof of `Machine.safe_compose` requires:

* **`body_deterministic`** — for a `noCall ∧ heapFree ∧ forkFree` body
  running from `bindParams h.params vs`, the per-thread trajectory and
  the helper's returned `v_h` are unique. Used to pin down the abstract
  state's `v_h` from the concrete state's reachability.

* **`simulation_init`** — `Sim composite h_pname h helper_post
    (Machine.initial composite) (Machine.initial composite)`. The
  initial configuration has a single thread `Thread.initial main` on
  both sides — Matching.

* **`simulation_step`** — given `Sim μ_a μ_c` and a concrete
  `Machine.Step composite μ_c μ_c'`, there exist `n_abs ∈ {0, 1}` and
  `μ_a'` with `Machine.StepStarN_abstract … n_abs μ_a μ_a'` and
  `Sim μ_a' μ_c'`. Four cases (see design).

* **`sim_transfer`** — given `Sim μ_a μ_c` and the abstract safety at
  `μ_a`, every thread of `μ_c` is value-or-reducible (with
  `composite_post` at index 0 on termination).

These are sketched in `COMPOSITION_DESIGN.md` and left as named
`sorry`s here for now. -/

/-! ### Auxiliary lemmas about `tstep`

The two lemmas below establish small invariants used by the simulation:
* `tstep_result_wf_preserves`: the post-thread is either `result = none`
  or terminated (proved by case-splitting `stmt`).
* `tstep_sp_result_none`: a freshly spawned thread (only possible via
  the `.fork` branch) has `result = none`.
* `tstep_sp_heapFree`: that spawned thread is heap-free when the
  parent thread and the proc table are heap-free.

Most cases of `tstep_result_wf_preserves` are straightforward; the
fiddly part is the multi-way `match` discharges on heap-touching
branches. We follow the `Iris/Completeness.lean` style of using `match
hev : ... , h with` to name the discriminant for `cases h`. -/
private theorem tstep_result_wf_preserves
    {procs : Name → Option Proc} {chosen : Option Loc} {m : Mem} {t : Thread}
    {m' : Mem} {t' : Thread} {sp : Option Thread}
    (hresult : t.result = none ∨
               (t.stmt = .skip ∧ t.cont = [] ∧ t.stack = []))
    (h : tstep procs chosen m t = some (m', t', sp)) :
    t'.result = none ∨ (t'.stmt = .skip ∧ t'.cont = [] ∧ t'.stack = []) := by
  -- If `t` was terminated, `tstep` fails — contradiction.
  rcases hresult with hres | ⟨hst, hco, hsk⟩
  · -- t.result = none. We'll case on stmt.
    obtain ⟨stmt, cont, env, stack, result⟩ := t
    simp only at hres; subst hres
    cases chosen with
    | some l =>
      cases stmt <;> (simp only [tstep] at h)
      all_goals try cases h
      -- only alloc fires
      rename_i x e
      split at h
      · cases h
      · split at h
        · cases h
        · cases h; left; rfl
    | none =>
      cases stmt with
      | skip =>
        simp only [tstep] at h
        match hev : cont, stack, h with
        | s :: _, _, h => cases h; left; rfl
        | [], [], h => cases h
        | [], fr :: rest, h =>
          simp only [doReturn] at h
          match hev : fr.cont, h with
          | [], h => cases h; left; rfl
          | s :: cs, h => cases h; left; rfl
      | assign x e =>
        simp only [tstep] at h
        match hev : Expr.eval env e, h with
        | none, h => cases h
        | some v, h => cases h; left; rfl
      | load x e =>
        simp only [tstep] at h
        match hev : Expr.eval env e, h with
        | none, h => cases h
        | some (.int _), h => cases h
        | some (.bool _), h => cases h
        | some (.unit), h => cases h
        | some (.struct _), h => cases h
        | some (.loc l), h =>
          simp only at h
          match hev : m.load l, h with
          | none, h => cases h
          | some w, h => cases h; left; rfl
      | store eL eV =>
        simp only [tstep] at h
        match hev : Expr.eval env eL, Expr.eval env eV, h with
        | some (.loc l), some v, h =>
          simp only at h
          match hev : m.store l v, h with
          | none, h => cases h
          | some m', h => cases h; left; rfl
        | none, _, h => cases h
        | some (.int _), _, h => cases h
        | some (.bool _), _, h => cases h
        | some (.unit), _, h => cases h
        | some (.struct _), _, h => cases h
        | some (.loc _), none, h => cases h
      | alloc x e => simp only [tstep] at h; cases h
      | free e =>
        simp only [tstep] at h
        match hev : Expr.eval env e, h with
        | none, h => cases h
        | some (.int _), h => cases h
        | some (.bool _), h => cases h
        | some (.unit), h => cases h
        | some (.struct _), h => cases h
        | some (.loc l), h =>
          simp only at h
          match hev : m.free l, h with
          | none, h => cases h
          | some m', h => cases h; left; rfl
      | cas x eL eO eN =>
        simp only [tstep] at h
        match hev : Expr.eval env eL, Expr.eval env eO, Expr.eval env eN, h with
        | some (.loc l), some vO, some vN, h =>
          simp only at h
          match hev : m.load l, h with
          | none, h => cases h
          | some cur, h =>
            by_cases heq : (cur == vO) = true
            · simp only [heq, if_true] at h
              match hev : m.store l vN, h with
              | none, h => cases h
              | some m', h => cases h; left; rfl
            · have hne : (cur == vO) = false := by
                rcases hcv : (cur == vO)
                · rfl
                · exact absurd hcv heq
              simp only [hne, if_false] at h
              cases h; left; rfl
        | none, _, _, h => cases h
        | some (.int _), _, _, h => cases h
        | some (.bool _), _, _, h => cases h
        | some (.unit), _, _, h => cases h
        | some (.struct _), _, _, h => cases h
        | some (.loc _), none, _, h => cases h
        | some (.loc _), some _, none, h => cases h
      | seq s₁ s₂ => simp only [tstep] at h; cases h; left; rfl
      | ite e s₁ s₂ =>
        simp only [tstep] at h
        match hev : Expr.eval env e, h with
        | some (.bool true), h => cases h; left; rfl
        | some (.bool false), h => cases h; left; rfl
        | none, h => cases h
        | some (.int _), h => cases h
        | some (.loc _), h => cases h
        | some (.unit), h => cases h
        | some (.struct _), h => cases h
      | whileDo e s => simp only [tstep] at h; cases h; left; rfl
      | call x f args =>
        simp only [tstep, callFrom] at h
        match hev : procs f, h with
        | none, h => cases h
        | some proc, h =>
          match hev : evalArgs env args, h with
          | none, h => cases h
          | some vs, h =>
            by_cases hlen : vs.length = proc.params.length
            · simp only [if_pos hlen] at h; cases h; left; rfl
            · simp only [if_neg hlen] at h; cases h
      | ret e =>
        simp only [tstep] at h
        match hev : Expr.eval env e, h with
        | none, h => cases h
        | some v, h =>
          simp only [doReturn] at h
          match hev : stack, h with
          | [], h => cases h; right; exact ⟨rfl, rfl, rfl⟩
          | fr :: rest, h =>
            simp only at h
            match hev : fr.cont, h with
            | [], h => cases h; left; rfl
            | s :: cs, h => cases h; left; rfl
      | fork f args =>
        simp only [tstep] at h
        match hev : procs f, h with
        | none, h => cases h
        | some proc, h =>
          match hev : evalArgs env args, h with
          | none, h => cases h
          | some vs, h =>
            by_cases hlen : vs.length = proc.params.length
            · simp only [if_pos hlen] at h; cases h; left; rfl
            · simp only [if_neg hlen] at h; cases h
  · -- t terminated → tstep can't fire.
    obtain ⟨stmt, cont, env, stack, result⟩ := t
    simp only at hst hco hsk
    subst hst; subst hco; subst hsk
    exfalso
    cases chosen with
    | some _ => simp only [tstep] at h; cases h
    | none => simp only [tstep] at h; cases h

/-- Spawned thread from `tstep` has `result = none`. The only branch
that spawns is `fork`, which builds a fresh thread with default
`result := none`. -/
private theorem tstep_sp_result_none
    {procs : Name → Option Proc} {chosen : Option Loc} {m : Mem} {t : Thread}
    {m' : Mem} {t' : Thread} {sp : Option Thread}
    (h : tstep procs chosen m t = some (m', t', sp))
    {ts : Thread} (hts : sp = some ts) :
    ts.result = none := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  cases chosen with
  | some l =>
    cases stmt <;> simp only [tstep] at h
    all_goals (try cases h)
    -- only alloc fires; sp = none
    rename_i x e
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; cases hts
  | none =>
    cases stmt with
    | skip =>
      simp only [tstep] at h
      match hev : cont, stack, h with
      | s :: _, _, h => cases h; cases hts
      | [], [], h => cases h
      | [], fr :: rest, h =>
        simp only [doReturn] at h
        match hev : fr.cont, h with
        | [], h => cases h; cases hts
        | s :: cs, h => cases h; cases hts
    | assign x e =>
      simp only [tstep] at h
      match hev : Expr.eval env e, h with
      | none, h => cases h
      | some v, h => cases h; cases hts
    | load x e =>
      simp only [tstep] at h
      match hev : Expr.eval env e, h with
      | none, h => cases h
      | some (.int _), h => cases h
      | some (.bool _), h => cases h
      | some (.unit), h => cases h
      | some (.struct _), h => cases h
      | some (.loc l), h =>
        simp only at h
        match hev : m.load l, h with
        | none, h => cases h
        | some w, h => cases h; cases hts
    | store eL eV =>
      simp only [tstep] at h
      match hev : Expr.eval env eL, Expr.eval env eV, h with
      | some (.loc l), some v, h =>
        simp only at h
        match hev : m.store l v, h with
        | none, h => cases h
        | some m', h => cases h; cases hts
      | none, _, h => cases h
      | some (.int _), _, h => cases h
      | some (.bool _), _, h => cases h
      | some (.unit), _, h => cases h
      | some (.struct _), _, h => cases h
      | some (.loc _), none, h => cases h
    | alloc x e => simp only [tstep] at h; cases h
    | free e =>
      simp only [tstep] at h
      match hev : Expr.eval env e, h with
      | none, h => cases h
      | some (.int _), h => cases h
      | some (.bool _), h => cases h
      | some (.unit), h => cases h
      | some (.struct _), h => cases h
      | some (.loc l), h =>
        simp only at h
        match hev : m.free l, h with
        | none, h => cases h
        | some m', h => cases h; cases hts
    | cas x eL eO eN =>
      simp only [tstep] at h
      match hev : Expr.eval env eL, Expr.eval env eO, Expr.eval env eN, h with
      | some (.loc l), some vO, some vN, h =>
        simp only at h
        match hev : m.load l, h with
        | none, h => cases h
        | some cur, h =>
          by_cases heq : (cur == vO) = true
          · simp only [heq, if_true] at h
            match hev : m.store l vN, h with
            | none, h => cases h
            | some m', h => cases h; cases hts
          · have hne : (cur == vO) = false := by
              rcases hcv : (cur == vO)
              · rfl
              · exact absurd hcv heq
            simp only [hne, if_false] at h
            cases h; cases hts
      | none, _, _, h => cases h
      | some (.int _), _, _, h => cases h
      | some (.bool _), _, _, h => cases h
      | some (.unit), _, _, h => cases h
      | some (.struct _), _, _, h => cases h
      | some (.loc _), none, _, h => cases h
      | some (.loc _), some _, none, h => cases h
    | seq s₁ s₂ => simp only [tstep] at h; cases h; cases hts
    | ite e s₁ s₂ =>
      simp only [tstep] at h
      match hev : Expr.eval env e, h with
      | some (.bool true), h => cases h; cases hts
      | some (.bool false), h => cases h; cases hts
      | none, h => cases h
      | some (.int _), h => cases h
      | some (.loc _), h => cases h
      | some (.unit), h => cases h
      | some (.struct _), h => cases h
    | whileDo e s => simp only [tstep] at h; cases h; cases hts
    | call x f args =>
      simp only [tstep, callFrom] at h
      match hev : procs f, h with
      | none, h => cases h
      | some proc, h =>
        match hev : evalArgs env args, h with
        | none, h => cases h
        | some vs, h =>
          by_cases hlen : vs.length = proc.params.length
          · simp only [if_pos hlen] at h; cases h; cases hts
          · simp only [if_neg hlen] at h; cases h
    | ret e =>
      simp only [tstep] at h
      match hev : Expr.eval env e, h with
      | none, h => cases h
      | some v, h =>
        simp only [doReturn] at h
        match hev : stack, h with
        | [], h => cases h; cases hts
        | fr :: rest, h =>
          simp only at h
          match hev : fr.cont, h with
          | [], h => cases h; cases hts
          | s :: cs, h => cases h; cases hts
    | fork f args =>
      simp only [tstep] at h
      match hev : procs f, h with
      | none, h => cases h
      | some proc, h =>
        match hev : evalArgs env args, h with
        | none, h => cases h
        | some vs, h =>
          by_cases hlen : vs.length = proc.params.length
          · simp only [if_pos hlen] at h
            cases h
            simp only [Option.some.injEq] at hts
            subst hts
            rfl
          · simp only [if_neg hlen] at h; cases h

/-- The spawned thread is heap-free when the source thread is and all
procs are heap-free. -/
private theorem tstep_sp_heapFree
    {procs : Name → Option Proc} {chosen : Option Loc} {m : Mem} {t : Thread}
    {m' : Mem} {t' : Thread} {sp : Option Thread}
    (htf : t.heapFree)
    (hprog : ∀ name proc, procs name = some proc → proc.heapFree)
    (h : tstep procs chosen m t = some (m', t', sp))
    {ts : Thread} (hts : sp = some ts) :
    ts.heapFree := by
  -- For `chosen = some l`, only alloc fires, producing sp = none.
  cases hch : chosen with
  | some l =>
    subst hch
    obtain ⟨stmt, cont, env, stack, result⟩ := t
    cases stmt <;> simp only [tstep] at h
    all_goals (try cases h)
    rename_i x e
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; cases hts
  | none =>
    subst hch
    have hpres := Agar.Logic.tstep_heapFree_preserves htf hprog h
    exact hpres.2 ts hts

/-- **Helper value extraction.** From a `StandaloneHelperSafe`, we get
*existence* of a return value the body actually delivers with
`helper_post`. This is now a one-liner because `StandaloneHelperSafe`
bundles the termination witness. (We don't need uniqueness with
respect to `helper_post`: the simulation argument picks the specific
`v` that the body operationally produces, which is unique by
`pstep_det` + heap/fork/noCall, and is one of the `helper_post`-satisfying
values.) -/
theorem helper_value_exists
    {h : Proc} {vs : List Val} {helper_post : List Val → Val → Prop}
    (h_safe : StandaloneHelperSafe h vs helper_post) :
    ∃ v, helper_post vs v := by
  obtain ⟨_n, _μ', _t, v, _, _, _, hpost⟩ := h_safe.reaches
  exact ⟨v, hpost⟩

/-- **Simulation init.** The initial configurations are Matching at all
indices, every thread is heap-free (since the composite's `main` is
heap-free), and every thread satisfies the result-well-formedness
invariant. -/
theorem simulation_init
    (composite : Program) (h_pname : Name) (h : Proc)
    (helper_post : List Val → Val → Prop)
    (h_comp_heapFree : composite.main.heapFree) :
    Sim composite h_pname h helper_post
      (Machine.initial composite) (Machine.initial composite) where
  mem_eq := rfl
  length_eq := rfl
  threads_heapFree := by
    intro i t ht
    -- The initial config has threads = [Thread.initial composite.main].
    simp only [Machine.initial] at ht
    rcases i with _ | i
    · simp at ht; subst ht
      exact Thread.heapFree_initial _ h_comp_heapFree
    · simp at ht
  threads_result_wf := by
    intro i t ht
    simp only [Machine.initial] at ht
    rcases i with _ | i
    · simp at ht; subst ht
      left; rfl
    · simp at ht
  thread_sim := by
    intro i t_a t_c ha hc
    -- The initial config has a single thread; t_a = t_c by hc, ha.
    rw [ha] at hc
    cases hc
    exact Or.inl rfl

/-- **Simulation step.** Given `Sim μ_a μ_c` and a concrete step
`μ_c → μ_c'`, the abstract takes 0 or 1 abstract steps to reach some
`μ_a'` with `Sim μ_a' μ_c'`. Case analysis on the stepping thread's
status (Matching vs InBody) and the kind of step. -/
theorem simulation_step
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (h_pure : h.body.heapFree ∧ h.body.forkFree ∧ h.body.noCall)
    (h_comp_hf : composite.heapFree)
    (helper_post : List Val → Val → Prop)
    (h_safe : ∀ vs, vs.length = h.params.length →
              StandaloneHelperSafe h vs helper_post)
    {μ_a μ_c μ_c' : Machine}
    (hsim : Sim composite h_pname h helper_post μ_a μ_c)
    (hstep : Machine.Step composite μ_c μ_c') :
    ∃ (n_abs : Nat) (μ_a' : Machine),
      n_abs ≤ 1 ∧
      Machine.StepStarN_abstract composite h_pname h helper_post n_abs μ_a μ_a' ∧
      Sim composite h_pname h helper_post μ_a' μ_c' := by
  sorry

/-- Concatenation of `StepStarN_abstract` chains. -/
theorem Machine.StepStarN_abstract.trans
    {composite : Program} {h_pname : Name} {h : Proc}
    {helper_post : List Val → Val → Prop}
    {μ₀ μ₁ μ₂ : Machine} {n m : Nat}
    (h1 : Machine.StepStarN_abstract composite h_pname h helper_post n μ₀ μ₁)
    (h2 : Machine.StepStarN_abstract composite h_pname h helper_post m μ₁ μ₂) :
    Machine.StepStarN_abstract composite h_pname h helper_post (n + m) μ₀ μ₂ := by
  induction h1 with
  | refl _ => simpa using h2
  | @step n' _μa _μb _μc h1' _h2' ih =>
      have hrest := ih h2
      -- (n' + 1) + m = (n' + m) + 1
      have heq : Nat.succ n' + m = Nat.succ (n' + m) := by
        simp [Nat.succ_add]
      rw [heq]
      exact .step h1' hrest

/-- **Lift to multi-step.** A concrete `StepStarN` of length `n` lifts
to an abstract `StepStarN_abstract` of length `≤ n` preserving Sim. -/
theorem simulation_lift
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (h_pure : h.body.heapFree ∧ h.body.forkFree ∧ h.body.noCall)
    (h_comp_hf : composite.heapFree)
    (helper_post : List Val → Val → Prop)
    (h_safe : ∀ vs, vs.length = h.params.length →
              StandaloneHelperSafe h vs helper_post)
    {μ_a μ_c μ_c' : Machine} {n : Nat}
    (hsim : Sim composite h_pname h helper_post μ_a μ_c)
    (htraj : Machine.StepStarN composite n μ_c μ_c') :
    ∃ (n_abs : Nat) (μ_a' : Machine),
      Machine.StepStarN_abstract composite h_pname h helper_post n_abs μ_a μ_a' ∧
      Sim composite h_pname h helper_post μ_a' μ_c' := by
  induction htraj generalizing μ_a with
  | refl _ => exact ⟨0, μ_a, .refl μ_a, hsim⟩
  | step h1 h2 ih =>
      obtain ⟨n_one, μ_mid, _hle, hone, hsim_mid⟩ :=
        simulation_step composite h_pname h h_registered h_pure h_comp_hf
          helper_post h_safe hsim h1
      obtain ⟨n_rest, μ_a', hrest, hsim'⟩ := ih hsim_mid
      exact ⟨n_one + n_rest, μ_a', hone.trans hrest, hsim'⟩

/-- **Transfer.** Given `Sim μ_a μ_c` and the per-state safety of
`μ_a` under the abstract relation, every thread of `μ_c` is
value-or-reducible (and at index 0, the value satisfies
`composite_post`). The InBody case appeals to standalone helper
safety: every body-mid state is reducible. -/
theorem sim_transfer
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (h_pure : h.body.heapFree ∧ h.body.forkFree ∧ h.body.noCall)
    (helper_post : List Val → Val → Prop)
    (h_safe : ∀ vs, vs.length = h.params.length →
              StandaloneHelperSafe h vs helper_post)
    {μ_a μ_c : Machine} (composite_post : Val → Prop)
    (hsim : Sim composite h_pname h helper_post μ_a μ_c)
    (habs_safe_here :
      ∀ k t, μ_a.threads[k]? = some t →
        (∃ v, t.toValue = some v ∧ (k = 0 → composite_post v)) ∨
        thread_reducible_abstract composite h_pname h helper_post μ_a.mem t) :
    ∀ k t, μ_c.threads[k]? = some t →
      (∃ v, t.toValue = some v ∧ (k = 0 → composite_post v)) ∨
      thread_reducible composite.procs μ_c.mem t := by
  intro k t_c hk
  -- The Sim's length_eq guarantees μ_a.threads[k]? = some <something>.
  have hlen := hsim.length_eq
  have hmem := hsim.mem_eq
  -- Extract the abstract counterpart at index k.
  cases ha : μ_a.threads[k]? with
  | none =>
      -- impossible: lengths agree.
      exfalso
      -- hk : μ_c.threads[k]? = some t_c → k < μ_c.threads.length
      have hk_lt : k < μ_c.threads.length := by
        rcases hkk : μ_c.threads[k]? with _ | t
        · rw [hkk] at hk; cases hk
        · exact List.getElem?_eq_some_iff.mp hkk |>.1
      have hk_lt_a : k < μ_a.threads.length := hlen ▸ hk_lt
      -- so getElem? at k on μ_a.threads is some, contradiction.
      have ha2 : μ_a.threads[k]? ≠ none := by
        rw [List.getElem?_eq_some_iff.mpr ⟨hk_lt_a, rfl⟩]
        simp
      exact ha2 ha
  | some t_a =>
      have hclass := hsim.thread_sim k t_a t_c ha hk
      rcases hclass with heq | hbody
      · -- Matching: transfer directly.
        subst heq
        have := habs_safe_here k t_a ha
        rcases this with hval | hred
        · exact Or.inl hval
        · -- thread_reducible_abstract → thread_reducible (with mems equal).
          right
          rcases hred with ⟨m', t', sp, hstep, _hno⟩ | ⟨x, args, vs, v, hstmt, hres, hargs, harity, hpost⟩
          · -- Regular concrete step is available.
            refine ⟨m', t', sp, ?_⟩
            -- hmem : μ_a.mem = μ_c.mem
            rw [← hmem]; exact hstep
          · -- A helper-call collapse — in the concrete world this
            -- corresponds to actually firing the `.call` step
            -- (which is itself a `thread_step`). We construct it.
            -- After `subst heq` (above), t_c was substituted to t_a.
            -- So hstmt/hres talk about t_a now.
            -- Destructure t_a to expose its env/cont/stack/result.
            rcases t_a with ⟨stmt_a, cont_a, env_a, stack_a, result_a⟩
            simp only at hstmt hres hargs
            subst hstmt
            subst hres
            -- Now the concrete thread = ⟨.call x h_pname args, cont_a, env_a, stack_a, none⟩.
            -- Fire tstep_call.
            have htstep :
                tstep composite.procs none μ_c.mem
                  ⟨.call x h_pname args, cont_a, env_a, stack_a, none⟩
                  = some (μ_c.mem,
                    ⟨h.body, [], bindParams h.params vs,
                      ⟨x, cont_a, env_a⟩ :: stack_a, none⟩, none) :=
              tstep_call composite.procs μ_c.mem x h_pname args h vs
                cont_a env_a stack_a h_registered hargs harity
            refine ⟨μ_c.mem,
              ⟨h.body, [], bindParams h.params vs,
                ⟨x, cont_a, env_a⟩ :: stack_a, none⟩, none, ?_⟩
            exact ⟨none, htstep⟩
      · -- InBody: concrete thread is mid-body. Reducibility comes
        -- directly from the Sim invariant's `thread_reducible` field.
        obtain ⟨_vs, _v_h, _cont, _env, _rv, _rest,
                _hpost, _hlen, _hta, _htstk, _htres, hred⟩ := hbody
        exact Or.inr hred

/-- **The composition lemma.** Combines the helper's standalone safety
(parametric in `vs`) with the composite's abstract safety to deliver
concrete `Machine.safe`. -/
theorem Machine.safe_compose
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (h_pure : h.body.heapFree ∧ h.body.forkFree ∧ h.body.noCall)
    (h_comp_hf : composite.heapFree)
    (helper_post : List Val → Val → Prop)
    (h_safe : ∀ vs, vs.length = h.params.length →
              StandaloneHelperSafe h vs helper_post)
    (composite_post : Val → Prop)
    (composite_abstract_safe :
      Machine.SafeTp_abstract composite h_pname h helper_post
        (Machine.initial composite) composite_post) :
    Machine.safe composite composite_post := by
  -- Reduce `Machine.safe` to its definition: every reachable concrete
  -- state has every thread value-or-reducible.
  intro n μ_c htraj k t_c hk
  -- Lift the concrete trajectory to an abstract one via simulation.
  have hsim_init :
      Sim composite h_pname h helper_post
        (Machine.initial composite) (Machine.initial composite) :=
    simulation_init composite h_pname h helper_post h_comp_hf.1
  -- htraj has type Machine.StepStarN composite n (Machine.initial composite) μ_c.
  -- The reduction `Machine.safe = Machine.SafeTp` from the empty heap
  -- gives us the initial config.
  have htraj' : Machine.StepStarN composite n (Machine.initial composite) μ_c := htraj
  obtain ⟨n_abs, μ_a, habs_traj, hsim⟩ :=
    simulation_lift composite h_pname h h_registered h_pure h_comp_hf
      helper_post h_safe hsim_init htraj'
  -- Apply abstract safety at the lifted abstract state.
  have habs_here :
      ∀ k t, μ_a.threads[k]? = some t →
        (∃ v, t.toValue = some v ∧ (k = 0 → composite_post v)) ∨
        thread_reducible_abstract composite h_pname h helper_post μ_a.mem t := by
    intro k t hk
    exact composite_abstract_safe n_abs μ_a habs_traj k t hk
  -- Transfer the disjunct from abstract to concrete via the
  -- simulation.
  exact sim_transfer composite h_pname h h_registered h_pure
    helper_post h_safe composite_post hsim habs_here k t_c hk

/-! ## Worked-example consumption smoke test

A purely structural test that the worked-example consumption pattern
from `COMPOSITION_DESIGN.md` lines up: a user can write the
`apply Machine.safe_compose`, refine the conjunction, and discharge
the four goals in sequence. We use trivially-stubbed inputs so the
test typechecks even though the actual `Machine.safe_compose` body
contains `sorry`s. -/

section WorkedExampleSmokeTest

/-- Trivial dummy helper. -/
def dummyHelper : Proc :=
  { params := [], body := .ret (.val Val.unit) }

/-- Trivial dummy composite that registers `dummyHelper` under name `"h"`. -/
def dummyComposite : Program where
  procs := fun n => if n = "h" then some dummyHelper else none
  main  := .skip

/-- Smoke test: the `apply Machine.safe_compose` pattern produces the
expected goal sequence. The `sorry`s here stand in for the real
client-supplied proofs (registration, purity, standalone safety,
abstract safety). -/
example : Machine.safe dummyComposite (fun _ => True) := by
  apply Machine.safe_compose dummyComposite "h" dummyHelper
    (helper_post := fun _ _ => True)
  · -- h_registered : dummyComposite.procs "h" = some dummyHelper
    rfl
  · -- h_pure : heapFree ∧ forkFree ∧ noCall
    refine ⟨?_, ?_, ?_⟩
    · -- heapFree of `.ret`
      trivial
    · -- forkFree
      trivial
    · -- noCall
      trivial
  · -- h_comp_hf : dummyComposite.heapFree
    refine ⟨?_, ?_⟩
    · -- main = .skip is heap-free
      trivial
    · -- every proc is heap-free
      intro name proc hp
      by_cases hn : name = "h"
      · simp only [dummyComposite, hn, if_pos] at hp; cases hp
        trivial
      · simp only [dummyComposite, hn, if_neg, if_false] at hp
        cases hp
  · -- h_safe : ∀ vs, vs.length = h.params.length → StandaloneHelperSafe …
    intro vs hlen
    sorry
  · -- composite_abstract_safe
    sorry

end WorkedExampleSmokeTest

end Agar

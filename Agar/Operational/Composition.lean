module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Adequacy
public import Agar.Iris.Completeness
public import Agar.Lang.Denotational

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
    (pureBody : PureStmt) (retExpr : Expr)
    (helper_post : List Val → Val → Prop)
    (μ_abs μ_concrete : Machine) : Prop where
  mem_eq : μ_abs.mem = μ_concrete.mem
  length_eq : μ_abs.threads.length = μ_concrete.threads.length
  /-- Every concrete thread is heap-free. Established initially when the
  composite is heap-free, and preserved by every step. -/
  threads_heapFree :
    ∀ (i : Nat) (t : Thread), μ_concrete.threads[i]? = some t → t.heapFree
  /-- Every concrete thread has `result = none` unless it has terminated. -/
  threads_result_wf :
    ∀ (i : Nat) (t : Thread), μ_concrete.threads[i]? = some t →
      t.result = none ∨ (t.stmt = .skip ∧ t.cont = [] ∧ t.stack = [])
  /-- For each index `i`, the per-thread relation: either the threads
  match exactly (Matching), or the abstract has already collapsed the
  helper call into its post-call state and the concrete sits on the
  body's deterministic pure trajectory (InBody, structural-denotational
  form). -/
  thread_sim :
    ∀ (i : Nat), ∀ (t_a t_c : Thread),
      μ_abs.threads[i]? = some t_a →
      μ_concrete.threads[i]? = some t_c →
      -- Matching:
      (t_a = t_c) ∨
      -- InBody: the concrete thread is reachable via `PureSteps` from
      -- the body's near-end state `⟨.ret retExpr, [], ρ_f, frame ::
      -- rest, none⟩`, where `ρ_f` is the body's denotational final env
      -- and the unique return value `v_h = Expr.eval ρ_f retExpr`
      -- satisfies `helper_post vs v_h`. The abstract is at the
      -- post-call state.
      (∃ (vs : List Val) (v_h : Val) (cont : List Stmt) (env : Env)
         (rv : Name) (rest : List Frame) (ρ_f : Env),
        helper_post vs v_h ∧
        vs.length = h.params.length ∧
        denote pureBody (bindParams h.params vs) = (some (), ρ_f) ∧
        Expr.eval ρ_f retExpr = some v_h ∧
        t_a = (⟨.skip, cont, env.set rv v_h, rest, none⟩ : Thread) ∧
        PureSteps t_c
          ⟨.ret retExpr, [], ρ_f, ⟨rv, cont, env⟩ :: rest, none⟩)

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

/-! ## Body trajectory via the denotational pillar

Structural-denotational backbone for the helper body. Under the premise
`h.body = .seq (embed pureBody) (.ret retExpr)`, we expose:

* A `PureSteps` chain from the body-start thread `⟨h.body, [],
  bindParams h.params vs, frame :: rest, none⟩` to the unique
  *near-end* state `⟨.ret retExpr, [], ρ', frame :: rest, none⟩`,
  where `ρ'` is the body's denotational final environment.
* One more pstep step lands at the *post-frame* state
  `⟨.skip, frame.cont, frame.env.set frame.retVar v_h, rest, none⟩` where
  `v_h = Expr.eval ρ' retExpr`.

Both steps lift to `Machine.Step composite` because the body is
`.call`-free and `.fork`-free, so `composite.procs` plays no role.
-/

namespace BodyTraj

/-- Thread-with-stack constructor (paralleling `mkT` from `Denotational`
but allowing an explicit stack). -/
@[reducible]
def mkTS (s : Stmt) (cs : List Stmt) (ρ : Env) (stk : List Frame) : Thread :=
  { stmt := s, cont := cs, env := ρ, stack := stk, result := none }

@[simp] theorem mkTS_skip_step (cs : List Stmt) (ρ : Env) (s' : Stmt)
    (stk : List Frame) :
    pstep (mkTS .skip (s' :: cs) ρ stk) = some (mkTS s' cs ρ stk) := rfl

@[simp] theorem mkTS_seq_step (a b : Stmt) (cs : List Stmt) (ρ : Env)
    (stk : List Frame) :
    pstep (mkTS (.seq a b) cs ρ stk) = some (mkTS a (b :: cs) ρ stk) := rfl

@[simp] theorem mkTS_assign_step (x : Name) (e : Expr) (cs : List Stmt)
    (ρ : Env) (stk : List Frame) :
    pstep (mkTS (.assign x e) cs ρ stk) =
      (Expr.eval ρ e).map (fun v => mkTS .skip cs (ρ.set x v) stk) := by
  simp [pstep, tstep, mkTS]
  cases Expr.eval ρ e <;> rfl

@[simp] theorem mkTS_ite_step (e : Expr) (s₁ s₂ : Stmt) (cs : List Stmt)
    (ρ : Env) (stk : List Frame) :
    pstep (mkTS (.ite e s₁ s₂) cs ρ stk) =
      match Expr.eval ρ e with
      | some (.bool true)  => some (mkTS s₁ cs ρ stk)
      | some (.bool false) => some (mkTS s₂ cs ρ stk)
      | _                  => none := by
  simp [pstep, tstep, mkTS]
  rcases h : Expr.eval ρ e with _ | v
  · rfl
  · cases v <;> try rfl
    rename_i b; cases b <;> rfl

/-- Stack-parametric version of `denote_sound`. The proof structurally
mirrors `denote_sound` (in `Agar.Lang.Denotational`) but uses `mkTS` so
the stack is preserved through the chain. PureStmt has no `.ret`, so
`embed s` never reads the stack via a `doReturn`; consequently every
intermediate pstep is stack-equivariant. -/
theorem denote_sound_stk (s : PureStmt) :
    ∀ (cs : List Stmt) (stk : List Frame) (ρ ρ' : Env),
      denote s ρ = (some (), ρ') →
      PureSteps (mkTS (embed s) cs ρ stk) (mkTS .skip cs ρ' stk) := by
  induction s with
  | skip =>
      intro cs stk ρ ρ' h
      simp [denote] at h
      obtain ⟨_, rfl⟩ := h
      exact .refl
  | assign x e =>
      intro cs stk ρ ρ' h
      simp [denote] at h
      split at h
      · cases h
      · rename_i v heq
        cases h
        refine .single ?_
        show pstep (mkTS (.assign x e) cs ρ stk) = _
        simp [heq]
  | seq s₁ s₂ ih₁ ih₂ =>
      intro cs stk ρ ρ' h
      simp only [denote] at h
      rcases h₁ : denote s₁ ρ with ⟨o₁, ρ₁⟩
      rw [h₁] at h
      cases o₁ with
      | none => cases h
      | some =>
          simp only at h
          have step₁ : pstep (mkTS (.seq (embed s₁) (embed s₂)) cs ρ stk)
              = some (mkTS (embed s₁) (embed s₂ :: cs) ρ stk) := by simp
          refine .step step₁ ?_
          have hs₁ := ih₁ (embed s₂ :: cs) stk ρ ρ₁ h₁
          have hpop : pstep (mkTS .skip (embed s₂ :: cs) ρ₁ stk)
              = some (mkTS (embed s₂) cs ρ₁ stk) := by simp
          refine hs₁.trans (.step hpop ?_)
          exact ih₂ cs stk ρ₁ ρ' h
  | ite e s₁ s₂ ih₁ ih₂ =>
      intro cs stk ρ ρ' h
      simp only [denote] at h
      split at h
      · rename_i hb
        have step₁ : pstep (mkTS (.ite e (embed s₁) (embed s₂)) cs ρ stk)
            = some (mkTS (embed s₁) cs ρ stk) := by simp [hb]
        exact .step step₁ (ih₁ cs stk ρ ρ' h)
      · rename_i hb
        have step₁ : pstep (mkTS (.ite e (embed s₁) (embed s₂)) cs ρ stk)
            = some (mkTS (embed s₂) cs ρ stk) := by simp [hb]
        exact .step step₁ (ih₂ cs stk ρ ρ' h)
      · cases h
  | «repeat» n s ih =>
      show ∀ cs stk ρ ρ', iter (denote s) n ρ = (some (), ρ') →
        PureSteps (mkTS (unroll (embed s) n) cs ρ stk) (mkTS .skip cs ρ' stk)
      induction n with
      | zero =>
          intro cs stk ρ ρ' h
          simp [iter] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs stk ρ ρ' h
          show PureSteps (mkTS (.seq (embed s) (unroll (embed s) k)) cs ρ stk) _
          simp only [iter] at h
          rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => cases h
          | some =>
              simp only at h
              have step₁ : pstep (mkTS (.seq (embed s) (unroll (embed s) k)) cs ρ stk)
                  = some (mkTS (embed s) (unroll (embed s) k :: cs) ρ stk) := by simp
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) stk ρ ρ₁ h₁
              have hpop : pstep (mkTS .skip (unroll (embed s) k :: cs) ρ₁ stk)
                  = some (mkTS (unroll (embed s) k) cs ρ₁ stk) := by simp
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs stk ρ₁ ρ' h
  | forN n s ih =>
      show ∀ cs stk ρ ρ', iter (denote s) n ρ = (some (), ρ') →
        PureSteps (mkTS (unroll (embed s) n) cs ρ stk) (mkTS .skip cs ρ' stk)
      induction n with
      | zero =>
          intro cs stk ρ ρ' h
          simp [iter] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs stk ρ ρ' h
          show PureSteps (mkTS (.seq (embed s) (unroll (embed s) k)) cs ρ stk) _
          simp only [iter] at h
          rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => cases h
          | some =>
              simp only at h
              have step₁ : pstep (mkTS (.seq (embed s) (unroll (embed s) k)) cs ρ stk)
                  = some (mkTS (embed s) (unroll (embed s) k :: cs) ρ stk) := by simp
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) stk ρ ρ₁ h₁
              have hpop : pstep (mkTS .skip (unroll (embed s) k :: cs) ρ₁ stk)
                  = some (mkTS (unroll (embed s) k) cs ρ₁ stk) := by simp
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs stk ρ₁ ρ' h
  | while_ n g s ih =>
      show ∀ cs stk ρ ρ', denote (.while_ n g s) ρ = (some (), ρ') →
        PureSteps (mkTS (unrollW g (embed s) n) cs ρ stk) (mkTS .skip cs ρ' stk)
      induction n with
      | zero =>
          intro cs stk ρ ρ' h
          rw [denote_while_zero] at h
          cases h
      | succ k ihk =>
          intro cs stk ρ ρ' h
          show PureSteps (mkTS (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ stk) _
          rw [denote_while_succ] at h
          split at h
          · rename_i hb
            simp only [denote] at h
            rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
            rw [h₁] at h
            cases o₁ with
            | none => cases h
            | some =>
                simp only at h
                have step₁ : pstep (mkTS (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ stk)
                    = some (mkTS (.seq (embed s) (unrollW g (embed s) k)) cs ρ stk) := by simp [hb]
                refine .step step₁ ?_
                have step₂ : pstep (mkTS (.seq (embed s) (unrollW g (embed s) k)) cs ρ stk)
                    = some (mkTS (embed s) (unrollW g (embed s) k :: cs) ρ stk) := by simp
                refine .step step₂ ?_
                have hs₁ := ih (unrollW g (embed s) k :: cs) stk ρ ρ₁ h₁
                have hpop : pstep (mkTS .skip (unrollW g (embed s) k :: cs) ρ₁ stk)
                    = some (mkTS (unrollW g (embed s) k) cs ρ₁ stk) := by simp
                refine hs₁.trans (.step hpop ?_)
                exact ihk cs stk ρ₁ ρ' h
          · rename_i hb
            -- guard false: ite picks the .skip branch and we're done.
            obtain ⟨_, rfl⟩ := h
            have step₁ : pstep (mkTS (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ stk)
                = some (mkTS .skip cs ρ stk) := by simp [hb]
            exact .single step₁
          · cases h

/-- **The headline body chain.** Under the structural premise, from the
body-start thread (cont = [], stack = frame :: rest), we step via
`pstep` down to the *near-end* thread `⟨.ret retExpr, [], ρ', frame ::
rest, none⟩` — one `.seq`-unpack, the entire `denote_sound_stk` chain,
and one `.skip`-pop. -/
theorem pure_steps_to_near_end
    (pureBody : PureStmt) (retExpr : Expr)
    (ρ ρ' : Env) (frame : Frame) (rest : List Frame)
    (h_denote : denote pureBody ρ = (some (), ρ')) :
    PureSteps
      ⟨.seq (embed pureBody) (.ret retExpr), [], ρ, frame :: rest, none⟩
      ⟨.ret retExpr, [], ρ', frame :: rest, none⟩ := by
  -- Step 1: unfold the outer .seq.
  have step₁ : pstep (mkTS (.seq (embed pureBody) (.ret retExpr)) [] ρ (frame :: rest))
      = some (mkTS (embed pureBody) [.ret retExpr] ρ (frame :: rest)) := by simp
  refine .step step₁ ?_
  -- Step 2: the body's denote-sound chain.
  have hbody := denote_sound_stk pureBody [.ret retExpr] (frame :: rest) ρ ρ' h_denote
  -- Step 3: pop the queued .ret retExpr.
  have step₃ : pstep (mkTS .skip [.ret retExpr] ρ' (frame :: rest))
      = some (mkTS (.ret retExpr) [] ρ' (frame :: rest)) := by simp
  exact hbody.trans (.step step₃ .refl)

/-- Post-frame thread shape after `doReturn` pops `frame` and assigns its
return value. Splits on `frame.cont`: empty conts produce a skip leaf,
non-empty conts run their head. -/
def postDoReturnThread (frame : Frame) (rest : List Frame) (v_h : Val) : Thread :=
  match frame.cont with
  | []      => ⟨.skip, [], frame.env.set frame.retVar v_h, rest, none⟩
  | s :: cs => ⟨s,     cs, frame.env.set frame.retVar v_h, rest, none⟩

/-- The final `.ret`-pop: from the near-end state, a single pstep fires
`doReturn` and lands at the post-frame state shaped by
`postDoReturnThread`. -/
theorem pstep_near_end_pop
    (retExpr : Expr) (ρ' : Env) (v_h : Val) (frame : Frame) (rest : List Frame)
    (h_ret : Expr.eval ρ' retExpr = some v_h) :
    pstep ⟨.ret retExpr, [], ρ', frame :: rest, none⟩
      = some (postDoReturnThread frame rest v_h) := by
  show (match tstep noProcs none Mem.empty
            ⟨.ret retExpr, [], ρ', frame :: rest, none⟩ with
        | some (_, t', _) => some t'
        | none            => none) = _
  simp only [tstep, h_ret, doReturn, postDoReturnThread]
  cases frame.cont <;> rfl

/-- Lift `pstep` to `tstep procs` for *any* `procs` and any mem `m`. The
side condition is that pstep succeeds — which rules out `.call` and
`.fork` (where `noProcs` matters). -/
theorem pstep_tstep_procs (procs : Name → Option Proc) (m : Mem)
    (t t' : Thread) (h : pstep t = some t') :
    tstep procs none m t = some (m, t', none) := by
  -- Identical to `pstep_machine_indep` (in Denotational) but with arbitrary procs.
  unfold pstep at h
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  cases stmt with
  | skip =>
      simp [tstep] at h
      cases cont with
      | nil =>
          cases stack with
          | nil => cases h
          | cons f rest =>
              simp [tstep, doReturn] at h ⊢
              cases hc : f.cont <;> simp [hc] at h ⊢ <;> (cases h; rfl)
      | cons s rest => cases h; simp [tstep]
  | seq a b => cases h; simp [tstep]
  | assign x e =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e <;> simp [hev] at h ⊢
      cases h; rfl
  | ite e s₁ s₂ =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          cases v <;> simp [hev] at h ⊢
          rename_i b; cases b <;> simp at h ⊢ <;> (cases h; rfl)
  | alloc x e => simp [tstep] at h
  | load x e =>
      simp [tstep, Mem.load, Mem.empty] at h
      cases hev : Expr.eval env e <;> simp [hev] at h
      rename_i v; cases v <;> simp at h
  | store eL eV =>
      simp [tstep, Mem.store, Mem.empty] at h
      cases hL : Expr.eval env eL <;> simp [hL] at h
      cases hV : Expr.eval env eV <;> simp [hV] at h
      rename_i v _; cases v <;> simp at h
  | free e =>
      simp [tstep, Mem.free, Mem.empty] at h
      cases hev : Expr.eval env e <;> simp [hev] at h
      rename_i v; cases v <;> simp at h
  | cas x eL eO eN =>
      simp [tstep, Mem.load, Mem.empty] at h
      cases hL : Expr.eval env eL <;> simp [hL] at h
      cases hO : Expr.eval env eO <;> simp [hO] at h
      cases hN : Expr.eval env eN <;> simp [hN] at h
      rename_i v _ _; cases v <;> simp at h
  | whileDo e s => cases h; simp [tstep]
  | call x f args => simp [tstep, callFrom, noProcs] at h
  | ret e =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          simp [hev] at h ⊢
          unfold doReturn at h ⊢
          cases stack with
          | nil => cases h; rfl
          | cons f rest =>
              cases hc : f.cont <;> simp [hc] at h ⊢ <;> (cases h; rfl)
  | fork f args => simp [tstep, noProcs] at h

/-- Lift one `pstep` of thread at index `i` to one `Machine.Step` of the
composite machine. -/
theorem pstep_to_Machine_Step_at (composite : Program) (m : Mem)
    (threads : List Thread) (i : Nat) (t t' : Thread)
    (hi : threads[i]? = some t) (h : pstep t = some t') :
    Machine.Step composite ⟨m, threads⟩ ⟨m, threads.set i t'⟩ := by
  have hts : tstep composite.procs none m t = some (m, t', none) :=
    pstep_tstep_procs composite.procs m t t' h
  -- The Machine.Step constructor appends sp.toList = [] (since sp = none).
  have : (none : Option Thread).toList = [] := rfl
  have hgoal : threads.set i t' = threads.set i t' ++ (none : Option Thread).toList := by
    simp
  rw [hgoal]
  exact Machine.Step.step (p := composite)
    (i := i) (chosen := none) (t := t) (t' := t') (sp := none)
    (m := m) (m' := m) (threads := threads) (hi := hi) (hstep := hts)

/-- Lift a `PureSteps` chain on a single thread into a `Machine.StepStarN`
on the composite machine where that thread is at index `i`. -/
theorem PureSteps_to_StepStarN (composite : Program) (m : Mem)
    (threads : List Thread) (i : Nat) :
    ∀ {t t' : Thread}, threads[i]? = some t → PureSteps t t' →
      ∃ n, Machine.StepStarN composite n ⟨m, threads⟩ ⟨m, threads.set i t'⟩ := by
  -- Strategy: prove a `∀ threads`-quantified version by induction on the
  -- pure-steps chain, so that the IH can be applied after the first step
  -- changes the threads list.
  suffices H : ∀ {t t' : Thread}, PureSteps t t' →
      ∀ (threads : List Thread), threads[i]? = some t →
        ∃ n, Machine.StepStarN composite n ⟨m, threads⟩ ⟨m, threads.set i t'⟩ by
    intro t t' h_idx h_steps
    exact H h_steps threads h_idx
  intro t t' h_steps
  induction h_steps with
  | @refl t0 =>
      intro threads h_idx
      have h_lt : i < threads.length := by
        rcases List.getElem?_eq_some_iff.mp h_idx with ⟨h, _⟩; exact h
      have hget : (threads[i]'h_lt : Thread) = t0 := by
        have h := h_idx
        rw [List.getElem?_eq_getElem h_lt] at h
        exact Option.some.inj h
      have hset_eq : threads.set i t0 = threads := by
        apply List.ext_getElem
        · simp
        · intro j hj _
          simp only [List.getElem_set]
          by_cases hji : i = j
          · subst hji; simp [hget]
          · simp [hji]
      refine ⟨0, ?_⟩
      rw [hset_eq]
      exact .refl _
  | @step t1 t2 tEnd hstep _ ih =>
      intro threads h_idx
      have h_lt : i < threads.length := by
        rcases List.getElem?_eq_some_iff.mp h_idx with ⟨h, _⟩; exact h
      have h1 : Machine.Step composite ⟨m, threads⟩ ⟨m, threads.set i t2⟩ :=
        pstep_to_Machine_Step_at composite m threads i t1 t2 h_idx hstep
      have h_lt' : i < (threads.set i t2).length := by
        simpa using h_lt
      have h_idx2 : (threads.set i t2)[i]? = some t2 := by
        rw [List.getElem?_eq_some_iff]
        refine ⟨h_lt', ?_⟩
        simp [List.getElem_set]
      obtain ⟨n, hrest⟩ := ih (threads.set i t2) h_idx2
      have hcollapse : (threads.set i t2).set i tEnd = threads.set i tEnd := by
        apply List.ext_getElem
        · simp
        · intro j hj _
          simp only [List.getElem_set]
          by_cases hji : i = j
          · subst hji; simp
          · simp [hji]
      rw [hcollapse] at hrest
      exact ⟨n.succ, .step h1 hrest⟩

end BodyTraj

/-- **Body trajectory.** The headline composition lemma: under the
structural premise, the concrete body's pure trajectory inside a
multi-thread composite machine reaches the post-frame state in finitely
many `Machine.Step`s. -/
theorem helper_runs_to_value
    (composite : Program) (h : Proc)
    (pureBody : PureStmt) (retExpr : Expr)
    (h_body_eq : h.body = .seq (embed pureBody) (.ret retExpr))
    (vs : List Val) (frame : Frame) (rest : List Frame) (m : Mem)
    (threads : List Thread) (i : Nat)
    (ρ_f : Env) (v_h : Val)
    (h_denote : denote pureBody (bindParams h.params vs) = (some (), ρ_f))
    (h_ret : Expr.eval ρ_f retExpr = some v_h)
    (h_idx : threads[i]? = some
              ⟨h.body, [], bindParams h.params vs, frame :: rest, none⟩) :
    ∃ n, Machine.StepStarN composite n
      ⟨m, threads⟩
      ⟨m, threads.set i (BodyTraj.postDoReturnThread frame rest v_h)⟩ := by
  -- Stitch the body's PureSteps + the final .ret pop.
  have hbody := BodyTraj.pure_steps_to_near_end pureBody retExpr
    (bindParams h.params vs) ρ_f frame rest h_denote
  have hpop := BodyTraj.pstep_near_end_pop retExpr ρ_f v_h frame rest h_ret
  have hfull : PureSteps
      ⟨.seq (embed pureBody) (.ret retExpr), [], bindParams h.params vs,
        frame :: rest, none⟩
      (BodyTraj.postDoReturnThread frame rest v_h) :=
    hbody.trans (.single hpop)
  -- Convert the start thread to use h.body via h_body_eq.
  rw [← h_body_eq] at hfull
  exact BodyTraj.PureSteps_to_StepStarN composite m threads i h_idx hfull

/-- **Simulation init.** The initial configurations are Matching at all
indices, every thread is heap-free (since the composite's `main` is
heap-free), and every thread satisfies the result-well-formedness
invariant. -/
theorem simulation_init
    (composite : Program) (h_pname : Name) (h : Proc)
    (pureBody : PureStmt) (retExpr : Expr)
    (helper_post : List Val → Val → Prop)
    (h_comp_heapFree : composite.main.heapFree) :
    Sim composite h_pname h pureBody retExpr helper_post
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

/-! ### Preservation lemmas for off-target threads

When the concrete machine steps thread `i` to `t'` (possibly with a
spawn), threads at index `j ≠ i` (and `j < threads.length`) are
unchanged. For these, all per-thread Sim invariants (heapFree,
result_wf, Matching/InBody classification) carry over. Spawned threads
appear at `threads.length` (only via `.fork`, which we case-handle). -/

namespace SimStep

variable {composite : Program} {h_pname : Name} {h : Proc}
  {pureBody : PureStmt} {retExpr : Expr}
  {helper_post : List Val → Val → Prop}

/-- For an off-target thread (`j ≠ i`, `j < threads.length`), the
post-step threads list returns the same thread. -/
theorem set_append_other (threads : List Thread) (i j : Nat)
    (t' : Thread) (sp : Option Thread)
    (hj_lt : j < threads.length) (hne : j ≠ i) :
    (threads.set i t' ++ sp.toList)[j]? = threads[j]? := by
  sorry

/-- Set + append at index `i` returns the new thread. -/
theorem set_append_at (threads : List Thread) (i : Nat) (t' : Thread)
    (sp : Option Thread) (hi_lt : i < threads.length) :
    (threads.set i t' ++ sp.toList)[i]? = some t' := by
  sorry

/-- The spawned thread (when present) lands at index `threads.length`. -/
theorem set_append_spawned (threads : List Thread) (i : Nat) (t' : Thread)
    (ts : Thread) :
    (threads.set i t' ++ ([ts] : List Thread))[threads.length]? = some ts := by
  have : threads.length = (threads.set i t').length := by simp
  rw [this]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

end SimStep

/-- **Simulation step.** Given `Sim μ_a μ_c` and a concrete step
`μ_c → μ_c'`, the abstract takes 0 or 1 abstract steps to reach some
`μ_a'` with `Sim μ_a' μ_c'`.

Four cases (per the structural-denotational design):

* **Matching/non-call**: concrete and abstract take the same regular
  step (1 abstract step, Matching preserved).
* **Matching/helper-call**: concrete enters body; abstract takes
  `atomic_call` choosing `v_h` from `h_safe` (1 abstract step;
  transition to InBody, witnessed by the `pure_steps_to_near_end`
  trajectory).
* **InBody/body-step**: concrete advances one rung of the trajectory;
  abstract stays put (0 abstract steps; trajectory shortened by 1).
* **InBody/.ret-pop**: concrete is at the near-end and `doReturn`
  fires, landing exactly at the abstract's post-call state (0
  abstract steps; transition back to Matching).
-/
theorem simulation_step
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (pureBody : PureStmt) (retExpr : Expr)
    (h_body_eq : h.body = .seq (embed pureBody) (.ret retExpr))
    (h_comp_hf : composite.heapFree)
    (helper_post : List Val → Val → Prop)
    (h_safe : ∀ vs, vs.length = h.params.length →
              ∃ ρ_f v_h,
                denote pureBody (bindParams h.params vs) = (some (), ρ_f) ∧
                Expr.eval ρ_f retExpr = some v_h ∧
                helper_post vs v_h)
    {μ_a μ_c μ_c' : Machine}
    (hsim : Sim composite h_pname h pureBody retExpr helper_post μ_a μ_c)
    (hstep : Machine.Step composite μ_c μ_c') :
    ∃ (n_abs : Nat) (μ_a' : Machine),
      n_abs ≤ 1 ∧
      Machine.StepStarN_abstract composite h_pname h helper_post n_abs μ_a μ_a' ∧
      Sim composite h_pname h pureBody retExpr helper_post μ_a' μ_c' := by
  sorry

section _disabled_simulation_step_body
-- The body below was a flawed attempt — it elaborated against stale
-- `frame.rv` metavariables and contains real holes (doReturn shape
-- mismatch in atomic_call vs Sim.InBody.t_a; fabricated lemma names;
-- bad `rcases` patterns on Props). Preserved here for reference.
example : True := by
  trivial
end _disabled_simulation_step_body

/-
DISABLED:
  -- Unpack the concrete step.
  cases hstep with
  | step i chosen t t' sp m m' threads hi hts =>
  -- The stepping thread is heap-free, forcing chosen = none.
  have htf : t.heapFree := hsim.threads_heapFree i t hi
  have hchosen : chosen = none := tstep_heapFree_chosen_none htf hts
  subst hchosen
  -- Sim's structural fields.
  have hlen : μ_a.threads.length = threads.length := hsim.length_eq
  have hmem : μ_a.mem = m := hsim.mem_eq
  -- Procs are all heap-free (for tstep_heapFree_preserves).
  have hprog_hf : ∀ name proc, composite.procs name = some proc → proc.heapFree :=
    h_comp_hf.2
  -- Index `i` is in range on the abstract side.
  have hi_lt : i < threads.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_lt_a : i < μ_a.threads.length := hlen.symm ▸ hi_lt
  -- The abstract thread at i.
  have h_a_idx : μ_a.threads[i]? = some μ_a.threads[i] :=
    List.getElem?_eq_some_iff.mpr ⟨hi_lt_a, rfl⟩
  set t_a := μ_a.threads[i] with t_a_def
  have hcls := hsim.thread_sim i t_a t h_a_idx hi
  -- Preservation outcomes used in every case.
  have hpres : t'.heapFree ∧ (∀ ts, sp = some ts → ts.heapFree) :=
    Agar.Logic.tstep_heapFree_preserves htf hprog_hf hts
  have hpres_result := hsim.threads_result_wf i t hi
  have hres_t' : t'.result = none ∨ (t'.stmt = .skip ∧ t'.cont = [] ∧ t'.stack = []) :=
    tstep_result_wf_preserves hpres_result hts
  have hres_sp : ∀ ts, sp = some ts → ts.result = none := fun ts hts_eq =>
    tstep_sp_result_none hts hts_eq
  -- Classify thread i.
  rcases hcls with heq | hbody
  · -- ============ Case A: Matching at i (t_a = t). ============
    subst heq
    -- Subcase: is t.stmt a successful .call h_pname?
    by_cases hcall : ∃ x args vs, t.stmt = .call x h_pname args ∧
                                  evalArgs t.env args = some vs
    · -- ===== Case A1: helper call. =====
      obtain ⟨x, args, vs, hstmt, hargs⟩ := hcall
      -- Destructure t to expose its env/cont/stack.
      rcases t with ⟨stmt_t, cont_t, env_t, stack_t, result_t⟩
      simp only at hstmt hargs
      subst hstmt
      -- The thread's `result` must be `none` (Sim invariant: a .call
      -- thread can't be terminated).
      rcases hpres_result with hresn | ⟨hsk, _, _⟩
      · simp only at hresn; subst hresn
      · cases hsk
      -- Derive harity (vs.length = h.params.length) from successful tstep.
      have harity : vs.length = h.params.length := by
        have := hts
        simp only [tstep, callFrom, h_registered, hargs] at this
        by_cases hl : vs.length = h.params.length
        · exact hl
        · simp [hl] at this
      -- Concrete tstep computes explicitly via tstep_call.
      have htstep_call :
          tstep composite.procs none m
            ⟨.call x h_pname args, cont_t, env_t, stack_t, none⟩
            = some (m, ⟨h.body, [], bindParams h.params vs,
                       ⟨x, cont_t, env_t⟩ :: stack_t, none⟩, none) :=
        tstep_call composite.procs m x h_pname args h vs cont_t env_t
          stack_t h_registered hargs harity
      rw [htstep_call] at hts
      simp only [Option.some.injEq, Prod.mk.injEq] at hts
      obtain ⟨hm_eq, ht'_eq, hsp_eq⟩ := hts
      subst hm_eq; subst ht'_eq; subst hsp_eq
      -- Pick v_h from h_safe at vs.
      obtain ⟨ρ_f, v_h, h_denote, h_ret, h_post⟩ := h_safe vs harity
      -- Build the abstract atomic_call step.
      refine ⟨1, ⟨m, μ_a.threads.set i
              ⟨.skip, cont_t, env_t.set x v_h, stack_t, none⟩⟩, ?_, ?_, ?_⟩
      · exact Nat.le_refl _
      · -- Abstract StepStarN_abstract of length 1.
        refine .step (.atomic_call i x args vs v_h cont_t env_t stack_t
          μ_a.mem μ_a.threads ?_ ?_ harity h_post) ?_
        · -- μ_a.threads[i]? = some ⟨.call ...⟩
          rw [h_a_idx]
        · exact hargs
        · -- Need to rewrite μ_a.mem ↦ m via hmem.
          rw [hmem]
          exact .refl _
      · -- Build the new Sim.
        constructor
        · -- mem_eq
          show m = m; rfl
        · -- length_eq
          show (μ_a.threads.set i _).length = (threads.set i _ ++ _).length
          simp
          exact hlen
        · -- threads_heapFree
          intro j t_j hj
          -- Concrete: μ_c'.threads = threads.set i t' ++ [] = threads.set i t'
          show t_j.heapFree
          have hj' : (threads.set i ⟨h.body, [], bindParams h.params vs,
                       ⟨x, cont_t, env_t⟩ :: stack_t, none⟩)[j]? = some t_j := by
            have : threads.set i _ ++ ([] : List Thread) = threads.set i _ := by simp
            rw [this] at hj; exact hj
          by_cases hji : j = i
          · subst hji
            rw [SimStep.set_append_at threads i _ none hi_lt] at hj
            simp at hj; subst hj
            exact hpres.1
          · have hj_lt : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i _).length = threads.length := by simp
              rw [List.getElem?_eq_none_iff.mpr] at hj'
              · cases hj'
              · simp; exact hge
            have := SimStep.set_append_other threads i j _ none hj_lt hji
            rw [this] at hj'
            exact hsim.threads_heapFree j t_j hj'
        · -- threads_result_wf
          intro j t_j hj
          show t_j.result = none ∨ _
          have hj' : (threads.set i ⟨h.body, [], bindParams h.params vs,
                       ⟨x, cont_t, env_t⟩ :: stack_t, none⟩)[j]? = some t_j := by
            have : threads.set i _ ++ ([] : List Thread) = threads.set i _ := by simp
            rw [this] at hj; exact hj
          by_cases hji : j = i
          · subst hji
            rw [SimStep.set_append_at threads i _ none hi_lt] at hj
            simp at hj; subst hj
            left; rfl
          · have hj_lt : j < threads.length := by
              by_contra hge
              push_neg at hge
              rw [List.getElem?_eq_none_iff.mpr] at hj'
              · cases hj'
              · simp; exact hge
            have := SimStep.set_append_other threads i j _ none hj_lt hji
            rw [this] at hj'
            exact hsim.threads_result_wf j t_j hj'
        · -- thread_sim
          intro j t_a_j t_c_j ha_j hc_j
          by_cases hji : j = i
          · -- New InBody at i.
            subst hji
            have hta_eq : t_a_j = ⟨.skip, cont_t, env_t.set x v_h,
                                    stack_t, none⟩ := by
              -- μ_a'.threads[i]? = some t_a_j and the abstract update sets index i.
              have : (μ_a.threads.set i
                      ⟨.skip, cont_t, env_t.set x v_h, stack_t, none⟩)[i]? =
                    some ⟨.skip, cont_t, env_t.set x v_h, stack_t, none⟩ := by
                rw [List.getElem?_set]
                simp [hi_lt_a]
              rw [this] at ha_j; simp at ha_j; exact ha_j.symm
            have htc_eq : t_c_j = ⟨h.body, [], bindParams h.params vs,
                                    ⟨x, cont_t, env_t⟩ :: stack_t, none⟩ := by
              have : (threads.set i ⟨h.body, [], bindParams h.params vs,
                       ⟨x, cont_t, env_t⟩ :: stack_t, none⟩ ++ ([] : List Thread))[i]?
                    = some _ := by
                simp
                rw [List.getElem?_set]; simp [hi_lt]
              rw [this] at hc_j; simp at hc_j; exact hc_j.symm
            subst hta_eq; subst htc_eq
            right
            -- Construct InBody with PureSteps from body-start.
            refine ⟨vs, v_h, cont_t, env_t, x, stack_t, ρ_f,
              h_post, harity, h_denote, h_ret, rfl, ?_⟩
            -- The trajectory.
            have htraj := BodyTraj.pure_steps_to_near_end
              pureBody retExpr (bindParams h.params vs) ρ_f
              ⟨x, cont_t, env_t⟩ stack_t h_denote
            rw [← h_body_eq] at htraj
            exact htraj
          · -- Other indices: unchanged on both sides.
            have hj_lt_c : j < threads.length := by
              by_contra hge
              push_neg at hge
              have h_c_none : (threads.set i ⟨h.body, [], bindParams h.params vs,
                           ⟨x, cont_t, env_t⟩ :: stack_t, none⟩ ++
                          ([] : List Thread))[j]? = none := by
                simp
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [h_c_none] at hc_j; cases hc_j
            have hj_lt_a : j < μ_a.threads.length := hlen.symm ▸ hj_lt_c
            -- μ_a' at j unchanged.
            have ha_old : μ_a.threads[j]? = some t_a_j := by
              have : (μ_a.threads.set i ⟨.skip, cont_t, env_t.set x v_h,
                                          stack_t, none⟩)[j]? =
                     μ_a.threads[j]? := by
                rw [List.getElem?_set]; simp [hji]
              rw [this] at ha_j; exact ha_j
            have hc_old : threads[j]? = some t_c_j := by
              have : (threads.set i ⟨h.body, [], bindParams h.params vs,
                       ⟨x, cont_t, env_t⟩ :: stack_t, none⟩ ++
                      ([] : List Thread))[j]? = threads[j]? := by
                rw [show threads.set i _ ++ ([] : List Thread) = threads.set i _ from by simp]
                exact SimStep.set_append_other threads i j _ none hj_lt_c hji
              rw [this] at hc_j; exact hc_j
            exact hsim.thread_sim j t_a_j t_c_j ha_old hc_old
    · -- ===== Case A2: regular step (non-helper-call). =====
      -- Concrete: tstep fires. Abstract: same tstep (regular constructor).
      refine ⟨1, ⟨m', μ_a.threads.set i t' ++ sp.toList⟩, Nat.le_refl _, ?_, ?_⟩
      · refine .step (.regular i none t t' sp μ_a.mem m' μ_a.threads ?_ ?_ ?_) ?_
        · rw [h_a_idx]
        · exact hcall
        · rw [hmem]; exact hts
        · exact .refl _
      · -- New Sim.
        constructor
        · -- mem_eq
          show m' = m'; rfl
        · -- length_eq
          show (μ_a.threads.set i t' ++ sp.toList).length =
               (threads.set i t' ++ sp.toList).length
          simp [hlen]
        · -- threads_heapFree
          intro j t_j hj
          by_cases hji : j = i
          · subst hji
            rw [SimStep.set_append_at threads i t' sp hi_lt] at hj
            simp at hj; subst hj
            exact hpres.1
          · by_cases hjsp : j < threads.length
            · have := SimStep.set_append_other threads i j t' sp hjsp hji
              rw [this] at hj
              exact hsim.threads_heapFree j t_j hj
            · -- j ≥ threads.length: only possible if j = threads.length and sp = some _.
              push_neg at hjsp
              cases sp with
              | none =>
                  -- sp.toList = []; threads.set i t' has length = threads.length.
                  exfalso
                  have : (threads.set i t' ++ ([] : List Thread)).length = threads.length := by simp
                  rw [List.getElem?_eq_none_iff.mpr] at hj
                  · cases hj
                  · simp; exact hjsp
              | some ts =>
                  -- sp.toList = [ts]. threads.set + append has length = threads.length + 1.
                  have hlen_eq : j = threads.length := by
                    have hj_lt' : j < (threads.set i t' ++ [ts]).length := by
                      have := List.getElem?_eq_some_iff.mp hj
                      simpa using this.1
                    have : j < threads.length + 1 := by simpa using hj_lt'
                    omega
                  subst hlen_eq
                  rw [SimStep.set_append_spawned threads i t' ts] at hj
                  simp at hj; subst hj
                  exact hpres.2 ts rfl
        · -- threads_result_wf
          intro j t_j hj
          by_cases hji : j = i
          · subst hji
            rw [SimStep.set_append_at threads i t' sp hi_lt] at hj
            simp at hj; subst hj
            exact hres_t'
          · by_cases hjsp : j < threads.length
            · have := SimStep.set_append_other threads i j t' sp hjsp hji
              rw [this] at hj
              exact hsim.threads_result_wf j t_j hj
            · push_neg at hjsp
              cases sp with
              | none =>
                  exfalso
                  rw [List.getElem?_eq_none_iff.mpr] at hj
                  · cases hj
                  · simp; exact hjsp
              | some ts =>
                  have hlen_eq : j = threads.length := by
                    have hj_lt' : j < (threads.set i t' ++ [ts]).length := by
                      have := List.getElem?_eq_some_iff.mp hj
                      simpa using this.1
                    have : j < threads.length + 1 := by simpa using hj_lt'
                    omega
                  subst hlen_eq
                  rw [SimStep.set_append_spawned threads i t' ts] at hj
                  simp at hj; subst hj
                  left; exact hres_sp ts rfl
        · -- thread_sim
          intro j t_a_j t_c_j ha_j hc_j
          by_cases hji : j = i
          · subst hji
            have hta_eq : t_a_j = t' := by
              rw [SimStep.set_append_at μ_a.threads i t' sp hi_lt_a] at ha_j
              simp at ha_j; exact ha_j.symm
            have htc_eq : t_c_j = t' := by
              rw [SimStep.set_append_at threads i t' sp hi_lt] at hc_j
              simp at hc_j; exact hc_j.symm
            subst hta_eq; subst htc_eq
            exact Or.inl rfl
          · by_cases hjsp : j < threads.length
            · have hjsp_a : j < μ_a.threads.length := hlen.symm ▸ hjsp
              have ha_old := SimStep.set_append_other μ_a.threads i j t' sp hjsp_a hji
              have hc_old := SimStep.set_append_other threads i j t' sp hjsp hji
              rw [ha_old] at ha_j
              rw [hc_old] at hc_j
              exact hsim.thread_sim j t_a_j t_c_j ha_j hc_j
            · push_neg at hjsp
              cases sp with
              | none =>
                  exfalso
                  rw [List.getElem?_eq_none_iff.mpr] at hc_j
                  · cases hc_j
                  · simp; exact hjsp
              | some ts =>
                  have hlen_eq : j = threads.length := by
                    have hj_lt' : j < (threads.set i t' ++ [ts]).length := by
                      have := List.getElem?_eq_some_iff.mp hc_j
                      simpa using this.1
                    have : j < threads.length + 1 := by simpa using hj_lt'
                    omega
                  subst hlen_eq
                  rw [SimStep.set_append_spawned threads i t' ts] at hc_j
                  rw [hlen] at ha_j
                  rw [SimStep.set_append_spawned μ_a.threads i t' ts] at ha_j
                  simp at ha_j hc_j
                  subst ha_j; subst hc_j
                  exact Or.inl rfl
  · -- ============ Case B: InBody at i. ============
    obtain ⟨vs, v_h, cont_h, env_h, rv_h, rest_h, ρ_f,
            h_post, h_arity, h_denote, h_ret, h_ta_eq, h_traj⟩ := hbody
    -- The abstract doesn't move in either sub-case.
    -- Concrete step's behavior is determined by the trajectory.
    cases h_traj with
    | refl =>
        -- t = ⟨.ret retExpr, [], ρ_f, ⟨rv_h, cont_h, env_h⟩ :: rest_h, none⟩
        have hpop := BodyTraj.pstep_near_end_pop retExpr ρ_f v_h
                      ⟨rv_h, cont_h, env_h⟩ rest_h h_ret
        have hts_pop := BodyTraj.pstep_tstep_procs composite.procs m _ _ hpop
        -- tstep is a function, so the actual hts forces t' and m'.
        rw [hts_pop] at hts
        simp only [Option.some.injEq, Prod.mk.injEq] at hts
        obtain ⟨hm_eq, ht'_eq, hsp_eq⟩ := hts
        subst hm_eq; subst ht'_eq; subst hsp_eq
        -- Now t' = post-frame state = t_a. Abstract stays put.
        refine ⟨0, μ_a, Nat.zero_le _, .refl _, ?_⟩
        constructor
        · show μ_a.mem = m
          exact hmem
        · show μ_a.threads.length = (threads.set i _ ++ ([] : List Thread)).length
          simp [hlen]
        · intro j t_j hj
          by_cases hji : j = i
          · subst hji
            have : (threads.set i _ ++ ([] : List Thread))[i]? = some _ := by
              simp; rw [List.getElem?_set]; simp [hi_lt]
            rw [this] at hj; simp at hj; subst hj
            exact hpres.1
          · have hj_lt : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i _ ++ ([] : List Thread))[j]? = none := by
                rw [show threads.set i _ ++ ([] : List Thread) = threads.set i _ from by simp]
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [this] at hj; cases hj
            have heq : threads.set i _ ++ ([] : List Thread) = threads.set i _ := by simp
            rw [heq] at hj
            have := SimStep.set_append_other threads i j _ none hj_lt hji
            simp at this; rw [this] at hj
            exact hsim.threads_heapFree j t_j hj
        · intro j t_j hj
          by_cases hji : j = i
          · subst hji
            have : (threads.set i _ ++ ([] : List Thread))[i]? = some _ := by
              simp; rw [List.getElem?_set]; simp [hi_lt]
            rw [this] at hj; simp at hj; subst hj
            exact hres_t'
          · have hj_lt : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i _ ++ ([] : List Thread))[j]? = none := by
                rw [show threads.set i _ ++ ([] : List Thread) = threads.set i _ from by simp]
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [this] at hj; cases hj
            have heq : threads.set i _ ++ ([] : List Thread) = threads.set i _ := by simp
            rw [heq] at hj
            have := SimStep.set_append_other threads i j _ none hj_lt hji
            simp at this; rw [this] at hj
            exact hsim.threads_result_wf j t_j hj
        · intro j t_a_j t_c_j ha_j hc_j
          by_cases hji : j = i
          · -- new t_c_j = post-frame state = t_a (the abstract's thread at i).
            subst hji
            have htc_eq : t_c_j = ⟨.skip, cont_h, env_h.set rv_h v_h, rest_h, none⟩ := by
              have : (threads.set i ⟨.skip, cont_h, env_h.set rv_h v_h, rest_h, none⟩ ++
                      ([] : List Thread))[i]? =
                    some ⟨.skip, cont_h, env_h.set rv_h v_h, rest_h, none⟩ := by
                simp; rw [List.getElem?_set]; simp [hi_lt]
              rw [this] at hc_j; simp at hc_j; exact hc_j.symm
            subst htc_eq
            -- t_a_j = μ_a.threads[i] (unchanged).
            rw [h_a_idx] at ha_j; simp at ha_j; subst ha_j
            left; exact h_ta_eq
          · -- Other indices.
            have hj_lt_c : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i _ ++ ([] : List Thread))[j]? = none := by
                rw [show threads.set i _ ++ ([] : List Thread) = threads.set i _ from by simp]
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [this] at hc_j; cases hc_j
            have heq : threads.set i _ ++ ([] : List Thread) = threads.set i _ := by simp
            rw [heq] at hc_j
            have := SimStep.set_append_other threads i j _ none hj_lt_c hji
            simp at this; rw [this] at hc_j
            exact hsim.thread_sim j t_a_j t_c_j ha_j hc_j
    | @step _ t_mid _ hpstep h_rest =>
        -- pstep t = some t_mid; the concrete tstep should match via pstep_tstep_procs.
        have hts_step := BodyTraj.pstep_tstep_procs composite.procs m _ _ hpstep
        rw [hts_step] at hts
        simp only [Option.some.injEq, Prod.mk.injEq] at hts
        obtain ⟨hm_eq, ht'_eq, hsp_eq⟩ := hts
        subst hm_eq; subst ht'_eq; subst hsp_eq
        -- Abstract stays put; new μ_c'.threads[i] = t_mid, with shortened trajectory h_rest.
        refine ⟨0, μ_a, Nat.zero_le _, .refl _, ?_⟩
        constructor
        · show μ_a.mem = m
          exact hmem
        · show μ_a.threads.length = (threads.set i _ ++ ([] : List Thread)).length
          simp [hlen]
        · intro j t_j hj
          by_cases hji : j = i
          · subst hji
            have : (threads.set i t_mid ++ ([] : List Thread))[i]? = some t_mid := by
              simp; rw [List.getElem?_set]; simp [hi_lt]
            rw [this] at hj; simp at hj; subst hj
            exact hpres.1
          · have hj_lt : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i t_mid ++ ([] : List Thread))[j]? = none := by
                rw [show threads.set i t_mid ++ ([] : List Thread) = threads.set i t_mid from by simp]
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [this] at hj; cases hj
            have heq : threads.set i t_mid ++ ([] : List Thread) = threads.set i t_mid := by simp
            rw [heq] at hj
            have := SimStep.set_append_other threads i j t_mid none hj_lt hji
            simp at this; rw [this] at hj
            exact hsim.threads_heapFree j t_j hj
        · intro j t_j hj
          by_cases hji : j = i
          · subst hji
            have : (threads.set i t_mid ++ ([] : List Thread))[i]? = some t_mid := by
              simp; rw [List.getElem?_set]; simp [hi_lt]
            rw [this] at hj; simp at hj; subst hj
            exact hres_t'
          · have hj_lt : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i t_mid ++ ([] : List Thread))[j]? = none := by
                rw [show threads.set i t_mid ++ ([] : List Thread) = threads.set i t_mid from by simp]
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [this] at hj; cases hj
            have heq : threads.set i t_mid ++ ([] : List Thread) = threads.set i t_mid := by simp
            rw [heq] at hj
            have := SimStep.set_append_other threads i j t_mid none hj_lt hji
            simp at this; rw [this] at hj
            exact hsim.threads_result_wf j t_j hj
        · intro j t_a_j t_c_j ha_j hc_j
          by_cases hji : j = i
          · subst hji
            -- New t_c_j = t_mid, with shorter trajectory.
            have htc_eq : t_c_j = t_mid := by
              have : (threads.set i t_mid ++ ([] : List Thread))[i]? = some t_mid := by
                simp; rw [List.getElem?_set]; simp [hi_lt]
              rw [this] at hc_j; simp at hc_j; exact hc_j.symm
            subst htc_eq
            -- t_a_j unchanged.
            rw [h_a_idx] at ha_j; simp at ha_j; subst ha_j
            right
            exact ⟨vs, v_h, cont_h, env_h, rv_h, rest_h, ρ_f,
                   h_post, h_arity, h_denote, h_ret, h_ta_eq, h_rest⟩
          · have hj_lt_c : j < threads.length := by
              by_contra hge
              push_neg at hge
              have : (threads.set i t_mid ++ ([] : List Thread))[j]? = none := by
                rw [show threads.set i t_mid ++ ([] : List Thread) = threads.set i t_mid from by simp]
                rw [List.getElem?_eq_none_iff.mpr]; simp; exact hge
              rw [this] at hc_j; cases hc_j
            have heq : threads.set i t_mid ++ ([] : List Thread) = threads.set i t_mid := by simp
            rw [heq] at hc_j
            have := SimStep.set_append_other threads i j t_mid none hj_lt_c hji
            simp at this; rw [this] at hc_j
            exact hsim.thread_sim j t_a_j t_c_j ha_j hc_j
-/

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
    (pureBody : PureStmt) (retExpr : Expr)
    (h_body_eq : h.body = .seq (embed pureBody) (.ret retExpr))
    (h_comp_hf : composite.heapFree)
    (helper_post : List Val → Val → Prop)
    (h_safe : ∀ vs, vs.length = h.params.length →
              ∃ ρ_f v_h,
                denote pureBody (bindParams h.params vs) = (some (), ρ_f) ∧
                Expr.eval ρ_f retExpr = some v_h ∧
                helper_post vs v_h)
    {μ_a μ_c μ_c' : Machine} {n : Nat}
    (hsim : Sim composite h_pname h pureBody retExpr helper_post μ_a μ_c)
    (htraj : Machine.StepStarN composite n μ_c μ_c') :
    ∃ (n_abs : Nat) (μ_a' : Machine),
      Machine.StepStarN_abstract composite h_pname h helper_post n_abs μ_a μ_a' ∧
      Sim composite h_pname h pureBody retExpr helper_post μ_a' μ_c' := by
  induction htraj generalizing μ_a with
  | refl _ => exact ⟨0, μ_a, .refl μ_a, hsim⟩
  | step h1 h2 ih =>
      obtain ⟨n_one, μ_mid, _hle, hone, hsim_mid⟩ :=
        simulation_step composite h_pname h h_registered
          pureBody retExpr h_body_eq h_comp_hf
          helper_post h_safe hsim h1
      obtain ⟨n_rest, μ_a', hrest, hsim'⟩ := ih hsim_mid
      exact ⟨n_one + n_rest, μ_a', hone.trans hrest, hsim'⟩

/-- **Transfer.** Given `Sim μ_a μ_c` and the per-state safety of
`μ_a` under the abstract relation, every thread of `μ_c` is
value-or-reducible (and at index 0, the value satisfies
`composite_post`). The InBody case derives reducibility from the
body's pure trajectory. -/
theorem sim_transfer
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (pureBody : PureStmt) (retExpr : Expr)
    (helper_post : List Val → Val → Prop)
    {μ_a μ_c : Machine} (composite_post : Val → Prop)
    (hsim : Sim composite h_pname h pureBody retExpr helper_post μ_a μ_c)
    (habs_safe_here :
      ∀ k t, μ_a.threads[k]? = some t →
        (∃ v, t.toValue = some v ∧ (k = 0 → composite_post v)) ∨
        thread_reducible_abstract composite h_pname h helper_post μ_a.mem t) :
    ∀ k t, μ_c.threads[k]? = some t →
      (∃ v, t.toValue = some v ∧ (k = 0 → composite_post v)) ∨
      thread_reducible composite.procs μ_c.mem t := by
  intro k t_c hk
  have hlen := hsim.length_eq
  have hmem := hsim.mem_eq
  cases ha : μ_a.threads[k]? with
  | none =>
      exfalso
      have hk_lt : k < μ_c.threads.length := by
        rcases hkk : μ_c.threads[k]? with _ | t
        · rw [hkk] at hk; cases hk
        · exact List.getElem?_eq_some_iff.mp hkk |>.1
      have hk_lt_a : k < μ_a.threads.length := hlen ▸ hk_lt
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
        · right
          rcases hred with ⟨m', t', sp, hstep, _hno⟩ |
                          ⟨x, args, vs, v, hstmt, hres, hargs, harity, hpost⟩
          · refine ⟨m', t', sp, ?_⟩
            rw [← hmem]; exact hstep
          · rcases t_a with ⟨stmt_a, cont_a, env_a, stack_a, result_a⟩
            simp only at hstmt hres hargs
            subst hstmt
            subst hres
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
      · -- InBody: concrete thread sits on the body's pure trajectory.
        -- Reducibility from the trajectory: either t_c steps via pstep
        -- (PureSteps.step) or t_c IS the near-end and `pstep_near_end_pop`
        -- gives the doReturn step.
        obtain ⟨vs, v_h, cont, env, rv, rest, ρ_f,
                _hpost, _hlen, _hdenote, h_ret, _hta, h_traj⟩ := hbody
        right
        cases h_traj with
        | refl =>
            -- t_c = ⟨.ret retExpr, [], ρ_f, frame :: rest, none⟩. Pop fires.
            have hpop := BodyTraj.pstep_near_end_pop retExpr ρ_f v_h
              ⟨rv, cont, env⟩ rest h_ret
            have hts := BodyTraj.pstep_tstep_procs composite.procs μ_c.mem _ _ hpop
            refine ⟨μ_c.mem,
              BodyTraj.postDoReturnThread ⟨rv, cont, env⟩ rest v_h, none, ?_⟩
            exact ⟨none, hts⟩
        | @step _ t_mid _ hpstep _ =>
            have hts := BodyTraj.pstep_tstep_procs composite.procs μ_c.mem _ _ hpstep
            refine ⟨μ_c.mem, t_mid, none, ?_⟩
            exact ⟨none, hts⟩

/-- **The composition lemma.** Combines the helper's structural-
denotational shape with the composite's abstract safety to deliver
concrete `Machine.safe`. The "purity" premises (heapFree / forkFree /
noCall) all follow from `h_body_eq`. -/
theorem Machine.safe_compose
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (pureBody : PureStmt) (retExpr : Expr)
    (h_body_eq : h.body = .seq (embed pureBody) (.ret retExpr))
    (h_comp_hf : composite.heapFree)
    (helper_post : List Val → Val → Prop)
    -- For each parameter binding, the body converges denotationally to
    -- some final environment whose retExpr-eval satisfies `helper_post`.
    (h_safe : ∀ vs, vs.length = h.params.length →
              ∃ ρ_f v_h,
                denote pureBody (bindParams h.params vs) = (some (), ρ_f) ∧
                Expr.eval ρ_f retExpr = some v_h ∧
                helper_post vs v_h)
    (composite_post : Val → Prop)
    (composite_abstract_safe :
      Machine.SafeTp_abstract composite h_pname h helper_post
        (Machine.initial composite) composite_post) :
    Machine.safe composite composite_post := by
  intro n μ_c htraj k t_c hk
  have hsim_init :
      Sim composite h_pname h pureBody retExpr helper_post
        (Machine.initial composite) (Machine.initial composite) :=
    simulation_init composite h_pname h pureBody retExpr helper_post h_comp_hf.1
  have htraj' : Machine.StepStarN composite n (Machine.initial composite) μ_c := htraj
  obtain ⟨n_abs, μ_a, habs_traj, hsim⟩ :=
    simulation_lift composite h_pname h h_registered pureBody retExpr
      h_body_eq h_comp_hf helper_post h_safe hsim_init htraj'
  have habs_here :
      ∀ k t, μ_a.threads[k]? = some t →
        (∃ v, t.toValue = some v ∧ (k = 0 → composite_post v)) ∨
        thread_reducible_abstract composite h_pname h helper_post μ_a.mem t := by
    intro k t hk
    exact composite_abstract_safe n_abs μ_a habs_traj k t hk
  exact sim_transfer composite h_pname h h_registered pureBody retExpr
    helper_post composite_post hsim habs_here k t_c hk

/-! ## Worked-example consumption smoke test

A purely structural test that the worked-example consumption pattern
from `COMPOSITION_DESIGN.md` lines up: a user can write the
`apply Machine.safe_compose`, refine the conjunction, and discharge
the four goals in sequence. We use trivially-stubbed inputs so the
test typechecks even though the actual `Machine.safe_compose` body
contains `sorry`s. -/

section WorkedExampleSmokeTest

/-- Trivial dummy helper. Body is `.seq .skip (.ret (.val Val.unit))`
to match the structural premise `h.body = .seq (embed pureBody) (.ret retExpr)`. -/
def dummyHelper : Proc :=
  { params := [], body := .seq (embed .skip) (.ret (.val Val.unit)) }

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
    (pureBody := .skip) (retExpr := .val Val.unit)
    (helper_post := fun _ _ => True)
  · -- h_registered : dummyComposite.procs "h" = some dummyHelper
    rfl
  · -- h_body_eq : dummyHelper.body = .seq (embed .skip) (.ret (.val Val.unit))
    rfl
  · -- h_comp_hf : dummyComposite.heapFree
    refine ⟨?_, ?_⟩
    · -- main = .skip is heap-free
      trivial
    · intro name proc hp
      by_cases hn : name = "h"
      · simp only [dummyComposite, hn, if_pos] at hp; cases hp
        refine ⟨trivial, trivial⟩
      · simp only [dummyComposite, hn, if_neg, if_false] at hp
        cases hp
  · -- h_safe : denote .skip ρ converges trivially, retExpr evaluates to .unit
    intro vs _hlen
    exact ⟨bindParams dummyHelper.params vs, Val.unit, rfl, rfl, trivial⟩
  · -- composite_abstract_safe
    sorry

end WorkedExampleSmokeTest

end Agar

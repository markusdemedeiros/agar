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
  `⟨.skip, frame.cont, frame.env.set frame.rv v_h, rest, none⟩` where
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

/-- The final `.ret`-pop: from the near-end state, a single pstep fires
`doReturn` and lands at the post-frame state. -/
theorem pstep_near_end_pop
    (retExpr : Expr) (ρ' : Env) (v_h : Val) (frame : Frame) (rest : List Frame)
    (h_ret : Expr.eval ρ' retExpr = some v_h) :
    pstep ⟨.ret retExpr, [], ρ', frame :: rest, none⟩
      = some ⟨.skip, frame.cont, frame.env.set frame.rv v_h, rest, none⟩ := by
  simp [pstep, tstep, h_ret, doReturn]
  cases hc : frame.cont with
  | nil => simp
  | cons s rest => simp

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
  intro t t' hi h
  induction h generalizing threads with
  | refl =>
      refine ⟨0, ?_⟩
      have : threads.set i t = threads := by
        apply List.set_of_getElem?
        exact hi
      rw [this]; exact .refl _
  | @step t₀ t₁ _ hpstep _ ih =>
      have hstep := pstep_to_Machine_Step_at composite m threads i t₀ t₁ hi hpstep
      -- After the step, the threads list becomes threads.set i t₁.
      have hi' : (threads.set i t₁)[i]? = some t₁ := by
        rcases h_lt : i < threads.length with _
        · simp [List.getElem?_set, List.getElem?_eq_some_iff]
          have : i < threads.length := by
            have := List.getElem?_eq_some_iff.mp hi
            exact this.1
          simp [this]
        · -- i ≥ threads.length, but then hi would be none, contradiction.
          have hkk : i < threads.length := (List.getElem?_eq_some_iff.mp hi).1
          exact absurd hkk (by simp [h_lt])
      obtain ⟨n_rest, hrest⟩ := ih hi'
      -- Compose: 1 + n_rest steps via Machine.StepStarN.step.
      refine ⟨n_rest + 1, ?_⟩
      have heq : (threads.set i t₁).set i t' = threads.set i t' := by
        simp [List.set_set]
      rw [← heq] at hrest
      have : n_rest + 1 = Nat.succ n_rest := rfl
      rw [this]
      exact .step hstep hrest

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
      ⟨m, threads.set i ⟨.skip, frame.cont, frame.env.set frame.rv v_h, rest, none⟩⟩ := by
  -- Stitch the body's PureSteps + the final .ret pop.
  have hbody := BodyTraj.pure_steps_to_near_end pureBody retExpr
    (bindParams h.params vs) ρ_f frame rest h_denote
  have hpop := BodyTraj.pstep_near_end_pop retExpr ρ_f v_h frame rest h_ret
  have hfull : PureSteps
      ⟨.seq (embed pureBody) (.ret retExpr), [], bindParams h.params vs,
        frame :: rest, none⟩
      ⟨.skip, frame.cont, frame.env.set frame.rv v_h, rest, none⟩ :=
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

/-- **Simulation step.** Given `Sim μ_a μ_c` and a concrete step
`μ_c → μ_c'`, the abstract takes 0 or 1 abstract steps to reach some
`μ_a'` with `Sim μ_a' μ_c'`. -/
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
            refine ⟨μ_c.mem, _, none, ?_⟩
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

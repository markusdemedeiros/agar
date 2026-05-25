# Compositional `Machine.safe` for pure procedures

## Goal

A purely Lean / operational lemma that combines:

1. **Standalone safety** of a pure helper procedure, AND
2. **Abstract safety** of a composite client (treating the helper's calls
   as atomic with a known input-output spec),

to produce **`Machine.safe composite composite_post`** for the *concrete*
composite (where helper calls execute their bodies normally).

This output plugs *directly* into the existing `Agar.Logic.completeness`
theorem to yield an Iris `wp` on the composite — no new completeness
variant, no per-call wp rule, no `▷^[M]`.

## Restrictions for tractability (v1)

- **`forN`-based helpers only.** The helper's body uses `.forN n s` (not
  `.while_`), so the body is deterministic and `unrollW`'s `.call`
  sentinel never appears. The body's `pstep` trajectory from any
  starting env is unique.
- **Helper body is `heapFree ∧ forkFree`.** No heap interaction during
  the helper's execution, no thread spawning.
- **Helper body is `noCall`** (no further `.call` inside). Eliminates a
  class of stack-bookkeeping bugs around nested calls.
- **Single helper procedure** registered in the composite under a
  specific `h_pname`. Generalising to multiple pure procedures is
  mechanical once one works.
- **Multiple threads may be in the helper body simultaneously.** This is
  the only "real" concurrency wrinkle — required by the
  two-worker-CAS-merge example.

## Definitions

### Abstract step relation

```lean
inductive Machine.Step_abstract
    (composite : Program) (h_pname : Name)
    (helper_post : List Val → Val → Prop) :
    Machine → Machine → Prop where
  | regular
      (μ μ' : Machine) (hstep : Machine.Step composite μ μ')
      (hnot_call : -- the step that fired is *not* a `.call x h_pname args`
        ¬ ∃ i x args vs cont env stack t,
          μ.threads[i]? = some t ∧
          t.stmt = .call x h_pname args ∧
          evalArgs t.env args = some vs) :
      Machine.Step_abstract composite h_pname helper_post μ μ'
  | atomic_call
      (i : Nat) (x : Name) (args : List Expr) (vs : List Val) (v : Val)
      (cont : List Stmt) (env : Env) (stack : List Frame)
      (m : Mem) (threads : List Thread)
      (t : Thread) (hi : threads[i]? = some t)
      (htstmt : t = ⟨.call x h_pname args, cont, env, stack, none⟩)
      (hargs : evalArgs env args = some vs)
      (hpost : helper_post vs v) :
      Machine.Step_abstract composite h_pname helper_post
        ⟨m, threads⟩
        ⟨m, threads.set i ⟨.skip, cont, env.set x v, stack, none⟩⟩
```

Notes:
* In the atomic case we *unify* skip+empty-cont and skip+cons-cont into
  one shape (cont passed through unchanged); the post-call thread state
  is `⟨.skip, cont, env.set x v, stack, none⟩`. Standard `.skip`-cont
  rule handles the next step.
* No heap change in the atomic case (heapFree).
* No spawn (forkFree).
* The thread at index `i` is the one calling.

### Abstract n-step closure / abstract SafeTp

```lean
inductive Machine.StepStarN_abstract … : Nat → Machine → Machine → Prop
def Machine.SafeTp_abstract composite h_pname helper_post μ post : Prop :=
  ∀ n μ', Machine.StepStarN_abstract … n μ μ' →
    ∀ k t, μ'.threads[k]? = some t →
      (∃ v, t.toValue = some v ∧ (k = 0 → post v)) ∨
      thread_reducible_abstract composite h_pname helper_post μ'.mem t
```

where `thread_reducible_abstract` mirrors `thread_reducible` but uses
the abstract step relation.

### Standalone helper safety (reuses bridge)

```lean
def StandaloneHelperSafe (h : Proc) (vs : List Val)
    (helper_post : List Val → Val → Prop) : Prop :=
  Machine.safe (programOfHelperAtVs h vs) (helper_post vs)
```

where `programOfHelperAtVs` is a one-shot Program:

```lean
def programOfHelperAtVs (h : Proc) (vs : List Val) : Program where
  procs := noProcs
  main  := assignAllParams h.params vs ; embed_h_body ; .ret h.retExpr
```

`assignAllParams` is a sequence of `.assign param_i (.val vs[i])` for
each param. After this sequence runs from `Env.empty`, the env equals
`bindParams h.params vs` — i.e., the same env a call would set up.

The bridge already produces this safety claim from a denotational
identity.

## The composition lemma

```lean
theorem Machine.safe_compose
    (composite : Program) (h_pname : Name) (h : Proc)
    (h_registered : composite.procs h_pname = some h)
    (h_pure :
      h.body.heapFree ∧ h.body.forkFree ∧ h.body.noCall ∧
      ∃ pureBody : PureStmt, h.body = .seq (embed pureBody) (.ret h_ret_expr))
    (helper_post : List Val → Val → Prop)
    -- Helper's safety, per parameter binding:
    (h_safe : ∀ vs, vs.length = h.params.length →
              StandaloneHelperSafe h vs helper_post)
    -- Composite's safety under the abstract step relation:
    (composite_abstract_safe :
      ∀ σ, Machine.SafeTp_abstract composite h_pname helper_post
            ⟨σ, [Thread.initial composite.main]⟩ composite_post) :
    Machine.safe composite composite_post
```

## Proof sketch — forward simulation

### Simulation invariant `Sim μ_abs μ_concrete`

```
Sim μ_abs μ_concrete ↔
  μ_abs.mem = μ_concrete.mem ∧
  μ_abs.threads.length = μ_concrete.threads.length ∧
  ∀ i, ThreadSim (μ_abs.threads.get? i) (μ_concrete.threads.get? i)
```

where `ThreadSim` is either:

* **Matching:** `μ_abs.threads[i] = μ_concrete.threads[i]`. The thread is
  not currently inside the helper's body.
* **InBody:** there exists a *helper invocation context* — a tuple
  `⟨vs, frame⟩` — such that:
  - `μ_abs.threads[i] = ⟨.skip, frame.cont, frame.env.set frame.rv v_h, rest, none⟩`
    for the *helper-produced* value `v_h` (deterministically computed by
    the helper at `vs`),
  - `μ_concrete.threads[i].stack = frame :: rest`,
  - `μ_concrete.threads[i]` is reachable via `pstep`s from
    `⟨h.body, [], bindParams h.params vs, frame :: rest, none⟩`,
  - The body's trajectory from there to the post-`.ret` state delivers
    `v_h`.

`v_h` is unique by determinism of the body (forN-based, no nondeterministic
constructs). The bridge's helper-safety pins it down.

### Simulation step

For each concrete `Machine.Step composite μ_c μ_c'`, prove
`∃ μ_a', (Sim μ_a μ_c ∧ Machine.StepStarN_abstract … (0 or 1) μ_a μ_a' ∧ Sim μ_a' μ_c')`.

Cases on the stepping thread's classification:

1. **Matching thread, step is *not* a `.call h_pname`.** Abstract takes
   one regular step. New states match.
2. **Matching thread, step *is* `.call h_pname`.** Abstract takes one
   atomic helper step. Concrete enters body. Both end up: abstract at
   `⟨.skip, cont, env.set x v_h, stack, none⟩`, concrete at
   `⟨h.body, [], bindParams, frame :: stack, none⟩`. Both are
   simulation-equivalent (`InBody` case).
3. **InBody thread, step is body-internal `pstep`.** Abstract doesn't
   step. Concrete advances one body step. Invariant preserved.
4. **InBody thread, step is the final `.ret` popping the helper-frame.**
   Concrete pops frame, becomes
   `⟨frame_cont_head_or_skip, frame_cont_tail, frame.env.set frame.rv v_h, rest, none⟩`.
   This *equals* the abstract's already-existing state for this thread.
   Sim transitions from `InBody` to `Matching`.

### Lifting from `SafeTp_abstract` to `SafeTp` (concrete)

Given `Sim μ_a μ_c`:
* If `Sim` is `Matching` at thread `k`, `μ_a.threads[k] = μ_c.threads[k]`.
  `toValue`s match, reducibility matches. Direct transfer.
* If `Sim` is `InBody` at thread `k`, the concrete thread is mid-body —
  reducible by the helper's standalone safety (every body state is
  reducible except the final `.ret`, which is *also* reducible —
  `doReturn` always fires). Abstract has already moved past this call,
  so its disjunct is whatever it is — but we don't need it; the
  concrete reducibility is established directly.

Combining: every concrete reachable state has every thread
reducible-or-value, with `composite_post` at the main thread's
termination (transferring from abstract, which only sees the main
thread in `Matching` mode at the end since helper calls are atomic).

### Length of proof

Realistic estimate: 400–600 lines, plus ~80 lines of auxiliary lemmas
(stack extension, helper-body determinism, simulation-equivalence
classes).

## Worked-example consumption

```lean
-- Client has rangeProdHelper a b, two worker procs that .call it,
-- and a main that forks both, spin-waits, then loads acc.

theorem rangeProd_composite_safe :
    Machine.safe rangeProd_composite (· = Val.int 3628800) := by
  apply Machine.safe_compose
  · exact (rangeProd_composite.procs_h_eq)         -- registered
  · refine ⟨?_, ?_, ?_, ?_⟩                        -- pure constraints
  · intro vs hlen                                  -- standalone safety
    exact rangeProd_bridge_safe vs hlen
  · intro σ                                        -- abstract safety
    exact rangeProd_abstract_safe σ                -- discharged via Iris on abstract program, or meta-level

-- Then existing completeness fires:
theorem rangeProd_composite_wp :
    ⊢ |={⊤}=> wp_⊤ (Thread.initial rangeProd_composite.main) (fun v => ⌜v = Val.int 3628800⌝) :=
  completeness GF F rangeProd_composite_heapFree rangeProd_composite_safe
```

`rangeProd_abstract_safe` is what the user still has to prove —
operationally easier than concrete safety because helper calls are
one step, but still requires CAS-interleaving reasoning. Tractable
combinatorially for our 2-worker example.

## Implementation roadmap

1. **`Machine.Step_abstract`** + `StepStarN_abstract` + `SafeTp_abstract`
   (definitions only; ~50 lines).
2. **`Machine.safe_compose`** statement + helper definitions (~50 lines).
3. **Auxiliary lemmas:** stack-extension, body determinism, helper-frame
   recognition (~150 lines).
4. **The simulation proof** — the meat (~300–400 lines).

Cap: 4 hours of subagent work. Expected partial progress acceptable if
the statement + simulation invariant compile cleanly even with some
`sorry`s in the per-case branches.

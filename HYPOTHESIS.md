# The callee-frame wp gap

> **2026-05-26 final update.** Route A is **end-to-end closed** for the
> pure-helper case. The headline showcase — taking an `Std.Do.Triple`
> over the helper's denotation and folding it down to a closed
> `Machine.safe` of the composite via Iris — runs through the
> following pipeline:
>
> ```
> Std.Do.Triple over denote(rangeProd_body)    ┐
>   │  Triple.iff unfolds; direct induction    │
>   ▼                                          │ Operational
> rangeProd_denote_converges                   │ side
>   │  denote_sound (pure adequacy)            │ (no Iris, no procs)
>   ▼                                          │
> helper_init_reaches_terminal (PureSteps)     │
>   │  helperProg_stepStarN_chain              │
>   ▼                                          │
> helperProg_safe : SafeTp under noProcs       ┘
>   │  SafeTp_procs_irrel_of_strict (StrictHelperShape — no .call/.fork)
>   ▼
> helper_safeTp : SafeTp under composite.procs ┐
>   │  completeness_open (Theorem 15, open-context — no fresh AgarG)
>   ▼                                          │
> wp at helper_init                            │ Iris side
>   │  wp_wand (reshape post)                  │ (fork_post := True
>   ▼                                          │  threaded throughout)
> wp at helper_init w/ post-doReturn wp        │
>   │  BodyTraj.wp_stack_push (callee-frame embedding)
>   ▼                                          │
> wp at wp_call residual                       ┘  ⟵ wp_callee_routeA
>   │
>   │  Iris-level walkthrough: wp_seq → wp_fork (True) → wp_call (True)
>   │                          → wp_callee_routeA → wp_ret_top
>   ▼
> wp at Thread.initial composite.main
>   │  wp_safe_bupd (pick fork_post := True for the existential)
>   ▼
> Machine.safe rangeProdComposite3 (fun _ => True)  ✓
> ```
>
> `rangeProd_composite_walkthrough_RouteA` compiles. The two list-
> bookkeeping sorrys (`set_append_other`, `set_append_at`) are also
> closed. The only remaining sorrys are in the **legacy operational
> `Machine.safe_compose` route** (`simulation_step` and one smoke-test
> example), which §8.6 marks as retired in favor of the Iris path.
>
> **File map.** The pipeline is split across two example files plus
> the supporting infrastructure:
>
> * `Agar/Examples/ExternalSolver.lean` — consolidated showcase: Std.Do
>   triple → operational `Machine.SafeTp` → Iris wp → `Machine.safe`
>   of the composite (the full pipeline).
> * `Agar/Iris/Completeness.lean` — `completeness_open` (Theorem 15
>   open-context variant).
> * `Agar/Iris/StackPush.lean` — `BodyTraj.wp_stack_push`.
> * `Agar/Operational/StackExt.lean` — `stackExt` + supporting `tstep`
>   lemmas underneath `wp_stack_push`.
> * `Agar/Operational/StrictHelper.lean` — `StrictHelperShape` +
>   `SafeTp_procs_irrel_of_strict`.

> **2026-05-25 update.** Route A produced reusable infrastructure
> (`completeness_general` and the open-context variant `completeness_open`).
> The closed-world `completeness_general` did not close the example
> directly, surfacing a "closed-world" structural issue (see §8) that
> motivated the open-context variant. See §8 for the diagnosis and the
> revised path forward (open-context Theorem 15 + Std.Do/mvcgen bridge
> to operational safety). The original §1–§7 below is preserved as a
> historical record of the framing.

---


## 0. Context & current state

`Machine.safe_compose` is the headline composition theorem in
`Agar/Operational/Composition.lean`. Its statement (current form):

```lean
theorem Machine.safe_compose
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
    (composite_post : Val → Prop)
    (composite_abstract_safe :
      Machine.SafeTp_abstract composite h_pname h helper_post
        (Machine.initial composite) composite_post) :
    Machine.safe composite composite_post
```

The proof is currently **not closed**. Active `sorry`s in
`Composition.lean`:

| Lemma | Status | Note |
|---|---|---|
| `BodyTraj.pstep_near_end_pop` | sorry | Statement is wrong for non-empty `frame.cont` — `doReturn` pops the head of `frame.cont` onto stmt, doesn't preserve the `⟨.skip, frame.cont, ...⟩` shape. Needs case-split RHS. |
| `BodyTraj.PureSteps_to_StepStarN` | sorry | Refl case used a fabricated `List.set_of_getElem?` lemma. Step case probably fine modulo the refl case. |
| `SimStep.set_append_other`, `set_append_at` | sorry | Bookkeeping; fixable. |
| `simulation_step` | sorry | The big one. Inherits the `pstep_near_end_pop` / `Step_abstract.atomic_call` shape mismatch — `atomic_call`'s output thread is `⟨.skip, cont, ...⟩` but `doReturn` produces `⟨head_of_cont, tail_of_cont, ...⟩` on non-empty `cont`. |

Working infrastructure that's solid: `denote_sound_stk` (stack-extended denote_sound), `pstep_tstep_procs` (procs-irrelevance for pstep success), `pstep_to_Machine_Step_at`, `pure_steps_to_near_end` modulo the bad `.ret` case in `pstep_near_end_pop`.

**The pure-operational composition route via `Machine.SafeTp_abstract` is unfinished and has a design issue** (the `Step_abstract.atomic_call` shape vs the actual `doReturn` shape). That route may still be viable with a doReturn-matched fix, but we're now considering a different angle.

---

## 1. The core gap (Iris angle)

We have two complementary tools:

* **Theorem 15** (`completeness_modulo_lemma14` in `Agar/Iris/Completeness.lean:1000`):
  ```
  prog.heapFree  ∧  ∀ σ, Machine.safeFrom prog σ φ
   ⇒  ⊢ |={⊤}=> ∃ Hsi fork_post,
          state_interp Mem.empty ∗
          wp prog.procs fork_post ⊤ (Thread.initial prog.main) (fun v => ⌜φ v⌝)
  ```
  i.e. **operational safety of a closed heap-free program → Iris `wp` for its main thread**.

* **`PureHelper.wp_of_denote`** (in `Agar/Iris/PureHelperBridge.lean`):
  bundles "denotational identity of a helper" → `Machine.safe` of the
  helper-as-program → (via Theorem 15) the Iris wp for its main.

* **`wp_call`** (in `Agar/Iris/Rules.lean:751`):
  ```
  ▷ wp procs fp ⊤ ⟨proc.body, [], bindParams ..., ⟨x, cont, env⟩ :: stack, none⟩ Φ
   ⊢ wp procs fp ⊤ ⟨.call x f args, cont, env, stack, none⟩ Φ
  ```
  At a `.call`, the residual obligation is a wp for the helper body running with a **non-empty stack** (saved caller frame) and the **outer caller's post** `Φ`.

**The gap.** Theorem 15 hands back a wp where:
- the thread starts at `Thread.initial prog.main = ⟨prog.main, [], Env.empty, [], none⟩` — **empty stack**, **empty cont**, **`Env.empty`**;
- the post is `fun v => ⌜φ v⌝` evaluated when the thread reaches the terminated leaf `(.skip, [], _, [], some v)` — i.e., **`.ret` terminates the thread**.

`wp_call`'s residual obligation needs a wp where:
- the thread starts at `⟨proc.body, [], bindParams ..., ⟨x, cont, env⟩ :: stack, none⟩` — **non-empty stack**, body's own initial env (`bindParams`);
- the post is the caller's outer Φ, evaluated when the **whole composite trace** eventually terminates (`.ret` here does `doReturn`, popping the frame and continuing in the caller).

The two wp's are about different programs (the helper-as-program vs the composite), different procs tables (`noProcs` vs `composite.procs`), and have different post-semantics at `.ret` (terminate vs pop-and-continue). The shapes do not unify directly.

**Witness:** `Agar/Examples/SimpleRangeProdComposition.lean` walks the composite (`fork rangeProdCaller; x := call rangeProd(1); ret x`) through Iris tactics to exactly the two `.call rangeProd` sites. Two open goals:

```
Goal 1 (forked thread):
  wp composite.procs ⊤ ⊤
     ⟨.call "r" "rangeProd" [.val (.int 5)], [.ret (.var "r")], Env.empty, [], none⟩
     Φ_fork

Goal 2 (main thread):
  wp composite.procs ⊤ ⊤
     ⟨.call "x" "rangeProd" [.val (.int 1)], [.ret (.var "x")], Env.empty, [], none⟩
     Φ_main
```

These are exactly what the gap-bridging tool must discharge.

---

## 2. Acceptance criterion

A successful resolution should:

1. Compile `Agar/Examples/SimpleRangeProdComposition.lean` with the two `.call rangeProd` `sorry`s **closed**.
2. Not introduce new `sorry`s in `Agar/Iris/Completeness.lean`, `Agar/Iris/Rules.lean`, or `Agar/Iris/Adequacy.lean` (modulo lemmas whose proofs are *new infrastructure* per the route — but those lemmas must themselves be closed).
3. Cleanly express the bridge as a reusable lemma — not just inline tactics that happen to discharge the two specific goals.

---

## 3. Route A — Generalize Theorem 15

**Idea.** Theorem 15 currently fixes the initial thread to `Thread.initial prog.main` (empty stack, empty cont, `Env.empty`) and the post to `⌜φ v⌝` (a Lean-prop wrap of an operational value-predicate). Generalize it to take an arbitrary initial thread state and an arbitrary Iris-level continuation post.

### A.1 Target statement

```lean
theorem completeness_general
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF]
    {prog : Program}
    (hpf : prog.heapFree)
    (t_init : Thread)
    (htf_init : t_init.heapFree)
    -- Operational safety from the single-thread machine starting at t_init,
    -- with an Iris-side characterisation of the eventual termination value.
    (hs : ∀ σ, Machine.SafeTp prog ⟨σ, [t_init]⟩
                (fun v => -- a value-level predicate that operational
                          -- safety can witness; see "shape of the post" below
                          True))
    -- Iris-level continuation: given the eventual termination value,
    -- the Iris user can produce whatever Φ_outer-shape they need.
    (Φ : Val → IProp GF) :
    ∀ [_LC : InvGS_gen false GF],
      ⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
        state_interp (GF := GF) Mem.empty ∗
        wp prog.procs fork_post ⊤ t_init Φ
```

**Key design choices for the post:**
- The current Theorem 15's post is `fun v => ⌜φ v⌝` because the underlying operational property `Machine.SafeTp prog μ φ` carries `φ` as a value-predicate. For a callee, we want `Φ` to be a **general iprop continuation** — Φ might mention ghost state, invariants, the caller's resources, etc.
- The simplest design: Φ is an arbitrary `Val → IProp GF`, and the operational side just needs *safety* (no value-predicate). The wp fires `Φ v` at the leaf where the thread terminates with value `v` (skip-empty-empty-some-v).

If `t_init` has empty stack, the wp fires Φ at `.ret`. **If `t_init` has non-empty stack**, the wp continues past the `.ret` (because doReturn doesn't terminate the thread — the thread becomes a non-leaf post-frame state). For this to make sense, the post Φ should only fire at the *eventual* leaf state — i.e., when the entire stack has been unwound and the thread truly terminates.

This means **the generalised theorem only fires Φ at thread-truly-terminated, regardless of intermediate `.ret`s**. The callee context exploits this by including the caller's continuation work inside Φ_outer — which is exactly how wp_call composes wp's.

### A.2 What changes inside

**`percomplete` (Lemma 14, `Completeness.lean:806`)** is already parametric over the per-thread index `n` and the per-thread state `t`. It does **not** need structural generalization — its statement already covers any heap-free thread in the threadpool. The Löb-induction body recursively handles `t`'s tsteps and uses `Machine.SafeTp.step_closed` to advance the SafeTp witness.

What **does** need generalization: the **invariant body `Icompl_pure prog φ γ`**. Currently it bundles `∃ ts, ⌜SafeTp prog ⟨Mem.empty, ts⟩ φ⌝ ∗ threadpool_auth γ ts`. We don't want to change the SafeTp shape (still threadpool-level, still φ : Val → Prop), but we do want to allow the threadpool to start with a custom initial thread.

The cleanest generalization keeps `Icompl_pure` as-is, but the **outer Theorem 15 wrapper** changes:

```lean
-- Old: starts the threadpool at [Thread.initial prog.main].
-- New: starts the threadpool at [t_init].
threadpool_init prog ⟨Mem.empty, [t_init]⟩
```

and the SafeTp witness becomes `hs Mem.empty : Machine.SafeTp prog ⟨Mem.empty, [t_init]⟩ φ_internal` for some operational φ_internal.

**Tricky bit — relating the operational `φ_internal` to the Iris Φ:**
- The operational SafeTp is parametrised by a `Val → Prop` (Lean-level value predicate). It fires at terminated threads with `t.toValue = some v ∧ φ v`.
- The Iris Φ is `Val → IProp GF`. It fires inside the wp at terminated thread states.
- These have to align: when the wp's underlying thread reaches `(.skip, [], _, [], some v)`, the wp's value step fires `Φ v` — and the operational SafeTp evidence has to certify `φ_internal v` for that same `v`.

The simplest alignment: take `φ_internal := fun _ => True` and require `Φ` to be the **invariant `inv N (Icompl_pure prog (fun _ => True) γ)`** plus a user-supplied iprop continuation. The user reads Φ off the threadpool's eventual terminal state via the invariant. The user then proves their own Iris-level claim about that value.

This is structurally similar to `weaken_post` but in reverse: instead of weakening an internal `percomplete_post γ 0 v` into `⌜φ v⌝`, you let the user *define* what they want at that value via their Φ.

### A.3 Sub-tasks for Route A

1. **Define `completeness_general`'s statement** with the chosen Φ-shape.
2. **Adapt the heap-init + threadpool-init + invariant-alloc bookkeeping** (Completeness.lean:1019–1080-ish) for the generalized initial thread.
3. **Apply `percomplete` to `t_init`** instead of `Thread.initial prog.main`. The lookup uses `n = 0` (only thread in the pool) and `t = t_init`.
4. **Reroute `weaken_post`** to fire Φ instead of `⌜φ v⌝` — or factor out a Φ-parametric variant.
5. **Apply the new theorem at the `.call` site** in `SimpleRangeProdComposition.lean`. Required:
   - A `Machine.SafeTp composite ⟨Mem.empty, [t_callee]⟩ (fun _ => True)` witness, where `t_callee` is the helper running as a callee. This needs an *operational procs-irrelevance lemma*: the helper-as-standalone-program is safe (from the bridge); lift that safety to a single-thread state running under `composite.procs` with a frame on its stack.
   - The Iris-level Φ that consumes the helper's eventual return value and continues the caller's wp.

### A.4 Subtleties / pitfalls (Route A)

* **Procs irrelevance at the operational level.** The helper-as-program uses `noProcs`. The callee runs under `composite.procs`. We need:
  ```lean
  ∀ σ t, Machine.SafeTp programOfHelperAtVs ⟨σ, [t]⟩ φ →
         Machine.SafeTp ⟨composite.procs, programOfHelperAtVs.main⟩ ⟨σ, [t]⟩ φ
  ```
  Because `h.body` is `noCall ∧ forkFree`, every reachable state's reducibility is the same under both proc tables. Provable but adds machinery.

* **Stack alignment with `t_init`.** If `t_init = ⟨h.body, [], bindParams h.params vs, ⟨x, cont, env⟩ :: outer_stack, none⟩`, the SafeTp evidence must witness safety of that exact state. Standalone safety witnesses a thread with empty stack; need a *stack-extension* lemma for SafeTp too: stack-extending a safe thread preserves safety, because `.ret` with non-empty stack does `doReturn` (continues) rather than terminating, and the post-frame state may or may not be reducible depending on the saved continuation — we'd need to assume the saved continuation is itself "safe enough."

  Alternative: make `t_init`'s stack be `[]` and have Φ handle the doReturn-style transfer to the caller. This is awkward because the helper body's `.ret` then *terminates the wp's thread* — but the caller wants the wp to *continue*. Mismatch.

  The cleanest fix is probably: at the `.call` site, **don't apply `wp_call` first**. Instead, apply the generalized Theorem 15 with `t_init = ⟨.call x h_pname args, cont, env, stack, none⟩` — the call thread itself. Then the wp's body steps through the call → body → ret-pop → continuation entirely under the wp, with Φ firing at the *outer* thread termination. This sidesteps the stack-extension issue: the wp's thread is the same throughout.

* **What value goes into Φ?** The thread eventually terminates with `composite_post v`. For our example, `composite_post = fun _ => True`, so Φ can be `fun _ => ⌜True⌝`. But the operational evidence in `composite_abstract_safe` (if used) talks about the abstract step relation; we want concrete safety here. Need to either (i) directly produce concrete safety for the relevant single-thread state, or (ii) lift abstract → concrete safety via the existing `safe_compose`.

* **Resource (`fork_post`)** parameter — the current Theorem 15 existentially picks `fork_post`. For the generalized version, the caller likely needs to supply or constrain `fork_post`, since the helper body's fork_post (trivial, helper is forkFree) might differ from the outer composite's fork_post.

### A.5 Complexity estimate (Route A)

* Operational procs-irrelevance lemma: ~50 LoC.
* Operational stack-extension for SafeTp: ~80 LoC (or skipped if we go the "don't use wp_call first" route).
* Generalized `completeness_general` statement + proof body (mostly bookkeeping reshuffle): ~100 LoC.
* Φ-parametric `weaken_post`: ~50 LoC.
* Application to `SimpleRangeProdComposition.lean` + helper feeds (the SafeTp witness, the Φ): ~80 LoC.

Total: **~360 LoC**, plus careful re-verification that `percomplete` still proves cleanly against the unchanged invariant.

**Risk concentration:** the operational procs-irrelevance (or its absence — if we route through abstract safety) and the stack-extension story.

---

## 4. Shared codebase notes

* **Where to put new code.** Route A's changes belong in `Agar/Iris/Completeness.lean` (extend Theorem 15) and possibly `Agar/Iris/Adequacy.lean`.

* **The walkthrough example.** `Agar/Examples/ExternalSolver.lean` is the test target — the consolidated Route A showcase.

* **The existing operational route (`Machine.safe_compose`)** has separate `sorry`s of its own (see §0). Route A should be expected to **not** touch those `sorry`s — they're an orthogonal effort. If Route A makes the operational route entirely unnecessary, note that in your work, but don't delete the operational scaffolding (we may still want it for non-Iris consumers).

* **PureHelper bridge** (`Agar/Iris/PureHelperBridge.lean`) is the natural source of the helper's Iris-side facts. Familiarize yourself with `Machine.safe_of_denoteHelper`, `PureHelper.wp_of_denote`, `denoteHelper_gauss` for the existing pattern.

* **Build hygiene.** Lake's incremental caching has bitten us before — after edits, force re-elaboration with:
  ```
  rm -f .lake/build/lib/lean/Agar/Iris/Completeness.*.hash \
        .lake/build/lib/lean/Agar/Iris/Completeness.trace
  lake build
  ```
  for whatever file you're editing. Trust the *clean* build, not the incremental one.

* **Fabricated lemma names are a real failure mode.** If you find yourself writing `List.xxx_of_yyy`, *probe Lean first* with a tiny test file or `exact?` — don't trust autocomplete or LLM-generated names. The previous attempt at the operational route shipped with `List.set_of_getElem?` (does not exist) and the build only flagged it on a clean rebuild.

* **The `frame.rv` typo** (Frame has field `retVar`, not `rv`) is something Lean silently elaborates to a metavariable in some contexts, especially inside `simp`'s machinery. Watch for it.

---

## 5. Suggested first steps

**First step:** state `completeness_general` with the chosen Φ-shape and **the same proof body as Theorem 15** modulo the t_init substitution. Get it to compile (with `sorry`s in the new bits). Then chase the bookkeeping until those `sorry`s close. Last, apply at the example.

The deliverable is a closed `rangeProd_composite_walkthrough` (or the equivalent — the theorem can be renamed) with the two `sorry`s replaced by the bridge application.

---

## 6. Outcomes and revised path forward (2026-05-25)

### 6.1 What was attempted

Route A (`completeness_general`):
- Added `completeness_general` to `Agar/Iris/Completeness.lean` (+79 LoC, fully closed). It's a `t_init`-parametric variant of Theorem 15: takes any `Thread`, a heap-freeness witness, and a per-σ `Machine.SafeTp prog ⟨σ, [t_init]⟩ φ` premise; produces an Iris `wp prog.procs fork_post ⊤ t_init (fun v => ⌜φ v⌝)`. Proof mirrors `completeness_modulo_lemma14` with `threadpool_init t_init` and `percomplete` applied at index 0.
- **Did not close the walkthrough directly.** The blocker (described below) was structural, not a matter of effort, and motivated the open-context variant.

### 6.2 The closed-world allocation blocker

Theorem 15 (and our generalized `completeness_general`) ends with

```
⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
    state_interp (GF := GF) Mem.empty ∗
    wp prog.procs fork_post ⊤ t_init Φ
```

The `∃ Hsi` is allocated **inside** the theorem's proof body, via `heap_init` (allocating a fresh heap-CMRA ghost) and `threadpool_init` (allocating a fresh threadpool ghost). This is appropriate for **closed-world adequacy**: the theorem is taking a "no Iris world yet" caller and bringing one into existence.

At the `.call rangeProd` site in the walkthrough, we are **already inside** an Iris wp proof. `adequacy_with_heap_intro_P` has *already* allocated a specific `StateInterp` / `AgarG` instance, and the wp goal uses that pre-existing instance. The freshly-allocated `Hsi` produced by `completeness_general` is a **different** ghost-state instance — it cannot unify with the in-scope one. Iris does not have an operation "merge two state_interps."

Closing the walkthrough therefore requires not just `completeness_general` but an **open-context** variant that:
1. Takes the **current** `AgarG` / `StateInterp` as a parameter, allocating none.
2. Allocates only the threadpool ghost + completeness invariant against the *existing* state_interp.
3. Returns just `wp prog.procs fork_post ⊤ t_init Φ`, framing through (or assuming) the existing heap fragment.

It is tractable (a refactor of the completeness bookkeeping in §A.4–A.5 of this doc, ~100–200 LoC additional).

### 6.3 Where this leaves us — the real story we want

The motivating use case (per the design conversation) is:

> Connect Iris-Lean and Std.Do, using mvcgen to solve denote-like results.

For that:
- Helpers should be allowed to **touch state** (read/write the heap, locally allocate, etc.) under appropriate framing.
- The helper-body specification should be a **Hoare triple over Std.Do**'s state monad: `{P heap env vs} body {Q heap env v}`, verified by mvcgen.
- The bridge should consume that Hoare triple, thread the caller's heap-fragment ownership through Iris's `state_interp`, and produce the callee-frame wp.

The pure-helper `denote`/`BodyTraj` story alone **cannot deliver this**. The reasons are structural:

| Limitation | Why it blocks |
|---|---|
| `body.heapFree` is a **structural assumption** of `BodyTraj.pure_steps_to_near_end` and its dependencies. | A heap-touching body has mem-changing intermediate steps; `pstep`'s "same-mem" trajectory no longer holds in a composite where other threads might have written. The body's trajectory is no longer self-contained. |
| `denote` is a pure function on `Env`. | A heap-touching body's "result" is state-indexed: `v_h` depends on the input heap, the output heap depends on the input heap. A pure `denote : Env → Option _ × Env` cannot express this. We'd need at minimum `denote : Env × Heap → Option _ × (Env × Heap)`, and we'd need separation-logic framing at the bridge boundary. |
| The Iris bridge sidesteps `state_interp` entirely. | At the call site, the caller owns some `state_interp σ` heap-fragment. A state-bearing bridge has to consume part of σ, hand it to the helper, get back the helper's output heap-effect, and return the updated `state_interp` to the caller. That's the standard Iris separation-logic dance — and it requires Iris machinery, which is *exactly* what Theorem 15 in its full state-aware form provides. |

**Theorem 15 generalizes to state.** Its statement is about arbitrary `prog` with arbitrary mem behavior; the `Machine.SafeTp` premise is state-aware; the resulting wp's underlying `state_interp` tracks the program's heap effects. The only thing wrong with Theorem 15 for our composition use case is the **closed-world allocator shape** (§6.2). Fix that and Theorem 15 becomes the universal bridge.

### 6.4 Revised path forward

The chain we want to build:

```
Std.Do specification of helper body
              │
              │  mvcgen / Std.Do verification
              ▼
Hoare triple about helper body's state-monad semantics
              │
              │  (small) adequacy bridge: Std.Do step ↔ Agar.Machine.Step
              │  on a single thread, modulo heap-fragment ownership
              ▼
Machine.SafeTp composite ⟨σ, [t_callee]⟩ Φ
              │
              │  open-context Theorem 15 variant
              ▼
wp composite.procs fork_post ⊤ t_callee Φ_outer
              │
              │  used inline at the .call site (no allocation)
              ▼
Walkthrough's call-site goal: discharged.
```

Each link's status:

1. **Std.Do specification + mvcgen verification of the helper body** — *exists outside this codebase*. The user mentions wanting to use mvcgen for "denote-like results." This is the entry point; no work on our side until the bridge below exists.

2. **Std.Do ↔ Agar.Machine adequacy on a single thread** — *new infrastructure, not yet written*. This is a purely operational lemma: given a Std.Do state-monadic computation `m : StateM Heap α` and a Hoare triple `{P} m {Q}` (in whatever shape mvcgen produces), and given a translation `embed_StdDo : (StateM Heap α) → Stmt` (or an existing such translation if any), then `Machine.SafeTp programOfStdDo ⟨σ, [t]⟩ φ` holds where σ satisfies P and φ characterizes the result via Q. Likely ~150–300 LoC depending on how Std.Do's semantics line up with Agar's `tstep`.

3. **Open-context Theorem 15** — **done** as of 2026-05-25. See `completeness_open` in `Agar/Iris/Completeness.lean` (immediately following `completeness_general`). The theorem takes `[AgarG GF F]` and `[InvGS_gen false GF]` as already-in-scope typeclasses, allocates only the (call-private) threadpool ghost γ and the `Icompl_pure` invariant, and returns `|={⊤}=> wp prog.procs True ⊤ t_init (fun v => ⌜φ v⌝)` — no `state_interp` output, no `∃ Hsi`. The fix turned out to be small (~60 LoC, mostly a copy of `completeness_general` with `heap_init` and the state_interp existential plumbing removed).

    *Caveat discovered during the implementation:* `completeness_open` produces a wp on `t_init` running **standalone** (the SafeTp premise is `∀ σ, SafeTp prog ⟨σ, [t_init]⟩ φ`, i.e., a singleton thread pool with empty stack). But the residual at a `wp_call` site has the helper running with a **non-empty stack** (the caller frame). So `completeness_open` alone does not close a call-site goal; it needs to be paired with a stack-frame embedding lemma.

    **Stack-embedding lemma — attempted 2026-05-26, deferred.** The natural shape is:
    ```
    wp procs fp ⊤ t (fun v => wp procs fp ⊤ (postDoReturnThread frame rest v) Φ)
      ⊢ wp procs fp ⊤ (stackExt t [frame, rest]) Φ
    ```
    where `stackExt t extra` appends `extra` to `t.stack`. The structure of the proof: Löb induction over thread states, with a *coupling invariant* "extended thread has stack `t.stack ++ [frame, rest]`, otherwise identical to standalone." The coupling is preserved by every `tstep` *except* `.ret e` with `t.stack = []`, where standalone terminates at `(.skip, [], _, [], some v)` while extended pops `frame` and continues at `postDoReturnThread frame rest v`. The Löb argument: at each step, either coupling is preserved (recurse via IH) or the divergence fires (extract `Φ_inner v` from the wp value rule applied to the terminated standalone state, which equals the wp at the extended post-state by definition of Φ_inner).

    *Why deferred:* the operational coupling lemma (one `tstep` on extended mirrored by one on standalone modulo the .ret divergence) requires a full case analysis on `Stmt` × `chosen` × stack/cont structure — ~13 stmt cases with sub-cases. Wrote a draft (`Agar/Operational/StackExt.lean`) but hit ~30 micro-errors in the case analysis (Lean's `nomatch`/`Option.noConfusion`/`split at` interactions) that aren't substantively hard but eat time. The file was removed pending a more careful re-attempt. The right path is probably Iris-level (use existing `wp_<stmt>` rules per case under a Löb hypothesis) rather than going through a standalone operational coupling lemma.

    **2026-05-26 follow-up: a subtle wrinkle with the implicit fall-through.** A second attempt revealed that the natural uniform Löb invariant "wp at t with Φ_v ⊢ wp at stackExt t (f::r) with Φ" is **not preserved across the full state space**. Specifically, it breaks on `t = (.skip, [], _, [], some v)` (standalone terminated post-`.ret`):
    - Standalone wp: at value disjunct, gives `Φ_v v = wp at postDoReturnThread(f,r,v)`.
    - Extended thread `(.skip, [], _, frame::rest, some v)`: stmt=.skip, cont=[], stack=f::_, so the tstep rule fires `[], _ :: _ => some (doReturn m t .unit)` — **passing `.unit`, not `t.result`**. So extended lands at `postDoReturnThread(f,r,.unit)`, while we need `postDoReturnThread(f,r,v)`. Mismatch.

    The operational explanation: `.ret e` with empty stack stores `result := some v` and lands at `(.skip,[],[],some v)`; the implicit fall-through rule (`.skip` with empty cont, non-empty stack) was written assuming `result = none` (fall-through means *no* explicit return), and unconditionally passes `.unit` to `doReturn`. So the standalone "trapped value" v is never observed by the extended-thread trajectory if we step through it; the divergence must be matched *at the `.ret e` step itself*, not after.

    **Implication for the proof structure:** the Löb induction can't be uniform on all `t`. The `.ret e` step needs special-cased handling: when `t.stmt = .ret e`, `t.stack = []`, and `Expr.eval t.env e = some v`, the standalone steps to `(.skip,[],[],some v)` (terminated, value disjunct gives `Φ_v v = wp at postDoReturn`), and the extended steps directly to `postDoReturnThread(f,r,v)`. These match without recursing through the IH. For all other steps the IH applies normally because they preserve `t.result = none` and stack-append. (Alternatively: tighten the invariant to require `t.result = none` and case-split `.ret e` at-step.)

    This wrinkle is small but real and explains why naive Löb attempts get stuck — there's no purely-mechanical case-split that works. Status remains deferred; the proof is structurally tractable but tedious, ~few hundred LoC.

    *Why this is the right next step:* with the stack-embedding in hand, the call-site pipeline becomes mechanical: an operational SafeTp witness for the helper (running standalone) → `completeness_open` → standalone wp → stack-embedding → callee-frame wp matching the `wp_call` residual. This delivers the pure-helper case and extends naturally to the state-bearing case.

4. **Open-context Theorem 15 used inline at the .call site** — *trivial once (3) lands*. The `wp_call → completeness_open + stack-embedding → wp_ret_top` chain is applied to a SafeTp witness obtained via link (2).

The pure-helper case is a degenerate instance: the helper has no state effects, so its Hoare triple is vacuous-on-state, and the heap-fragment ownership is `emp` — at which point link (1)+(2)+(3) collapse to "the `denote` equation."

### 6.5 What to keep, what to retire

**Keep:**
- `Agar/Examples/ExternalSolver.lean` — the consolidated Route A walkthrough.
- `Agar/Iris/Completeness.lean`'s `completeness_general` — closed-world variant, useful when one *is* starting closed-world. Not load-bearing for the inline-at-call-site story.
- `Agar/Iris/Completeness.lean`'s `completeness_open` (the open-context follow-up, added 2026-05-25) — the call-site-friendly variant. Load-bearing for the future state-bearing pipeline: it is the link between an operational SafeTp witness and an Iris wp without re-allocating the world.
- The `BodyTraj` namespace in `Agar/Operational/Composition.lean` (`denote_sound_stk`, `pstep_tstep_procs`, `pure_steps_to_near_end`, `pstep_near_end_pop`, `PureSteps_to_StepStarN`). Pure-fragment operational infrastructure; reusable for the degenerate-case branch of the general story.

**Retire (or de-emphasize):**
- The operational `Machine.safe_compose` work in `Agar/Operational/Composition.lean` (the `simulation_step` route). It has its own pre-existing `sorry`s (atomic_call/doReturn shape mismatch); given that the Iris path is the real story, finishing the operational route adds little. Acceptable to mark as legacy and not invest more in.

**To build:**
- The Std.Do ↔ Agar adequacy bridge (link 2 above). A new file, probably `Agar/StdDoBridge/...` or similar.
- A worked state-bearing example, paralleling the existing walkthrough but with a helper that touches the heap (e.g., an accumulator-into-a-loc helper). This is the proper test of the new story.

### 6.6 Open questions worth resolving before more code

1. **What is the precise shape of mvcgen's output?** Is it a Hoare triple (`triple m P Q` for some `triple` predicate), or a wp (`mvc.wp m Q P`)? The shape of link (2)'s premise depends on this.
2. **Does Std.Do have an existing operational semantics expressed as a step relation?** If yes, link (2) translates step ↔ step. If no, we have to define the embedding ourselves.
3. **How does Std.Do represent the heap?** A `Heap`-keyed `StateM`? An `IO`-style monad with `IORef`s? An abstract `MonadState`? The translation to Agar's `Mem` depends on this.
4. **Do we want the helper to be expressible in Agar's native `Stmt` (translated from Std.Do), or expressible directly in Std.Do with Std.Do's own semantics treated as the ground truth?** The former gives us a single operational model; the latter requires Iris-Lean to be parametric in the helper's semantics.
5. **What's the right shape of the helper-spec interface at the bridge?** For the pure case it was `(denote ρ = (some (), ρ_f), Expr.eval ρ_f e = some v)`. For the state-bearing case it's some triple/wp. We need a clean abstraction so the bridge doesn't have to know about Std.Do internals — analogous to how the current bridge consumes "any denote equation."

Resolving these informs whether the Std.Do bridge is a small lift or a larger interpretive project.

### 6.7 Update (2026-05-26): walkthrough closed

The walkthrough (`rangeProd_composite_walkthrough_RouteA` in
`Agar/Examples/ExternalSolver.lean`) is now closed.
There was no fork-post mismatch with the adequacy entry-point: the
`adequacy_with_heap_intro_P` macro does *not* pin `fork_post := emp` —
it leaves an existential that the proof picks. Closing the walkthrough
just required inlining the macro's body and choosing
`fork_post := iprop(True : IProp GF)` throughout (at the `wp_safe_bupd`
existential pick, at each `wp_fork` site, and at each `wp_call` site),
so the value matches the `True` that `completeness_open` (and hence
`wp_callee_routeA`) threads through the residual. The standalone-SafeTp
obligation (`helper_safeTp`) is discharged via
`SafeTp_procs_irrel_of_strict` applied to `helperProg_safe`, so the
only remaining sorrys in the RangeProd stack are the pre-existing
carve-outs in `SimpleRangeProdHelperSafe.lean` and
`SimpleRangeProdComposition.lean`.

### 6.8 Update (2026-05-26): `rangeProd_spec` closed via direct induction

The Std.Do "pretty endpoint" Hoare triple `rangeProd_spec` in
`Agar/Examples/SimpleRangeProdHelperSafe.lean` is now closed without
mvcgen. `denote (prodProg n)` is a plain pure `Env → Option Unit × Env`
function — it does not live in do-notation, so mvcgen has no structural
do/forIn machinery to engage with; even the `forN` is a custom
`iter`-based recursor, not Std.Do's `forIn`. The Triple unfolds
definitionally for `StateM`: after `intro ρ hpre`, the goal reduces
(via `WP.wp` for `StateT` + `PostCond.noThrow`) to a pair of
conjuncts about `(denote (prodProg n) ρ).fst` and `(denote …).snd "acc"`.
Closing it is then a direct induction over the inner `forN`, with
the invariant *"after k iterations starting from `acc = A, i = I`,
we end with `acc = A · rangeProdValue I k` and `i = I + k`"*. The
generalised helper `forN_prodBody_spec` (private to the file) handles
the loop; `rangeProd_spec` instantiates it at `A = 1, I = a`. Roughly
100 lines added. The broader Std.Do ↔ Agar adequacy bridge question
of §6.4/§6.5 is unaffected by this — it remains future work; this
update simply removes the in-file `sorry` so downstream consumers of
`helperProg_safe` no longer rely on an unproven triple.

### 6.9 Update (2026-05-26): Std.Do shape investigated — answers to §6.6 Q1–Q4

Direct read of `Std.Do` source (Lean 4.29.0 toolchain) clarifies the
shape of the bridge work in §6.4/§6.5.

**Q1 (mvcgen output shape).** `Std.Do.Triple x P Q` is *definitionally*
`P ⊢ₛ wp⟦x⟧ Q` (`Std/Do/Triple/Basic.lean:37`). `mvcgen` produces a
sub-proof of that entailment; the result the bridge consumes is a
Hoare-triple-wrapped wp at the user's monad's predicate transformer.
The premise the bridge will accept is a `Triple x P Q` value (or
equivalently, an `P ⊢ₛ wp⟦x⟧ Q`).

**Q2 (Std.Do operational semantics).** **There isn't one.** Std.Do
exposes a `WP` typeclass that interprets a monadic program `x : m α` as
a predicate transformer `PredTrans ps α`, parameterised by the monad's
`PostShape ps`. There is no step relation, no small-step semantics, and
no "thread" abstraction. **This means the bridge cannot be step↔step.**
It must be: "Std.Do `Triple x P Q` → Agar `Machine.SafeTp` of an
embedded translation of `x`." The translation is operational on Agar's
side; Std.Do contributes only the wp-flavoured spec.

**Q3 (heap representation).** Std.Do is monad-agnostic. It has `WPMonad`
instances for `Id`, `StateT σ m` (and hence `StateM σ`), `ReaderT`,
`ExceptT`, `OptionT`, `EStateM`, `Except`, `Option`. The "heap" is
whatever the user picks for `σ` in `StateM σ` (or for the appropriate
shape in their preferred monad). For matching Agar, the natural choice
is `StateM Mem` (or `StateM (Mem × Env)` if the helper-spec wants Env
too). No `IORef` / `IO` runtime entanglement.

**Q4 (translate to Agar `Stmt` vs. trust Std.Do directly).** Both are
viable, with different trade-offs:

* *Translate to `Stmt`*: the bridge becomes "if `denote_state s ρ σ`
  agrees with `x.run σ`, then a Std.Do triple for `x` lifts to a SafeTp
  witness for the embedded `Stmt` form of `s`." Requires defining a
  state-aware `denote_state : PureStmt → Env → Mem → Option α × Env ×
  Mem` (generalisation of the current pure `denote`) and an embedding
  `stateEmbed : StateStmt → Stmt` analogous to today's `embed`. Single
  operational model on Agar's side; clean.

* *Trust Std.Do directly*: keep the helper expressed as `m : StateM Mem
  α` (or whichever monad) and prove SafeTp of an abstract
  "interpretation" operation against Std.Do's wp. Requires extending
  Agar's `tstep` to recognise an "opaque atomic Std.Do block" as a
  primitive — i.e., a new `Stmt.std_do` constructor or a per-thread
  side-channel. More invasive; relaxes the "single operational model"
  property.

The first option is closer in spirit to the current `denote`/`embed`
chain and reuses the strict-helper procs-irrelevance lift. Recommended
default.

**Q5 (helper-spec interface at the bridge).** With the above settled,
the bridge premise becomes:

```
∀ ρ σ, P ρ σ →
  ∃ ρ' σ' v_h,
    denote_state pureBody ρ σ = (some (), ρ', σ') ∧
    Expr.eval ρ' retExpr = some v_h ∧
    Q v_h ρ' σ'
```

i.e., the pure-case's pair `(denote_eq, ret_eq)` plus a heap component.
Derived from `Triple pureBody P Q` by unfolding the `StateM`'s `WP`
instance (analogous to today's `Triple.iff_conseq` reduction).

**Implication for the next coding milestone.** Two concrete pieces:

1. **`denote_state`**: a state-aware variant of `Agar.Lang.Denotational.denote`,
   operating on `Env × Mem`. Define for the same `PureStmt`
   constructors, with `assign/load/store/free/cas/alloc` actually
   touching the heap component. `forN/while_/repeat` unchanged
   structurally. Adequacy: prove `denote_state s ρ σ = (some (), ρ', σ')`
   implies `PureSteps_with_heap ⟨embed s, [], ρ, …⟩ ⟨.skip, [], ρ', …⟩`
   at the operational level (state-aware analogue of `denote_sound`).

2. **State-bearing callee bridge** (`wp_callee_of_state_helper`):
   mirrors the pure-helper Route A chain with a state component in the
   premise and a `state_interp` framing through the heap fragment. This
   is the real Iris work; the operational lemmas in (1) are the
   supporting chain.

Both can wait on a concrete state-bearing example to motivate them
(e.g., an accumulator-into-a-loc helper). For now, this update
documents that the bridge shape is settled at the level of design.

### 6.10 Update (2026-05-26): state-bearing example sketch

To motivate the `denote_state` / `wp_callee_of_state_helper` design,
sketch a minimal heap-touching helper. Goal: small enough to fit in
one example file, large enough to exercise *all* the new bridge
machinery without redundancy.

**Candidate: `accInto`**

```
proc accInto(loc : Loc, n : Nat) :
  let total : Loc = alloc 0
  i := 1
  while i ≤ n:
    cur := load total
    store total (cur + i)
    i := i + 1
  result := load total
  free total
  store loc result
  return ()
```

Spec (Std.Do triple over `StateM Mem`):

```
⦃fun σ => ⌜σ.fn loc = some (.int _)⌝⦄
  accInto_body loc n
⦃⇓ _ => fun σ' => ⌜σ'.fn loc = some (.int (n·(n+1)/2)) ∧ σ'.dom = σ.dom⌝⦄
```

Why this shape:
* **Local allocation + free** (`total`): tests that intermediate heap
  resources can be created and disposed of inside the helper without
  leaking back into the caller's frame.
* **Read + write loop** (`load`/`store` in the body): tests the
  `denote_state`'s heap component on the most common operations.
* **Write to the caller's location** (`store loc result`): tests the
  ownership-transfer interface — the helper must consume a points-to
  fragment for `loc` and return it updated. This is what no pure helper
  exercises, and what `state_interp` framing has to handle.
* **No `cas`**: deliberate. `cas` adds atomicity machinery; once the
  basic story works, a follow-up example can layer it in.
* **`while_` with bounded fuel** rather than `forN`: matches `accInto`'s
  natural form, plus exercises that the state-aware bridge handles
  the same `while_` fuel discipline as the pure case.

The composite for this example mirrors `rangeProdComposite3`:

```
proc accIntoCaller(): { l := alloc 0; accInto(l, 5); return load l }
fork accIntoCaller; { l := alloc 0; accInto(l, 7); return load l }
```

Two concurrent calls into the helper, each on its own freshly-
allocated location. No interference; tests that the bridge composes
cleanly with multi-threading even though the helper itself touches
only its own arguments.

**Implication for `denote_state`'s signature**

```
abbrev StateDenot := StateM (Env × Mem) (Option Unit)

def denote_state : StateStmt → StateDenot
```

where `StateStmt` extends `PureStmt` with `.load / .store / .free /
.cas / .alloc` constructors (mirroring `Stmt`'s heap fragment minus
`.call / .fork / .ret`). For `.alloc`, the location is supplied
externally — either via an oracle parameter `(fresh : Nat → Loc)` or
by carrying it in a reader component. The simplest is to thread a
fresh-name supply through the denotation:

```
abbrev StateDenot := StateM (Env × Mem × FreshSupply) (Option Unit)
```

where `FreshSupply := Nat` and `.alloc` consumes `n` and returns
`Loc.mk n` (or similar). The operational `.alloc` step then has to
match the same fresh-name choice — this is where the bridge's
existential-allocation story has to be threaded carefully.

**Implication for `wp_callee_of_state_helper`**

Premise needs *two* extra hypotheses beyond the pure bridge:
1. `state_interp σ` consumption: the caller's heap fragment for the
   argument locations must be threaded through. Concretely, the
   bridge consumes `σ` and returns `σ'` via `state_interp σ` →
   `state_interp σ'`.
2. A Hoare-triple-style premise:
   `Triple body P Q` where `P, Q : SPred (.arg (Env × Mem) .pure)`.

The premise's `Q` predicate fires Φ at the post-state. The bridge
discharges the operational SafeTp (now state-aware) via the same
`SafeTp_procs_irrel_of_strict`-style lift, *modulo* the procs-irrel
lift being generalised from `StrictHelperShape` to a state-aware
variant that allows `.load / .store / etc.` It will likely call for a
new predicate `StateHelperShape ⊃ StrictHelperShape` covering the
heap-touching fragment.

**Implementation order (suggested)**

1. Define `StateStmt`, `denote_state`, prove `denote_state_sound`
   (operational adequacy) — parallels `Agar/Lang/Denotational.lean`.
2. Define `StateHelperShape` / `StateHelperThread`; prove procs-
   irrelevance for it. This is mechanical (mirrors `StrictHelper.lean`,
   adds heap-touching cases that are procs-independent anyway).
3. Prove `accInto_body_safe` operationally (Agar `Machine.SafeTp`),
   parametrised by an allocation oracle.
4. Define `wp_callee_of_state_helper`; prove via the `wp_stack_push`
   chain (which is heap-agnostic — state_interp threads through).
5. Write the walkthrough as a sibling of
   `Agar/Examples/ExternalSolver.lean`.
6. Optionally: write the Std.Do triple `accInto_spec` with mvcgen;
   discharge `accInto_body_safe` via the same `Triple.iff` unfolding
   pattern used for `rangeProd_spec`.

Estimated total scope: ~800–1200 LoC (`denote_state` + state-aware
procs-irrel + bridge + example). Most of it is mechanical mirror of
the pure-helper chain; the genuinely new work is the
`state_interp`/points-to threading in `wp_callee_of_state_helper`.

The pure-helper chain stands as the spine; state-bearing extends it
along one axis (the heap component) without altering the other.

### 6.11 Update (2026-05-26): `denote_state` + `embed_state` landed

First concrete step from §8.11's implementation order. New file
`Agar/Lang/DenotationalState.lean` (~165 LoC, no `sorry`s):

* **`StateStmt`** — heap-touching extension of `PureStmt`: adds
  `.load / .store / .free / .cas / .alloc` constructors (mirroring
  `Stmt`'s heap fragment minus `.call / .fork / .ret`).
* **`StatePack`** — bundle of `(env, mem, fresh : Nat)` threaded
  through `denote_state`. The `fresh` counter is a deterministic
  allocation supply; the bridge will pin operational `chosen : Loc`
  to it.
* **`denote_state : StateStmt → StateM StatePack (Option Unit)`** —
  total denotation. Heap operations read/update `p.mem` via
  `Mem.load / store / free / alloc`. `.alloc` bumps `p.fresh`.
* **`iter_st / iterWhile_st`** — state-bearing analogues of
  `iter / iterWhile`.
* **`embed_state : StateStmt → Stmt`** — operational embedding,
  mirroring `embed` and forwarding heap constructors directly to
  `Stmt`'s heap fragment.
* Simp lemmas for `skip / assign / forN_zero / forN_succ /
  while_zero / while_succ`.

Open follow-ups (next ticks):
1. **`denote_state_sound`**: operational adequacy — convergent
   `denote_state s p = (some (), p')` implies a `PureSteps_with_heap`
   chain from `⟨embed_state s, [], p.env, [], none⟩` at memory
   `p.mem` to `⟨.skip, [], p'.env, [], none⟩` at memory `p'.mem`,
   with the `chosen : Loc` arguments along the chain matching the
   `p.fresh`-supplied sequence. This is the state-aware analogue of
   `Agar.denote_sound`.
2. **`StateHelperShape`** + procs-irrelevance for the heap-touching
   fragment. The case analysis on `tstep` is procs-independent on all
   the heap operations (procs is only touched by `.call / .fork`), so
   this should be a near-mechanical mirror of `StrictHelper.lean`.
3. **`accInto`** definition + `wp_callee_of_state_helper`.

This update covers the data-layer plumbing; the proof obligations
above are the next concrete subgoals.

### 6.12 Recipe: how to use Route A for a new pure helper

The pipeline factors cleanly enough that adapting it to a fresh
helper is a matter of plugging in a new spec at the top and threading
the same chain through. The six concrete steps:

1. **Write your helper as a `Proc`** whose body has the canonical shape
   `.seq (embed pureBody) (.ret retExpr)`, with `pureBody : PureStmt`
   built from the heap-free fragment (no `.load / .store / .cas / .alloc /
   .free`) and `pureBody.whileFree` (no `.while_` — use `.forN` or
   `.repeat` for bounded iteration). Models: `rangeProd` in
   `Agar/Examples/ExternalSolver.lean`.

2. **State the `Std.Do.Triple`** for `denote pureBody` over `StateM Env`.
   The `wp` instance for plain `StateM` reduces the `Triple` definitionally
   to a pointwise `denote`-convergence + post statement (no `Triple.iff`
   API needed; `intro ρ hpre; refine ⟨?_, ?_⟩` lands directly on the
   reduction). Model: `rangeProd_spec` in `SimpleRangeProdHelperSafe.lean`.
   For a loop you'll typically need a generalized invariant lemma proved
   by induction on the iteration count (see `forN_prodBody_spec`).

3. **Derive `helper_init_reaches_terminal`** — a `PureSteps` chain from
   the parameter-bound init thread to `helperTerminal ρ_f v`. The
   chain is built from one `.seq` pop, the `denote_sound` chain on
   the body, one `.skip`-pop, and one `.ret`-with-empty-stack. Model:
   `helper_init_reaches_terminal` in `SimpleRangeProdHelperSafe.lean`.
   Generic: ~20 lines.

4. **Prove `helperProg_safe`** by walking the `Machine.StepStarN`
   trajectory through `machineStepStarN_helper` (singleton-pool
   `HelperThread` folding) and `PureSteps.stuck_unique` at the
   terminal. Model: `helperProg_safe`. Generic: ~30 lines.

5. **Lift to `helper_safeTp` under the composite** with one application
   of `SafeTp_procs_irrel_of_strict` to a `helper_init_strictHelperThread`
   witness. Two lines. The strict-helper witness itself is `~6` lines
   (constructor application using `embed_strictHelperShape` +
   `prodProg.whileFree`).

6. **Write the walkthrough** — `wp_safe_bupd` opener, pick
   `fork_post := iprop(True : IProp GF)`, peel the composite's main
   with `wp_seq`/`wp_fork`/`wp_call`, and at each `.call yourhelper`
   site fire the three-line bridge:
   ```
   iapply fupd_wp
   refine .trans ?_ (wp_callee_yourHelper …)
   iintro _; iintro %v Hpv; icases Hpv with %hv; subst hv
   iintro _; iapply wp_ret_top _ _ _ <closedForm> _ _ _ rfl
   ipure_intro; trivial
   ```
   where `wp_callee_yourHelper` is a fresh specialization of
   `wp_callee_routeA`'s shape (essentially: substitute your helper's
   spec into the bridge's premise wand). Model: lines 209–238 of
   `Agar/Examples/ExternalSolver.lean`.

The Iris infrastructure pieces (`completeness_open`, `wp_stack_push`,
`SafeTp_procs_irrel_of_strict`) are **fully reusable** — they're
parametric in the program, thread, and predicate. The only per-helper
work is steps 1–3 (the spec) and step 6 (the walkthrough's call-site
boilerplate).

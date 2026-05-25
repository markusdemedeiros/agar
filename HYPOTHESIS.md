# Two routes for the callee-frame wp gap

> **2026-05-25 update.** Both routes were attempted (see §8 at the end of
> this document). Route B landed — a no-state bridge lemma
> (`Agar/Iris/CalleeBridge.lean`) closes the walkthrough example. Route
> A produced reusable infrastructure (`completeness_general`) but did
> *not* close the example, surfacing a deeper "closed-world" structural
> issue. The current bridge is a useful sanity check on the
> structural-denotational shape but **does not generalize to state-
> bearing helpers** — which is what we actually need. See §8 for the
> diagnosis and the revised path forward (open-context Theorem 15 +
> Std.Do/mvcgen bridge to operational safety). The original §1–§7
> below is preserved as a historical record of the framing.

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

## 2. Acceptance criterion (both routes)

A successful resolution should:

1. Compile `Agar/Examples/SimpleRangeProdComposition.lean` with the two `.call rangeProd` `sorry`s **closed**.
2. Not introduce new `sorry`s in `Agar/Iris/Completeness.lean`, `Agar/Iris/Rules.lean`, or `Agar/Iris/Adequacy.lean` (modulo lemmas whose proofs are *new infrastructure* per the chosen route — but those lemmas must themselves be closed).
3. Cleanly express the bridge as a reusable lemma — not just inline tactics that happen to discharge the two specific goals.

The two routes below are alternative ways to provide that bridge.

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

## 4. Route B — Separate bridge lemma

**Idea.** Treat Theorem 15 as a black box. Prove a fresh "callee-frame" wp lemma whose conclusion is exactly what `wp_call` leaves us with, and whose premise is the helper's *standalone* Iris wp (from Theorem 15) plus a continuation.

### B.1 Target statement

```lean
theorem wp_callee_of_pure_helper
    {GF : BundledGFunctors.{0,0,0}} [InvGS_gen false GF] [StateInterp GF]
    (composite : Program) (h : Proc)
    (pureBody : PureStmt) (retExpr : Expr)
    (h_body_eq : h.body = .seq (embed pureBody) (.ret retExpr))
    (vs : List Val) (x : Name) (cont : List Stmt) (env : Env) (stack : List Frame)
    (fp : IProp GF) (Φ : Val → IProp GF)
    -- The helper's denotational fact pins down the return value.
    (ρ_f : Env) (v_h : Val)
    (h_denote : denote pureBody (bindParams h.params vs) = (some (), ρ_f))
    (h_ret : Expr.eval ρ_f retExpr = some v_h)
    -- The caller's continuation: from the post-doReturn state, the
    -- caller's wp closes under Φ.
    (h_cont :
       wp composite.procs fp ⊤
         (postDoReturnThread x cont env stack v_h) Φ) :
    -- Conclusion: the wp at the body-start (after wp_call) closes under Φ.
    wp composite.procs fp ⊤
      ⟨h.body, [], bindParams h.params vs, ⟨x, cont, env⟩ :: stack, none⟩ Φ
```

where

```lean
def postDoReturnThread (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) (v_h : Val) : Thread :=
  match cont with
  | []      => ⟨.skip, [], env.set x v_h, stack, none⟩
  | s :: cs => ⟨s,     cs, env.set x v_h, stack, none⟩
```

i.e., the actual doReturn-shape of the thread after popping the helper's frame.

### B.2 Two implementation sub-routes

**(B1) Manual stepping.** Prove the bridge by inducting / walking through the helper body's pstep trajectory using Iris wp tactics directly. Lean on the existing `BodyTraj` infrastructure:

* `denote_sound_stk` gives us a `PureSteps` chain from body-start to near-end thread (modulo fixing `pstep_near_end_pop`'s shape per §0).
* For each pstep in that chain, a wp-level "pure step" rule (`wp_pure_step` or its constituents) advances the wp.
* The trajectory's terminal step (`.ret retExpr` with non-empty stack) fires `doReturn` and lands at `postDoReturnThread x cont env stack v_h`. This wp step requires a custom rule — call it `wp_ret_pop_to_thread` — that knows the post-pop shape and hands off to `h_cont`.

The hard work: prove the wp-level analogue of `pure_steps_to_near_end`, namely

```lean
theorem wp_pure_chain_body
    (procs : Name → Option Proc) (fp : IProp GF) (Φ : Val → IProp GF)
    (pureBody : PureStmt) (retExpr : Expr)
    (ρ ρ_f : Env)
    (frame : Frame) (rest : List Frame)
    (h_denote : denote pureBody ρ = (some (), ρ_f))
    (h_next : wp procs fp ⊤
                ⟨.ret retExpr, [], ρ_f, frame :: rest, none⟩ Φ) :
    wp procs fp ⊤
      ⟨.seq (embed pureBody) (.ret retExpr), [], ρ, frame :: rest, none⟩ Φ
```

with proof by induction on `pureBody`, paralleling `denote_sound`. Then chain with `wp_ret_pop_to_thread` to discharge the wp at `.ret retExpr` by handing off to `h_cont`.

**(B2) Transport from Theorem 15.** Take the helper-as-program's Iris wp (from `PureHelper.wp_of_denote` / Theorem 15) and transport it to the callee setting by:

1. **Procs-irrelevance for wp**: prove that a wp over `noProcs` lifts to a wp over `composite.procs` when the body is `noCall ∧ forkFree`. Iris-level analogue of operational `pstep_tstep_procs`.
2. **Initial-env retargeting**: the helper-as-program starts at `Env.empty` and runs `assignAllParams h.params vs` before reaching the body. Bypass this by proving a "after the assigns, the wp at body with bindParams env follows from the wp at main with Env.empty."
3. **Stack-extension for wp**: prove that a wp at `⟨body, cont, env, [], none⟩ Φ` (where Φ fires at `.ret`-termination) yields a wp at `⟨body, cont, env, frame :: rest, none⟩ Φ'` (where Φ' fires after doReturn-and-continuation), provided the body never touches the stack until its final `.ret`. Lean on `body.noCall ∧ body.forkFree` for stack-equivariance of intermediate tsteps.

(B2) is more modular but each sub-lemma is substantial. (B1) is more direct — fewer intermediate lemmas — but inlines the body-stepping with the wp continuation, so the proof is monolithic.

### B.3 Required sub-lemmas (shared)

Regardless of B1 vs B2:

* **Fix `BodyTraj.pstep_near_end_pop`** with the correct case-split RHS:
  ```lean
  pstep ⟨.ret retExpr, [], ρ', frame :: rest, none⟩ =
    some (postDoReturnThread frame.retVar frame.cont frame.env rest v_h)
  ```
* **Operational procs-irrelevance for tstep success** is already in place (`BodyTraj.pstep_tstep_procs`). Need an Iris-level uplift.
* **A wp rule for "skip with empty cont and non-empty stack"** (the doReturn step). May already exist as `wp_skip_frame_cons` / `wp_skip_frame_nil` (see `Agar/Iris/Rules.lean`); verify and reuse.
* **A wp rule for ".ret with non-empty stack"** (the doReturn after a value). Likely `wp_ret_pop_cons` / `wp_ret_pop_nil` already exist; verify they produce the right post-frame shape.

### B.4 Application to the example

In `SimpleRangeProdComposition.lean`, at each of the two `.call rangeProd` goals:

```lean
-- Forked-thread goal (sketch):
iapply wp_call _ _ _ _ _ _ _ _ _ _ _ rfl (by agar_eval) rfl
iintro !>
-- Goal: wp ... ⟨rangeProd.body, [], bindParams ["a"] [Val.int 5], ⟨"r", [.ret (.var "r")], env_at_fork⟩ :: [], none⟩ Φ_fork
apply wp_callee_of_pure_helper
  (composite := rangeProdComposite3) (h := rangeProd 3)
  (pureBody := prodProg 3) (retExpr := .var "acc")
  (h_body_eq := rfl)
  (vs := [Val.int 5])
  (h_denote := denote_prodProg_at 5 3)  -- new helper lemma
  (h_ret := by simp [...])
-- Remaining sub-goal: wp ... (postDoReturnThread "r" [.ret (.var "r")] env_at_fork [] (Val.int (rangeProdValue 5 3))) Φ_fork
-- which is: wp ... ⟨.ret (.var "r"), [], env_at_fork.set "r" (Val.int (rangeProdValue 5 3)), [], none⟩ Φ_fork
-- discharge by wp_ret_top + ipure_intro + arithmetic.
```

The shape of the residual sub-goal **after** `wp_callee_of_pure_helper` is exactly the caller's continuation — `.ret (.var "r")` for the forked thread, `.ret (.var "x")` for the main thread. Both terminate the respective threads with the helper's return value.

### B.5 Subtleties / pitfalls (Route B)

* **`pstep_near_end_pop`'s shape** must be fixed first. The case-split RHS cascades through `pure_steps_to_near_end` (which currently composes pstep_near_end_pop at its tail) and through any wp-level analogue. Get this right early.

* **`wp_ret_pop_*` rules' exact shape.** Check the existing rules in `Agar/Iris/Rules.lean` — they may already do the `match frame.cont` case-split, in which case (B1) chains naturally; if not, we'll need to prove the matching shape ourselves.

* **Φ as an arbitrary iprop.** The bridge needs to be parametric in Φ — no fixing Φ to `⌜φ v⌝`. That's the whole point of being a bridge from a closed wp to an open callee wp.

* **Procs-irrelevance for wp (Route B2)** is a real lemma. It says: if `wp noProcs fp ⊤ t Φ` and `t.stmt`, all queued conts, and the body's reachable-tstep stmts are `noCall ∧ forkFree`, then `wp composite.procs fp ⊤ t Φ`. Provable via Löb induction over the wp; about 80 LoC. The Iris analogue of the operational `pstep_tstep_procs`.

* **Iris instance / typeclass plumbing.** `wp` is parametric in `GF`, `F`, `InvGS_gen`, `AgarG`, `TpGpreS`, etc. The bridge lemma needs the same instance constraints as Theorem 15. The example file already brings these in via `adequacy_with_heap_intro`'s setup.

### B.6 Complexity estimate (Route B)

* Fixing `pstep_near_end_pop` + downstream `pure_steps_to_near_end`: ~30 LoC.
* `wp_pure_chain_body` (B1) — induction on `PureStmt`, paralleling `denote_sound`: ~150 LoC.
* OR `procs_irrelevance_wp` + `wp_assignParams_chain` + `wp_stack_extend` (B2): ~250 LoC across three lemmas.
* The bridge lemma `wp_callee_of_pure_helper` itself: ~80 LoC (B1) or ~30 LoC (B2 — just composition).
* Helper denote-equation lemmas for the example (`denote_prodProg_at`-style): ~80 LoC.
* Plugging in at the example's two call sites: ~40 LoC.

Total: **~380 LoC for B1** or **~480 LoC for B2**.

**Risk concentration:** for B1, the `wp_pure_chain_body` induction on `PureStmt` (similar in spirit to `denote_sound_stk` but at the wp level — needs to interact with all the wp_seq / wp_assign / wp_ite / wp_while rules correctly). For B2, the three sub-lemmas each have their own gotchas; the procs-irrelevance is the most likely to surprise.

---

## 5. Picking between A and B (notes for both agents)

Neither route is dominant. Both are non-trivial. Differences:

| Aspect | Route A | Route B |
|---|---|---|
| **Touches load-bearing infrastructure** | Yes (Theorem 15, possibly percomplete invariant) | No (Theorem 15 untouched; new lemmas additive) |
| **Composability with future helpers** | High — one generalized Theorem 15 can absorb many shapes | High — one bridge lemma serves any callee-frame wp |
| **Risk of breaking existing examples** | Higher — existing Theorem 15 consumers may need adaptation | Low — additive lemma |
| **Conceptual elegance** | Cleaner: one theorem does it all | Cleaner: separation of concerns (Theorem 15 stays minimal) |
| **Effort estimate** | ~360 LoC | ~380–480 LoC |
| **Surprise potential** | Operational procs-irrelevance + stack-extension surprises | Iris procs-irrelevance for wp surprise (B2); long induction (B1) |
| **Reusability** | Theorem 15 itself becomes more useful | Bridge lemma is a useful new tool but specialized |

If forced to bet: **Route B** is slightly more likely to land cleanly because it isolates changes; **Route A** is slightly more satisfying philosophically because it makes Theorem 15 the right shape for the job. We are not forced to choose — we are running both in parallel.

---

## 6. Shared codebase notes (for both agents)

* **Where to put new code.** Route A's changes belong in `Agar/Iris/Completeness.lean` (extend Theorem 15) and possibly `Agar/Iris/Adequacy.lean`. Route B's new bridge lemma belongs in a new file `Agar/Iris/CalleeBridge.lean` (or similar), imported by `Agar/Examples/SimpleRangeProdComposition.lean`.

* **The walkthrough example.** `Agar/Examples/SimpleRangeProdComposition.lean` is the test target. It currently builds with two `sorry`s at the `.call rangeProd` sites (lines 184 and 189 of the file as of this writing). After the work, replace those `sorry`s with applications of the route's bridge.

* **The existing operational route (`Machine.safe_compose`)** has separate `sorry`s of its own (see §0). Both Route A and Route B should be expected to **not** touch those `sorry`s — they're an orthogonal effort. If your route makes the operational route entirely unnecessary, note that in your work, but don't delete the operational scaffolding (we may still want it for non-Iris consumers).

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

## 7. Suggested first steps (per route)

**Route A's first step:** state `completeness_general` with the chosen Φ-shape and **the same proof body as Theorem 15** modulo the t_init substitution. Get it to compile (with `sorry`s in the new bits). Then chase the bookkeeping until those `sorry`s close. Last, apply at the example.

**Route B's first step:** fix `BodyTraj.pstep_near_end_pop`'s statement and proof with the case-split RHS, restore `BodyTraj.pure_steps_to_near_end`. Then state `wp_callee_of_pure_helper` with `sorry`. Apply at the example to confirm the shape lines up. Then go back and prove the bridge.

Both routes should produce, as a deliverable, a closed `rangeProd_composite_walkthrough` (or the equivalent — the theorem can be renamed) with the two `sorry`s replaced by the bridge application.

---

## 8. Outcomes and revised path forward (2026-05-25)

### 8.1 What was attempted

Two agents ran in parallel git worktrees, one per route.

**Route A** (`completeness_general`):
- Added `completeness_general` to `Agar/Iris/Completeness.lean` (+79 LoC, fully closed). It's a `t_init`-parametric variant of Theorem 15: takes any `Thread`, a heap-freeness witness, and a per-σ `Machine.SafeTp prog ⟨σ, [t_init]⟩ φ` premise; produces an Iris `wp prog.procs fork_post ⊤ t_init (fun v => ⌜φ v⌝)`. Proof mirrors `completeness_modulo_lemma14` with `threadpool_init t_init` and `percomplete` applied at index 0.
- **Did not close the walkthrough.** The blocker (described below) was structural, not a matter of effort.

**Route B** (`wp_callee_of_pure_helper`):
- Added `Agar/Iris/CalleeBridge.lean` (185 LoC, fully closed). The bridge composes `BodyTraj.pure_steps_to_near_end` + `BodyTraj.pstep_near_end_pop` + a wp-level lift of single pstep success (`wp_of_pstep`, `wp_of_pure_steps`). No invocation of Theorem 15 at any layer.
- Fixed the pre-existing bugs in `Agar/Operational/Composition.lean`: `pstep_near_end_pop`'s doReturn-shape mismatch (now a case-split RHS via `postDoReturnThread`); `PureSteps_to_StepStarN` (the fabricated `List.set_of_getElem?` is gone).
- **Closed the walkthrough.** `Agar/Examples/SimpleRangeProdComposition.lean`'s `rangeProd_composite_walkthrough` discharges both `.call rangeProd` sites via `wp_call → wp_callee_of_pure_helper → wp_ret_top`. Clean rebuild verified.

### 8.2 The Route A blocker: closed-world allocation

Theorem 15 (and our generalized `completeness_general`) ends with

```
⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
    state_interp (GF := GF) Mem.empty ∗
    wp prog.procs fork_post ⊤ t_init Φ
```

The `∃ Hsi` is allocated **inside** the theorem's proof body, via `heap_init` (allocating a fresh heap-CMRA ghost) and `threadpool_init` (allocating a fresh threadpool ghost). This is appropriate for **closed-world adequacy**: the theorem is taking a "no Iris world yet" caller and bringing one into existence.

At the `.call rangeProd` site in the walkthrough, we are **already inside** an Iris wp proof. `adequacy_with_heap_intro_P` has *already* allocated a specific `StateInterp` / `AgarG` instance, and the wp goal uses that pre-existing instance. The freshly-allocated `Hsi` produced by `completeness_general` is a **different** ghost-state instance — it cannot unify with the in-scope one. Iris does not have an operation "merge two state_interps."

Closing the walkthrough via Route A therefore requires not just `completeness_general` but an **open-context** variant that:
1. Takes the **current** `AgarG` / `StateInterp` as a parameter, allocating none.
2. Allocates only the threadpool ghost + completeness invariant against the *existing* state_interp.
3. Returns just `wp prog.procs fork_post ⊤ t_init Φ`, framing through (or assuming) the existing heap fragment.

The Route A agent identified this and stopped. It is tractable (a refactor of the completeness bookkeeping in §A.4–A.5 of this doc, ~100–200 LoC additional) but was not undertaken in the run.

### 8.3 What Route B's success actually means — and doesn't

Route B closed the walkthrough cleanly and quickly. **But this is a degenerate case.** The bridge works because:

1. **`rangeProd.body` is heap-free, fork-free, call-free.** This is what makes the operational `BodyTraj` machinery applicable: pstep on the body is stack-equivariant, procs-irrelevant, and same-mem.
2. **`denote` is a total pure function on `Env`.** Lean's kernel can `rfl`-reduce `denote (prodProg 3) (bindParams ["a"] [Val.int k])` to a specific `(some (), ρ_f)` term by ~30 definitional unfoldings. The "denote equation" premise of the bridge is therefore not a proof obligation at all — it's a computation.
3. **The example's spec is parametric in nothing operational.** No heap fragment owned by the caller, no resource ownership traded, no shared invariant. The bridge has nothing to thread.

The walkthrough has **zero invocations** of Theorem 15, mvcgen, or any Hoare-style reasoning. It's "the helper's value is computed by `rfl`, plug it in." That is the *whole machinery*. Useful as a sanity check on the structural shape; **not the right machinery for any realistic helper**.

### 8.4 Where this leaves us — the real story we want

The motivating use case (per the design conversation) is:

> Connect Iris-Lean and Std.Do, using mvcgen to solve denote-like results.

For that:
- Helpers should be allowed to **touch state** (read/write the heap, locally allocate, etc.) under appropriate framing.
- The helper-body specification should be a **Hoare triple over Std.Do**'s state monad: `{P heap env vs} body {Q heap env v}`, verified by mvcgen.
- The bridge should consume that Hoare triple, thread the caller's heap-fragment ownership through Iris's `state_interp`, and produce the callee-frame wp.

Our current bridge — and the underlying `denote`/`BodyTraj` story — **cannot deliver this**. The reasons are structural:

| Limitation | Why it blocks |
|---|---|
| `body.heapFree` is a **structural assumption** of `BodyTraj.pure_steps_to_near_end` and its dependencies. | A heap-touching body has mem-changing intermediate steps; `pstep`'s "same-mem" trajectory no longer holds in a composite where other threads might have written. The body's trajectory is no longer self-contained. |
| `denote` is a pure function on `Env`. | A heap-touching body's "result" is state-indexed: `v_h` depends on the input heap, the output heap depends on the input heap. A pure `denote : Env → Option _ × Env` cannot express this. We'd need at minimum `denote : Env × Heap → Option _ × (Env × Heap)`, and we'd need separation-logic framing at the bridge boundary. |
| The Iris bridge sidesteps `state_interp` entirely. | At the call site, the caller owns some `state_interp σ` heap-fragment. A state-bearing bridge has to consume part of σ, hand it to the helper, get back the helper's output heap-effect, and return the updated `state_interp` to the caller. That's the standard Iris separation-logic dance — and it requires Iris machinery, which is *exactly* what Theorem 15 in its full state-aware form provides. |

**Theorem 15 generalizes to state.** Its statement is about arbitrary `prog` with arbitrary mem behavior; the `Machine.SafeTp` premise is state-aware; the resulting wp's underlying `state_interp` tracks the program's heap effects. The only thing wrong with Theorem 15 for our composition use case is the **closed-world allocator shape** (§8.2). Fix that and Theorem 15 becomes the universal bridge.

### 8.5 Revised path forward

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

3. **Open-context Theorem 15** — *partially done* (`completeness_general` exists; needs the closed-world fix per §8.2). The fix is to thread an existing `[AgarG GF F]` instance through the theorem's signature, refactor the `heap_init`/`threadpool_init`/invariant-alloc dance to NOT re-allocate the heap (it's already in scope), and emit just the bare `wp` (no `∃ Hsi`, no fresh `state_interp Mem.empty` since the caller's `state_interp σ` is already in scope). ~150–250 LoC.

4. **Open-context Theorem 15 used inline at the .call site** — *trivial once (3) lands*. Replace the current `wp_call → wp_callee_of_pure_helper → wp_ret_top` chain with `wp_call → (open Theorem 15)` applied to a SafeTp witness obtained via link (2).

The pure-helper case becomes a degenerate instance: the helper has no state effects, so its Hoare triple is vacuous-on-state, and the heap-fragment ownership is `emp` — at which point link (1)+(2)+(3) collapse to "the `denote` equation," recovering the current bridge as a corollary.

### 8.6 What to keep, what to retire

**Keep:**
- `Agar/Iris/CalleeBridge.lean` — useful as the pure-case bridge. Retains pedagogical value: demonstrates that the structural-denotational shape composes at the Iris level for the simplest case.
- `Agar/Examples/SimpleRangeProdComposition.lean` — the walkthrough exists as a worked example. The `rangeProd_composite_walkthrough` theorem stands.
- `Agar/Iris/Completeness.lean`'s `completeness_general` (Route A's artifact) — closed-world variant, useful when one *is* starting closed-world. Not load-bearing for the inline-at-call-site story.
- The `BodyTraj` namespace in `Agar/Operational/Composition.lean` (`denote_sound_stk`, `pstep_tstep_procs`, `pure_steps_to_near_end`, `pstep_near_end_pop`, `PureSteps_to_StepStarN`). Pure-fragment operational infrastructure; reusable for the degenerate-case branch of the general story.

**Retire (or de-emphasize):**
- The framing of `wp_callee_of_pure_helper` as "the answer." It's the no-state corner of the answer.
- The operational `Machine.safe_compose` work in `Agar/Operational/Composition.lean` (the `simulation_step` route). It has its own pre-existing `sorry`s (atomic_call/doReturn shape mismatch); given that the Iris path is the real story and the no-state case is already covered by CalleeBridge, finishing the operational route adds little. Acceptable to mark as legacy and not invest more in.

**To build:**
- The Std.Do ↔ Agar adequacy bridge (link 2 above). A new file, probably `Agar/StdDoBridge/...` or similar.
- The open-context Theorem 15 (link 3 above). An additional theorem in `Agar/Iris/Completeness.lean`, or a new file `Agar/Iris/CompletenessOpen.lean`.
- A worked state-bearing example, paralleling `SimpleRangeProdComposition.lean` but with a helper that touches the heap (e.g., an accumulator-into-a-loc helper). This is the proper test of the new story.

### 8.7 Open questions worth resolving before more code

1. **What is the precise shape of mvcgen's output?** Is it a Hoare triple (`triple m P Q` for some `triple` predicate), or a wp (`mvc.wp m Q P`)? The shape of link (2)'s premise depends on this.
2. **Does Std.Do have an existing operational semantics expressed as a step relation?** If yes, link (2) translates step ↔ step. If no, we have to define the embedding ourselves.
3. **How does Std.Do represent the heap?** A `Heap`-keyed `StateM`? An `IO`-style monad with `IORef`s? An abstract `MonadState`? The translation to Agar's `Mem` depends on this.
4. **Do we want the helper to be expressible in Agar's native `Stmt` (translated from Std.Do), or expressible directly in Std.Do with Std.Do's own semantics treated as the ground truth?** The former gives us a single operational model; the latter requires Iris-Lean to be parametric in the helper's semantics.
5. **What's the right shape of the helper-spec interface at the bridge?** For the pure case it was `(denote ρ = (some (), ρ_f), Expr.eval ρ_f e = some v)`. For the state-bearing case it's some triple/wp. We need a clean abstraction so the bridge doesn't have to know about Std.Do internals — analogous to how the current bridge consumes "any denote equation."

Resolving these informs whether the Std.Do bridge is a small lift or a larger interpretive project.

# The Agar proof-mode tactic suite — reference card

A reference for the Agar-specific Iris tactics. The base logic is
sound (full `wp_strong_adequacy`, zero sorries) and a mature tactic
suite now sits on top of it: `wp_step` / `wp_steps` / `wp_pures` drive
pure reduction, `wp_alloc_intro` / `wp_load_inv` / `wp_store_atomic` /
`wp_cas_inv` discharge heap-and-invariant obligations, and
`start_closed_proof_with_heap` opens an adequacy proof in one line.
End-to-end examples — sequential (`Recursion.lean`, `InsertionSort3.lean`),
concurrent (`Fork.lean`, `Mutex.lean`, `Counter.lean`), and
invariant-driven (`Invariant.lean`, `Spin.lean`) — live in
`Agar/Examples/`. This document records the design rationale and the
historical friction that motivated each tactic, so future additions
preserve the same conventions.

## What hurt before the suite existed

### 1. Threading explicit arguments through every WP rule

Each `wp_*` lemma has on the order of 8–13 explicit positional
arguments (statement parts, environment, stack, continuation, post,
plus the evaluation/step witnesses). Lean's inference can't propagate
them through the `⟨stmt, cont, env, stack, result⟩` tuple, so the
proof boilerplate looks like:

```lean
iapply wp_assign (E := E) procs fp x e v cont env stack Φ heval
iintro !>
iapply wp_skip_cons (E := E) procs fp s rest env stack Φ
iintro !>
iapply wp_ret_top (E := E) procs fp _ v cont env Φ hret
```

Each line is a fight against `Function expected at term, but term has type`
or `iapply: cannot apply` because some sub-piece didn't match.

### 2. Common Lean tactics are intercepted by IPM

Inside `istart … iintro …` blocks (which is most of any non-trivial
proof), several "obvious" tactics give "unknown tactic":

- `set lenv := bindParams ["n"] [.int n]` — can't bind named
  abbreviations
- `show iprop(…)` — can't change/clarify the goal shape
- `change …` — same, sometimes
- `simp only [foo]` at the goal — works at *hypotheses* (`at H`) but
  not at the iris goal directly
- `decide` on a `⌜φ⌝` goal — works only after exiting IPM with
  `ipure_intro`

Workarounds (`unfold` outside IPM blocks, intermediate `have`s) are
verbose and ugly.

### 3. `decide` can't reduce `Expr.eval`

Pure facts like

```lean
Expr.eval (bindParams ["n"] [Val.int 0]) (.bin .lt (.var "n") (.val (.int 1)))
  = some (.bool true)
```

don't yield to `decide` — the function definitions are not marked
reducible enough and the `Val.int (Int.ofNat n)` coercion blocks
reduction. We end up writing:

```lean
have hlt : … = some (.bool true) := by
  simp [Expr.eval, bindParams, Env.set, Env.empty, BinOp.eval]
  -- and maybe omega / decide / push_cast / ring after
```

Every step of the proof needs one or two of these.

### 4. `iapply` with many `%`-args fails opaquely

For an IH like

```lean
∀ (n : Nat) (x : Name) (e : Expr) (cont : List Stmt) (env : Env)
  (stack : List Frame) (Φ : Val → IProp GF),
  ⌜Expr.eval env e = some (.int n)⌝ -∗ ▷ wp … -∗ wp ⟨.call …⟩ Φ
```

the application

```lean
iapply IH $$ %k %"r" %(.bin .sub …) %([.ret …]) %(bindParams …)
  %(⟨x, cont, env⟩ :: stack) %Φ %hsub
```

fails silently — the goal doesn't change and a downstream `iintro !>`
reports `unsolved goals` listing IH, Hcont, and the unchanged WP. The
error gives no hint of *which* `%` arg failed to unify or whether the
parser even accepted the call.

### 5. Procedure bodies need an explicit `unfold`

After `wp_call`, the goal is `wp ⟨Examples.fact.body, [],
bindParams Examples.fact.params […], …⟩ Φ`. None of the `wp_*` rules
match `Examples.fact.body` against their pattern (`Stmt.ite …` etc.),
because Lean doesn't β-reduce the body. We need `unfold Examples.fact`
at exactly the right point.

## Sketch: tactics we want

### `wp_pures`

> Take whatever pure steps are available — `skip`, `seq`, `assign`,
> `ite`-with-known-condition, `whileDo`-unrolling-once — and chain them
> until we hit something that needs user input (a heap op, a `call`,
> a `ret`, or an `ite` whose guard doesn't reduce).

Spec: when the goal is `wp ⟨s, cont, env, stack, none⟩ Φ` and `s`
reduces via a pure-step rule to a new state, do the step, strip the
resulting `▷`, and repeat.

This alone eliminates ~half the proof lines in a typical script.

### `wp_call <ident>`

> Step into the named procedure call. Verify the procedure exists in
> the table (via `simp` or `decide` on `procs.find?`), unfold the
> procedure body, and leave the user at the entry of the body with the
> call frame on the stack.

Should subsume `iapply wp_call procs fp x f args proc vs cont env
stack Φ hproc hargs harity; iintro !>; unfold Examples.fact`.

### `wp_load`/`wp_store`/`wp_alloc`/`wp_free`/`wp_cas`

> Step the named heap op. Auto-pull the `points_to` from the IPM
> context that matches the location expression, discharge the
> evaluation side condition by `simp [Expr.eval, Env.set, …]`, then
> hand back the post-step `▷` and re-introduce the (possibly
> updated) `points_to`.

Spec for `wp_load x e`: when goal is `wp ⟨.load x e, …⟩ Φ` and the
context has `HP : l ↦ v` plus `e` evaluates to `.loc l`, finish the
load and leave `HP : l ↦ v` plus a `▷` over the continuation.

### `wp_ret`

> Step a top-of-stack or stack-pop return. Evaluate the return
> expression in the local env, then either commit `Φ v` (top-level) or
> step into the caller's continuation with `x := v` (pop).

### `wp_apply <spec>`

> Apply a Hoare-style call spec lemma (like `wp_fact_call`). Should
> handle the dance of `wp_call → step into body → use spec → step out
> via wp_ret_pop`.

This is the most powerful single addition — it's what makes large
verifications composable.

### `agar_expr_eval` (a `simp`-set)

> A `@[simp]`-tagged collection covering `Expr.eval`, `bindParams`,
> `Env.set`, `Env.empty`, `BinOp.eval`, `UnOp.eval`, `Fields.proj`,
> `Fields.upd`. Plus a tactic `agar_expr` that runs `simp` over those
> lemmas and finishes with `omega` or `push_cast; ring` as needed.

Eliminates the 4-line `have hlt : Expr.eval … := by simp […]; omega`
pattern.

## What we lose without these

Verifying `fact(n) = factNat n` by hand takes ~150 lines of dense
proof script for ~20 lines of program. The ratio should be more like
2–3:1.

Verifying `progCounter` (the spinlock) would be infeasible without
these — the proof script length would be measured in thousands of
lines.

## Implementation notes / order of attack

If we land these one at a time:

1. **`agar_expr_eval`** (~50 lines, ~1 hr). Lowest-risk, immediate
   wins. Tag a `@[simp]` set, write a wrapper tactic, ship.
2. **`wp_pures`** (~150 lines, ~3-4 hr). Macros over `iapply
   wp_skip_cons`/`wp_seq`/`wp_assign`/`wp_ite_*`. The decision
   procedure for "which pure rule applies" is straightforward pattern
   match on the head `Stmt` constructor.
3. **`wp_load`, `wp_store`, `wp_alloc`, `wp_free`, `wp_cas`** (~300
   lines each, ~half-day apiece). Each needs to search the IPM context
   for a matching `points_to`, discharge eval side conditions, and
   re-introduce resources. The hard part is the IPM context inspection
   (probably needs to drop to `Lean.Elab.Tactic` for a custom syntax).
4. **`wp_apply`** (~200 lines, ~half-day). Generic — given a lemma
   with shape `[preconds] -∗ ▷ wp ⟨…, cont, env, stack, none⟩ Φ ⊢ wp
   ⟨…, cont, env, stack, none⟩ Φ` (or similar), apply it.
5. **`wp_ret`, `wp_call <ident>`** (~150 lines combined). Niche, but
   the call-site form is needed for procedure composition.

Once items 1–4 are done, factorial becomes:

```lean
theorem wp_fact_call : … := by
  apply BILoeb.loeb_weak
  iintro IH %n %x %e %cont %env %stack %Φ %heval Hcont
  wp_call "fact"
  wp_pures              -- steps through `.ite`-on-known
  cases n with
  | zero =>
      wp_ret; iexact Hcont
  | succ k =>
      wp_apply IH; · agar_expr; iintro Hcont'
      wp_pures
      wp_ret; iexact Hcont'
```

That's the target.

## Status

Not built yet. The notes above are recorded so the next session
(probably an Agent dispatch) can pick this up.

# Per-procedure adequacy + concurrent factorial — wishlist

## The artifact

A worked concurrent example: two threads each compute a partial range
product `∏_{i=a}^{b-1} i` via a *pure Agar procedure*, then atomically
multiply their result into a shared accumulator via CAS. Adequacy
delivers `Val.int (10!)` at the end.

The point: **the pure factorial is a separate Agar procedure**, and
its correctness inside the concurrent client is established by feeding
its denotational identity into completeness (Theorem 15) *per
procedure call site*. The client's Iris proof invokes a one-shot
"pure-procedure call" lemma; it never steps through factorial loops
with `wp_pure_step`.

## Design constraints

- **No `▷^[M]` exposure, and no `wp_pure_step` in the proof.** The
  body's trajectory is a witness, not something to be symbolically
  executed. The lemma is proved by generalised Löb over trajectory
  positions (same idiom as `wp_spin`, with "trajectory position" as
  the loop-iteration analogue). Each unfolding of `wp` consumes the
  `▷` that Löb's IH supplies at the next position. Wp's own
  contractiveness absorbs the M body laters. **No `wp_pure_step` is
  invoked, internally or externally.**
- **forN-only helpers for now.** `unrollW` (from `while_`) inserts a
  `.call "_no_proc_"` sentinel in the out-of-fuel branch, which would
  break procs-independence at the client's program. `forN` doesn't.
  This keeps the side condition trivially discharged for the example.
- **Helpers are env-parametric.** Params are read from the env via
  `.var "a"`, `.var "b"`. `bindParams` (from Agar's call semantics)
  populates them. No meta-level baking.
- **Completeness is the load-bearing theorem.** Every adequacy result
  for a pure procedure routes through `completeness GF F`, not through
  hand-rolled wp reasoning over the body.

## Infrastructure pieces

| # | Piece                                | Depends on        | Subagent-able |
|---|--------------------------------------|-------------------|---------------|
| 1 | `rangeProdHelper a b` + denotation   | existing forN     | yes           |
| 2 | `denote_sound_general` — any ρ₀, any stack/result trailing | existing denote_sound | yes |
| 3 | `noCall` predicate + `embed`-of-forN ⊆ noCall | (1), (2)   | yes           |
| 4 | `wp_call_pureProc` rule via Löb      | (2), (3)          | no — design   |
| 5 | Composite client `Program`           | (1)               | yes           |
| 6 | Worker verification (CAS loop)       | (4), (5)          | partly        |
| 7 | Main verification (spin-wait)        | (5), (6)          | partly        |
| 8 | Closing adequacy                     | (6), (7)          | yes           |

## The `wp_call_pureProc` interface (design target)

```lean
theorem wp_call_pureProc
    (procs : Name → Option Proc) (fork_post : IProp GF) (E : CoPset)
    (h : PureHelperParametric)   -- formal params + body + ret
    (p_name : Name)
    (hp : procs p_name = some h.toProc)
    {φ : List Val → Val → Prop}
    (hd : ∀ vs, vs.length = h.params.length →
            ∃ v, denoteHelperAt h vs = some v ∧ φ vs v)
    (hno_call : noCall (embed h.body))
    (x : Name) (args : List Expr) (vs : List Val)
    (hargs : evalArgs env args = some vs)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF) :
    ▷ (∀ v, ⌜φ vs v⌝ -∗
        wp procs fork_post E
          ⟨post_call_stmt cont, post_call_cont cont,
           env.set x v, stack, none⟩ Φ)
    ⊢ wp procs fork_post E ⟨.call x p_name args, cont, env, stack, none⟩ Φ
```

The caller supplies a wand from `⌜φ vs v⌝` to the post-call wp; the
lemma hides everything in between.

## Out of scope (this iteration)

- `while_`-based helpers (need a more careful side condition).
- Recursive pure procedures (recursion would need Löb on params too).
- Procedure-call rule for *impure* helpers (irrelevant to the bridge's
  story).

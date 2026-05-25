# Completeness of the Agar program logic — porting §3.2 of Hostert et al.

Reference: Hostert, Zhang, Liu, Gregersen, Jung, Tassarotti.
*Completeness of Iris-Based Program Logics*, §3.2 (ConcLang case).
PDF: <https://simongregersen.com/papers/2026-completeness.pdf>

§3.2 of the paper develops completeness for ConcLang — a concurrent
imperative language with heap, fork, and atomic CAS. The recipe maps
onto Agar almost line-for-line: only *encoding* differs, not the
structural argument.

This file records both the design and the current state of the port
in the Agar codebase.

## Status

### Landed

| Paper item                         | Agar landing                                                                                  |
|------------------------------------|-----------------------------------------------------------------------------------------------|
| `safe-tp_φ` / `safe_φ`             | `Machine.SafeTp` / `Machine.safeFrom` / `Machine.safe` (`Agar/Iris/Adequacy.lean:734-755`)    |
| Lemma 11 (pointwise projection)    | `Machine.SafeTp.here` (`Agar/Iris/Adequacy.lean:760-765`)                                     |
| Lemma 12 (step closure)            | `Machine.SafeTp.step_closed` (`Agar/Iris/Adequacy.lean:769-773`)                              |
| Theorem 13 (Soundness)             | `wp_safe[_bupd]` (`Agar/Iris/Adequacy.lean`)                                                  |
| Thread-pool ghost-map RA           | `threadpool_auth γ ts` + `thread_at γ n t` (`Agar/Iris/Algebra/ThreadpoolRA.lean`)             |
| Bootstrap `threadpool_init`        | `Agar/Iris/Algebra/ThreadpoolRA.lean`                                                         |
| Heap-free predicates               | `Stmt.heapFree` / `Thread.heapFree` / `Program.heapFree` (`Agar/Iris/Completeness.lean`)      |
| `tstep_heapFree_mem_unchanged`     | `Agar/Iris/Completeness.lean`                                                                 |
| `Icompl_pure` (heap-free `Icompl`) | `Agar/Iris/Completeness.lean`                                                                 |

### Modulo-landed

| Paper item                                       | Form                                                                                                                  |
|--------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------|
| `wp_wand` (iprop-level post weakening)           | Full proof (`Agar/Iris/Completeness.lean`)                                                                            |
| Theorem 15 (Completeness) **modulo Lemma 14**    | `completeness_modulo_lemma14` — full proof, takes Lemma 14 and the post-weakening wand as hypotheses                  |

### Not landed

| Paper item                          | Why                                                                                                                                                |
|-------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------|
| Lemma 14 (per-thread completeness)  | Substantial Iris proof-mode work (~200-400 LoC). The case split is laid out in this doc; the threadpool RA, `Icompl_pure`, and `wp_wand` are ready. |
| Post-weakening wand                 | The wand `inv N _ ⊢ ∀ v, percomplete_post γ 0 v -∗ ⌜φ v⌝` reduces to the same `▷`-extraction technique as Lemma 14's step case.                     |
| Heap support inside `Icompl`        | Conflicts with Agar's exclusive `state_interp = heap_auth`; see "Heap obstacle" below.                                                              |

## Match-up, term by term

| §3.2 ingredient                                                | Agar analogue                                                                              |
|----------------------------------------------------------------|--------------------------------------------------------------------------------------------|
| Configuration `(ē, σ)`                                         | `Machine = ⟨mem, threads⟩`                                                                |
| Thread-pool step `(ē, σ) →tp (ē', σ')`                         | `Machine.Step prog μ μ'`                                                                  |
| Per-thread base step `e →base e'` with fork list `ē_f`         | `tstep procs chosen m t = some (m', t', sp)`, `sp : Option Thread` (≤1 fork per step)     |
| `red(e, σ)`                                                    | `thread_reducible prog.procs m t`                                                         |
| `safe-tp_φ`                                                    | `Machine.SafeTp`                                                                          |
| `safe_φ(e, σ)`                                                 | `Machine.safeFrom prog σ φ`                                                               |
| Lemma 11                                                       | `Machine.SafeTp.here`                                                                     |
| Lemma 12                                                       | `Machine.SafeTp.step_closed`                                                              |
| Theorem 13 (Soundness)                                         | `wp_safe[_bupd]` (already in place)                                                       |
| Threadpool ghost-map `γ : ℕ →fin Expr`                          | `γ : ℕ →fin Thread` via `HeapView F Nat (Agree (LeibnizO Thread)) HeapMap`                |
| Fragment `n ↪^γ e`                                              | `thread_at γ n t` (notation `n ↪[γ] t`)                                                  |
| Authority `•^γ ē`                                              | `threadpool_auth γ ts`                                                                    |
| `GhostMapLookup`                                               | `threadpool_lookup` / `threadpool_lookup_frame`                                          |
| `GhostMapUpdate`                                               | `threadpool_update`                                                                       |
| `GhostMapInsert`                                               | `threadpool_insert`                                                                       |
| `GhostMapAlloc`                                                | `threadpool_init`                                                                         |

The forward direction (soundness) is fully wired up in Agar. The
threadpool RA mirrors `Agar/Iris/Heap.lean` exactly, with `Nat` keys
and `Thread` values (wrapped in `Agree (LeibnizO …)`).

## The heap obstacle

The paper's `Icompl` carries the iterated separating conjunction of
all heap points-tos inside the invariant:

```
I_compl ≜ ∃ ē, σ. ⌜safe-tp_φ(ē, σ)⌝ ∗ •^γ ē ∗ ⊛_{(ℓ↦v)∈σ} ℓ ↦ v
```

This is *the* mechanism by which the proof of Lemma 14 obtains a
points-to at the location an atomic load/store/CAS is about to touch.

Direct translation to Agar runs into a structural conflict:

1. **`state_interp m = heap_auth m`** in Agar (`Agar/Iris/Heap.lean:206-207`),
   exclusive at fraction `own 1`.
2. **The big-sep `[∗ map] l ↦ v ∈ σ, l ↦ v`** is the entire heap's
   fragment side. Combining it with `state_interp m` saturates the
   `HeapView` RA at this ghost name — the auth and the union of all
   fragments at fraction 1 each is the *complete* heap, valid only when
   `σ = m`.
3. So putting the big-sep inside `Icompl` is fine — when the invariant
   is opened, you can derive `σ ⊆ m` from the auth/frag agreement.
   But the **other direction** (`m ⊆ σ`) requires an additional
   invariant (e.g. `entries enumerates supp(m)` maintained by hand) or
   a redesign of `state_interp`.

Workable resolutions, in increasing order of intrusiveness:

* **(a) Heap-free fragment.** Restrict to programs that never use
  `load/store/alloc/free/cas`. The operational heap stays at
  `Mem.empty`, the big-sep is `emp`, and the obstacle vanishes. This
  is what `Agar/Iris/Completeness.lean` does today. The completeness
  theorem becomes: "every heap-free, safe concurrent program has a wp
  proof." Captures the structural Löb-induction argument over the
  threadpool fully; heap reasoning is sidestepped.

* **(b) Maintained pure invariant.** Track `entries enumerates
  supp(σ)` as a pure conjunct inside `Icompl`, updated alongside every
  heap step in the Lemma-14 proof. Requires the Löb invariant to
  thread the maintenance argument through every case — clean but
  bookkeeping-heavy. Doesn't touch `state_interp`.

* **(c) Half-fraction `heap_auth`.** Change Agar's `state_interp` and
  the heap RA to use fractional ownership; have `state_interp` hold
  half and `Icompl` hold the other half, with agreement giving `σ = m`
  automatically. Breaks every existing heap-rule proof in
  `Agar/Iris/Rules.lean` until they're re-derived.

* **(d) Parameterised state_interp.** Generalise `wp_pre` so the
  state interpretation is an explicit parameter (or use a different
  typeclass instance under a local scope). Define the standard heap
  rules over a `gen_heap`-style state-interp that's the auth + the
  big-sep together; then the completeness invariant `Icompl` holds
  the big-sep inside, the state-interp keeps the auth outside, and
  agreement is enforced by the RA. Most faithful to iris-coq's
  `gen_heap` design.

Path (a) is the minimum-friction "show the recipe works" version,
landed today. Path (d) is the right long-term refactor.

## What is wired up today

`Agar/Iris/Algebra/ThreadpoolRA.lean` defines the new ghost-state RA:

```lean
abbrev TpF (F : Type _) [UFraction F] : OFunctorPre :=
  constOF <| HeapView F Nat (Agree (LeibnizO Thread)) HeapMap

class TpGpreS (GF : BundledGFunctors.{0,0,0}) (F : outParam (Type _))
    [UFraction F] extends ElemG GF (TpF F)

def threadpool_auth (γ : GName) (ts : List Thread) : IProp GF
def thread_at      (γ : GName) (n : Nat) (t : Thread) : IProp GF
scoped notation:50 n " ↪[" γ "] " t => thread_at γ n t

theorem threadpool_lookup       -- agreement
theorem threadpool_lookup_frame -- agreement, framed
theorem threadpool_update       -- step
theorem threadpool_insert       -- fork
theorem threadpool_init         -- bootstrap a singleton pool + frag at 0
```

`Agar/Iris/Completeness.lean` defines the heap-free fragment and the
specialised completeness invariant:

```lean
def Stmt.heapFree    : Stmt → Prop
def Thread.heapFree  : Thread → Prop
def Program.heapFree : Program → Prop

theorem tstep_heapFree_mem_unchanged
    (htf : t.heapFree)
    (h : tstep procs none m t = some (m', t', sp)) :
    m' = m

def Icompl_pure (prog : Program) (φ : Val → Prop) (γ : GName) : IProp GF :=
  iprop(∃ ts : List Thread,
    ⌜Machine.SafeTp prog ⟨Mem.empty, ts⟩ φ⌝ ∗
    threadpool_auth γ ts)
```

`Agar/Iris/Adequacy.lean` adds the paper-aligned forward direction:

```lean
def Machine.SafeTp (prog : Program) (μ : Machine) (φ : Val → Prop) : Prop
def Machine.safeFrom (prog : Program) (σ : Mem) (φ : Val → Prop) : Prop
def Machine.safe (prog : Program) (φ : Val → Prop) : Prop

theorem Machine.SafeTp.here          -- Lemma 11
theorem Machine.SafeTp.step_closed   -- Lemma 12

theorem wp_safe_bupd    -- Theorem 13 (soundness)
```

Whole codebase builds clean: 209/209 targets, zero `sorry`s.

## Lemma 14 (per-thread completeness, heap-free case) — the path forward

The intended statement, in the heap-free setting:

```lean
theorem percomplete {GF F} [UFraction F] [TpGpreS GF F] [InvGS_gen false GF]
    {prog : Program} {φ : Val → Prop} (hpf : prog.heapFree) (γ : GName)
    (n : Nat) (t : Thread) (htf : t.heapFree) :
    Icompl_pure prog φ γ ∗ thread_at γ n t ⊢
      wp prog.procs (·= True) ⊤ t
        (fun v => iprop(∃ t', thread_at γ n t' ∗ ⌜t'.toValue = some v⌝))
```

Proof by Löb induction. After unfolding `wp_pre`:

* **Value case.** `t.toValue = some v` for some `v`. Provide `v`,
  conclude `Φ v = ∃ t', n ↪γ t' ∗ ⌜t'.toValue = some v⌝` by exhibiting
  `t' = t`.
* **Step branch.** `t.terminated = false`. For arbitrary `m`, receive
  `state_interp m`. Open `Icompl_pure` (gives `ts` and `SafeTp`
  witness). By `threadpool_lookup_frame`, `ts[n]? = some t`. By
  `SafeTp.here` + non-termination, `t` is reducible. Provide
  reducibility; after the step is taken, case on what kind of step it
  was:
  - **Pure step.** Heap-freeness + `tstep_heapFree_mem_unchanged` ⇒
    `m' = m`. Threadpool: `ts.set n t'`. Use `threadpool_update` to
    update the ghost map. Use `Machine.SafeTp.step_closed` to update
    the pure witness. Re-close `Icompl_pure`. Apply the Löb IH on the
    new thread.
  - **Fork.** `sp = some t_child`. Append `t_child` to `ts`. Use
    `threadpool_insert` to extend the ghost map. Re-close. Apply the
    Löb IH *twice* — once for the parent (with the same `n`), once
    for the child (at the fresh index `ts.length`, with post `True`).

Theorem 15 then follows by allocating the threadpool with
`threadpool_init`, allocating the invariant, and combining with
`Lemma 14` via `WpWand` to extract `⌜φ v⌝` from the projection-style
post.

## What the heap extension (path d) would add

```lean
-- new ghost name in `AgarG`:
heap_compl_name : GName
-- new state_interp:
state_interp m := heap_auth_full m   -- half at primary, half at compl
-- new Icompl with heap inside:
def Icompl ... : IProp GF :=
  iprop(∃ μ : Machine,
    ⌜Machine.SafeTp prog μ φ⌝ ∗
    threadpool_auth γ_tp μ.threads ∗
    heap_auth_compl μ.mem ∗
    [∗ list] (l, v) ∈ enumerate μ.mem, l ↦ v)
```

This requires defining/extracting a `enumerate : Mem → List (Loc ×
Val)` (which needs `Mem` to be finitely-supported — true for reachable
states, encodable via an extra component or by reaching for the
underlying `HeapMap`'s structure).

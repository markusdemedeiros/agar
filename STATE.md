# Agar — state of the development

A small concurrent imperative language, mechanised in Lean 4 against a
custom Iris-style separation-logic program logic. The artifact stands
at ~13 kLOC across three layers (`Lang/`, `Iris/`, `Examples/`), with
**202 build targets clean, zero `sorry`s**.

This document summarises the design and exhibits the headline theorems.

## 1. Surface language

`Agar/Lang/` carries the syntax, small-step semantics, surface
parser-macros, and a pure denotational fragment.

A program is a procedure table plus an entry-point statement; the
operational machine is a thread pool over a partial heap:

```lean
structure Program where
  procs : Name → Option Proc
  main  : Stmt

structure Machine where
  mem     : Mem               -- Loc → Option Val
  threads : List Thread

inductive Machine.Step (p : Program) : Machine → Machine → Prop
  -- existentially picks a thread index, a step result (incl. a
  -- possible spawned thread), and (for `alloc`) a fresh location.
```

Concrete syntax is supplied by the `ags(...)` / `age(...)` macros.
The factorial procedure reads naturally:

```lean
def fact : Proc where
  params := ["n"]
  body := ags(
    if n < 1 then return 1
    else (r := call fact(n - 1) ; return n * r)
  )
```

## 2. The weakest precondition

`Agar/Iris/Wp.lean` defines a *mask-aware fancy-update* WP, built as
the Löb fixed point of a contractive functional:

```lean
def wp_pre (procs : Name → Option Proc) (fork_post : IProp GF)
    (wp : CoPset → Thread → (Val → IProp GF) → IProp GF)
    (E : CoPset) (t : Thread) (Φ : Val → IProp GF) : IProp GF := iprop(
  (∃ v : Val, ⌜t.toValue = some v⌝ ∗ |={E}=> Φ v) ∨
  (⌜t.terminated = false⌝ ∗
    ∀ m, state_interp m ={E, ∅}=∗
      ⌜thread_reducible procs m t⌝ ∗
      ▷ ∀ m' t' sp, ⌜thread_step procs m t m' t' sp⌝ ={∅, E}=∗
        (state_interp m' ∗ wp E t' Φ ∗
         (∀ ts, ⌜sp = some ts⌝ -∗ wp CoPset.full ts (fun _ => fork_post)))))
```

The mask `E` brackets a single operational step via the standard
`={E,∅}=∗ … ▷ … ={∅,E}=∗ …` idiom, so invariants in `E` can be opened
for the duration of one step. Forked threads run at `⊤`.

`Iris/Heap.lean` supplies the state interpretation as the `HeapView`
authority over a partial map of `Val`s, with the standard points-to
fragment `l ↦ v`. Ghost updates (`heap_alloc`, `heap_store`,
`heap_free`) live there.

## 3. Per-statement rules

`Iris/Rules.lean` derives the per-statement Hoare-shape rules from
`wp_unfold` plus the ghost updates. Heap rules come in two flavours —
classical "give-me-the-points-to" form, and **atomic-invariant** form
that opens an `inv N (∃ v, l ↦ v)` for the duration of the step:

```lean
theorem wp_cas_inv
    (Hsub : ↑N ⊆ E)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (heq : (vO == vO) = true)
    (hne_of_ne : ∀ v, v ≠ vO → (v == vO) = false) :
    (inv N (∃ v : Val, l ↦ v) ∗
      ▷ wp procs fp E ⟨.skip, cont, env.set x vO, stack, none⟩ Φ ∗
      ▷ ∀ (v : Val), ⌜v ≠ vO⌝ -∗
           wp procs fp E ⟨.skip, cont, env.set x v, stack, none⟩ Φ)
    ⊢ wp procs fp E ⟨.cas x eL eO eN, cont, env, stack, none⟩ Φ
```

Structural rules — `wp_mono`, `wp_value`, `wp_value_fupd`, `wp_frame`,
`wp_pure_step`, `fupd_wp` — round out the toolkit.

## 4. Tactic suite

`Iris/Tactics.lean` and `Iris/TacticsAtomic.lean` lift the rule set
into proof-mode macros mirroring HeapLang's:

| Tactic                  | Effect                                                                 |
|-------------------------|------------------------------------------------------------------------|
| `wp_step`               | One pure or call step, auto-discharging the eval side condition.       |
| `wp_pures`              | Chain pure steps until something interactive (heap / call / fork).      |
| `wp_done`               | Close a terminal WP (top-level return or `wp_value`).                  |
| `wp_load h` / `wp_store h` | Step a heap op, threading the named `points_to`.                      |
| `wp_load_keep h` / `wp_store_atomic h` | Variants for invariant-protected loads/stores.        |
| `wp_alloc` / `wp_alloc_intro HP` | Step `alloc`, optionally naming the fresh location and `points_to`. |
| `wp_cas_succ`/`wp_cas_fail` / `wp_cas_atomic_split` | The three CAS shapes.                                |
| `wp_call`/`wp_call f`   | Step into a procedure body (optionally unfolding the named callee).    |
| `wp_apply h` / `wp_apply_gen_call_spec h …` | Apply an external Hoare spec at a call site.       |
| `wp_fork`               | Step `fork`, splitting resources across the two threads.               |
| `wp_spin` / `wp_spin_invariant` | Discharge a spin-loop via Löb-style invariants.                |
| `start_closed_proof_with_heap p` | Boilerplate prelude for closed adequacy theorems.            |

A typical proof script — verifying `progFactWith` returns `factorial n`
— reduces to ~15 lines of high-level moves:

```lean
theorem progFactWith_implements_factorial :
    Program.implementsUnary progFactWith (fun n => (factorial n : Int)) := by
  intro GF F _ _ _ n steps μ' htr
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int (factorial n : Int)) (progFactWith n) ?_ steps μ' htr
  start_closed_proof_with_heap progFactWith
  wp_step                       -- wp_seq
  iintro !>
  wp_apply_gen_call_spec factProc_spec_gen
    (fun nm => if nm = "fact" then some Examples.fact else none)
    (fun v => iprop(⌜(fun w : Val => w = Val.int (factorial n : Int)) v⌝))
    n "v" (Expr.val (Val.int (n : Int))) [ags(return v)] Env.empty []
  iintro !>
  unfold factProc_post
  wp_steps
  itrivial
```

## 5. Adequacy

`Iris/Adequacy.lean` discharges threadwise WPs into machine-level
guarantees over the full multi-thread `Machine.StepStarN` relation
(including `fork`):

```lean
theorem wp_strong_adequacy
    {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF]
    (p : Program) (φ : Val → Prop)
    (H : ∀ [_LC : InvGS_gen false GF],
         ⊢ ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
             state_interp Mem.empty ∗
               wp p.procs fork_post ⊤ (Thread.initial p.main)
                 (fun v => iprop(⌜φ v⌝ : IProp GF)))
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN p n (Machine.initial p) μ') :
    -- (1) per-thread safety
    (∀ t ∈ μ'.threads, t.terminated ∨ thread_reducible p.procs μ'.mem t) ∧
    -- (2) main-thread postcondition
    (∀ th rest, μ'.threads = th :: rest → ∀ v, th.toValue = some v → φ v)
```

A pool invariant `pool_wp` (big-sep of per-thread WPs, with index 0
carrying the user post and the rest carrying `fork_post`) is preserved
across `Machine.Step`; iteration gives an n-step soundness tower
discharged by `step_fupdN_soundness_no_lc'`.

The `Machine.Adequate` predicate packages safety + main-postcondition
for downstream use:

```lean
def Machine.Adequate (prog : Program) (μ : Machine) (v : Val) : Prop :=
  Machine.Safe prog.procs μ ∧ Machine.MainReturns μ v
```

Every `_closed` example proof in `Examples/` concludes
`Machine.Adequate prog μ' v` for a concrete `v`.

## 6. Denotational fragment

`Lang/Denotational.lean` carves out a pure terminating sub-language and
gives it a clean state-monadic denotation:

```lean
inductive PureStmt where
  | skip   : PureStmt
  | assign : Name → Expr → PureStmt
  | seq    : PureStmt → PureStmt → PureStmt
  | ite    : Expr → PureStmt → PureStmt → PureStmt
  | repeat : Nat → PureStmt → PureStmt
  | forN   : Nat → PureStmt → PureStmt
  /-- Fuel-bounded `while`. -/
  | while_ : Nat → Expr → PureStmt → PureStmt

abbrev Denot := StateM Env (Option Unit)
```

The marquee theorem is a *bidirectional* iff between the denotation
and the multi-thread operational machine, which packages the two
soundness lemmas (`Machine.denote_sound`, `Machine.exec_sound`):

```lean
theorem Machine.denote_iff (s : PureStmt) (ρ' : Env) :
    denote s Env.empty = (some (), ρ') ↔
      Machine.StepStar (programOf s) (Machine.initial (programOf s))
        ⟨Mem.empty, [mkT .skip [] ρ']⟩
```

Closed-form corollaries follow at the operational level for free.
Three concrete marquees:

```lean
-- Gauss: ∑_{k=1..n} k = n(n+1)/2
theorem denote_sumProg (n : Nat) :
    denote (sumProg n) Env.empty = (some (), gaussEnv (gauss n) (n + 1))

-- Euclid: gcd(a,b) by repeated subtraction
theorem denote_gcdPure (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    denote (gcdPure a b) Env.empty = (some (), gcdEnv a b)

-- Square via non-recursive procedure call
theorem denote_callSquare (m : Int) :
    denote (callSquare m) Env.empty = (some (), squareEnv m)
```

Non-recursive procedure call is a *smart constructor* over the
existing grammar — no new `PureStmt` case is needed:

```lean
def assignAll : List (Name × Expr) → PureStmt
def pcall (params : List (Name × Expr)) (body : PureStmt)
          (out : Name) (retExpr : Expr) : PureStmt :=
  .seq (assignAll params) (.seq body (.assign out retExpr))
```

## 7. Verification gallery

`Examples/` contains the closed verifications. Each terminates a
`_closed` theorem at `Machine.Adequate`:

| File                        | What it proves                                                 |
|-----------------------------|----------------------------------------------------------------|
| `Sanity.lean`               | One-step sanity per WP rule.                                   |
| `Sequential.lean`           | Straight-line heap manipulation.                               |
| `Recursion.lean`            | Recursive `factProc`, Löb-driven spec generalisation.          |
| `DataStructures.lean`       | Swap, field access.                                            |
| `Fork.lean` / `ParAdd.lean` | Forked threads with persistent invariant / disjoint heap.      |
| `Invariant.lean`            | Open / close `inv N P` via the atomic rules.                   |
| `Mutex.lean` / `Spin.lean`  | Spinlock-style mutual exclusion (safety).                      |
| `TicketLock.lean`           | FAA-via-CAS ticket lock mechanism (single-thread closed).      |
| `Counter.lean`              | 2-thread CAS-increment with `counter_auth` / `counter_frag`.   |
| `ProducerConsumer.lean`     | Single-slot buffer; asymmetric two-state invariant.            |
| `TreiberPush.lean`          | Lock-free push onto a Treiber stack (safety).                  |
| `ReaderCount.lean`          | Shared reader-count with disjunctive invariant.                |
| `Peterson.lean`             | Peterson's algorithm safety (no mutual-exclusion proof).       |
| `LaterCredits.lean`         | Late-credit elimination demo.                                  |
| `InsertionSort3.lean`       | 3-cell network sort with `min`/`med`/`max` + sum-preservation. |
| `GcdMarquee.lean`           | Denotational Gcd corollary plus operational reachability.      |
| `SquareMarquee.lean`        | Denotational `pcall` example.                                  |

The headline concurrent example, **Counter**, uses a disjunctive
invariant so the non-duplicable ghost authority lives in exactly one
branch:

```lean
def counterInv (cLoc : Loc) (γ : GName) : IProp GF :=
  iprop((cLoc ↦ Val.int 0 ∗ counter_auth γ 0 ∗ counter_frag γ 0)
        ∨ (cLoc ↦ Val.int 1 ∗ counter_auth γ 1 ∗ counter_frag γ 1))

theorem progCounterCas_closed (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCounterCas n
            (Machine.initial progCounterCas) μ') :
    Machine.Adequate progCounterCas μ' Val.unit
```

The 3-cell **insertion sort** is the artifact's largest end-to-end
heap-mutation proof (~460 LoC):

```lean
theorem progIsort3_sorted (v1 v2 v3 : Int) ... :
    Machine.Adequate (progIsort3 v1 v2 v3) μ' (Val.int (med3 v1 v2 v3))
  ∧ (min3 v1 v2 v3 ≤ med3 v1 v2 v3 ∧ med3 v1 v2 v3 ≤ max3 v1 v2 v3)
  ∧ min3 v1 v2 v3 + med3 v1 v2 v3 + max3 v1 v2 v3 = v1 + v2 + v3
```

## 8. `implements` — top-level functional specs

`Iris/Implements.lean` lifts the per-program `Machine.Adequate`
conclusions into a named predicate connecting a parameterised program
family to its mathematical denotation:

```lean
def Program.implementsUnary (prog : Nat → Program) (f : Nat → Int) : Prop :=
  ∀ {GF : BundledGFunctors.{0,0,0}} {F : Type} [UFraction F]
    [InvGpreS GF] [AgarGpreS GF F]
    (n : Nat) (steps : Nat) (μ' : Machine),
      Machine.StepStarN (prog n) steps (Machine.initial (prog n)) μ' →
      Machine.Adequate (prog n) μ' (Val.int (f n))
```

with concrete instances for factorial, sum, and binary max:

```lean
theorem progFactWith_implements_factorial :
    Program.implementsUnary progFactWith (fun n => (factorial n : Int))

theorem progSumWith_implements_sumNat :
    Program.implementsUnary progSumWith (fun n => (sumNat n : Int))

theorem progMaxWith_implements_max :
    Program.implementsBinary progMaxWith
      (fun a b => if (a : Int) < (b : Int) then (b : Int) else (a : Int))
```

## 9. Known limitations

- **`wp_pures` eats `wp_while`.** The macro's `first |` alternative
  list fires the while-unroll rule before the user can apply a Löb IH.
  Workaround: explicit `wp_step; iintro !>` before any `whileDo`
  head. A `wp_pures_nowhile` variant is the obvious follow-up.
- **Ticket-lock mutual exclusion.** `TicketLock.lean` ships a
  single-thread closed proof exercising the FAA-via-CAS mechanism on
  both `next` and `now` cells; the multi-thread Hoare specs with
  `locked γ` tokens collapsed twice under proof-mode friction, so the
  multi-thread version is deferred.
- **Peterson mutual exclusion.** `Peterson.lean` proves safety only —
  no mutex claim. The flag/turn interleaving argument requires
  Peterson-specific ghost reasoning beyond the standard idioms.
- **Decrement on `CounterRA`.** Reader-count examples currently use a
  disjunctive heap invariant rather than a fractional / decrement-able
  ghost counter; `CounterRA` ships only `counter_increment`.

## 10. Build

`lake build` from the repo root. Toolchain pinned to
`leanprover/lean4:v4.29.0`; iris-lean pinned to a pre-monorepo commit
that ships the `WSat` / `FUpd` / `Invariants` / `LaterCredits`
libraries.

`#print axioms` on the headline theorems
(`wp_strong_adequacy`, `Machine.denote_iff`, `progIsort3_sorted`,
`progFactWith_implements_factorial`) returns only the standard Lean
axioms `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`.

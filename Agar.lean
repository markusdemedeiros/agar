-- This module serves as the root of the `Agar` library.
--
-- # Architecture
--
-- Agar is a small concurrent imperative language verified in Lean 4
-- using a custom Iris-style separation-logic WP. The codebase is laid
-- out in three layers, mirrored by the three subdirectories under
-- `Agar/`:
--
-- ## `Agar/Lang/` — the surface language
--   * `Syntax`        — `Val`, `Expr`, `Stmt`, `Proc`, `Program`.
--   * `Semantics`     — `Mem`, `Thread`, `Machine`, the small-step
--                       relation `Machine.Step`.
--   * `Notation`      — concrete-syntax macros `age(...)` / `ags(...)`.
--   * `Denotational`  — a pure terminating denotation `denote : PureStmt
--                       → Env → (Option Unit × Env)` plus the
--                       bidirectional marquee theorem `Machine.denote_iff`.
--                       Constructors include `seq`, `assign`, `ite`,
--                       `forN`, `while_`, `repeat`.
--
-- ## `Agar/Iris/` — the program-logic infrastructure
--   * `Wp`            — `wp_pre`, the contractive WP functional, the
--                       fixed-point `wp` and `wp_unfold`.
--   * `Heap`          — heap CMRA, `state_interp`, `points_to`, ghost
--                       update lemmas.
--   * `Rules`         — per-statement WP rules (`wp_assign`, `wp_load`,
--                       `wp_cas`, `wp_call`, `wp_fork`, `wp_alloc`, …).
--   * `WpSpin`        — additional spin-loop rules.
--   * `Tactics`       — proof-mode macros (`wp_pures`, `wp_call <ident>`,
--                       `wp_load`, `wp_store`, `wp_alloc`, `wp_cas_*`,
--                       `wp_apply_*_spec`, `heap_adequacy_intro`,
--                       `start_closed_proof_with_heap`,
--                       `adequacy_with_heap_intro`, …).
--   * `TacticsAtomic` — atomic-triple tactics (`wp_cas_atomic_split`).
--   * `Adequacy`      — `Machine.safe`, the closed-adequacy theorem
--                       `wp_strong_adequacy`, `heap_adequacy_intro`.
--   * `Hoare`         — `{{ P }} s {{ v, Q }}` notation.
--   * `Implements`    — "program implements function" abstraction tying
--                       closed adequacy proofs to math functions.
--   * `Library`       — Hoare-spec'd reusable procedures (`maxProc`,
--                       `minProc`, `absProc`, `gcdProc`, `sumProc`, …).
--   * `Delab`         — pretty-printing for goal-state legibility.
--   * `Algebra/{Counter,Lock}RA` — ghost RAs.
--   * `Completeness`  — Theorem 15: from `Machine.safeFrom` of a
--                       heap-free program, derive a closed Iris
--                       derivation of `wp_⊤ (Thread.initial main) {⌜φ⌝}`.
--   * `PureHelperBridge` — `PureHelper { body, ret }` packages a
--                       `PureStmt` body with a return expression.
--                       `Machine.safe_of_denoteHelper` bridges
--                       `denoteHelper h Env.empty = some v ∧ φ v` to
--                       `Machine.safe`-from-any-σ; composed with
--                       completeness this yields a closed `wp_⊤` for
--                       the helper from a purely denotational spec.
--
-- ## `Agar/Examples/` — end-to-end verifications
--   Each file uses the program logic to verify a Agar program.
--   Sequential examples (Sanity, Recursion, Sequential, DataStructures)
--   exercise the basic rules; concurrent ones (Fork, ParAdd, Invariant,
--   Mutex, Spin, LaterCredits, Counter, ProducerConsumer) exercise
--   forking + invariants + ghost state, several closing via
--   `Machine.safe`. `Readback` is the lone concurrent example
--   closing adequacy at a *nontrivial* value (`Val.int 42`, not
--   `Val.unit`) — its main thread spin-loads a producer-written shared
--   register and returns the observed value, demonstrating
--   functional-correctness adequacy in the presence of forking.

module

-- Surface language: syntax, semantics, parser-notation, denotational
-- semantics.
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Lang.Denotational

-- Iris program-logic infrastructure: WP, heap interp + points-to,
-- WP rules (incl. invariant atomic triples), spin-loop rules, tactic
-- macros, adequacy, Hoare-triple notation, library specs, and ghost
-- algebras (lock / counter).
public import Agar.Iris.Wp
public import Agar.Iris.Delab
public import Agar.Iris.Heap
public import Agar.Iris.Rules
public import Agar.Iris.WpSpin
public import Agar.Iris.Tactics
public import Agar.Iris.TacticsAtomic
public import Agar.Iris.Adequacy
public import Agar.Iris.Hoare
public import Agar.Iris.Library
public import Agar.Iris.Algebra.LockRA
public import Agar.Iris.Algebra.CounterRA
public import Agar.Iris.Algebra.ThreadpoolRA
public import Agar.Iris.Completeness
public import Agar.Iris.PureHelperBridge
public import Agar.Operational.StackExt
public import Agar.Iris.StackPush
public import Agar.Examples.SimpleRangeProdCompositionRouteA
public import Agar.Examples.RangeProdStdDo

-- Example programs and their closed-adequacy proofs, plus the
-- per-WP-rule sanity suite.
public import Agar.Examples.Sanity
public import Agar.Examples.Recursion
public import Agar.Examples.Sequential
public import Agar.Examples.DataStructures
public import Agar.Examples.Fork
public import Agar.Examples.ParAdd
public import Agar.Examples.Invariant
public import Agar.Examples.Mutex
public import Agar.Examples.Spin
public import Agar.Examples.LaterCredits
public import Agar.Examples.Counter
public import Agar.Examples.ProducerConsumer
public import Agar.Examples.GcdMarquee
public import Agar.Examples.InsertionSort3
public import Agar.Examples.SquareMarquee
public import Agar.Examples.TicketLock
public import Agar.Examples.TreiberPush
public import Agar.Examples.ReaderCount
public import Agar.Examples.Peterson
public import Agar.Examples.Readback
public import Agar.Examples.StackPushPop
public import Agar.Examples.StackReverse
public import Agar.Examples.TreiberReverseClient
public import Agar.Examples.NextGreater

-- High-level `implements` predicate tying closed adequacy theorems
-- to mathematical functions.
public import Agar.Iris.Implements

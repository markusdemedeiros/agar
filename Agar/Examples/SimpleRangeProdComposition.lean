module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.CalleeBridge

@[expose] public section

/-! # Simplified CAS-merge composition example (no interference)

**Status: historical / legacy route.** This file predates the Route A
showcase and uses the original `Machine.safe_compose` operational
bridge (now marked `@[deprecated]`). It is kept as a reference for the
pre-Std.Do pure-helper story. For the current pipeline that dispatches
a pure helper's `Std.Do.Triple` spec down to closed safety, see
`SimpleRangeProdHelperSafe` + `SimpleRangeProdCompositionRouteA` +
`RangeProdStdDo`, with the design in `HYPOTHESIS.md` §8.

Two threads each call a pure `rangeProd` helper. No shared memory, no
CAS, no spin — just a single `fork` and two parallel helper calls. The
helper is one designated pure proc; the worker thread and the main
thread both call it.

We use this as a stress-test of `Machine.safe_compose`:

* The helper has the structural shape `.seq (embed prodProg) (.ret retExpr)`.
* The composite is `fork worker; call rangeProd; ret r`.
* We instantiate `safe_compose`, discharging registration / body-shape
  / heap-freeness / denotational convergence directly, leaving only
  `composite_abstract_safe` as the client's obligation.

The helper computes `a * (a+1) * … * (a+n-1)` where `n` is baked into
the helper proc (no variable-length loops in `PureStmt`).
-/

namespace Agar
open Agar.Logic
namespace SimpleRangeProd

/-! ## The helper -/

/-- Loop body: `acc := acc * i ; i := i + 1`. -/
def prodBody : PureStmt :=
  .seq (.assign "acc" (.bin .mul (.var "acc") (.var "i")))
       (.assign "i" (.bin .add (.var "i") (.val (.int 1))))

/-- Full body PureStmt: `acc := 1 ; i := a ; forN n prodBody`. The
parameter `a` is bound by the caller via `bindParams`. -/
def prodProg (n : Nat) : PureStmt :=
  .seq (.assign "acc" (.val (.int 1)))
   (.seq (.assign "i" (.var "a"))
    (.forN n prodBody))

/-- `rangeProd n`: pure helper proc. Param `a` is the start; the loop
count `n` is baked at the proc level. -/
def rangeProd (n : Nat) : Proc where
  params := ["a"]
  body   := .seq (embed (prodProg n)) (.ret (.var "acc"))

/-- Closed-form: `a * (a+1) * … * (a+k-1)`. -/
def rangeProdValue (a : Int) : Nat → Int
  | 0     => 1
  | k + 1 => a * rangeProdValue (a + 1) k

/-- The helper-post: at vs = [int a], the return value is the closed
form `rangeProdValue a n`. -/
def helper_post (n : Nat) (vs : List Val) (v : Val) : Prop :=
  ∃ a : Int, vs = [Val.int a] ∧ v = Val.int (rangeProdValue a n)

/-! ## The composite

Both threads call `rangeProd`:

* **Main thread**: forks the worker, then calls `rangeProd(1)` itself,
  then returns the result.
* **Worker thread** (the fork target): calls `rangeProd(5)` and returns
  the result (the return value of the forked thread is abandoned — no
  shared state, no interference).

This is the bare-bones "two pure helper calls in parallel" pattern: no
CAS, no spin, no shared variable.  The point is to exercise
`Machine.safe_compose` against a program with two concurrent invocations
of the same pure helper. -/

/-- Worker proc: a thin caller of `rangeProd`. -/
def rangeProdCaller : Proc where
  params := []
  body   :=
    .seq (.call "r" "rangeProd" [.val (.int 5)])
         (.ret (.var "r"))

/-- The composite program: `fork rangeProdCaller; x := call rangeProd(1); ret x`. -/
def rangeProdComposite (n : Nat) : Program where
  procs := fun name =>
    if name = "rangeProd" then some (rangeProd n)
    else if name = "rangeProdCaller" then some rangeProdCaller
    else none
  main  :=
    .seq (.fork "rangeProdCaller" [])
     (.seq (.call "x" "rangeProd" [.val (.int 1)])
           (.ret (.var "x")))

/-! ## Apply `Machine.safe_compose`

We discharge everything except `composite_abstract_safe`, which is
the client-side proof obligation (verifying the composite under the
abstract-step relation where helper calls are atomic). That stays as a
`sorry` here — the point of this example is to see whether the
`safe_compose` API plugs in cleanly.

**RETIRED 2026-05-26.** `Machine.safe_compose` itself is deprecated in
favor of the Iris/Route A pipeline. The Iris walkthrough lives at
`rangeProd_composite_walkthrough` (this file) and
`rangeProd_composite_walkthrough_RouteA` (sibling file); both are
fully closed. This `safe_compose`-based proof attempt is preserved
only as a historical illustration of the abandoned API shape; the
`sorry`s here are inherited from the deprecated route. -/

set_option linter.deprecated false in
@[deprecated "Use rangeProd_composite_walkthrough or rangeProd_composite_walkthrough_RouteA (both closed). See HYPOTHESIS.md §8.6." (since := "2026-05-26")]
theorem rangeProd_composite_safe (n : Nat) :
    Machine.safe (rangeProdComposite n) (fun _ => True) := by
  apply Machine.safe_compose (rangeProdComposite n) "rangeProd" (rangeProd n)
    (pureBody := prodProg n) (retExpr := .var "acc")
    (helper_post := helper_post n)
  · -- h_registered : composite.procs "rangeProd" = some (rangeProd n)
    rfl
  · -- h_body_eq
    rfl
  · -- h_comp_hf : composite is heap-free (main + all procs)
    refine ⟨?_, ?_⟩
    · -- main heap-free
      sorry
    · -- procs heap-free
      sorry
  · -- h_safe : denote convergence + helper_post
    sorry
  · -- composite_abstract_safe (the client's obligation)
    sorry

/-! ## Iris-tactic walkthrough

Step through the composite via Iris WP tactics until each thread is
sitting at a `.call rangeProd` instruction. This shows what
`safe_compose`'s `composite_abstract_safe` premise looks like in
practice — the two `wp (call rangeProd …) …` goals are exactly what
the abstract-relation client would dispatch via the atomic-call rule.
-/

open Iris Iris.BI Iris.OFE

/-- Pin a concrete `n = 3` so the program is fully ground (needed for
`adequacy_with_heap_intro` which takes an identifier, not an arbitrary
term). Inline the `rangeProdComposite` body so `unfold rangeProdComposite3`
exposes the main statement directly. -/
def rangeProdComposite3 : Program where
  procs := fun name =>
    if name = "rangeProd" then some (rangeProd 3)
    else if name = "rangeProdCaller" then some rangeProdCaller
    else none
  main  :=
    .seq (.fork "rangeProdCaller" [])
     (.seq (.call "x" "rangeProd" [.val (.int 1)])
           (.ret (.var "x")))

theorem rangeProd_composite_walkthrough
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe rangeProdComposite3 (fun _ => True) := by
  adequacy_with_heap_intro_P rangeProdComposite3 (fun _ => True)
  -- Goal: WP at main = `.seq (.fork "rangeProdCaller" []) (.seq (.call "x" "rangeProd" [1]) (.ret "x"))`.
  -- Peel the outer .seq so the head is `.fork "rangeProdCaller" []`.
  iapply wp_seq
  iintro !>
  -- Fire the fork rule. `cont` = the parent's queued continuation
  -- (everything after the fork in main).
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "rangeProdCaller" ([] : List Expr) rangeProdCaller ([] : List Val)
    [Stmt.seq (.call "x" "rangeProd" [.val (.int 1)]) (.ret (.var "x"))]
    _ [] _
    (by show rangeProdComposite3.procs _ = _; rfl)
    (by agar_eval)
    rfl
  isplitr
  · -- Forked thread: WP at `rangeProdCaller.body = .seq (.call "r" "rangeProd" [5]) (.ret "r")`.
    iintro !>
    unfold rangeProdCaller
    wp_pures
    -- Goal (1/2): WP at `.call "r" "rangeProd" [.val (.int 5)]` on the forked thread.
    iapply wp_call (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "r" "rangeProd" [.val (.int 5)] (rangeProd 3) [Val.int 5]
      [.ret (.var "r")] _ _ _
      (by show rangeProdComposite3.procs _ = _; rfl)
      (by agar_eval)
      rfl
    iintro !>
    -- Bridge: convert callee-frame wp to a wp at the post-doReturn state.
    -- The bridge's two arithmetic side conditions (the helper's denote
    -- equation and the retExpr eval) are left as explicit named goals.
    refine .trans ?bridge_premise_fork
      (Agar.CalleeBridge.wp_callee_of_pure_helper (GF := GF) (F := F)
        rangeProdComposite3 (rangeProd 3)
        (prodProg 3) (.var "acc") rfl [Val.int 5] "r" [.ret (.var "r")]
        Env.empty ([] : List Frame) iprop(emp : IProp GF)
        (fun _ => iprop(emp : IProp GF))
        ?ρ_f_fork (.int 210) ?denote_eq_fork ?ret_eq_fork)
    -- The body's denotation at vs = [5] terminates at some ρ_f where
    -- `acc` holds the product 5·6·7 = 210.
    case denote_eq_fork =>
      -- Goal: denote (prodProg 3) (bindParams ["a"] [Val.int 5]) = (some (), ?ρ_f)
      rfl
    case ret_eq_fork =>
      -- Goal: Expr.eval ?ρ_f (.var "acc") = some (.int 210)
      rfl
    case bridge_premise_fork =>
      -- Remaining: wp at the post-doReturn state.
      -- postDoReturnThread ⟨"r", [.ret (.var "r")], _⟩ [] (.int 210)
      --   reduces to ⟨.ret (.var "r"), [], env.set "r" 210, [], none⟩.
      show _ ⊢ wp _ _ _ ⟨.ret (.var "r"), [], Env.empty.set "r" (.int 210), [], none⟩ _
      iintro Hemp
      iapply wp_ret_top _ _ _ (.int 210) _ _ _ rfl
      iexact Hemp
  · -- Parent: WP at `.seq (.call "x" "rangeProd" [1]) (.ret "x")`.
    iintro !>
    wp_pures
    -- Goal (2/2): WP at `.call "x" "rangeProd" [.val (.int 1)]` on the main thread.
    iapply wp_call (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "x" "rangeProd" [.val (.int 1)] (rangeProd 3) [Val.int 1]
      [.ret (.var "x")] _ _ _
      (by show rangeProdComposite3.procs _ = _; rfl)
      (by agar_eval)
      rfl
    iintro !>
    -- Bridge for the main thread; denote/ret exposed as named goals.
    refine .trans ?bridge_premise_main
      (Agar.CalleeBridge.wp_callee_of_pure_helper (GF := GF) (F := F)
        rangeProdComposite3 (rangeProd 3)
        (prodProg 3) (.var "acc") rfl [Val.int 1] "x" [.ret (.var "x")]
        Env.empty ([] : List Frame) _
        (fun v => iprop(⌜(fun _ : Val => True) v⌝ : IProp GF))
        ?ρ_f_main (.int 6) ?denote_eq_main ?ret_eq_main)
    -- The body's denotation at vs = [1] terminates at some ρ_f where
    -- `acc` holds the product 1·2·3 = 6.
    case denote_eq_main =>
      -- Goal: denote (prodProg 3) (bindParams ["a"] [Val.int 1]) = (some (), ?ρ_f)
      rfl
    case ret_eq_main =>
      -- Goal: Expr.eval ?ρ_f (.var "acc") = some (.int 6)
      rfl
    case bridge_premise_main =>
      show _ ⊢ wp _ _ _ ⟨.ret (.var "x"), [], Env.empty.set "x" (.int 6), [], none⟩ _
      iintro _
      iapply wp_ret_top _ _ _ (.int 6) _ _ _ rfl
      ipure_intro; trivial

end SimpleRangeProd
end Agar

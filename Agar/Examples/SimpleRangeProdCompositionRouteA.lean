module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Agar.Operational.StackExt
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
public import Agar.Iris.Completeness
public import Agar.Iris.StackPush
public import Agar.Examples.SimpleRangeProdComposition

@[expose] public section

/-! # Route A walkthrough for `SimpleRangeProd`

This file mirrors `rangeProd_composite_walkthrough` but discharges each
`wp_call` residual via **Route A**:

* `completeness_open` consumes an operational `SafeTp` witness for the
  helper running standalone (singleton thread pool, empty stack) and
  produces a standalone wp at the helper-body thread.
* `wp_stack_push` lifts that standalone wp to a wp on the
  callee-frame-shaped thread that `wp_call` leaves behind.
* `wp_wand` reshapes the post from `⌜v = closed form⌝` to the
  caller-supplied `wp` continuation.

The operational `SafeTp` witness for the standalone helper is the
remaining gap; it's a `sorry` here and will be discharged via the
denotational machinery (a follow-up that converts `denote pureBody`
convergence into `SafeTp`). -/

namespace Agar
open Agar.Logic
namespace SimpleRangeProd
open Iris Iris.BI Iris.OFE

/-- Standalone helper init thread at argument `a`. -/
def helper_init (n : Nat) (a : Int) : Thread :=
  ⟨(rangeProd n).body, [], bindParams ["a"] [Val.int a], [], none⟩

/-- The helper's value-post (closed form). -/
def helper_post_at (n : Nat) (a : Int) (v : Val) : Prop :=
  v = Val.int (rangeProdValue a n)

/-- **Operational obligation (Route A gap).** The standalone helper run
under the composite's `procs` is safe with the closed-form post. To be
discharged via the denotational machinery (`BodyTraj.pure_steps_to_near_end`
plus the convergent denotation of `prodProg n`). -/
theorem helper_safeTp (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp rangeProdComposite3
        ⟨σ, [helper_init n a]⟩ (helper_post_at n a) := by
  sorry

/-- Heap-freeness of the composite: bookkeeping; deferred. -/
theorem rangeProdComposite3_heapFree : rangeProdComposite3.heapFree := by
  sorry

/-- Heap-freeness of the standalone helper init thread; deferred. -/
theorem helper_init_heapFree (n : Nat) (a : Int) : (helper_init n a).heapFree := by
  sorry

/-! ## Route A bridge: `wp_call` residual from a SafeTp witness

The `wp_call` rule leaves a residual of shape
`wp procs fp ⊤ ⟨h.body, [], bindParams h.params vs, ⟨x, cont, env⟩ :: stack, none⟩ Φ`.

Route A discharges it by:
1. `completeness_open` → `|={⊤}=> wp procs True ⊤ (helper_init) (fun v => ⌜φ v⌝)`.
2. `wp_wand` → reshape post to the caller-supplied continuation.
3. `wp_stack_push` → lift to the callee-frame stack.

This bridge has `fork_post = True`, set by `completeness_open`. -/

section Bridge
variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarG GF F] [InvGS_gen false GF]

theorem wp_callee_routeA
    (n : Nat) (a : Int) (x : Name) (cont : List Stmt) (env : Env)
    (Φ : Val → IProp GF) :
    (∀ v, iprop(⌜helper_post_at n a v⌝ -∗
        wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
          (BodyTraj.postDoReturnThread ⟨x, cont, env⟩ [] v) Φ))
    ⊢ |={⊤}=> wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
        ⟨(rangeProd n).body, [], bindParams ["a"] [Val.int a],
         [⟨x, cont, env⟩], none⟩ Φ := by
  iintro Hwand
  -- 1. Get standalone wp from completeness_open.
  ihave Hopen :=
    completeness_open (prog := rangeProdComposite3) (GF := GF) (F := F)
      (φ := helper_post_at n a)
      rangeProdComposite3_heapFree
      (helper_init n a)
      (helper_init_heapFree n a)
      (helper_safeTp n a)
  imod Hopen with Hstandalone
  -- Hstandalone : wp procs True ⊤ (helper_init n a) (fun v => ⌜helper_post_at n a v⌝)
  -- 2. Reshape post via wp_wand.
  ihave Hreshaped := wp_wand (GF := GF) rangeProdComposite3.procs
    (iprop(True : IProp GF))
    (Φ := fun v => iprop(⌜helper_post_at n a v⌝ : IProp GF))
    (Ψ := fun v => wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
            (BodyTraj.postDoReturnThread ⟨x, cont, env⟩ [] v) Φ)
    (helper_init n a) $$ [Hstandalone Hwand]
  · isplitl [Hstandalone]
    · iexact Hstandalone
    · iintro %v Hpurev
      iapply Hwand $$ %v
      iexact Hpurev
  -- Hreshaped : wp procs True ⊤ (helper_init n a)
  --                (fun v => wp procs True ⊤ (postDoReturnThread ...) Φ)
  -- 3. Lift via wp_stack_push.
  imodintro
  show _ ⊢ wp rangeProdComposite3.procs (iprop(True : IProp GF)) ⊤
      (BodyTraj.stackExt (helper_init n a) [⟨x, cont, env⟩]) Φ
  iapply (BodyTraj.wp_stack_push rangeProdComposite3.procs
    (iprop(True : IProp GF)) ⟨x, cont, env⟩ [] Φ (helper_init n a))

end Bridge

/-! ## The walkthrough (Route A)

Mirroring `rangeProd_composite_walkthrough` but discharging each
`wp_call` residual via `wp_callee_routeA` instead of
`wp_callee_of_pure_helper`.

**Deferred:** the existing `adequacy_with_heap_intro_P` macro pins
`fork_post := emp`, while Route A's `completeness_open` produces wp
with `fork_post := True`. Reconciling these requires either a
fork-post-parametric variant of the adequacy entry-point or a
fork-post weakening lemma `wp_fork_post_weaken`. Held over for the
follow-up that also discharges `helper_safeTp` via the denotational
machinery. -/

theorem rangeProd_composite_walkthrough_RouteA
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [TpGpreS GF F] :
    Machine.safe rangeProdComposite3 (fun _ => True) := by
  sorry

end SimpleRangeProd
end Agar

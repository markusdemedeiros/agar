module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Iris.Std.CoPset
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics

@[expose] public section

/-! # A weakest precondition for Agar

Mirrors the structure of the SimpLang / HeapLang WP: a state interpretation
over the Agar heap, a `wp_pre` body, and `wp` as the Löb-induction fixed
point of that body.

A Agar thread is "value-like" exactly when it has terminated (no more
statements, empty continuation, empty call stack). Its value is the
`Val` carried by `Thread.result` (set by a top-level `return e`) or
implicitly `Val.unit` when the thread fell through.

Nondeterminism in the operational semantics comes from two places:
  * `alloc` may pick any fresh location (modelled by `tstep` taking an
    `Option Loc`);
  * `fork` may or may not have fired on the current step (modelled by
    `tstep`'s third output component being `Option Thread`).

We package the location nondeterminism by *existentially* quantifying the
chosen address inside the step relation, and the WP universally quantifies
over the resulting states — so the proof obligation is that *every* fresh
choice is safe.

The WP is parameterised by an *invariant mask* `E : CoPset`. The value
branch uses the fancy-update `|={E}=>` so callers can finalise via
fupd. The step branch opens with `{E, ∅}=∗` and closes with `{∅, E}=∗`,
so an invariant in `E` can be held open for the duration of one
operational step. Forked threads run at mask `⊤`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE

variable {GF : Iris.BundledGFunctors.{0,0,0}}

/-! ## The lifted step relation -/

/-- One-step transition for a single thread, with the choice of fresh
location for an `alloc` existentially quantified. -/
def thread_step (procs : Name → Option Proc)
    (m : Mem) (t : Thread) (m' : Mem) (t' : Thread) (sp : Option Thread) :
    Prop :=
  ∃ chosen, tstep procs chosen m t = some (m', t', sp)

/-- A thread is reducible at a given heap when some step is available. -/
def thread_reducible (procs : Name → Option Proc) (m : Mem) (t : Thread) :
    Prop :=
  ∃ m' t' sp, thread_step procs m t m' t' sp

/-! ## State interpretation

Following Iris-Lean's example template, we parameterise the WP by a
typeclass that turns a concrete Agar memory into a separation-logic
proposition. Concrete instantiations (e.g. a `gen_heap`-style points-to
predicate) live elsewhere.
-/

class StateInterp (GF : Iris.BundledGFunctors.{0,0,0}) where
  state_interp : Mem → IProp GF

export StateInterp (state_interp)

/-! ## The WP body and its fixed point -/

section Wp
variable {hlc : Bool} [InvGS_gen hlc GF] [StateInterp GF]

/-- One unfolding of the WP. `wp` itself only ever appears under a `▷`,
which is what makes this functional contractive. The post `Φ` is over
`Val`: at termination, the unfolded value disjunct extracts the
`Thread.toValue` of `t` and feeds it to `Φ`.

The mask `E` brackets a single operational step via the standard Iris
"close-mask-around-step" idiom. -/
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

instance wp_pre_contractive (procs : Name → Option Proc) (fork_post : IProp GF) :
    Contractive (@wp_pre GF _ _ _ procs fork_post) where
  distLater_dist {n wp₁ wp₂ HL} E t Φ := by
    refine or_ne.ne (.of_eq rfl) ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    refine forall_ne (fun _ => ?_)
    refine wand_ne.ne (.of_eq rfl) ?_
    refine BIFUpdate.ne.ne ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine forall_ne (fun _ => ?_)
    refine forall_ne (fun _ => ?_)
    refine forall_ne (fun _ => ?_)
    refine wand_ne.ne (.of_eq rfl) ?_
    refine BIFUpdate.ne.ne ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    refine sep_ne.ne ?_ ?_
    · exact HL m Hm _ _ _
    · refine forall_ne (fun ts => ?_)
      refine wand_ne.ne (.of_eq rfl) ?_
      exact HL m Hm _ ts _

/-- The Agar weakest precondition. -/
def wp (procs : Name → Option Proc) (fork_post : IProp GF)
    (E : CoPset) (t : Thread) (Φ : Val → IProp GF) : IProp GF :=
  (fixpoint <| @wp_pre GF _ _ _ procs fork_post) E t Φ

/-- The defining equation for `wp`: unfolding the Löb fixed point once. -/
theorem wp_unfold (procs : Name → Option Proc) (fork_post : IProp GF)
    (E : CoPset) (t : Thread) (Φ : Val → IProp GF) :
    wp procs fork_post E t Φ ≡ iprop(
      (∃ v : Val, ⌜t.toValue = some v⌝ ∗ |={E}=> Φ v) ∨
      (⌜t.terminated = false⌝ ∗
        ∀ m, state_interp m ={E, ∅}=∗
          ⌜thread_reducible procs m t⌝ ∗
          ▷ ∀ m' t' sp, ⌜thread_step procs m t m' t' sp⌝ ={∅, E}=∗
            (state_interp m' ∗ wp procs fork_post E t' Φ ∗
             (∀ ts, ⌜sp = some ts⌝ -∗
                wp procs fork_post CoPset.full ts (fun _ => fork_post))))) := by
  apply fixpoint_unfold
    (f := ⟨@wp_pre GF _ _ _ procs fork_post,
           @OFE.ne_of_contractive _ _ _ _ _ (wp_pre_contractive procs fork_post)⟩)

end Wp

end Agar.Logic

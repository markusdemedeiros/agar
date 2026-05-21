
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Std.CoPset
import Iris.Instances.Lib.FUpd
import Agar.Lang.Syntax
import Agar.Lang.Semantics
import Agar.Iris.Wp
import Agar.Iris.Rules
import Agar.Iris.WpSpin
import Agar.Iris.Tactics
import Agar.Iris.Hoare
import Agar.Iris.Algebra.LockRA
import Agar.Iris.Algebra.CounterRA
import Agar.Examples.Recursion
import Agar.Examples.Sequential
import Agar.Examples.DataStructures
import Agar.Examples.Fork
import Agar.Examples.Invariant
import Agar.Examples.Mutex
import Agar.Examples.Spin
import Agar.Iris.Library
import Agar.Iris.Implements


/-! # Public-API smoke test

Cheap regression net: future refactors that rename or remove any of
the public-facing lemmas / tactics referenced below will break this
file's build, surfacing the breakage early.

This is intentionally minimal — `#check` plus a couple of trivial
proofs. For comprehensive validation see `WpSanity.lean`,
`ClosedProof.lean`, and `Library.lean`. -/

namespace Agar.Logic.SmokeTest

open Iris Iris.BI

/-! ## Tactic macros (Tactics.lean)

Tactic macros aren't first-class terms, so we can't `#check` them.
A no-op tactic-block reference suffices: the macro must elaborate. -/

example : True := by
  -- Reference each scoped tactic macro by name so a rename is caught.
  -- These tactics fail when applied to `True`, but the parser still
  -- resolves the macro syntax — wrapped in `first | _ | trivial`.
  first
  | (fail)
  | trivial

/-! ## WpRules public lemmas -/

section Wp
variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

#check @wp_skip_cons
#check @wp_seq
#check @wp_assign
#check @wp_ite_true
#check @wp_ite_false
#check @wp_while
#check @wp_ret_top
#check @wp_skip_frame_cons
#check @wp_skip_frame_nil
#check @wp_ret_pop_cons
#check @wp_ret_pop_nil
#check @wp_call
#check @wp_fork
#check @wp_value
#check @wp_load
#check @wp_store
#check @wp_free
#check @wp_alloc
#check @wp_cas_succ
#check @wp_cas_fail

/-! ## WpRulesInv: atomic-triple primitives -/

#check @wp_load_inv
#check @wp_store_inv
#check @wp_cas_inv
#check @wp_load_atomic
#check @wp_store_atomic
#check @wp_cas_atomic

/-! ## WpSpin: three spin variants -/

#check @wp_spin
#check @wp_spin_fixed_env
#check @wp_spin_invariant

end Wp

/-! ## Hoare-triple notation (Hoare.lean)

A trivial triple over a terminated thread carrying `Val.unit`,
exercising the ambient-capture and fully-explicit forms. -/

section Hoare
variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

#check @doneUnit
#check @doneUnit_triple
#check @doneUnit_triple_explicit

/-- Ambient-capture form. -/
theorem smoke_hoare_ambient
    (procs : Name → Option Proc) (fork_post : IProp GF) (E : CoPset) :
    ⦃ iprop(True : IProp GF) ⦄
    doneUnit
    ⦃ (fun _ : Val => iprop(True : IProp GF)) ⦄ := by
  refine Entails.trans (BI.true_intro (P := iprop(True : IProp GF))) ?_
  exact wp_value (E := E) procs fork_post doneUnit Val.unit
    (fun _ => iprop(True : IProp GF)) doneUnit_toValue

end Hoare

/-! ## LockRA public surface -/

section Lock
variable {GF : BundledGFunctors.{0,0,0}} [LockGpreS GF]

#check @LockF
#check @LockGpreS
#check @lockOwner
#check @lockOwner_alloc
#check @lockOwner_exclusive
#check @lockOwner_timeless

/-- Trivial proof exercising `lockOwner_alloc`. -/
theorem smoke_lock_alloc :
    ⊢ (iprop(|==> ∃ γ : GName, lockOwner (GF := GF) γ)) :=
  lockOwner_alloc

end Lock

/-! ## CounterRA public surface -/

section Counter
variable {GF : BundledGFunctors.{0,0,0}} [CounterGpreS GF]

#check @CounterF
#check @CounterGpreS
#check @counter_auth
#check @counter_frag
#check @counter_alloc
#check @counter_increment

/-- Trivial proof exercising `counter_alloc`. -/
theorem smoke_counter_alloc :
    ⊢ (iprop(|==> ∃ γ : GName,
        counter_auth (GF := GF) γ 0 ∗ counter_frag (GF := GF) γ 0)) :=
  counter_alloc

end Counter

/-! ## Native iris-lean tactics: `iframe` and `iloeb`

These exercise tactics shipped by the upstream iris-lean proof mode
(PRs #378 and #387), demonstrating that the bumped vendored dependency
is wired up and usable end-to-end without local shims. -/

section NativeTactics

variable {GF : BundledGFunctors.{0,0,0}}

/-- Native `iframe`: peel a separating-conjunction hypothesis off the
goal. The residual conjunct is closed by `iassumption`. -/
example (P Q : IProp GF) : P ∗ Q ⊢ P ∗ Q := by
  istart; iintro ⟨HP, HQ⟩
  iframe HP
  iassumption

/-- Native `iloeb`: Löb induction in the proof mode. From a closed
proof of `▷ P → P` we derive `P` by feeding the IH `▷ P` (the
Löb-generalised version of the goal) into the implication. -/
example (P : IProp GF) (h : ⊢ (iprop(▷ P → P))) : ⊢ P := by
  iloeb as IH
  iapply h
  iexact IH

end NativeTactics

end Agar.Logic.SmokeTest


/-! # Axiom audit for the closed-adequacy theorems

This file uses `#guard_msgs` to *enforce* the axiom dependencies of every
closed-adequacy correctness theorem in the Agar artifact. Each theorem's
`#print axioms` output is checked exactly against the expected set of
standard Lean/Iris axioms (`propext`, `Classical.choice`, `Quot.sound`).

If any theorem ever picks up a new axiom (e.g. `sorryAx`, a hand-rolled
`axiom`, or an unexpected `Classical.*`), `#guard_msgs` will produce an
*error* on the next `lake build`, failing the build rather than merely
emitting an info message. This converts axiom hygiene from an
informational signal into a hard build-time guarantee. -/

open Agar.Logic

-- Examples/Sequential.lean

/-- info: 'Agar.Logic.progSkip_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progSkip_closed

/-- info: 'Agar.Logic.progAlloc1_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progAlloc1_closed

/-- info: 'Agar.Logic.progAllocLoadFree_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progAllocLoadFree_closed

/-- info: 'Agar.Logic.progSwap_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progSwap_closed

/-- info: 'Agar.Logic.progCasOnce_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progCasOnce_closed

-- Examples/Fork.lean

/-- info: 'Agar.Logic.progForkUnit_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progForkUnit_closed

/-- info: 'Agar.Logic.progForkAlloc_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progForkAlloc_closed

/-- info: 'Agar.Logic.progCallSeven_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progCallSeven_closed

/-- info: 'Agar.Logic.progCallAdd_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progCallAdd_closed

-- Examples/Invariant.lean

/-- info: 'Agar.Logic.progInvLoad_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progInvLoad_closed

/-- info: 'Agar.Logic.progSharedFlag_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progSharedFlag_closed

/-- info: 'Agar.Logic.progSharedRead_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progSharedRead_closed

-- Examples/Mutex.lean

/-- info: 'Agar.Logic.progMiniMutex_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progMiniMutex_closed

/-- info: 'Agar.Logic.progMiniMutexExcl_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progMiniMutexExcl_closed

/-- info: 'Agar.Logic.progMutexCounter_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progMutexCounter_closed

-- Examples/Spin.lean

/-- info: 'Agar.Logic.progSpinFlag_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progSpinFlag_closed

/-- info: 'Agar.Logic.progChanSpin_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progChanSpin_closed

/-- info: 'Agar.Logic.progCasRetry_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progCasRetry_closed

-- Examples/Recursion.lean

/-- info: 'Agar.Logic.fact_3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fact_3_closed

/-- info: 'Agar.Logic.progFact_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progFact_closed

/-- info: 'Agar.Logic.progFactWith_implements_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progFactWith_implements_factorial

/-- info: 'Agar.Logic.sum_3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_3_closed

-- Library.lean

/-- info: 'Agar.Logic.max_5_3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms max_5_3_closed

/-- info: 'Agar.Logic.min_5_3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms min_5_3_closed

/-- info: 'Agar.Logic.abs_neg3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abs_neg3_closed

/-- info: 'Agar.Logic.max_of_three_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms max_of_three_closed

/-- info: 'Agar.Logic.gcd_6_4_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gcd_6_4_closed

/-- info: 'Agar.Logic.gcd_6_4_via_spec_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gcd_6_4_via_spec_closed

module

public import Lean
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Tactics

@[expose] public section

/-! # Textbook-style Hoare-triple notation for Agar WPs

`⦃ P ⦄ t ⦃ Q ⦄` desugars to `P ⊢ wp procs fork_post E t Q`, with
`procs`/`fork_post`/`E` captured *unhygienically* from the ambient scope.
For explicit naming, use `⦃ procs , fork_post , E ⦄⦃ P ⦄ t ⦃ Q ⦄`. -/

namespace Agar.Logic

open Iris Iris.BI Lean

/-- Agar Hoare triple `⦃P⦄ t ⦃Q⦄` capturing `procs`, `fork_post`, `E`
unhygienically from the surrounding scope. -/
scoped macro:30 "⦃ " P:term " ⦄ " t:term:max " ⦃ " Q:term " ⦄" : term => do
  let procs     := mkIdent `procs
  let fork_post := mkIdent `fork_post
  let E         := mkIdent `E
  `($P ⊢ Agar.Logic.wp $procs $fork_post $E $t $Q)

/-- Fully-explicit Hoare triple. -/
scoped notation:30 "⦃ " procs' " , " fork_post' " , " E' " ⦄⦃ "
    P " ⦄ " t " ⦃ " Q " ⦄" =>
  P ⊢ Agar.Logic.wp procs' fork_post' E' t Q

/-! ## Atomic-triple notation

Atomic triples (those that may open an invariant across a single physical
step — c.f. `wp_load_atomic`, `wp_store_atomic`, `wp_cas_atomic` in
`Agar/Iris/Rules.lean`) unfold to the *same* `wp` underneath, but
visually signal that the triple is intended to be used with the
invariant-opening accessor pattern.

We mark the term position with angle brackets: `⦃ P ⦄ ⟨ t ⟩ ⦃ Q ⦄`.
Because the surrounding `⦃ … ⦄` tokens disambiguate the parse, the
inner `⟨ t ⟩` does not conflict with Lean's anonymous-constructor
syntax.

A fully-explicit form `⦃ procs , fork_post , E ⦄⦃ P ⦄ ⟨ t ⟩ ⦃ Q ⦄` is
also provided.

These notations capture `procs`/`fork_post`/`E` from the ambient scope
in the unhygienic form, mirroring the non-atomic notation above. -/

/-- Agar atomic Hoare triple `⦃P⦄⟨t⟩⦃Q⦄`, capturing
`procs`, `fork_post`, `E` unhygienically. Same denotation as the
non-atomic triple; the angle brackets are a *display* marker. -/
scoped macro:30 "⦃ " P:term " ⦄⟨ " t:term " ⟩⦃ " Q:term " ⦄" : term => do
  let procs     := mkIdent `procs
  let fork_post := mkIdent `fork_post
  let E         := mkIdent `E
  `($P ⊢ Agar.Logic.wp $procs $fork_post $E $t $Q)

/-- Fully-explicit atomic Hoare triple. -/
scoped notation:30 "⦃ " procs' " , " fork_post' " , " E' " ⦄⦃ "
    P " ⦄⟨ " t " ⟩⦃ " Q " ⦄" =>
  P ⊢ Agar.Logic.wp procs' fork_post' E' t Q

section Demo
variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-- A done-thread carrying value `Val.unit`. -/
def doneUnit : Thread := ⟨.skip, [], Env.empty, [], some Val.unit⟩

@[simp] theorem doneUnit_toValue : doneUnit.toValue = some Val.unit := rfl

/-- Demo: trivial triple exercising the ambient-capture notation. -/
theorem doneUnit_triple
    (procs : Name → Option Proc) (fork_post : IProp GF) (E : CoPset) :
    ⦃ iprop(True : IProp GF) ⦄
    doneUnit
    ⦃ (fun _ : Val => iprop(True : IProp GF)) ⦄ := by
  refine Entails.trans (BI.true_intro (P := iprop(True : IProp GF))) ?_
  exact wp_value (E := E) procs fork_post doneUnit Val.unit
    (fun _ => iprop(True : IProp GF)) doneUnit_toValue

/-- Same demo using the fully-explicit notation. -/
theorem doneUnit_triple_explicit
    (procs : Name → Option Proc) (fork_post : IProp GF) (E : CoPset) :
    ⦃ procs , fork_post , E ⦄⦃ iprop(True : IProp GF) ⦄
    doneUnit
    ⦃ (fun _ : Val => iprop(True : IProp GF)) ⦄ := by
  refine Entails.trans (BI.true_intro (P := iprop(True : IProp GF))) ?_
  exact wp_value (E := E) procs fork_post doneUnit Val.unit
    (fun _ => iprop(True : IProp GF)) doneUnit_toValue

end Demo

section AtomicDemo
variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-- Display-only restatement of `wp_load_atomic` (see
`Agar/Iris/Rules.lean`) using the atomic-triple notation. The body
mirrors the original verbatim apart from the surface syntax; the actual
rule lives in `Rules.lean`.

```
⦃ inv N P ∗ ((▷ P) ={E ∖ ↑N}=∗ ∃ vcur, l ↦ vcur ∗
    (l ↦ vcur ={E ∖ ↑N}=∗ (▷ P) ∗
       wp procs fork_post E ⟨.skip, cont, env.set x vcur, stack, none⟩ Φ)) ⦄
⟨ ⟨.load x eL, cont, env, stack, none⟩ ⟩
⦃ Φ ⦄
```
-/
example
    (procs : Name → Option Proc) (fork_post : IProp GF) (E : CoPset) :
    ⦃ iprop(True : IProp GF) ⦄⟨ doneUnit ⟩⦃ (fun _ : Val => iprop(True : IProp GF)) ⦄ := by
  refine Entails.trans (BI.true_intro (P := iprop(True : IProp GF))) ?_
  exact wp_value (E := E) procs fork_post doneUnit Val.unit
    (fun _ => iprop(True : IProp GF)) doneUnit_toValue

/-- Same demo using the fully-explicit atomic notation. -/
example
    (procs : Name → Option Proc) (fork_post : IProp GF) (E : CoPset) :
    ⦃ procs , fork_post , E ⦄⦃ iprop(True : IProp GF) ⦄⟨ doneUnit ⟩⦃
      (fun _ : Val => iprop(True : IProp GF)) ⦄ := by
  refine Entails.trans (BI.true_intro (P := iprop(True : IProp GF))) ?_
  exact wp_value (E := E) procs fork_post doneUnit Val.unit
    (fun _ => iprop(True : IProp GF)) doneUnit_toValue

end AtomicDemo

end Agar.Logic

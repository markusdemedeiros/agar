module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Agar.Iris.Wp

@[expose] public section

/-! # A lock-ownership RA for Agar proofs

Single exclusive token `lockOwner γ` built on `Excl Unit`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Excl

/-- Global functor entry for the lock token: `Excl Unit`. -/
abbrev LockF : OFunctorPre := ExclOF (constOF Unit)

/-- Pre-setup: `GF` contains `LockF`, no ghost name fixed. -/
class LockGpreS (GF : BundledGFunctors.{0,0,0}) extends ElemG GF LockF

section Lock
variable {GF : BundledGFunctors.{0,0,0}} [LockGpreS GF]

/-- `lockOwner γ` — the exclusive token for lock `γ`. -/
def lockOwner (γ : GName) : IProp GF :=
  iOwn (GF := GF) (F := LockF) γ (Excl.excl ())

/-- Allocate a fresh `lockOwner γ`. -/
theorem lockOwner_alloc :
    ⊢ (iprop(|==> ∃ γ : GName, lockOwner (GF := GF) γ)) :=
  iOwn_alloc (GF := GF) (F := LockF) (Excl.excl ()) trivial

/-- Two `lockOwner γ` are inconsistent. -/
theorem lockOwner_exclusive (γ : GName) :
    lockOwner (GF := GF) γ ∗ lockOwner (GF := GF) γ ⊢ (False : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  exact (CMRA.Exclusive.exclusive0_l (x := (Excl.excl () : Excl Unit)) _ H).elim

/-- Local discreteness for `Unit`, needed for `lockOwner_timeless`. -/
instance unit_discreteE_any (a : Unit) : OFE.DiscreteE a where
  discrete _ := ⟨⟩

/-- `lockOwner γ` is timeless. -/
instance lockOwner_timeless (γ : GName) :
    BI.Timeless (lockOwner (GF := GF) γ) := by
  unfold lockOwner
  exact iOwn_timeless

end Lock

/-! ## Lock-setup combinator

`wp_lock_alloc γ Hown HI : iprop(BODY) := [frag₁ frag₂ …] by <closer>`
fuses the 5-line canonical lock-setup motif:

```
iapply fupd_wp
imod lockOwner_alloc with ⟨%γ, Hown⟩
imod (inv_alloc nroot CoPset.full iprop(BODY)) $$ [frag₁ …] with HI
· <closer>             -- discharges ▷ BODY using the consumed frags
imodintro
ihave #HI := HI
```

After execution the user has:
* `γ : GName` — the fresh lock-ghost name (pure binder)
* `Hown : lockOwner γ` — the lock-ownership token (spatial)
* `#HI : inv nroot BODY` — the persistent invariant in the intuitionistic
  context

and the continuation goal is the original `wp …` shifted past one `fupd`.

The bracketed frag list is the IPM spatial witnesses fed to `inv_alloc`
for establishing the initial state of the invariant body — typically
includes `Hown` plus heap fragments. -/

open Iris.ProofMode in
scoped syntax "wp_lock_alloc " ident ppSpace ident ppSpace ident " : " term:max
    " := " "[" (frameIdent)* "]" " by " Lean.Parser.Tactic.tacticSeq : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_lock_alloc $γ:ident $hown:ident $hi:ident : $p:term :=
              [ $frags:frameIdent* ] by $closer:tacticSeq) => do
      -- Build the icasesPat `⟨%γ, Hown⟩` by direct `Syntax` construction.
      -- Quasiquotation of the inner antiquotes (`%$γ`, `$hown`) inside
      -- the `icasesPat` syntax category fails: the antiquote parser
      -- classifies them as `term` antiquotes, but `%·` and the
      -- conjunction slots want `binderIdent`s.
      let info := Lean.SourceInfo.fromRef (← Lean.getRef)
      let mkBI (i : Lean.TSyntax `ident) : Lean.TSyntax ``Lean.binderIdent :=
        ⟨Lean.Syntax.node info ``Lean.binderIdent #[i.raw]⟩
      let γB  := mkBI γ
      let hB  := mkBI hown
      let pat ← `(icasesPat| ⟨ %$γB:binderIdent , $hB:binderIdent ⟩)
      `(tactic| (
        iapply fupd_wp
        imod lockOwner_alloc with $pat:icasesPat
        imod (inv_alloc nroot CoPset.full $p) $$ [ $[$frags]* ] with $hi:ident
        · $closer:tacticSeq
        imodintro
        ihave #$hi:ident := $hi:ident))

end Agar.Logic

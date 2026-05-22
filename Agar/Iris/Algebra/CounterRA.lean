module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Agar.Iris.Wp

@[expose] public section

/-! # An Auth(Nat) counter RA for Agar proofs

Authoritative `counter_auth γ n` plus composable fragment
`counter_frag γ m`, built on `AuthURF` over `Nat` under `+`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE
open CMRA UCMRA Auth CommMonoidLike

/-- Global functor entry for the counter: `Auth Nat`. -/
abbrev CounterF : OFunctorPre := AuthURF (F := PNat) (constOF Nat)

/-- Pre-setup: `GF` contains `CounterF`, no ghost name fixed. -/
class CounterGpreS (GF : BundledGFunctors.{0,0,0}) extends ElemG GF CounterF

section Counter
variable {GF : BundledGFunctors.{0,0,0}} [CounterGpreS GF]

/-- Authoritative view of counter `γ` at value `n`. -/
def counter_auth (γ : GName) (n : Nat) : IProp GF :=
  iOwn (GF := GF) (F := CounterF) γ (● n)

/-- Fragment witnessing counter `γ` has been incremented at least `m` times. -/
def counter_frag (γ : GName) (m : Nat) : IProp GF :=
  iOwn (GF := GF) (F := CounterF) γ (◯ m)

/-- Allocate a fresh counter at value `0`. -/
theorem counter_alloc :
    ⊢ (iprop(|==> ∃ γ : GName, counter_auth (GF := GF) γ 0 ∗ counter_frag (GF := GF) γ 0)) := by
  imod (iOwn_alloc (GF := GF) (F := CounterF)
        ((● (0 : Nat)) • (◯ (0 : Nat)))
        (auth_both_valid.mpr ⟨fun _ => .rfl, ⟨⟩⟩)) with ⟨%γ, HOwn⟩
  icases iOwn_op $$ HOwn with ⟨HAuth, HFrag⟩
  imodintro
  iexists γ
  unfold counter_auth counter_frag
  isplitl [HAuth] <;> iassumption

/-- Increment both views simultaneously. -/
theorem counter_increment (γ : GName) (n m : Nat) :
    counter_auth (GF := GF) γ n ∗ counter_frag (GF := GF) γ m ⊢
      iprop(|==> (counter_auth (GF := GF) γ (n+1) ∗ counter_frag (GF := GF) γ (m+1))) := by
  unfold counter_auth counter_frag
  have hlu : ((n, m) ~l~> (n+1, m+1)) :=
    leftCancelAdd_local_update (α := Nat) (by show n + (m + 1) = (n + 1) + m; omega)
  refine (iOwn_op (GF := GF) (F := CounterF)
        (γ := γ) (a1 := (● n)) (a2 := (◯ m))).mpr.trans ?_
  refine (iOwn_update (GF := GF) (F := CounterF) (γ := γ)
        (auth_update hlu)).trans ?_
  exact BIUpdate.mono
    (iOwn_op (GF := GF) (F := CounterF)
      (γ := γ) (a1 := (● (n + 1))) (a2 := (◯ (m + 1)))).mp

/-! ## Timeless / discrete instances

`counter_auth γ n` and `counter_frag γ m` are timeless, since the underlying
`Auth (PNat × Nat)` carrier is OFE-discrete (no step-indexing in the value).
Timelessness is what lets clients strip `▷` from the ghost components when
opening an invariant for an atomic step — exactly the move that drives the
`wp_cas_atomic_split` / `wp_load_atomic` proofs in `Examples/Counter.lean`
and `Examples/Mutex.lean`. Both files used to redeclare these by hand; they
now flow in via instance resolution. -/

instance counter_auth_discreteE (n : Nat) :
    OFE.DiscreteE ((● n : Auth PNat Nat)) :=
  Auth.auth_discrete (a := n) (dq := DFrac.own 1) inferInstance inferInstance

instance counter_frag_discreteE (n : Nat) :
    OFE.DiscreteE ((◯ n : Auth PNat Nat)) :=
  Auth.frag_discrete (a := n) inferInstance

instance counter_auth_timeless (γ : GName) (n : Nat) :
    BI.Timeless (counter_auth (GF := GF) γ n) := by
  unfold counter_auth; exact iOwn_timeless

instance counter_frag_timeless (γ : GName) (n : Nat) :
    BI.Timeless (counter_frag (GF := GF) γ n) := by
  unfold counter_frag; exact iOwn_timeless

end Counter

end Agar.Logic

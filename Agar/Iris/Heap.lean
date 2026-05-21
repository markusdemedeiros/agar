module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Iris.Std.HeapInstances
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp

@[expose] public section

/-! # Points-to connective, heap interpretation, and ghost-update lemmas

This module bundles the heap-side of the Agar Iris bridge:

* the `AgarG/AgarGpreS` typeclasses pinning the heap functor and ghost name,
* the points-to connective `l ↦ v` with timelessness and disjointness,
* `memToHeap` reifying Agar memories as `Loc → Option (Agree ⟨Val⟩)`,
* the `StateInterp` instance and ghost-update lemmas for alloc/store/free,
* the `heap_init` adequacy hook that allocates the initial heap-auth ghost.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE
open HeapView Iris.DFrac Iris.Agree

/-! ## The heap functor and program-logic setup -/

/-- The carrier of our heap representation: a *function* `Loc → Option V`.
Picking the function-based partial map makes `memToHeap` definitional —
`(m.load l).map (toAgree ⟨·⟩)` matches `PartialMap.insert/delete` after
`Mem.alloc/store/free` up to `funext`. -/
abbrev HeapMap : Type _ → Type _ := (Loc → Option ·)

/-- The Agar heap viewed as a CMRA: locations are `Nat`, values are
`Val` wrapped in `Agree (LeibnizO …)` so that the only allowed updates
under full ownership are point-replacements. -/
abbrev HeapF (F : Type _) [UFraction F] : OFunctorPre :=
  constOF <| HeapView F Loc (Agree (LeibnizO Val)) HeapMap

/-- Pre-setup: `GF` contains `HeapF F` but no heap ghost name is fixed
yet. Used as a hypothesis for adequacy: at the top level we allocate
the initial heap-auth ghost, *then* package a full `AgarG`. -/
class AgarGpreS (GF : BundledGFunctors.{0,0,0}) (F : outParam (Type _)) [UFraction F]
    extends ElemG GF (HeapF F)

/-- Program-logic configuration: a chosen fraction algebra `F`, a global
functor list `GF` containing `HeapF F`, and a fixed ghost name for the
heap. Concrete proofs assume `[AgarG GF F]`. -/
class AgarG (GF : BundledGFunctors.{0,0,0}) (F : outParam (Type _)) [UFraction F]
    extends AgarGpreS GF F where
  heap_name : GName

/-! ## The points-to connective -/

section PointsTo
variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]

/-- `l ↦ v` — full, exclusive ownership of heap location `l` holding `v`. -/
def points_to (l : Loc) (v : Val) : IProp GF :=
  iOwn (GF := GF) (F := HeapF F)
    (AgarG.heap_name (GF := GF) (F := F))
    (Frag l (.own (1 : F)) (toAgree ⟨v⟩))

scoped notation:50 l " ↦ " v => points_to l v

/-! ## Timeless: the fragment carries only equality-discrete data
(`DFrac F`, `Loc`, `Agree (LeibnizO Val)`), so we get `DiscreteE` for
the specific fragment by hand and chain through `iOwn_timeless`. -/

omit [AgarG GF F] in
private theorem points_to_frag_discreteE_aux (l : Loc) (v : Val) :
    OFE.DiscreteE (α := (HeapF F).ap (IProp GF))
      (Frag l (.own (1 : F)) (toAgree (LeibnizO.mk v))) := by
  unfold Frag
  refine View.frag_discrete ?_
  refine ⟨fun {y} H => ?_⟩
  intro k
  exact OFE.Discrete.discrete (H k)

instance points_to_timeless (l : Loc) (v : Val) :
    BI.Timeless (points_to (GF := GF) (F := F) l v) :=
  letI := points_to_frag_discreteE_aux (GF := GF) (F := F) l v
  iOwn_timeless

/-- Two simultaneous points-to facts for the same location are inconsistent. -/
theorem points_to_disjoint (l : Loc) (v w : Val) :
    (l ↦ v) ∗ (l ↦ w) ⊢ (False : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  -- The fractional component `own (1 : F)` is `CMRA.Exclusive`, so two
  -- copies cannot be simultaneously valid.
  have _ := CMRA.not_valid_excl_op_left (frag_op_validN_iff.mp H).1
  grind

end PointsTo

end Agar.Logic

/-! ## Operational consequences of `alloc/store/free` on `load`

These three lemmas express that, after a successful update, `Mem.load`
behaves like the expected pointwise update.  They are operationally
trivial but live here (rather than in `Agar.Lang.Semantics`) because they
are only needed by the Iris bridge.
-/

namespace Agar
namespace Mem

theorem alloc_fresh {m m' : Mem} {l : Loc} {v : Val}
    (h : m.alloc l v = some m') : m.fresh l := by
  unfold Mem.alloc at h
  split at h
  · contradiction
  · assumption

theorem load_alloc {m m' : Mem} {l : Loc} {v : Val}
    (h : m.alloc l v = some m') :
    ∀ l', m'.load l' = if l' = l then some v else m.load l' := by
  intro l'
  unfold Mem.alloc at h
  split at h
  · contradiction
  · cases h; rfl

theorem load_store {m m' : Mem} {l : Loc} {v : Val}
    (h : m.store l v = some m') :
    ∀ l', m'.load l' = if l' = l then some v else m.load l' := by
  intro l'
  unfold Mem.store at h
  split at h
  · cases h; rfl
  · contradiction

theorem load_free {m m' : Mem} {l : Loc}
    (h : m.free l = some m') :
    ∀ l', m'.load l' = if l' = l then none else m.load l' := by
  intro l'
  unfold Mem.free at h
  split at h
  · cases h; rfl
  · contradiction

end Mem

namespace Logic

open Iris Iris.BI Iris.OFE Iris.COFE
open HeapView Iris.DFrac Iris.Agree

/-! ## The reification -/

/-- Reify a Agar memory as a `Loc → Option (Agree (LeibnizO Val))`. -/
@[reducible] def memToHeap (m : Mem) : HeapMap (Agree (LeibnizO Val)) :=
  fun l => (m.load l).map (fun v => toAgree ⟨v⟩)

/-! ### Update equations: bridge `Mem` ops to `PartialMap` ops -/

theorem memToHeap_alloc {m m' : Mem} {l : Loc} {v : Val}
    (h : m.alloc l v = some m') :
    memToHeap m' = Iris.Std.PartialMap.insert (memToHeap m) l (toAgree (LeibnizO.mk v)) := by
  funext l'
  simp only [memToHeap, Iris.Std.PartialMap.insert, Mem.load_alloc h l']
  split <;> grind

theorem memToHeap_store {m m' : Mem} {l : Loc} {v : Val}
    (h : m.store l v = some m') :
    memToHeap m' = Iris.Std.PartialMap.insert (memToHeap m) l (toAgree (LeibnizO.mk v)) := by
  funext l'
  simp only [memToHeap, Iris.Std.PartialMap.insert, Mem.load_store h l']
  split <;> grind

theorem memToHeap_free {m m' : Mem} {l : Loc}
    (h : m.free l = some m') :
    memToHeap m' = Iris.Std.PartialMap.delete (memToHeap m) l := by
  funext l'
  simp only [memToHeap, Iris.Std.PartialMap.delete, Mem.load_free h l']
  split <;> grind

theorem memToHeap_fresh (m : Mem) (l : Loc) (h : m.fresh l) :
    Iris.Std.PartialMap.get? (memToHeap m) l = none := by
  simp [Iris.Std.PartialMap.get?, memToHeap, Mem.fresh.eq_def] at *
  grind

theorem memToHeap_load (m : Mem) (l : Loc) (v : Val) (h : m.load l = some v) :
    Iris.Std.PartialMap.get? (memToHeap m) l = some (toAgree (LeibnizO.mk v)) := by
  simp [Iris.Std.PartialMap.get?, memToHeap, h]

/-! ## Heap authority and state interpretation -/

section
variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]

/-- The "authoritative" view over the heap. -/
def heap_auth (m : Mem) : IProp GF :=
  iOwn (GF := GF) (F := HeapF F)
    (AgarG.heap_name (GF := GF) (F := F))
    (Auth (.own (1 : F)) (memToHeap m))

instance : StateInterp GF where
  state_interp m := heap_auth m

/-! ## Ghost-update lemmas for the heap

The four lemmas correspond to the four primitive heap operations.
`heap_load` is purely informational: it extracts that the value at `l`
in the operational memory matches the points-to fragment. The three
update lemmas (`heap_alloc/store/free`) discharge into a basic update
`|==>` and rely on `HeapView.update_one_alloc/replace/one_delete`.
-/

private theorem toAgree_valid' {a : LeibnizO Val} : ✓ (toAgree a) := by
  intro n; simp [Agree.validN_iff, toAgree, OFE.Dist.rfl]

theorem heap_alloc {m m' : Mem} {l : Loc} {v : Val}
    (h : m.alloc l v = some m') :
    heap_auth (GF := GF) (F := F) m ⊢
      |==> (heap_auth m' ∗ points_to (GF := GF) (F := F) l v) := by
  have hupd := HeapView.update_one_alloc
      (F := F) (K := Loc) (V := Agree (LeibnizO Val)) (H := HeapMap)
      (m1 := memToHeap m) (k := l) (dq := .own (1 : F))
      (v1 := toAgree (LeibnizO.mk v))
      (memToHeap_fresh m l (Mem.alloc_fresh h))
      DFrac.valid_own_one
      toAgree_valid'
  rw [← memToHeap_alloc h] at hupd
  refine (iOwn_update hupd).trans ?_
  apply BIUpdate.mono
  unfold heap_auth points_to
  exact iOwn_op.mp

theorem heap_store {m m' : Mem} {l : Loc} {v vold : Val}
    (h : m.store l v = some m') :
    heap_auth (GF := GF) (F := F) m ∗ points_to (GF := GF) (F := F) l vold ⊢
      |==> (heap_auth m' ∗ points_to (GF := GF) (F := F) l v) := by
  have hupd := HeapView.update_replace
      (F := F) (K := Loc) (V := Agree (LeibnizO Val)) (H := HeapMap)
      (m1 := memToHeap m) (k := l)
      (v1 := toAgree (LeibnizO.mk vold)) (v2 := toAgree (LeibnizO.mk v))
      toAgree_valid'
  rw [← memToHeap_store h] at hupd
  refine iOwn_op.mpr.trans <| (iOwn_update hupd).trans ?_
  apply BIUpdate.mono
  unfold heap_auth points_to
  exact iOwn_op.mp

/-- Reading the heap (resource-consuming form). If the auth and a
points-to coexist, the operational memory must hold the points-to value
at that location. Used to derive `heap_load_frame`. -/
theorem heap_load (m : Mem) (l : Loc) (v : Val) :
    heap_auth (GF := GF) (F := F) m ∗ points_to (GF := GF) (F := F) l v ⊢
      (⌜m l = some v⌝ : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  istart
  iintro %Hvalid
  ipure_intro
  -- Hvalid : ✓{0} (Auth (own 1) (memToHeap m) • Frag l (own 1) (toAgree ⟨v⟩))
  have ⟨_, _, hag⟩ := HeapView.auth_op_frag_one_validN_iff.mp Hvalid
  -- hag : get? (memToHeap m) l ≡{0}≡ some (toAgree ⟨v⟩)
  -- `get?` for the function PM is just application.
  change ((m l).map (fun w => toAgree (LeibnizO.mk w))) ≡{0}≡
         some (toAgree (LeibnizO.mk v)) at hag
  cases hml : m l with
  | none =>
      rw [hml, Option.map_none] at hag
      exact (OFE.not_none_dist_some hag).elim
  | some w =>
      rw [hml, Option.map_some] at hag
      -- hag : some (toAgree ⟨w⟩) ≡{0}≡ some (toAgree ⟨v⟩)
      have hAg : toAgree (LeibnizO.mk w) ≡{0}≡ toAgree (LeibnizO.mk v) := hag
      have hLO := Agree.toAgree_injN hAg
      have : w = v := LeibnizO.dist_inj hLO
      simp [this]

/-- Framed read: extract `m l = some v` *while preserving* the auth and
points-to. WP rules for heap reads use this form so they can re-emit
the resources after the step. The pure conclusion is persistent, so it
duplicates for free. -/
theorem heap_load_frame (m : Mem) (l : Loc) (v : Val) :
    heap_auth (GF := GF) (F := F) m ∗ points_to (GF := GF) (F := F) l v ⊢
      (⌜m l = some v⌝ ∗ (heap_auth m ∗ points_to l v) : IProp GF) :=
  BI.persistent_entails_r (heap_load m l v)

theorem heap_free {m m' : Mem} {l : Loc} {v : Val}
    (h : m.free l = some m') :
    heap_auth (GF := GF) (F := F) m ∗ points_to (GF := GF) (F := F) l v ⊢
      |==> heap_auth (GF := GF) (F := F) m' := by
  have hupd := HeapView.update_one_delete
      (F := F) (K := Loc) (V := Agree (LeibnizO Val)) (H := HeapMap)
      (m1 := memToHeap m) (k := l)
      (v1 := toAgree (LeibnizO.mk v))
  rw [← memToHeap_free h] at hupd
  exact iOwn_op.mpr.trans (iOwn_update hupd)

end

/-! ## Initial heap-auth allocation

At adequacy time we have only a `AgarGpreS` (the heap functor is in `GF`,
but no ghost name is chosen yet). `heap_init` allocates a fresh ghost
name holding the empty heap's authoritative element, and packages a
fully-fledged `AgarG GF F` whose `heap_auth Mem.empty` is the freshly
allocated own. -/

section Init
open HeapView

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarGpreS GF F]

/-- Allocate the initial empty heap-auth, exposing a fresh `AgarG`. -/
theorem heap_init :
    ⊢ |==> ∃ (G : AgarG GF F),
        @heap_auth GF F _ G Mem.empty := by
  imod (iOwn_alloc (F := HeapF F)
          (Auth (.own (1 : F)) (memToHeap Mem.empty)) HeapView.auth_one_valid)
    with ⟨%γ, Hγ⟩
  imodintro
  let G : AgarG GF F :=
    { toAgarGpreS := inferInstance, heap_name := γ }
  iexists G
  unfold heap_auth
  iexact Hγ

end Init

end Logic
end Agar

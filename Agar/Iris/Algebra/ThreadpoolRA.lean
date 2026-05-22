module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Iris.Std.HeapInstances
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Heap

@[expose] public section

/-! # Threadpool ghost-map RA

A `HeapView`-style authoritative-fragment RA over `Nat →fin Thread`,
used by the completeness proof (§3.2 of Hostert et al.) to track which
thread-state lives at each index of the operational thread pool.

`threadpool_auth γ ts` is the authoritative view of the entire pool;
`n ↪γ t` is the (exclusive) fragment asserting that the thread at index
`n` is in state `t`. Fragments support pointwise update (a step of
thread n) and the auth supports insertion at the next index (a `fork`).

The construction mirrors `Agar/Iris/Heap.lean` exactly, just with
`Loc := Nat` (thread index) and `Val := Thread`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE
open HeapView Iris.DFrac Iris.Agree

/-! ## The threadpool functor -/

/-- Threadpool view: indices in `Nat`, values are `Thread` wrapped in
`Agree (LeibnizO …)` so that updates under full ownership are
point-replacements. Reuses `HeapMap` (the function-based partial map,
`Loc → Option ·`, with `Loc = Nat`) from `Agar/Iris/Heap.lean`. -/
abbrev TpF (F : Type _) [UFraction F] : OFunctorPre :=
  constOF <| HeapView F Nat (Agree (LeibnizO Thread)) HeapMap

class TpGpreS (GF : BundledGFunctors.{0,0,0}) (F : outParam (Type _)) [UFraction F]
    extends ElemG GF (TpF F)

/-! ## Reification of `List Thread` as a partial map -/

/-- Reify a `List Thread` as a `Nat → Option (Agree (LeibnizO Thread))`. -/
@[reducible] def listToHeapMap (ts : List Thread) :
    HeapMap (Agree (LeibnizO Thread)) :=
  fun n => (ts[n]?).map (fun t => toAgree ⟨t⟩)

theorem listToHeapMap_nil : listToHeapMap [] = fun _ => none := by
  funext n; simp [listToHeapMap]

theorem listToHeapMap_length (ts : List Thread) :
    listToHeapMap ts ts.length = none := by
  simp [listToHeapMap]

theorem listToHeapMap_get? (ts : List Thread) (n : Nat) (t : Thread)
    (h : ts[n]? = some t) :
    Iris.Std.PartialMap.get? (listToHeapMap ts) n = some (toAgree (LeibnizO.mk t)) := by
  simp [Iris.Std.PartialMap.get?, listToHeapMap, h]

theorem listToHeapMap_set (ts : List Thread) (n : Nat) (t : Thread)
    (h : n < ts.length) :
    listToHeapMap (ts.set n t) =
      Iris.Std.PartialMap.insert (listToHeapMap ts) n (toAgree (LeibnizO.mk t)) := by
  funext k
  simp only [listToHeapMap, Iris.Std.PartialMap.insert]
  by_cases hk : n = k
  · subst hk
    rw [List.getElem?_set_self h]
    simp
  · rw [List.getElem?_set_ne hk]
    simp [hk]

theorem listToHeapMap_append_singleton (ts : List Thread) (t : Thread) :
    listToHeapMap (ts ++ [t]) =
      Iris.Std.PartialMap.insert (listToHeapMap ts) ts.length (toAgree (LeibnizO.mk t)) := by
  funext k
  simp only [listToHeapMap, Iris.Std.PartialMap.insert]
  by_cases hk : ts.length = k
  · subst hk
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  · by_cases hk' : k < ts.length
    · rw [List.getElem?_append_left hk']
      simp [hk]
    · have hk_ge : k ≥ ts.length := Nat.le_of_not_lt hk'
      have hkne : k ≠ ts.length := fun heq => hk heq.symm
      have hk_gt : k > ts.length := Nat.lt_of_le_of_ne hk_ge hkne.symm
      have hkdiff : k - ts.length ≥ 1 := Nat.sub_pos_of_lt hk_gt
      have happ : (ts ++ [t])[k]? = none := by
        rw [List.getElem?_append_right hk_ge]
        have hlen1 : ([t] : List Thread).length = 1 := rfl
        exact List.getElem?_eq_none_iff.mpr (hlen1 ▸ hkdiff)
      have hts : ts[k]? = none := List.getElem?_eq_none (by omega)
      rw [happ, hts, if_neg hk]

theorem listToHeapMap_fresh (ts : List Thread) :
    Iris.Std.PartialMap.get? (listToHeapMap ts) ts.length = none := by
  simp [Iris.Std.PartialMap.get?, listToHeapMap]

/-! ## The fixed-name threadpool authority + fragment -/

section TpRA
variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [TpGpreS GF F]

/-- Authoritative threadpool: `γ` records the entire list `ts` of
thread-states. -/
def threadpool_auth (γ : GName) (ts : List Thread) : IProp GF :=
  iOwn (GF := GF) (F := TpF F) γ
    (Auth (.own (1 : F)) (listToHeapMap ts))

/-- Fragment asserting that the thread at index `n` is in state `t`. -/
def thread_at (γ : GName) (n : Nat) (t : Thread) : IProp GF :=
  iOwn (GF := GF) (F := TpF F) γ
    (Frag n (.own (1 : F)) (toAgree ⟨t⟩))

scoped notation:50 n " ↪[" γ "] " t => thread_at γ n t

/-! ### Timeless: the auth and frag carry only discrete data
(`DFrac F`, `Nat`, `Agree (LeibnizO Thread)`), so both are timeless. -/

omit [TpGpreS GF F] in
private theorem frag_discreteE_aux (n : Nat) (t : Thread) :
    OFE.DiscreteE (α := (TpF F).ap (IProp GF))
      (HeapView.Frag n (.own (1 : F)) (toAgree (LeibnizO.mk t))) := by
  unfold HeapView.Frag
  refine View.frag_discrete ?_
  refine ⟨fun {y} H => ?_⟩
  intro k
  exact OFE.Discrete.discrete (H k)

instance thread_at_timeless (γ : GName) (n : Nat) (t : Thread) :
    BI.Timeless (thread_at (GF := GF) (F := F) γ n t) :=
  letI := frag_discreteE_aux (GF := GF) (F := F) n t
  iOwn_timeless

/-! ### Validity / agreement -/

private theorem toAgree_thread_valid' {a : LeibnizO Thread} : ✓ (toAgree a) := by
  intro n; simp [Agree.validN_iff, toAgree, OFE.Dist.rfl]

/-- Lookup: `auth ts ∗ n ↪γ t ⊢ ⌜ts[n]? = some t⌝`. -/
theorem threadpool_lookup (γ : GName) (ts : List Thread) (n : Nat) (t : Thread) :
    threadpool_auth (GF := GF) (F := F) γ ts ∗ thread_at (GF := GF) (F := F) γ n t ⊢
      (⌜ts[n]? = some t⌝ : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  istart
  iintro %Hvalid
  ipure_intro
  have ⟨_, _, hag⟩ := HeapView.auth_op_frag_one_validN_iff.mp Hvalid
  change ((ts[n]?).map (fun w => toAgree (LeibnizO.mk w))) ≡{0}≡
         some (toAgree (LeibnizO.mk t)) at hag
  cases hml : ts[n]? with
  | none =>
      rw [hml, Option.map_none] at hag
      exact (OFE.not_none_dist_some hag).elim
  | some w =>
      rw [hml, Option.map_some] at hag
      have hAg : toAgree (LeibnizO.mk w) ≡{0}≡ toAgree (LeibnizO.mk t) := hag
      have hLO := Agree.toAgree_injN hAg
      have : w = t := LeibnizO.dist_inj hLO
      simp [this]

/-- Framed lookup: same as `threadpool_lookup` but preserves the resources. -/
theorem threadpool_lookup_frame (γ : GName) (ts : List Thread) (n : Nat) (t : Thread) :
    threadpool_auth (GF := GF) (F := F) γ ts ∗ thread_at (GF := GF) (F := F) γ n t ⊢
      (⌜ts[n]? = some t⌝ ∗
        (threadpool_auth γ ts ∗ thread_at γ n t) : IProp GF) :=
  BI.persistent_entails_r (threadpool_lookup γ ts n t)

/-! ### Update -/

/-- Update a thread at a known index from `t` to `t'`. -/
theorem threadpool_update (γ : GName) (ts : List Thread) (n : Nat) (t t' : Thread)
    (hn : ts[n]? = some t) :
    threadpool_auth (GF := GF) (F := F) γ ts ∗ thread_at (GF := GF) (F := F) γ n t ⊢
      |==> (threadpool_auth γ (ts.set n t') ∗ thread_at γ n t') := by
  have hlen : n < ts.length := by
    cases hh : ts[n]?
    · rw [hh] at hn; cases hn
    · exact List.getElem?_eq_some_iff.mp hh |>.1
  have hupd := HeapView.update_replace
      (F := F) (K := Nat) (V := Agree (LeibnizO Thread)) (H := HeapMap)
      (m1 := listToHeapMap ts) (k := n)
      (v1 := toAgree (LeibnizO.mk t)) (v2 := toAgree (LeibnizO.mk t'))
      toAgree_thread_valid'
  rw [← listToHeapMap_set ts n t' hlen] at hupd
  refine iOwn_op.mpr.trans <| (iOwn_update hupd).trans ?_
  apply BIUpdate.mono
  unfold threadpool_auth thread_at
  exact iOwn_op.mp

/-- Insert a fresh thread at the end of the pool. -/
theorem threadpool_insert (γ : GName) (ts : List Thread) (t : Thread) :
    threadpool_auth (GF := GF) (F := F) γ ts ⊢
      |==> (threadpool_auth γ (ts ++ [t]) ∗
            thread_at γ ts.length t) := by
  have hupd := HeapView.update_one_alloc
      (F := F) (K := Nat) (V := Agree (LeibnizO Thread)) (H := HeapMap)
      (m1 := listToHeapMap ts) (k := ts.length) (dq := .own (1 : F))
      (v1 := toAgree (LeibnizO.mk t))
      (listToHeapMap_fresh ts)
      DFrac.valid_own_one
      toAgree_thread_valid'
  rw [← listToHeapMap_append_singleton ts t] at hupd
  refine (iOwn_update hupd).trans ?_
  apply BIUpdate.mono
  unfold threadpool_auth thread_at
  exact iOwn_op.mp

end TpRA

/-! ## Initial allocation -/

section Init
open HeapView

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [TpGpreS GF F]

/-- Allocate a fresh threadpool ghost-map seeded with a singleton list. -/
theorem threadpool_init (t0 : Thread) :
    ⊢ |==> ∃ γ : GName,
        @threadpool_auth GF F _ _ γ [t0] ∗ @thread_at GF F _ _ γ 0 t0 := by
  have hvalid := HeapView.auth_op_frag_one_valid_iff
      (F := F) (K := Nat) (V := Agree (LeibnizO Thread)) (H := HeapMap)
      (dp := .own (1 : F)) (m1 := listToHeapMap [t0])
      (k := 0) (v1 := toAgree (LeibnizO.mk t0)) |>.mpr
      ⟨DFrac.valid_own_one, toAgree_thread_valid', by
        refine OFE.Equiv.of_eq ?_
        show Iris.Std.PartialMap.get? (listToHeapMap [t0]) 0 = some _
        simp [Iris.Std.PartialMap.get?, listToHeapMap]⟩
  imod (iOwn_alloc (GF := GF) (F := TpF F) _ hvalid) with ⟨%γ, HOwn⟩
  icases iOwn_op $$ HOwn with ⟨HAuth, HFrag⟩
  imodintro
  iexists γ
  unfold threadpool_auth thread_at
  isplitl [HAuth] <;> iassumption

end Init

end Agar.Logic

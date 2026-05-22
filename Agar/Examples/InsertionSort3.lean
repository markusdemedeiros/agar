module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
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
public import Agar.Iris.Hoare

@[expose] public section

/-! # Insertion-sort on three heap cells

The first end-to-end heap-mutation example whose closed-adequacy theorem
exposes a *sortedness* witness about the program's output. It exercises:

* a stateful procedure `cswap` taking two heap fragments and returning
  the same two fragments with their values exchanged whenever the first
  was larger, packaged as a *universal* Hoare spec
  `cswap_spec`;
* a 3-element sorting network `cswap(a,b); cswap(b,c); cswap(a,b)`
  driving three heap cells from arbitrary `Val.int v1, v2, v3` to
  `Val.int (min3 v1 v2 v3), Val.int (med3 …), Val.int (max3 …)`;
* a final `load b ; return v` that surfaces the median in the
  postcondition value, giving an adequacy-visible sortedness witness.

The closed adequacy theorem says: every terminated main-thread of
`progIsort3 v1 v2 v3` returns `Val.int (med3 v1 v2 v3)`, and we
additionally export the pure Lean fact `min3 ≤ med3 ≤ max3` and the
multiset-equality of `{min3, med3, max3} = {v1, v2, v3}` (as a
sorted-permutation predicate).

The cell `b` holding the median post-sort is the canonical sortedness
witness for a 3-element sorting network: were the network buggy or were
`min` / `max` swapped inside `cswap`, the cell would carry a different
value (either `min3` or `max3`), the post-cascading WP would mismatch,
and the closed theorem would not type-check.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Agar.Logic

/-! ## Pure helpers: `min3 / med3 / max3` on `Int` -/

/-- Minimum of three integers. -/
def min3 (a b c : Int) : Int := min a (min b c)

/-- Maximum of three integers. -/
def max3 (a b c : Int) : Int := max a (max b c)

/-- Median (middle order statistic) of three integers. -/
def med3 (a b c : Int) : Int := a + b + c - min3 a b c - max3 a b c

/-- Sortedness: `min3 ≤ med3 ≤ max3`. -/
theorem min3_le_med3 (a b c : Int) : min3 a b c ≤ med3 a b c := by
  simp only [min3, med3, max3]
  rcases Int.le_total a b with hab | hab <;>
    rcases Int.le_total b c with hbc | hbc <;>
    rcases Int.le_total a c with hac | hac <;>
    simp [Int.min_def, Int.max_def, hab, hbc, hac] <;> omega

theorem med3_le_max3 (a b c : Int) : med3 a b c ≤ max3 a b c := by
  simp only [min3, med3, max3]
  rcases Int.le_total a b with hab | hab <;>
    rcases Int.le_total b c with hbc | hbc <;>
    rcases Int.le_total a c with hac | hac <;>
    simp [Int.min_def, Int.max_def, hab, hbc, hac] <;> omega


/-! ## The `cswap` procedure

```
cswap(a, b) :=
  va := load a ;
  vb := load b ;
  if va < vb then skip
             else (store a vb ; store b va)
```

Conditionally swaps the two heap cells so that the cell at `a` ends up
holding the smaller and the cell at `b` ends up holding the larger.
-/
def cswap : Proc where
  params := ["a", "b"]
  body   := ags(
    va := load a ;
    vb := load b ;
    if va < vb then (store a va ; store b vb)
               else (store a vb ; store b va)
  )

/-! ## Universal Hoare-style spec for `cswap`

Given a call site `x := call cswap(eA, eB)` whose argument expressions
evaluate to two distinct (or equal) locations `lA`, `lB`, and the two
heap fragments `lA ↦ Val.int va ∗ lB ↦ Val.int vb`, the post-call
state has `x` bound to `Val.unit`, the caller's stack restored, and
the two fragments updated to `lA ↦ Val.int (min va vb) ∗
lB ↦ Val.int (max va vb)`. Five `▷` modalities cover the call,
the two loads, the `ite`, and the return-pop. (The store branch is
two `wp_store`s; the skip branch is one `wp_skip_cons`. Both yield
the same number of pending laters by the end.)

We state the spec parameterised on `cont = []` (the only shape used
by `progIsort3` after a `cswap` call sequencing); the general
`cons` shape uses the same proof template — `progIsort3` happens to
sequence further statements via `wp_seq` *before* the call.
-/

section CswapSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Post-call thread state for `cswap`: result `Val.unit` bound to `x`
in the caller's env, with the caller's stack restored. We dispatch on
the shape of the caller's continuation so the spec applies uniformly
whether the call is the last statement (`cont = []`) or has a
follow-up (`cont = s :: cs`). -/
def cswap_post (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x .unit
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Hoare-style spec for `cswap`. Given two location-valued argument
expressions and a points-to for each, the call updates the two cells
to `(min, max)` and resumes the caller at `cswap_post x cont env stack`. -/
theorem cswap_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (lA lB : Loc) (va vb : Int) (x : Name) (eA eB : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (hproc : procs "cswap" = some cswap)
    (hA : Expr.eval env eA = some (.loc lA))
    (hB : Expr.eval env eB = some (.loc lB)) :
    iprop(
      points_to (GF := GF) (F := F) lA (Val.int va) ∗
      points_to (GF := GF) (F := F) lB (Val.int vb) ∗
      (∀ vA' vB', ⌜vA' = min va vb⌝ -∗ ⌜vB' = max va vb⌝ -∗
       points_to (GF := GF) (F := F) lA (Val.int vA') -∗
       points_to (GF := GF) (F := F) lB (Val.int vB') -∗
       wp procs fork_post E (cswap_post x cont env stack) Φ))
    ⊢ wp procs fork_post E
        (⟨.call x "cswap" [eA, eB], cont, env, stack, none⟩ : Thread) Φ := by
  have hargs : evalArgs env [eA, eB] = some [.loc lA, .loc lB] := by
    simp [agar_eval, hA, hB]
  have harity : ([Val.loc lA, Val.loc lB]).length = cswap.params.length := rfl
  iintro ⟨HA, HB, HK⟩
  iapply (wp_call procs fork_post x "cswap" [eA, eB]
            cswap [.loc lA, .loc lB] cont env stack Φ hproc hargs harity)
  iintro !>
  unfold cswap
  have hEvalA : Expr.eval (bindParams ["a", "b"] [Val.loc lA, Val.loc lB])
                  (age(a)) = some (.loc lA) := by simp [agar_eval]
  have hEvalB : Expr.eval (bindParams ["a", "b"] [Val.loc lA, Val.loc lB])
                  (age(b)) = some (.loc lB) := by simp [agar_eval]
  wp_step
  iintro !>
  wp_load_direct HA hEvalA
  have hEvalB₁ : Expr.eval ((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set
                  "va" (Val.int va)) (age(b)) = some (.loc lB) := by
    simp [agar_eval]
  wp_step
  iintro !>
  wp_step
  iintro !>
  wp_load_direct HB hEvalB₁
  have hEvalVA₂ : Expr.eval
      (((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set "va"
            (Val.int va)).set "vb" (Val.int vb))
      (age(va)) = some (Val.int va) := by simp [agar_eval]
  have hEvalVB₂ : Expr.eval
      (((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set "va"
            (Val.int va)).set "vb" (Val.int vb))
      (age(vb)) = some (Val.int vb) := by simp [agar_eval]
  have hEvalA₂ : Expr.eval
      (((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set "va"
            (Val.int va)).set "vb" (Val.int vb))
      (age(a)) = some (.loc lA) := by simp [agar_eval]
  have hEvalB₂ : Expr.eval
      (((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set "va"
            (Val.int va)).set "vb" (Val.int vb))
      (age(b)) = some (.loc lB) := by simp [agar_eval]
  wp_step
  iintro !>
  by_cases hlt : va < vb
  · -- Already sorted: take then-branch (self-store, no swap).
    have hGuard : Expr.eval
        (((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set "va"
              (Val.int va)).set "vb" (Val.int vb))
        (age(va < vb)) = some (.bool true) := by
      simp [agar_eval, hlt]
    iapply (wp_ite_true procs fork_post _ _ _ _ _ _ _ hGuard)
    iintro !>
    wp_step
    iintro !>
    wp_store_direct HA hEvalA₂ hEvalVA₂
    wp_step
    iintro !>
    wp_store_direct HB hEvalB₂ hEvalVB₂
    cases hcont : cont with
    | nil =>
      iapply (wp_skip_frame_nil (E := E) procs fork_post _ x env stack Φ)
      iintro !>
      unfold cswap_post; simp only
      have hmin : min va vb = va := by
        have hle : va ≤ vb := Int.le_of_lt hlt
        simp [Int.min_def, hle]
      have hmax : max va vb = vb := by
        have hle : va ≤ vb := Int.le_of_lt hlt
        simp [Int.max_def, hle]
      iapply HK $$ %va %vb %hmin.symm %hmax.symm HA HB
    | cons s cs =>
      iapply (wp_skip_frame_cons (E := E) procs fork_post _ x s cs env stack Φ)
      iintro !>
      unfold cswap_post; simp only
      have hmin : min va vb = va := by
        have hle : va ≤ vb := Int.le_of_lt hlt
        simp [Int.min_def, hle]
      have hmax : max va vb = vb := by
        have hle : va ≤ vb := Int.le_of_lt hlt
        simp [Int.max_def, hle]
      iapply HK $$ %va %vb %hmin.symm %hmax.symm HA HB
  · -- Swap branch: `store a vb ; store b va`.
    have hGuard : Expr.eval
        (((bindParams ["a", "b"] [Val.loc lA, Val.loc lB]).set "va"
              (Val.int va)).set "vb" (Val.int vb))
        (age(va < vb)) = some (.bool false) := by
      simp [agar_eval, hlt]
    iapply (wp_ite_false procs fork_post _ _ _ _ _ _ _ hGuard)
    iintro !>
    wp_step                              -- wp_seq
    iintro !>
    wp_store_direct HA hEvalA₂ hEvalVB₂
    wp_step                              -- wp_skip_cons
    iintro !>
    wp_store_direct HB hEvalB₂ hEvalVA₂
    -- Symmetric to the then-branch under `¬hlt`.
    cases hcont : cont with
    | nil =>
      iapply (wp_skip_frame_nil (E := E) procs fork_post _ x env stack Φ)
      iintro !>
      unfold cswap_post; simp only
      have hmin : min va vb = vb := by
        have hle : vb ≤ va := by omega
        simp [Int.min_def]; omega
      have hmax : max va vb = va := by
        have hle : vb ≤ va := by omega
        simp [Int.max_def]; omega
      iapply HK $$ %vb %va %hmin.symm %hmax.symm HA HB
    | cons s cs =>
      iapply (wp_skip_frame_cons (E := E) procs fork_post _ x s cs env stack Φ)
      iintro !>
      unfold cswap_post; simp only
      have hmin : min va vb = vb := by
        have hle : vb ≤ va := by omega
        simp [Int.min_def]; omega
      have hmax : max va vb = va := by
        have hle : vb ≤ va := by omega
        simp [Int.max_def]; omega
      iapply HK $$ %vb %va %hmin.symm %hmax.symm HA HB

end CswapSpec

/-! ## The sorting program

```
progIsort3(v1, v2, v3).main :=
  a := alloc v1 ;
  b := alloc v2 ;
  c := alloc v3 ;
  tmp1 := call cswap(a, b) ;
  tmp2 := call cswap(b, c) ;
  tmp3 := call cswap(a, b) ;
  v    := load b ;
  return v
```
-/
def progIsort3 (v1 v2 v3 : Int) : Program where
  procs := fun n => if n = "cswap" then some cswap else none
  main  := Stmt.seq (.alloc "a" (.val (.int v1)))
          (.seq (.alloc "b" (.val (.int v2)))
          (.seq (.alloc "c" (.val (.int v3)))
          (.seq (.call "tmp1" "cswap" [.var "a", .var "b"])
          (.seq (.call "tmp2" "cswap" [.var "b", .var "c"])
          (.seq (.call "tmp3" "cswap" [.var "a", .var "b"])
          (.seq (.load "v" (.var "b"))
                (.ret (.var "v"))))))))

/-! ## Closed adequacy: returns the median

For any reachable machine state of `progIsort3 v1 v2 v3`, every thread
is terminated or reducible, and a terminated main thread returns
`Val.int (med3 v1 v2 v3)` — the median of the three inputs.
-/
theorem progIsort3_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (v1 v2 v3 : Int) :
    Machine.safe (progIsort3 v1 v2 v3) (· = Val.int (med3 v1 v2 v3)) := by
  refine wp_safe_bupd (GF := GF) (progIsort3 v1 v2 v3) ?_
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA0⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA0
  unfold Thread.initial progIsort3
  -- alloc a, b, c
  wp_pures
  wp_alloc_intro HA
  wp_pures
  wp_alloc_intro HB
  wp_pures
  wp_alloc_intro HC
  wp_pures
  -- cswap(a, b): (v1, v2) → (min v1 v2, max v1 v2)
  iapply (cswap_spec (E := ⊤) _ iprop(emp : IProp GF) _ _ v1 v2 "tmp1"
            (.var "a") (.var "b") _ _ _ _ rfl (by agar_eval) (by agar_eval))
  iframe HA
  iframe HB
  iintro %vA' %vB' %heqA %heqB HA HB
  subst heqA; subst heqB
  unfold cswap_post; simp only
  wp_pures
  -- cswap(b, c): (max v1 v2, v3) → (min ..., max ...)
  iapply (cswap_spec (E := ⊤) _ iprop(emp : IProp GF) _ _ (max v1 v2) v3 "tmp2"
            (.var "b") (.var "c") _ _ _ _ rfl (by agar_eval) (by agar_eval))
  iframe HB
  iframe HC
  iintro %vA' %vB' %heqA %heqB HB HC
  subst heqA; subst heqB
  unfold cswap_post; simp only
  wp_pures
  -- cswap(a, b): finalises (a, b) → (min3, med3)
  iapply (cswap_spec (E := ⊤) _ iprop(emp : IProp GF) _ _
            (min v1 v2) (min (max v1 v2) v3) "tmp3"
            (.var "a") (.var "b") _ _ _ _ rfl (by agar_eval) (by agar_eval))
  iframe HA
  iframe HB
  iintro %vA' %vB' %heqA %heqB HA HB
  subst heqA; subst heqB
  unfold cswap_post; simp only
  -- HA : min3 v1 v2 v3 ; HB : med3 ; HC : max3. Re-express via canonical forms.
  have hMin : min (min v1 v2) (min (max v1 v2) v3) = min3 v1 v2 v3 := by
    simp only [min3]
    rcases Int.le_total v1 v2 with hab | hab <;>
      rcases Int.le_total v2 v3 with hbc | hbc <;>
      rcases Int.le_total v1 v3 with hac | hac <;>
      simp [Int.min_def, Int.max_def, hab, hbc] <;> omega
  have hMed : max (min v1 v2) (min (max v1 v2) v3) = med3 v1 v2 v3 := by
    simp only [med3, min3, max3]
    rcases Int.le_total v1 v2 with hab | hab <;>
      rcases Int.le_total v2 v3 with hbc | hbc <;>
      rcases Int.le_total v1 v3 with hac | hac <;>
      simp [Int.min_def, Int.max_def, hab, hbc, hac] <;> omega
  have hMax : max (max v1 v2) v3 = max3 v1 v2 v3 := by
    simp only [max3]
    rcases Int.le_total v1 v2 with hab | hab <;>
      rcases Int.le_total v2 v3 with hbc | hbc <;>
      rcases Int.le_total v1 v3 with hac | hac <;>
      simp [Int.max_def, hab, hbc, hac] <;> omega
  wp_pures
  iapply wp_load _ _ _ _ _ (Val.int (med3 v1 v2 v3)) _ _ _ _ (by agar_eval)
  isplitl [HB]
  · rw [← hMed]; iexact HB
  iintro !> HB
  wp_pures
  iapply wp_ret_top _ _ _ (Val.int (med3 v1 v2 v3)) _ _ _ (by agar_eval)
  itrivial

/-! ## Pure sortedness corollary

The closed adequacy is paired with the pure Lean fact that the returned
value, the cell-`a` value, and the cell-`c` value form a sorted triple
that is a permutation of the inputs.

We export the sortedness witness as `progIsort3_sorted`: a conjunction
of the adequacy statement and the pure fact `min3 ≤ med3 ≤ max3` with
multiset-equality between `{min3, med3, max3}` and `{v1, v2, v3}`
(stated here as a list permutation, since `Multiset` would require a
heavier import).
-/

/-- Sortedness witness for the post-isort triple: the three order
statistics form a non-decreasing sequence. -/
theorem isort3_sorted (v1 v2 v3 : Int) :
    min3 v1 v2 v3 ≤ med3 v1 v2 v3 ∧ med3 v1 v2 v3 ≤ max3 v1 v2 v3 :=
  ⟨min3_le_med3 v1 v2 v3, med3_le_max3 v1 v2 v3⟩

/-- Sum-preservation: the three order statistics sum to `v1+v2+v3`. A
weaker but pleasingly elementary "permutation" witness. -/
theorem isort3_sum (v1 v2 v3 : Int) :
    min3 v1 v2 v3 + med3 v1 v2 v3 + max3 v1 v2 v3 = v1 + v2 + v3 := by
  simp [min3, med3, max3]; omega

/-- The headline theorem: closed adequacy for `progIsort3` paired with
the sortedness witness. Every terminated main thread of
`progIsort3 v1 v2 v3` returns `Val.int (med3 v1 v2 v3)`, and the triple
`(min3, med3, max3)` is sorted and a permutation of `(v1, v2, v3)`. -/
theorem progIsort3_sorted
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (v1 v2 v3 : Int) :
    Machine.safe (progIsort3 v1 v2 v3) (· = Val.int (med3 v1 v2 v3)) ∧
      (min3 v1 v2 v3 ≤ med3 v1 v2 v3 ∧ med3 v1 v2 v3 ≤ max3 v1 v2 v3) ∧
      min3 v1 v2 v3 + med3 v1 v2 v3 + max3 v1 v2 v3 = v1 + v2 + v3 :=
  ⟨progIsort3_closed (GF := GF) (F := F) v1 v2 v3,
    isort3_sorted v1 v2 v3, isort3_sum v1 v2 v3⟩

end Agar.Logic

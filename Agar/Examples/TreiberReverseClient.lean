module

public import Agar.Examples.StackReverse
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
public import Agar.Iris.WpSpin

@[expose] public section

/-! # Modular client: list reversal via the Treiber stack interface

This file imports the Treiber-stack development from
`Agar.Examples.StackReverse` and uses ONLY the public specs
`pushProc_spec` and `popProc_spec` (plus the abstract predicate
`tstack`) to build and verify list reversal. The proof never opens
the underlying chain or the head-pointer cell except through one
`load src` per iteration to refresh the loop guard — and even that
operation reads the head VALUE (which the spec exposes via `tstack`'s
existential), not the chain structure.

If the underlying `pushProc` / `popProc` bodies were swapped for a
CAS-loop implementation that proved the SAME call-level specs, this
client would re-typecheck unchanged. That is the modularity claim. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## The driver

`while h != 0 do (v := pop src ; push dst v ; h := load src)`. The
single `load src` per iteration reads the head VALUE for the guard
test — it does not touch the chain. -/

def reverseStacks : Proc where
  params := ["src", "dst"]
  body := ags(
    h := load src ;
    while h != 0 do (
      v   := call popProc(src) ;
      tmp := call pushProc(dst, v) ;
      h   := load src
    )
  )

/-- Loop invariant: a split `(ys, zs)` of the original list with
`ys.reverse ++ zs = xs`. `zs` is still on `src` (with named head `hv`
matching `env "h"`); `ys` is already on `dst`. We unfold `tstack zs src`
to its existential body so `hv` can be named alongside `env "h"`; `dst`
stays packaged. -/
private abbrev revStacksInv (xs : List Int) (src dst : Loc)
    (env : Env) : IProp GF :=
  iprop(∃ (ys zs : List Int) (hv : Val),
    ⌜List.reverse ys ++ zs = xs ∧
      env "src" = some (Val.loc src) ∧
      env "dst" = some (Val.loc dst) ∧
      env "h"   = some hv⌝ ∗
    points_to (GF := GF) (F := F) src hv ∗
    term(llist (GF := GF) (F := F) zs hv) ∗
    term(tstack (GF := GF) (F := F) ys dst))

/-! ## Functional-correctness spec

For any source list `xs` and any pair of distinct (well, irrelevant —
the spec is parametric) stack handles, draining `src` into `dst`
leaves `src` empty and `dst` holding `xs.reverse`. The reverse identity
`(x :: ys).reverse ++ tail = ys.reverse ++ (x :: tail)` composes the
loop invariant across one pop-push transfer. -/

theorem reverseStacks_wp_body
    (procs : Name → Option Proc)
    (hpush : procs "pushProc" = some pushProc)
    (hpop  : procs "popProc"  = some popProc)
    (xs : List Int) (src dst : Loc) :
    tstack (GF := GF) (F := F) xs src ∗ tstack (GF := GF) (F := F) [] dst ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨reverseStacks.body, [],
          bindParams reverseStacks.params [Val.loc src, Val.loc dst],
          [], none⟩
        (fun _ => iprop(term(tstack (GF := GF) (F := F) [] src) ∗
                        term(tstack (GF := GF) (F := F) xs.reverse dst))) := by
  istart
  iintro ⟨HSsrc, HSdst⟩
  icases HSsrc with ⟨%hv0, HPsrc, HLsrc⟩
  unfold reverseStacks
  wp_lstep
  wp_load_keep HPsrc
  wp_lstep
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := revStacksInv (GF := GF) (F := F) xs src dst) _
    (HGuard := fun env => ?HGuard)
    (HBody  := fun env => ?HBody)
    (HExit  := fun env => ?HExit))
  case HGuard =>
    iintro HI
    icases HI with ⟨%ys, %zs, %hv, %hpure, HPs, HLs, HSd⟩
    obtain ⟨hsplit, hsrc, hdst, hh⟩ := hpure
    cases zs with
    | nil =>
        icases HLs with %hhv0
        subst hhv0
        isplitl [HPs HSd]
        · iexists ys; iexists []; iexists (Val.int 0)
          isplitr
          · ipure_intro; exact ⟨hsplit, hsrc, hdst, hh⟩
          isplitl [HPs]
          · iexact HPs
          isplitr
          · unfold llist; ipure_intro; rfl
          iexact HSd
        ipure_intro
        refine ⟨false, ?_⟩
        simp [agar_eval, hh]; rfl
    | cons x xs' =>
        icases HLs with ⟨%l, %hhv, %nx, HC, HT⟩
        subst hhv
        isplitl [HPs HC HT HSd]
        · iexists ys; iexists (x :: xs'); iexists (Val.loc l)
          isplitr
          · ipure_intro; exact ⟨hsplit, hsrc, hdst, hh⟩
          isplitl [HPs]
          · iexact HPs
          isplitl [HC HT]
          · iexists l
            isplitr
            · ipure_intro; rfl
            iexists nx
            isplitl [HC]
            · iexact HC
            iexact HT
          iexact HSd
        ipure_intro
        refine ⟨true, ?_⟩
        simp [agar_eval, hh]; rfl
  case HBody =>
    iintro ⟨HIH, %hgtrue, HI⟩
    icases HI with ⟨%ys, %zs, %hv, %hpure, HPs, HLs, HSd⟩
    obtain ⟨hsplit, hsrc, hdst, hh⟩ := hpure
    cases zs with
    | nil =>
        icases HLs with %hhv0
        exfalso
        subst hhv0
        exact absurd hgtrue (by simp [agar_eval, hh]; decide)
    | cons x xs' =>
        icases HLs with ⟨%l, %hhv, %nx, HC, HT⟩
        subst hhv
        wp_lstep
        -- Modular call: popProc_spec abstracts pop's body away.
        iapply (popProc_spec (procs := procs) (hproc := hpop)
          (x := "v") (eStk := Expr.var "src") (popped := x) (xs := xs')
          (stk := src) (hStk := by simpa using hsrc))
        isplitl [HPs HC HT]
        · iexists (Val.loc l)
          isplitl [HPs]
          · iexact HPs
          iexists l
          isplitr
          · ipure_intro; rfl
          iexists nx
          isplitl [HC]
          · iexact HC
          iexact HT
        iintro HSsrc
        unfold popProc_post
        wp_lstep
        -- Modular call: pushProc_spec abstracts push's body away.
        iapply (pushProc_spec (procs := procs) (hproc := hpush)
          (xs := ys) (stk := dst) (v := x) (x := "tmp")
          (eStk := Expr.var "dst") (eV := Expr.var "v")
          (hStk := by simp [agar_eval, hdst])
          (hV := by simp [agar_eval]))
        isplitl [HSd]
        · iexact HSd
        iintro HSd'
        unfold pushProc_post
        -- The single direct heap access: refresh `h` from `src`'s head cell.
        icases HSsrc with ⟨%hv', HPs', HLs'⟩
        wp_load_direct HPs' (by simpa using hsrc)
        wp_lstep
        ihave HIH := HIH $$
          %(((env.set "v" (Val.int x)).set "tmp" Val.unit).set "h" hv')
        iapply HIH
        iexists (x :: ys); iexists xs'; iexists hv'
        isplitr
        · ipure_intro
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [List.reverse_cons, List.append_assoc] using hsplit
          · simp [agar_eval, hsrc]
          · simp [agar_eval, hdst]
          · simp [agar_eval]
        isplitl [HPs']
        · iexact HPs'
        isplitl [HLs']
        · iexact HLs'
        iexact HSd'
  case HExit =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with ⟨%ys, %zs, %hv, %hpure, HPs, HLs, HSd⟩
    obtain ⟨hsplit, hsrc, hdst, hh⟩ := hpure
    cases zs with
    | nil =>
        icases HLs with %hhv0
        subst hhv0
        have hys : ys = xs.reverse := by
          have h := congrArg List.reverse hsplit
          simpa using h
        rw [← hys]
        iapply (wp_value _ _ _ Val.unit _ rfl)
        isplitl [HPs]
        · iexists (Val.int 0)
          isplitl [HPs]
          · iexact HPs
          unfold llist; ipure_intro; rfl
        iexact HSd
    | cons x xs' =>
        icases HLs with ⟨%l, %hhv, %nx, HC, HT⟩
        exfalso
        subst hhv
        have hbeq : Val.beq (Val.loc l) (Val.int 0) = false := by simp [Val.beq]
        simp [agar_eval, hh, BEq.beq, hbeq] at hgfalse
  -- Initial invariant: ys = [], zs = xs, hv = hv0.
  iexists []; iexists xs; iexists hv0
  isplitr
  · ipure_intro
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp [agar_eval]
    · simp [agar_eval]
    · simp [agar_eval]
  isplitl [HPsrc]
  · iexact HPsrc
  isplitl [HLsrc]
  · iexact HLsrc
  iexact HSdst

/-! ## Worked example: build a `tstack [4, 2, 0]`

A small client program that allocates a fresh head cell and then
performs three `pushProc` calls, producing a Treiber stack representing
the list `[4, 2, 0]` (with `4` on top). The proof uses ONLY the public
`pushProc_spec` for each push; the chain ownership never appears
explicitly in the proof script except as the abstract `tstack` carried
between calls. -/

def progBuildTstack420 : Program where
  procs := fun n =>
    if n = "pushProc" then some pushProc
    else if n = "popProc" then some popProc
    else none
  main := ags(
    stk  := alloc 0 ;
    tmp0 := call pushProc(stk, 0) ;
    tmp1 := call pushProc(stk, 2) ;
    tmp2 := call pushProc(stk, 4) ;
    return stk
  )

theorem progBuildTstack420_wp
    (procs : Name → Option Proc)
    (hpush : procs "pushProc" = some pushProc) :
    iprop(emp : IProp GF) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        (Thread.initial progBuildTstack420.main)
        (fun r => iprop(∃ stk : Loc, ⌜r = Val.loc stk⌝ ∗
          term(tstack (GF := GF) (F := F) [4, 2, 0] stk))) := by
  istart
  iintro _
  unfold Thread.initial progBuildTstack420
  wp_steps
  wp_alloc_intro lStk HStk
  wp_steps
  iapply (pushProc_spec (procs := procs) (hproc := hpush)
    (xs := []) (stk := lStk) (v := 0) (x := "tmp0")
    (eStk := Expr.var "stk") (eV := age(0))
    (hStk := by simp [agar_eval]) (hV := by simp [agar_eval]))
  isplitl [HStk]
  · iexists (Val.int 0); isplitl [HStk]
    · iexact HStk
    unfold llist; ipure_intro; rfl
  iintro HS0
  unfold pushProc_post
  wp_lstep
  iapply (pushProc_spec (procs := procs) (hproc := hpush)
    (xs := [0]) (stk := lStk) (v := 2) (x := "tmp1")
    (eStk := Expr.var "stk") (eV := age(2))
    (hStk := by simp [agar_eval]) (hV := by simp [agar_eval]))
  isplitl [HS0]
  · iexact HS0
  iintro HS1
  unfold pushProc_post
  wp_lstep
  iapply (pushProc_spec (procs := procs) (hproc := hpush)
    (xs := [2, 0]) (stk := lStk) (v := 4) (x := "tmp2")
    (eStk := Expr.var "stk") (eV := age(4))
    (hStk := by simp [agar_eval]) (hV := by simp [agar_eval]))
  isplitl [HS1]
  · iexact HS1
  iintro HS2
  unfold pushProc_post
  wp_step
  iexists lStk
  isplitr
  · ipure_intro; rfl
  iexact HS2

end Agar.Logic

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
public import Agar.Iris.WpSpin

@[expose] public section

/-! # Linked-list representation predicate + functional reversal spec

`llist xs hv` is a separation-logic predicate that asserts:
* `hv : Val` is the head-pointer value of a heap-resident linked list
  whose payloads, read top to bottom, are the Lean list `xs : List Int`.

It owns the chain of node cells outright; `xs = []` corresponds to
`hv = Val.int 0` (null head) with no heap ownership.

The main theorem `reverseProc_wp_body` proves that running `reverseProc`
on any `hv` representing `xs` yields a head-pointer value `hv'` such
that `llist xs.reverse hv'` — the program produces a destructively-
reversed linked list, captured at the Lean-list level. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## The representation predicate

A linked-list node is stored as a struct cell holding `("v", payload)`
and `("nx", next-head-value)`. The chain terminates when `nx = Val.int 0`. -/

@[reducible] def llist : List Int → Val → IProp GF
  | [],      hv => iprop(⌜hv = Val.int 0⌝)
  | x :: xs, hv =>
      iprop(∃ l : Loc, ⌜hv = Val.loc l⌝ ∗
        ∃ nx : Val, points_to (GF := GF) (F := F) l
            (Val.struct [("v", Val.int x), ("nx", nx)]) ∗
          term(llist xs nx))

/-- `lnodeExpr v nx` builds a struct literal `{v, nx}` as an Agar
expression. (Local to this file to avoid the name clash with the
identically-shaped helper in `StackPushPop`.) -/
def lnodeExpr (v nx : Expr) : Expr :=
  Expr.mk [("v", v), ("nx", nx)]

/-! ## Constructive example: building `llist [1, 2, 3]`

A small straight-line program that allocates three cells and ends with
ownership of `llist [1, 2, 3] hv` for the produced head value `hv`.
Witnesses that `llist` is nontrivial. -/

def progBuild123 : Program where
  procs := fun _ => none
  main := ags(
    -- Bottom node (payload 3, next = null).
    a1 := alloc #(lnodeExpr (Expr.val (Val.int 3)) (Expr.val (Val.int 0))) ;
    -- Middle node (payload 2, next = a1).
    a2 := alloc #(lnodeExpr (Expr.val (Val.int 2)) (Expr.var "a1")) ;
    -- Top node (payload 1, next = a2).
    a3 := alloc #(lnodeExpr (Expr.val (Val.int 1)) (Expr.var "a2")) ;
    return a3
  )

theorem progBuild123_wp
    (procs : Name → Option Proc) :
    iprop(emp : IProp GF) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        (Thread.initial progBuild123.main)
        (fun r => llist (GF := GF) (F := F) [1, 2, 3] r) := by
  istart
  iintro _
  unfold Thread.initial progBuild123
  wp_steps
  wp_alloc_intro l1 H1
  wp_steps
  wp_alloc_intro l2 H2
  wp_steps
  wp_alloc_intro l3 H3
  wp_steps
  -- Goal: llist [1, 2, 3] (Val.loc l3).
  unfold llist
  iexists l3
  isplitr
  · ipure_intro; rfl
  iexists (Val.loc l2)
  isplitl [H3]
  · iexact H3
  unfold llist
  iexists l2
  isplitr
  · ipure_intro; rfl
  iexists (Val.loc l1)
  isplitl [H2]
  · iexact H2
  unfold llist
  iexists l1
  isplitr
  · ipure_intro; rfl
  iexists (Val.int 0)
  isplitl [H1]
  · iexact H1
  unfold llist
  ipure_intro; rfl

/-! ## The reversal procedure

Destructively transfers nodes from `srcHead` to a freshly-built
`dstHead`, one at a time. Each iteration reads the top struct, saves
its payload `v` and next-pointer `nx`, frees the source cell, allocates
a new node `{v, nx = dstHead}`, then advances `dstHead` to the new node
and `srcHead` to `nx`. -/

def reverseProc : Proc where
  params := ["srcHead"]
  body := ags(
    dstHead := 0 ;
    (while srcHead != 0 do (
      s    := load srcHead ;
      v    := #(Expr.proj (Expr.var "s") "v") ;
      nx   := #(Expr.proj (Expr.var "s") "nx") ;
      free srcHead ;
      new  := alloc #(lnodeExpr (Expr.var "v") (Expr.var "dstHead")) ;
      dstHead := new ;
      srcHead := nx
    )) ;
    return dstHead
  )

/-! ## Functional-correctness spec for `reverseProc`

Loop invariant: at every iteration the original list `xs` splits into
* `ys : List Int` — already-reversed prefix held by `dstHead`;
* `zs : List Int` — yet-to-process suffix held by `srcHead`;
with `ys.reverse ++ zs = xs`. At exit `zs = []` so `ys.reverse = xs`,
hence `ys = xs.reverse`. -/

private abbrev revInv (xs : List Int) (env : Env) : IProp GF :=
  iprop(∃ (ys zs : List Int) (sh dh : Val),
    ⌜List.reverse ys ++ zs = xs ∧
      env "srcHead" = some sh ∧ env "dstHead" = some dh⌝ ∗
    term(llist (GF := GF) (F := F) zs sh) ∗
    term(llist (GF := GF) (F := F) ys dh))

theorem reverseProc_wp_body
    (procs : Name → Option Proc) (xs : List Int) (hv : Val) :
    llist (GF := GF) (F := F) xs hv ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨reverseProc.body, [],
          bindParams reverseProc.params [hv],
          [], none⟩
        (fun r => llist (GF := GF) (F := F) xs.reverse r) := by
  istart
  iintro HL
  unfold reverseProc
  wp_pures_no_loop
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := revInv (GF := GF) (F := F) xs) _
    (HGuard := fun env => ?HGuard)
    (HBody  := fun env => ?HBody)
    (HExit  := fun env => ?HExit))
  case HGuard =>
    iintro HI
    icases HI with ⟨%ys, %zs, %sh, %dh, %hpure, HZ, HY⟩
    obtain ⟨hsplit, hsrc, hdst⟩ := hpure
    cases zs with
    | nil =>
        icases HZ with %hsh
        isplitl [HY]
        · iexists ys; iexists []; iexists sh; iexists dh
          isplitr
          · ipure_intro; exact ⟨hsplit, hsrc, hdst⟩
          isplitr
          · unfold llist; ipure_intro; exact hsh
          iexact HY
        ipure_intro
        refine ⟨false, ?_⟩
        subst hsh; simp [agar_eval, hsrc]; rfl
    | cons x xs' =>
        icases HZ with ⟨%l, %hsh, %nx, HC, HT⟩
        isplitl [HC HT HY]
        · iexists ys; iexists (x :: xs'); iexists sh; iexists dh
          isplitr
          · ipure_intro; exact ⟨hsplit, hsrc, hdst⟩
          isplitl [HC HT]
          · iexists l
            isplitr
            · ipure_intro; exact hsh
            iexists nx
            isplitl [HC]
            · iexact HC
            iexact HT
          iexact HY
        ipure_intro
        refine ⟨true, ?_⟩
        subst hsh; simp [agar_eval, hsrc]; rfl
  case HBody =>
    iintro ⟨HIH, %hgtrue, HI⟩
    icases HI with ⟨%ys, %zs, %sh, %dh, %hpure, HZ, HY⟩
    obtain ⟨hsplit, hsrc, hdst⟩ := hpure
    cases zs with
    | nil =>
        icases HZ with %hsh
        exfalso
        subst hsh
        exact absurd hgtrue (by simp [agar_eval, hsrc]; decide)
    | cons x xs' =>
        icases HZ with ⟨%l, %hsh, %nx, HC, HT⟩
        subst hsh
        wp_lstep
        wp_load_direct HC (by simpa using hsrc)
        wp_assign_simp
        wp_assign_simp
        wp_lstep
        wp_lstep
        iapply wp_free (GF := GF) (F := F) (l := l)
          (heval := by simpa using hsrc)
        iframe HC
        iintro !>
        wp_lstep
        wp_lstep
        iapply wp_alloc (heval := by
          simp [agar_eval, lnodeExpr, hdst]; rfl)
        iintro !> %lNew HNew
        wp_assign_simp
        wp_lstep
        iapply wp_assign (heval := by simp [agar_eval]; rfl)
        iintro !>
        wp_lstep
        ihave HIH := HIH $$ %(((((((env.set "s"
          (Val.struct [("v", Val.int x), ("nx", nx)])).set "v"
          (Val.int x)).set "nx" nx).set "new"
          (Val.loc lNew)).set "dstHead" (Val.loc lNew)).set "srcHead" nx))
        iapply HIH
        iexists (x :: ys); iexists xs'; iexists nx; iexists (Val.loc lNew)
        isplitr
        · ipure_intro
          refine ⟨?_, ?_, ?_⟩
          · simpa [List.reverse_cons, List.append_assoc] using hsplit
          · simp [agar_eval]
          · simp [agar_eval]
        isplitl [HT]
        · iexact HT
        iexists lNew
        isplitr
        · ipure_intro; rfl
        iexists dh
        isplitl [HNew]
        · iexact HNew
        iexact HY
  case HExit =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with ⟨%ys, %zs, %sh, %dh, %hpure, HZ, HY⟩
    obtain ⟨hsplit, hsrc, hdst⟩ := hpure
    cases zs with
    | nil =>
        icases HZ with %hsh
        subst hsh
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "dstHead") dh [] _ _
          (heval := by simpa using hdst))
        simp at hsplit
        have hxs : ys = xs.reverse := by
          have h := congrArg List.reverse hsplit
          simpa using h
        rw [← hxs]
        iexact HY
    | cons x xs' =>
        icases HZ with ⟨%l, %hsh, %nx, HC, HT⟩
        exfalso
        subst hsh
        have hbeq : Val.beq (Val.loc l) (Val.int 0) = false := by simp [Val.beq]
        simp [agar_eval, hsrc, BEq.beq, hbeq] at hgfalse
  -- Initial revInv: ys = [], zs = xs, sh = hv, dh = Val.int 0.
  unfold revInv
  iexists []; iexists xs; iexists hv; iexists (Val.int 0)
  isplitr
  · ipure_intro
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp [agar_eval]
    · simp [agar_eval]
  isplitl [HL]
  · iexact HL
  unfold llist; ipure_intro; rfl

end Agar.Logic

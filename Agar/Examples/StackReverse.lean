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

/-! # Treiber stacks: predicate + push/pop specs + two-stack reversal

The development above destructively reuses the *nodes* of the input
list. A genuine Treiber-stack implementation has each operation go
through a stable head-pointer cell `stk : Loc` that always holds the
current head value. `tstack xs stk` packages the head cell with the
underlying chain. Push and pop are stand-alone procedures with
modular specs; the reversal driver pops from one stack and pushes onto
the other, never inspecting the chain directly. -/

/-- Treiber-stack representation: the head-pointer cell at `stk`
holds some value `hv` for which the chain ownership `llist xs hv`
is held. -/
@[reducible] def tstack (xs : List Int) (stk : Loc) : IProp GF :=
  iprop(∃ hv : Val, points_to (GF := GF) (F := F) stk hv ∗ term(llist xs hv))

/-! ## `pushProc` — top-of-stack push -/

def pushProc : Proc where
  params := ["stk", "v"]
  body := ags(
    old := load stk ;
    new := alloc #(lnodeExpr (Expr.var "v") (Expr.var "old")) ;
    store stk new
  )

theorem pushProc_wp_body
    (procs : Name → Option Proc) (xs : List Int) (stk : Loc) (v : Int) :
    tstack (GF := GF) (F := F) xs stk ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨pushProc.body, [],
          bindParams pushProc.params [Val.loc stk, Val.int v],
          [], none⟩
        (fun _ => tstack (GF := GF) (F := F) (v :: xs) stk) := by
  istart
  iintro HS
  icases HS with ⟨%hv, HP, HL⟩
  unfold pushProc
  wp_lstep
  wp_load_keep HP
  wp_lstep
  wp_lstep
  iapply wp_alloc (heval := by simp [agar_eval, lnodeExpr]; rfl)
  iintro !> %lNew HNew
  wp_lstep
  iapply wp_store (GF := GF) (F := F) (l := stk) (v := Val.loc lNew)
    (heL := by simp [agar_eval])
    (heV := by simp [agar_eval])
  iframe HP
  iintro !> HP
  iapply (wp_value _ _ _ Val.unit _ rfl)
  iexists (Val.loc lNew)
  isplitl [HP]
  · iexact HP
  iexists lNew
  isplitr
  · ipure_intro; rfl
  iexists hv
  isplitl [HNew]
  · iexact HNew
  iexact HL

/-! ## `popProc` — top-of-stack pop

Precondition requires the stack to be non-empty (`tstack (x :: xs) stk`).
Returns `Val.int x` and leaves the stack at `tstack xs stk`. -/

def popProc : Proc where
  params := ["stk"]
  body := ags(
    top := load stk ;
    s   := load top ;
    v   := #(Expr.proj (Expr.var "s") "v") ;
    nx  := #(Expr.proj (Expr.var "s") "nx") ;
    store stk nx ;
    free top ;
    return v
  )

theorem popProc_wp_body
    (procs : Name → Option Proc) (x : Int) (xs : List Int) (stk : Loc) :
    tstack (GF := GF) (F := F) (x :: xs) stk ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨popProc.body, [],
          bindParams popProc.params [Val.loc stk],
          [], none⟩
        (fun r => iprop(⌜r = Val.int x⌝ ∗
          term(tstack (GF := GF) (F := F) xs stk))) := by
  istart
  iintro HS
  icases HS with ⟨%hv, HP, HL⟩
  -- llist (x :: xs) hv unfolds to: ∃ l, hv = Val.loc l ∗ ∃ nx, l ↦ struct ∗ llist xs nx.
  icases HL with ⟨%l, %hhv, %nx, HC, HT⟩
  subst hhv
  unfold popProc
  wp_lstep
  wp_load_keep HP
  wp_lstep
  wp_lstep
  wp_load_keep HC
  wp_assign_simp
  wp_assign_simp
  wp_lstep
  wp_lstep
  iapply wp_store (GF := GF) (F := F) (l := stk) (v := nx)
    (heL := by simp [agar_eval])
    (heV := by simp [agar_eval])
  iframe HP
  iintro !> HP
  wp_lstep
  wp_lstep
  iapply wp_free (GF := GF) (F := F) (l := l)
    (heval := by simp [agar_eval])
  iframe HC
  iintro !>
  wp_lstep
  iapply (wp_ret_top _ _ (Expr.var "v") (Val.int x) [] _ _
    (heval := by simp [agar_eval]))
  isplitr
  · ipure_intro; rfl
  iexists nx
  isplitl [HP]
  · iexact HP
  iexact HT

/-! ## Call-level specs

Lift `pushProc_wp_body` and `popProc_wp_body` to call sites: at a
`.call x procName [args]` thread state, given the input ownership and
a continuation wand over the output ownership, derive the at-call WP. -/

/-- Post-call thread state for `pushProc`: the call's return binder `x`
gets `Val.unit` (push falls through), caller's `cont`/`stack` resume. -/
def pushProc_post (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x Val.unit
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- An empty Treiber stack is just a head cell holding the sentinel `0`.
Convenient for closed examples that allocate a fresh head and need
`tstack [] stk` as a precondition. -/
theorem tstack_nil_intro (stk : Loc) :
    points_to (GF := GF) (F := F) stk (Val.int 0) ⊢
      tstack (GF := GF) (F := F) [] stk := by
  istart
  iintro HP
  iexists (Val.int 0); isplitl [HP]
  · iexact HP
  unfold llist; ipure_intro; rfl

theorem pushProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "pushProc" = some pushProc)
    (Φ : Val → IProp GF) (xs : List Int) (stk : Loc) (v : Int)
    (x : Name) (eStk eV : Expr) (cont : List Stmt) (env : Env)
    (stack : List Frame)
    (hStk : Expr.eval env eStk = some (Val.loc stk))
    (hV   : Expr.eval env eV  = some (Val.int v)) :
    tstack (GF := GF) (F := F) xs stk ∗
      (tstack (GF := GF) (F := F) (v :: xs) stk -∗
        wp (GF := GF) procs fork_post CoPset.full
          (pushProc_post x cont env stack) Φ)
    ⊢ wp (GF := GF) procs fork_post CoPset.full
        ⟨.call x "pushProc" [eStk, eV], cont, env, stack, none⟩ Φ := by
  istart
  iintro ⟨HS, HK⟩
  have hargs : evalArgs env [eStk, eV] = some [Val.loc stk, Val.int v] := by
    simp [agar_eval, hStk, hV]
  have harity : ([Val.loc stk, Val.int v]).length = pushProc.params.length := rfl
  iapply (wp_call procs fork_post x "pushProc" [eStk, eV] pushProc
    [Val.loc stk, Val.int v] cont env stack Φ hproc hargs harity)
  iintro !>
  icases HS with ⟨%hv, HP, HL⟩
  unfold pushProc
  wp_lstep
  wp_load_keep HP
  wp_lstep
  wp_lstep
  iapply wp_alloc (heval := by simp [agar_eval, lnodeExpr]; rfl)
  iintro !> %lNew HNew
  wp_lstep
  iapply wp_store (GF := GF) (F := F) (l := stk) (v := Val.loc lNew)
    (heL := by simp [agar_eval])
    (heV := by simp [agar_eval])
  iframe HP
  iintro !> HP
  -- Pop the caller's frame to land in `pushProc_post`.
  unfold pushProc_post
  cases hcont : cont with
  | nil =>
    iapply wp_skip_frame_nil
    iintro !>
    iapply HK
    iexists (Val.loc lNew)
    isplitl [HP]
    · iexact HP
    iexists lNew
    isplitr
    · ipure_intro; rfl
    iexists hv
    isplitl [HNew]
    · iexact HNew
    iexact HL
  | cons s cs =>
    iapply wp_skip_frame_cons
    iintro !>
    iapply HK
    iexists (Val.loc lNew)
    isplitl [HP]
    · iexact HP
    iexists lNew
    isplitr
    · ipure_intro; rfl
    iexists hv
    isplitl [HNew]
    · iexact HNew
    iexact HL

/-- Post-call thread state for `popProc`: the call's return binder `x`
receives `Val.int popped_value`, caller's `cont`/`stack` resume. -/
def popProc_post (x : Name) (popped : Int) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x (Val.int popped)
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

theorem popProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "popProc" = some popProc)
    (Φ : Val → IProp GF) (x : Name) (eStk : Expr) (cont : List Stmt)
    (env : Env) (stack : List Frame) (popped : Int) (xs : List Int)
    (stk : Loc)
    (hStk : Expr.eval env eStk = some (Val.loc stk)) :
    tstack (GF := GF) (F := F) (popped :: xs) stk ∗
      (tstack (GF := GF) (F := F) xs stk -∗
        wp (GF := GF) procs fork_post CoPset.full
          (popProc_post x popped cont env stack) Φ)
    ⊢ wp (GF := GF) procs fork_post CoPset.full
        ⟨.call x "popProc" [eStk], cont, env, stack, none⟩ Φ := by
  istart
  iintro ⟨HS, HK⟩
  have hargs : evalArgs env [eStk] = some [Val.loc stk] := by
    simp [agar_eval, hStk]
  have harity : ([Val.loc stk]).length = popProc.params.length := rfl
  iapply (wp_call procs fork_post x "popProc" [eStk] popProc
    [Val.loc stk] cont env stack Φ hproc hargs harity)
  iintro !>
  icases HS with ⟨%hv, HP, HL⟩
  icases HL with ⟨%l, %hhv, %nx, HC, HT⟩
  subst hhv
  unfold popProc
  wp_lstep
  wp_load_keep HP
  wp_lstep
  wp_lstep
  wp_load_keep HC
  wp_assign_simp
  wp_assign_simp
  wp_lstep
  wp_lstep
  iapply wp_store (GF := GF) (F := F) (l := stk) (v := nx)
    (heL := by simp [agar_eval])
    (heV := by simp [agar_eval])
  iframe HP
  iintro !> HP
  wp_lstep
  wp_lstep
  iapply wp_free (GF := GF) (F := F) (l := l)
    (heval := by simp [agar_eval])
  iframe HC
  iintro !>
  wp_lstep
  -- Body's `return v` pops the caller's frame and binds `x` in caller's env.
  unfold popProc_post
  cases hcont : cont with
  | nil =>
    iapply (wp_ret_pop_nil _ _ (Expr.var "v") (Val.int popped) [] _ _ _ _ _
      (heval := by simp [agar_eval]))
    iintro !>
    iapply HK
    iexists nx
    isplitl [HP]
    · iexact HP
    iexact HT
  | cons s cs =>
    iapply (wp_ret_pop_cons _ _ (Expr.var "v") (Val.int popped) [] _ _ _ _ _ _ _
      (heval := by simp [agar_eval]))
    iintro !>
    iapply HK
    iexists nx
    isplitl [HP]
    · iexact HP
    iexact HT

end Agar.Logic

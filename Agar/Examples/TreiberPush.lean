module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Std.Namespaces
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.TacticsAtomic

@[expose] public section

/-! # `progTreiberPush` — Treiber-stack single-attempt push (safety)

Two threads each alloc a node and `cas stk 0 node` once. `treiberInv`
is EMPTY (`stk ↦ 0`) vs ONE-NODE (`∃ l v, stk ↦ Val.loc l ∗ l ↦ v`);
the CAS-loser leaks its node into the post (memory leak, not a safety
violation). Adequacy at `Val.unit`. Functional specs (retry-to-success,
which value won) need ghost tokens — out of scope. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## The program -/

/-- A single-attempt push: allocate a new node holding `v`, then CAS
the shared head from `0` (empty) to the new node's location. -/
def pushOnceProc : Proc where
  params := ["stk", "v"]
  body   := ags(
    node := alloc v ;
    prev := cas stk 0 node
  )

/-- The Treiber-push program: allocate the shared head, fork two
push-attempt workers (with distinct payload values), fall through to
`Val.unit`. -/
def progTreiberPush : Program where
  procs := fun n => if n = "pushOnceProc" then some pushOnceProc else none
  main  := ags(
    stk := alloc 0 ;
    fork pushOnceProc(stk, 1) ;
    fork pushOnceProc(stk, 2)
  )

/-- The disjunctive shared invariant body. -/
private abbrev treiberInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    (sLoc : Loc) : IProp GF :=
  iprop(
    points_to (GF := GF) (F := F) sLoc (Val.int 0)
      ∨ ∃ l : Loc, ∃ v : Int,
          points_to (GF := GF) (F := F) sLoc (Val.loc l) ∗
          points_to (GF := GF) (F := F) l (Val.int v))

/-! ## Push-thread WP body (alloc fresh node, single-attempt CAS) -/

private theorem pushOnceProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (sLoc : Loc) (vPay : Int) :
    iprop(inv (GF := GF) nroot (treiberInv GF F sLoc)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨pushOnceProc.body, [],
          bindParams pushOnceProc.params [Val.loc sLoc, Val.int vPay],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold pushOnceProc
  wp_pures
  wp_alloc_intro nodeLoc HN
  wp_pures
  wp_cas_atomic_split HI
    (treiberInv GF F sLoc) (Val.int 0) (Val.loc nodeLoc)
    (val_beq_int_false 0)
    with (>HS | ⟨%lOld, %vOld, >HS, >HOld⟩)
  · -- Open EMPTY; CAS succeeds, publish the fresh node into ONE-NODE.
    imodintro
    iexists (Val.int 0)
    iframe HS
    isplitl [HN]
    · iintro %_hv0 HS'
      imodintro
      isplitl [HS' HN]
      · inext; iright; iexists nodeLoc, vPay; iframe HS'; iexact HN
      wp_done
    · cas_dead
  · -- Open ONE-NODE; CAS fails (a pointer ≠ Val.int 0), HN leaks into the post.
    imodintro
    iexists (Val.loc lOld)
    iframe HS
    isplitr
    · cas_dead
    · iintro %_hne HS'
      imodintro
      isplitl [HS' HOld]
      · inext; iright; iexists lOld, vOld; iframe HS'; iexact HOld
      wp_done

theorem progTreiberPush_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progTreiberPush (· = Val.unit) := by
  adequacy_with_heap_intro progTreiberPush Val.unit
  wp_pures
  wp_alloc_intro sLoc' HPS
  wp_pures
  inv_alloc_left (treiberInv GF F sLoc') HPS
  wp_fork_emp "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 1)] pushOnceProc
    [Val.loc _, Val.int 1]
    [Stmt.fork "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 2)]]
  isplitr
  · -- Forked push-thread #1 (payload 1).
    iintro !>
    iapply pushOnceProc_wp_body
    iexact HI
  · -- Parent continuation: second fork (payload 2), then fall through.
    iintro !>
    wp_pures
    wp_fork_emp "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 2)] pushOnceProc
      [Val.loc _, Val.int 2] []
    isplitr
    · -- Forked push-thread #2 (payload 2).
      iintro !>
      iapply pushOnceProc_wp_body
      iexact HI
    · -- Final parent continuation: fall through at Val.unit.
      iintro !>
      wp_done

/-! ## `progTreiberPushRace` — predicate-form adequacy on the stack head

Same two pushers, but main reads `stk` once and returns. The
disjunctive invariant pins the head to either `Val.int 0` (empty) or
`Val.loc _` (some pushed node), so the predicate form captures the
race precisely. -/

def progTreiberPushRace : Program where
  procs := fun n => if n = "pushOnceProc" then some pushOnceProc else none
  main  := ags(
    stk := alloc 0 ;
    fork pushOnceProc(stk, 1) ;
    fork pushOnceProc(stk, 2) ;
    v := load stk ;
    return v
  )

theorem progTreiberPushRace_closedP
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progTreiberPushRace
      (fun v => v = Val.int 0 ∨ ∃ l : Loc, v = Val.loc l) := by
  adequacy_with_heap_intro_P progTreiberPushRace
    (fun v => v = Val.int 0 ∨ ∃ l : Loc, v = Val.loc l)
  wp_pures
  wp_alloc_intro sLoc' HPS
  wp_pures
  inv_alloc_left (treiberInv GF F sLoc') HPS
  wp_fork_emp "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 1)] pushOnceProc
    [Val.loc _, Val.int 1]
    [ags(fork pushOnceProc(stk, 2) ; v := load stk ; return v)]
  isplitr
  · iintro !>
    iapply pushOnceProc_wp_body
    iexact HI
  · iintro !>
    wp_pures
    wp_fork_emp "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 2)] pushOnceProc
      [Val.loc _, Val.int 2]
      [ags(v := load stk ; return v)]
    isplitr
    · iintro !>
      iapply pushOnceProc_wp_body
      iexact HI
    · iintro !>
      wp_pures
      iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
        (P := treiberInv GF F sLoc')
        (Hsub := by rw [nclose_root])
        (heL := by agar_eval)
      iframe HI
      iintro HP
      ihave HP := BI.later_or.mp $$ HP
      icases HP with (>HC | >⟨%l, %vp, HC, HL⟩)
      · imodintro
        iexists (Val.int 0)
        isplitl [HC]
        · iexact HC
        iintro HC
        imodintro
        isplitl [HC]
        · inext; ileft; iexact HC
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "v") (Val.int 0) [] _ _
          (heval := by agar_eval))
        ipure_intro; left; rfl
      · imodintro
        iexists (Val.loc l)
        isplitl [HC]
        · iexact HC
        iintro HC
        imodintro
        isplitl [HC HL]
        · inext; iright; iexists l; iexists vp; iframe HC; iexact HL
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "v") (Val.loc l) [] _ _
          (heval := by agar_eval))
        ipure_intro; right; exact ⟨l, rfl⟩

end Agar.Logic

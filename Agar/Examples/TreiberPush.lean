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

The canonical lock-free Treiber stack collapsed to its essence: two
threads each try a *single* CAS-attempt push onto a shared head cell
initially holding `Val.int 0` (the empty sentinel). The push body is
the standard:

```
pushOnceProc(stk, v) := ags(
  node := alloc v ;
  prev := cas stk 0 node       -- node is a Val.loc; CAS expects empty
)

progTreiberPush.main := ags(
  stk := alloc 0 ;
  fork pushOnceProc(stk, 1) ;
  fork pushOnceProc(stk, 2)
)
```

### Two-state disjunctive invariant

The shared head cell is protected by a disjunctive invariant mirroring
the ProducerConsumer shape, but with the RIGHT disjunct existentially
quantified over a node location and its stored value (the *list shape*
abstracted out — we don't track which thread pushed, only that one
pushed succeeded):

```
treiberInv stk :=
  inv N ((stk ↦ Val.int 0)                                     -- EMPTY
       ∨ (∃ l v, stk ↦ Val.loc l ∗ l ↦ Val.int v))             -- ONE NODE
```

* LEFT (empty) admits a CAS-from-0 success: the freshly allocated
  node is folded into the existential to close into RIGHT.
* RIGHT (one node) makes the second CAS fail (`vcur` is a `Val.loc`,
  never equal to `Val.int 0`); the freshly allocated node is *leaked*
  (memory leak, not a safety violation), and RIGHT is re-established
  with the same witnesses.

### What this proves (and what it does NOT)

`progTreiberPush_closed` discharges `Machine.Adequate progTreiberPush
μ' Val.unit`: every thread is terminated or reducible, and the main
thread (when terminated) returns `Val.unit`. Safety alone.

What we deliberately do *not* prove:

* No retry. With a single CAS attempt, the *losing* thread does not
  see its value on the stack. A full retry-to-success spec would
  require driving `wp_spin_invariant` with a body that re-loads the
  head, re-allocates if needed, and re-attempts the CAS — doable but
  out of scope for this safety baseline.
* No list shape. The RIGHT disjunct only witnesses that *some* node
  is on the stack; it doesn't track *which* value (`1` or `2`) won.
  Routing the actual pushed value through a CAS-success branch needs
  asymmetric ghost tokens (cf. the Mutex/Counter examples) — also
  out of scope here.

The invariant additionally guarantees, post-hoc, that the heap value
at `stk` is always either `Val.int 0` or a `Val.loc` pointing to a
node we own; but adequacy itself does not expose that meta-fact. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## CAS-failure-branch discriminator -/

private theorem val_beq_int0_false :
    ∀ v : Val, v ≠ Val.int 0 → (v == Val.int 0) = false := by
  intro v hne
  cases v with
  | int i =>
      show (i == 0) = false
      have : i ≠ 0 := fun h => hne (by cases h; rfl)
      simp [this]
  | bool _ => rfl
  | loc _ => rfl
  | unit => rfl
  | struct _ => rfl

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

/-! ## Push-thread WP body

Single-attempt push under the disjunctive invariant. The alloc
produces a fresh node `node ↦ Val.int v`; the subsequent CAS either
succeeds (folding the node into RIGHT) or fails (leaking the node;
RIGHT re-established unchanged). -/

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
  -- Body: (node := alloc v) ; (prev := cas stk 0 node)
  wp_step                                       -- wp_seq exposing alloc
  iintro !>
  wp_alloc
  iintro !> %nodeLoc HN                         -- HN : nodeLoc ↦ Val.int vPay
  wp_step                                       -- wp_skip_cons
  iintro !>
  -- Goal: wp ⟨cas "prev" stk 0 node, [], env', [], none⟩
  -- env' = (env.set "node" (Val.loc nodeLoc))
  wp_cas_atomic_split HI
    (treiberInv GF F sLoc) (Val.int 0) (Val.loc nodeLoc)
    val_beq_int0_false
    with (>HS | ⟨%lOld, %vOld, >HS, >HOld⟩)
  · -- LEFT disjunct: stk ↦ Val.int 0. CAS will succeed.
    imodintro
    iexists (Val.int 0)
    iframe HS
    isplitl [HN]
    · -- Success wand: vcur = 0, holds stk ↦ Val.loc nodeLoc; close RIGHT.
      iintro %_hv0 HS'
      imodintro
      isplitl [HS' HN]
      · inext; iright
        iexists nodeLoc, vPay
        iframe HS'
        iexact HN
      wp_done
    · -- Failure wand: vcur = 0 was our value; vcur ≠ 0 contradiction.
      iintro %hne _
      exfalso; exact hne rfl
  · -- RIGHT disjunct: stk ↦ Val.loc lOld, lOld ↦ Val.int vOld. CAS fails.
    imodintro
    iexists (Val.loc lOld)
    iframe HS
    isplitr
    · -- Success wand: vcur = Val.int 0 required; vcur = Val.loc lOld; absurd.
      iintro %heq _
      exfalso; cases heq
    · -- Failure wand: re-establish RIGHT with the same witnesses.
      -- (We leak HN — the freshly allocated node — into the post.)
      iintro %_hne HS'
      imodintro
      isplitl [HS' HOld]
      · inext; iright
        iexists lOld, vOld
        iframe HS'
        iexact HOld
      wp_done

/-! ## Closed adequacy theorem -/

/-- **Closed adequacy** for `progTreiberPush`: under any reachable
machine trace, every thread is terminated or reducible, and a
terminated main thread returns `Val.unit`. -/
theorem progTreiberPush_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progTreiberPush n
            (Machine.initial progTreiberPush) μ') :
    Machine.Adequate progTreiberPush μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progTreiberPush ?_ n μ' htr
  start_closed_proof_with_heap progTreiberPush
  -- main := alloc "stk" 0 ; fork pushOnceProc(stk,1) ; fork pushOnceProc(stk,2)
  wp_step                                       -- wp_seq exposing alloc
  iintro !>
  wp_alloc
  iintro !> %sLoc' HPS                          -- HPS : sLoc' ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing first fork
  iintro !>
  -- Allocate the disjunctive invariant in LEFT (empty) disjunct.
  iapply fupd_wp
  imod (inv_alloc nroot CoPset.full (treiberInv GF F sLoc'))
        $$ [HPS]
        with HI
  · inext; ileft; iexact HPS
  imodintro
  ihave #HI := HI
  -- First fork: pushOnceProc(stk, 1).
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 1)] pushOnceProc
    [Val.loc _, Val.int 1]
    [Stmt.fork "pushOnceProc"
      [Expr.var "stk", Expr.val (Val.int 2)]] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked push-thread #1 (payload 1).
    iintro !>
    iapply pushOnceProc_wp_body
    iexact HI
  · -- Parent continuation: second fork (payload 2), then fall through.
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
      _ "pushOnceProc" [Expr.var "stk", Expr.val (Val.int 2)] pushOnceProc
      [Val.loc _, Val.int 2]
      [] _ [] _
      rfl (by agar_eval) rfl
    isplitr
    · -- Forked push-thread #2 (payload 2).
      iintro !>
      iapply pushOnceProc_wp_body
      iexact HI
    · -- Final parent continuation: fall through at Val.unit.
      iintro !>
      wp_done

end Agar.Logic

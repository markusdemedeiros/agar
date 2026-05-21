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
public import Agar.Iris.WpSpin

@[expose] public section

/-! # Invariant examples: `inv N P` for shared-heap reasoning

Four closed adequacy proofs that exercise Iris invariants of shape
`inv N (∃ v, l ↦ v)` and its disjunctive variants:

* `progInvLoad` — single thread, single invariant-mediated load.
* `progSharedFlag` — parent + forked writer share an invariant on `l`.
* `progSharedRead` — parent + forked reader, both consume the invariant
  via `wp_load_inv`.
* `progCasFlip` — CAS over a two-state disjunctive invariant.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-! ## The program

A single allocation, a single invariant-mediated load, and fall-through. -/

/-- `x := alloc 42 ; v := load x` and then fall through. -/
def progInvLoad : Program where
  procs := fun _ => none
  main  := ags(
    x := alloc 42 ;
    v := load x
  )

/-! ## The closed theorem

Adequacy conclusion: every terminated head thread of `progInvLoad`
carries `Val.unit`. The post-load local `v` is bound to *some* value,
but because the invariant has abstracted the cell's contents we
cannot — and do not — say which. -/

theorem progInvLoad_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progInvLoad n
            (Machine.initial progInvLoad) μ') :
    Machine.Adequate progInvLoad μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progInvLoad ?_ n μ' htr
  start_closed_proof_with_heap progInvLoad
  -- main := alloc "x" 42 ; load "v" x
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc_intro HP                             -- HP : l ↦ 42
  wp_steps                                      -- wp_skip_cons; wp_seq
  -- Goal: wp ⟨load "v" x, [], env.set "x" l, [], none⟩ ⌜·=Val.unit⌝
  -- Allocate `inv N (∃ v, l ↦ v)` *before* the load.
  wp_inv_alloc_pt HP HI 42
  -- Now perform the invariant-mediated load.
  iapply wp_load_inv (GF := GF) (F := F) (N := nroot)
    (Hsub := by rw [nclose_root])
    (heval := by agar_eval)
  iframe HI
  iintro !> %v HP
  iframe HP
  -- After the load: thread is `⟨skip, [], env.set "v" v, [], none⟩`,
  -- terminated with `toValue = some Val.unit`. Close via `wp_done`.
  wp_done

/-! ## Shared-heap concurrent closed adequacy

`progSharedFlag` is our first concurrent program with a SHARED heap
cell accessed by two threads via an invariant:

```
writeOne(l) := store l 1                -- forked thread body
main        := x := alloc 0 ;
               fork writeOne(x)         -- spawn child writer
                                        -- main then falls through to skip
```

Both threads access the cell `l` through the SAME invariant
`inv N (∃ v, l ↦ v)`. The forked thread uses `wp_store_inv` to open
the invariant atomically across its write.

### How the invariant is shared across the fork

After `inv_alloc`, the hypothesis `HI : inv N (...)` is *persistent*
(because `inv` lives under `□`). We immediately demote it to the
intuitionistic context with `iintro #HI` (after `imodintro` from
`fupd_wp`). When `wp_fork` splits the proof obligation into the
forked-thread WP and the parent-continuation WP via `isplitr`,
intuitionistic hypotheses are duplicated across the split — so BOTH
sub-proofs have `#HI` in scope, and the forked thread can feed it to
`wp_store_inv`.

Safety conclusion only: every thread terminates or is reducible, and a
terminated main thread carries `Val.unit`. The final value of the
shared cell is racy (could be `0` or `1`) and we make no claim about
it; the invariant has abstracted it away anyway. -/

def writeOne : Proc where
  params := ["l"]
  body   := ags( store l 1 )

def progSharedFlag : Program where
  procs := fun n => if n = "writeOne" then some writeOne else none
  main  := ags(
    x := alloc 0 ;
    fork writeOne(x)
  )

theorem progSharedFlag_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSharedFlag n
            (Machine.initial progSharedFlag) μ') :
    Machine.Adequate progSharedFlag μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progSharedFlag ?_ n μ' htr
  start_closed_proof_with_heap progSharedFlag
  -- main := alloc "x" 0 ; fork "writeOne" [.var "x"]
  wp_pures
  wp_alloc_intro HP                             -- HP : l ↦ 0
  -- `wp_pures` (not `wp_steps`): `wp_steps` would eagerly apply
  -- `wp_fork` and consume the fork before we get a chance to allocate
  -- the shared invariant.
  wp_pures
  -- Goal: wp ⟨fork "writeOne" [.var "x"], [], env.set "x" l, [], none⟩ ⌜·=Val.unit⌝
  -- Allocate `inv N (∃ v, l ↦ v)` BEFORE the fork; demote to intuitionistic
  -- so the persistent invariant survives `isplitr` across the fork.
  wp_inv_alloc_pt HP HI 0
  ihave #HI := HI
  -- Apply `wp_fork`. fork_post := emp; the forked thread's WP closes at `emp`.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "writeOne" [Expr.var "x"] writeOne [Val.loc _] [] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked thread: body = store l 1; env = bindParams ["l"] [.loc l].
    iintro !>
    unfold writeOne
    -- Goal: wp ⟨store (.var "l") 1, [], bindParams ["l"] [.loc l], [], none⟩
    --         (fun _ => emp)
    -- Use the atomic-triple form with the explicit body `∃ v, l ↦ v`,
    -- demonstrating that `wp_store_atomic` subsumes `wp_store_inv` even for
    -- the simple existential-body shape that `wp_store_inv` hard-codes.
    iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
      (P := iprop(∃ v : Val, points_to (GF := GF) (F := F) _ v))
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    -- Accessor: open `▷ ∃ v, l ↦ v`, pick the current vcur, hand it
    -- to the success wand, then close back with the new value `1`.
    iintro HP
    icases HP with ⟨%vcur, >HLk⟩
    imodintro
    iexists vcur
    iframe HLk
    iintro HLk
    imodintro
    isplitl [HLk]
    · inext; iexists (Val.int 1); iexact HLk
    wp_done
  · -- Parent continuation: terminal `⟨skip, [], _, [], none⟩` at Val.unit.
    iintro !>
    wp_done

/-! ## Shared-READ concurrent closed adequacy

`progSharedRead` complements `progSharedFlag` by exercising the
*read* side of the invariant on BOTH threads:

```
readerProc(l) := v := load l
main          := x := alloc 42 ;
                 fork readerProc(x) ;
                 w := load x
```

Both the forked reader and the main-thread's trailing load go
through the SAME invariant `inv N (∃ v, l ↦ v)`, validating
`wp_load_inv` under sharing. -/

def readerProc : Proc where
  params := ["l"]
  body   := ags( v := load l )

def progSharedRead : Program where
  procs := fun n => if n = "readerProc" then some readerProc else none
  main  := ags(
    x := alloc 42 ;
    fork readerProc(x) ;
    w := load x
  )

theorem progSharedRead_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSharedRead n
            (Machine.initial progSharedRead) μ') :
    Machine.Adequate progSharedRead μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progSharedRead ?_ n μ' htr
  start_closed_proof_with_heap progSharedRead
  -- main := alloc "x" 42 ; fork "readerProc" [.var "x"] ; load "w" x
  wp_pures
  wp_alloc_intro HP                             -- HP : l ↦ 42
  -- Allocate the shared invariant BEFORE the fork.
  -- Step through to expose `fork` as the head statement.
  wp_pures
  -- Allocate the shared invariant; demote to intuitionistic so it survives
  -- both fork splits AND the parent's trailing `load`.
  wp_inv_alloc_pt HP HI 42
  ihave #HI := HI
  -- Apply `wp_fork`.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "readerProc" [Expr.var "x"] readerProc [Val.loc _]
    [Stmt.load "w" (Expr.var "x")] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked reader thread: body = v := load l.
    iintro !>
    unfold readerProc
    -- Goal: wp ⟨load "v" (.var "l"), [], bindParams ["l"] [.loc l], [], none⟩
    --         (fun _ => emp)
    iapply wp_load_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heval := by agar_eval)
    iframe HI
    iintro !> %v HP
    iframe HP
    wp_done
  · -- Parent continuation: still has `w := load x` to execute.
    wp_pures
    -- Goal: wp ⟨load "w" (.var "x"), [], env.set "x" l, [], none⟩ ⌜·=Val.unit⌝
    -- The persistent `#HI` is duplicated by `isplitr`, so it is still
    -- available here for the main thread's load.
    iapply wp_load_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heval := by agar_eval)
    iframe HI
    iintro !> %v HP
    iframe HP
    wp_done

/-! ## CAS over a disjunctive invariant: `progCasFlip`

A minimal demo of the `wp_cas_atomic_split` combinator. The invariant
body is the disjunction `(x ↦ 0) ∨ (x ↦ 1)`; the program performs a
single `cas x 0 1` mediated by the invariant. -/

/-- `x := alloc 0 ; r := cas x 0 1` and then fall through. -/
def progCasFlip : Program where
  procs := fun _ => none
  main  := ags(
    x := alloc 0 ;
    r := cas x 0 1
  )

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

theorem progCasFlip_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCasFlip n
            (Machine.initial progCasFlip) μ') :
    Machine.Adequate progCasFlip μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progCasFlip ?_ n μ' htr
  start_closed_proof_with_heap progCasFlip
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc_intro HP                             -- HP : l ↦ 0
  wp_steps                                      -- wp_skip_cons; wp_seq
  -- Allocate `inv N ((l ↦ 0) ∨ (l ↦ 1))` from HP : l ↦ 0.
  iapply fupd_wp
  imod (inv_alloc nroot CoPset.full
          iprop(points_to (GF := GF) (F := F) l (Val.int 0)
                ∨ points_to (GF := GF) (F := F) l (Val.int 1))) $$ [HP] with HI
  · inext; ileft; iexact HP
  imodintro
  -- Demo: `wp_cas_atomic_split` strips ▷ across the disjunction and
  -- leaves two goals (success-disjunct present / failure-disjunct present).
  wp_cas_atomic_split HI
    iprop(points_to (GF := GF) (F := F) l (Val.int 0)
          ∨ points_to (GF := GF) (F := F) l (Val.int 1))
    (Val.int 0) (Val.int 1)
    val_beq_int0_false
    with (>HLk0 | >HLk1)
  · -- Disjunct 1: l ↦ 0. CAS succeeds; fail-wand discharged by contradiction.
    imodintro
    iexists (Val.int 0)
    iframe HLk0
    isplitl []
    · -- Success wand: receives ⌜0 = 0⌝ and l ↦ 1; close into right disjunct.
      iintro %_ HLk1'
      imodintro
      isplitl [HLk1']
      · inext; iright; iexact HLk1'
      wp_done
    · -- Failure wand: ⌜0 ≠ 0⌝ — impossible.
      iintro %hne _
      exact absurd rfl hne
  · -- Disjunct 2: l ↦ 1. CAS fails; success-wand discharged by contradiction.
    imodintro
    iexists (Val.int 1)
    iframe HLk1
    isplitl []
    · -- Success wand: requires ⌜1 = 0⌝ — impossible.
      iintro %heq _
      exact Val.noConfusion heq (fun h => absurd h (by decide))
    · -- Failure wand: receives ⌜1 ≠ 0⌝ and l ↦ 1; close into right disjunct.
      iintro %_ HLk1'
      imodintro
      isplitl [HLk1']
      · inext; iright; iexact HLk1'
      wp_done

end Agar.Logic

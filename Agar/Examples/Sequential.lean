module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Examples.Recursion

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

@[expose] public section

/-! # Sequential heap-touching example programs

* `progSwap` — swap two heap cells via locals; exercises
                `alloc` / `load` / `store` / `free`.

We re-use `Examples.procTable` from `Recursion.lean`.
-/

namespace Agar
namespace Examples

/-! ## Heap swap

Allocate two cells, swap their contents through temporaries, free both.
-/

def progSwap : Program where
  procs := procTable []
  main  := ags(
    p := alloc 1 ;
    q := alloc 2 ;
    a := load p ;
    b := load q ;
    store p b ;
    store q a ;
    free p ;
    free q
  )

example : progSwap.procs "anything" = none := rfl

end Examples
end Agar


namespace Agar.Logic

open Iris Iris.BI Iris.OFE

def progSkip : Program where
  procs := fun _ => none
  main  := Stmt.skip

/-- Closed safety + main-postcondition for `progSkip` via
`wp_strong_adequacy`. Pure-Lean conclusion, no Iris-level
proposition leaks. -/
theorem progSkip_closed
    {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSkip n (Machine.initial progSkip) μ') :
    Machine.Adequate progSkip μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy (GF := GF)
    (φ := fun v => v = Val.unit) progSkip ?_ n μ' htr
  intro _LC
  letI SI : StateInterp GF := ⟨fun _ => iprop(emp)⟩
  refine BI.exists_intro' SI ?_
  refine BI.exists_intro' iprop(emp : IProp GF) ?_
  -- `state_interp Mem.empty = emp` under `SI`; the initial thread
  -- `⟨skip, [], _, [], none⟩` is at value `Val.unit`, so the WP is
  -- the value disjunct of `wp_unfold`.
  istart
  iintro _
  isplitr
  · iemp_intro
  · iapply (equiv_iff.mp (wp_unfold (GF := GF) progSkip.procs
      iprop(emp : IProp GF) CoPset.full (Thread.initial progSkip.main)
      (fun v => iprop(⌜v = Val.unit⌝ : IProp GF)))).mpr
    ileft
    iexists Val.unit
    isplitr
    · itrivial
    · imodintro; itrivial


/-! ## A heap-touching adequacy-closed theorem

`progAlloc1` allocates a single cell holding `1`, then terminates. The
proof uses `wp_strong_adequacy_bupd` to first allocate the initial heap
ghost (via `heap_init`), package a `AgarG` instance, and then discharge
the WP via `wp_alloc` followed by the value branch of the unfolded WP. -/

/-- Allocate one cell holding `1`, then fall through. -/
def progAlloc1 : Program where
  procs := fun _ => none
  main  := Stmt.alloc "x" (Expr.val (.int 1))

theorem progAlloc1_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progAlloc1 n (Machine.initial progAlloc1) μ') :
    Machine.Adequate progAlloc1 μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progAlloc1 ?_ n μ' htr
  intro _LC
  -- Allocate initial heap-auth, package AgarG/SI, supply emp-frame, and
  -- frame HA; leaves the WP for `alloc "x" 1` to be discharged below.
  heap_adequacy_intro progAlloc1
  -- Goal: `wp _ emp ⊤ (Thread.initial (alloc "x" 1)) (fun v => ⌜v = Val.unit⌝)`.
  -- Apply `wp_alloc` via the tactic-suite shorthand `wp_alloc_intro`.
  wp_alloc_intro _Hpt
  -- Goal: `wp _ emp ⊤ ⟨skip, [], env.set "x" (.loc l), [], none⟩ ⌜·=Val.unit⌝`.
  -- Terminal value-thread at `Val.unit`; closed by `wp_done`.
  wp_done


/-! ## A round-trip heap program

`progAllocLoadFree` allocates a cell holding `7`, reads it back into `v`,
frees the cell, and returns `v`. The closed theorem says: any terminated
main thread carries `Val.int 7`. The proof drives the WP via the
`wp_alloc / wp_load HP / wp_free HP` tactic suite. -/

def progAllocLoadFree : Program where
  procs := fun _ => none
  main  := ags(
    x := alloc 7 ;
    v := load x ;
    free x ;
    return v
  )

theorem progAllocLoadFree_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progAllocLoadFree n
            (Machine.initial progAllocLoadFree) μ') :
    Machine.Adequate progAllocLoadFree μ' (Val.int 7) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 7) progAllocLoadFree ?_ n μ' htr
  intro _LC
  heap_adequacy_intro progAllocLoadFree
  -- main := alloc "x" 7 ; load "v" x ; free x ; return v
  wp_steps                 -- wp_seq, drop later
  wp_alloc_intro HP        -- alloc, bind l and HP : l ↦ 7
  wp_steps                 -- wp_skip_cons; wp_seq
  wp_load_keep HP          -- consume load, keep points-to
  wp_steps                 -- wp_skip_cons; wp_seq
  wp_free HP               -- consume free
  wp_steps                 -- wp_skip_cons then wp_ret_top
  itrivial


/-! ## Two-cell swap

`progSwap` from `Examples/DataStructures.lean`: allocate cells `p ↦ 1` and `q ↦ 2`, load
both into locals `a` and `b`, store them back swapped, then free both. The
closed theorem says: every terminated main thread carries `Val.unit`. The
proof exercises four heap-step tactics (`wp_alloc_intro`, `wp_load`,
`wp_store`, `wp_free`) on two distinct cells. -/

theorem progSwap_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN Examples.progSwap n
            (Machine.initial Examples.progSwap) μ') :
    Machine.Adequate Examples.progSwap μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) Examples.progSwap ?_ n μ' htr
  intro _LC
  heap_adequacy_intro Examples.progSwap
  wp_steps
  wp_alloc_intro HP              -- p ↦ 1
  wp_steps
  wp_alloc_intro HQ              -- q ↦ 2
  wp_steps
  wp_load_keep HP
  wp_steps
  wp_load_keep HQ
  wp_steps
  wp_store_keep HP
  wp_steps
  wp_store_keep HQ
  wp_steps
  wp_free HP
  wp_steps
  wp_free HQ
  wp_steps
  wp_done


/-! ## Single-CAS round trip

`progCasOnce` allocates `x ↦ 5`, runs a successful `cas x 5 7` binding the
old value to `y`, then loads `x` into `v`, frees `x`, and returns `v`.
Since the CAS succeeds, the cell becomes `x ↦ 7`, and the final returned
value is `Val.int 7`. The closed theorem says: every terminated main
thread carries `Val.int 7`. The reflexivity obligation
`(Val.int 5 == Val.int 5) = true` is discharged by `val_beq_refl _`. -/

def progCasOnce : Program where
  procs := fun _ => none
  main  := ags(
    x := alloc 5 ;
    y := cas x 5 7 ;
    v := load x ;
    free x ;
    return v
  )

theorem progCasOnce_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCasOnce n
            (Machine.initial progCasOnce) μ') :
    Machine.Adequate progCasOnce μ' (Val.int 7) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 7) progCasOnce ?_ n μ' htr
  intro _LC
  heap_adequacy_intro progCasOnce
  -- main := alloc "x" 5 ; cas "y" x 5 7 ; load "v" x ; free x ; return v
  wp_steps                                                -- wp_seq, drop later
  wp_alloc_intro HP                                       -- x ↦ 5
  wp_steps                                                -- skip_cons; seq
  wp_cas_succ HP                                          -- x ↦ 7
  iintro !> HP
  wp_steps
  wp_load_keep HP                                         -- load returns 7
  wp_steps
  wp_free HP                                              -- free x
  wp_steps                                                -- skip_cons; ret_top
  itrivial


/-! ## First closed adequacy with a procedure call

`progCallSeven` defines a parameterless procedure `seven` whose body is
`return 7`, and a main thread that calls it, binds the result to `v`,
and returns `v`. Every terminated main thread carries `Val.int 7`.

The new piece exercised here is the `wp_call` / `wp_ret_pop_nil` chain:
`wp_step` recognises `call x f ()` and enters the callee body under a
fresh frame `⟨v, [], env⟩`; the callee's `return 7` is handled by
`wp_ret_pop_nil` (frame popped, return value bound to `v`); the caller
resumes at `⟨skip, [], env.set v 7, [], none⟩`, and finally
`wp_ret_top` closes the post at `Val.int 7`. -/

def seven : Proc where
  params := []
  body   := ags( return 7 )

def progCallSeven : Program where
  procs := fun n => if n = "seven" then some seven else none
  main  := ags(
    v := call seven() ;
    return v
  )

theorem progCallSeven_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCallSeven n
            (Machine.initial progCallSeven) μ') :
    Machine.Adequate progCallSeven μ' (Val.int 7) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 7) progCallSeven ?_ n μ' htr
  intro _LC
  heap_adequacy_intro progCallSeven
  wp_call_pure seven


/-! ## Closed adequacy with a procedure call carrying arithmetic arguments

`progCallAdd` defines a procedure `addProc` taking two parameters `a` and
`b` whose body is `return a + b`. The main thread calls it with arguments
`3` and `4`, binds the result to `v`, and returns `v`. Every terminated
main thread carries `Val.int 7`.

The new piece relative to `progCallSeven`: `wp_call` succeeds with
`evalArgs ∅ [3, 4] = some [.int 3, .int 4]` and the arity check
`2 = 2`. The callee's body then runs under an `Env` extended with
`a ↦ 3, b ↦ 4`, and the `return a + b` step uses `BinOp.eval` on the
binop. Both side-conditions are discharged by `agar_eval`. -/

def addProc : Proc where
  params := ["a", "b"]
  body   := ags( return a + b )

def progCallAdd : Program where
  procs := fun n => if n = "addProc" then some addProc else none
  main  := ags(
    v := call addProc(3, 4) ;
    return v
  )

theorem progCallAdd_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCallAdd n
            (Machine.initial progCallAdd) μ') :
    Machine.Adequate progCallAdd μ' (Val.int 7) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 7) progCallAdd ?_ n μ' htr
  intro _LC
  heap_adequacy_intro progCallAdd
  wp_call_pure addProc


end Agar.Logic

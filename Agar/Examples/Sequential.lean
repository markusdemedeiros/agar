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


/-! ## `progAlloc1` — single heap-touching alloc + terminate -/

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
  heap_adequacy_intro progAlloc1
  wp_alloc_intro _Hpt
  wp_done


/-! ## `progAllocLoadFree` — alloc, load, free, return `Val.int 7` -/

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
  adequacy_with_heap_intro progAllocLoadFree (Val.int 7)
  wp_steps
  wp_alloc_intro HP
  wp_steps
  wp_load_keep HP
  wp_steps                 -- wp_skip_cons; wp_seq
  wp_free HP               -- consume free
  wp_steps                 -- wp_skip_cons then wp_ret_top
  itrivial


/-! ## `progSwap` — alloc two cells, swap their contents, free both -/

theorem progSwap_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN Examples.progSwap n
            (Machine.initial Examples.progSwap) μ') :
    Machine.Adequate Examples.progSwap μ' Val.unit := by
  adequacy_with_heap_intro Examples.progSwap Val.unit
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


/-! ## `progCasOnce` — alloc 5, CAS 5→7, load, free, return `Val.int 7` -/

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
  adequacy_with_heap_intro progCasOnce (Val.int 7)
  wp_steps
  wp_alloc_intro HP
  wp_steps
  wp_cas_succ HP
  iintro !> HP
  wp_steps
  wp_load_keep HP
  wp_steps
  wp_free HP                                              -- free x
  wp_steps                                                -- skip_cons; ret_top
  itrivial


/-! ## `progCallSeven` — call a parameterless procedure, return its result -/

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
  adequacy_with_heap_intro progCallSeven (Val.int 7)
  wp_call_pure seven


/-! ## `progCallAdd` — call `addProc(3, 4)`, return `Val.int 7` -/

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
  adequacy_with_heap_intro progCallAdd (Val.int 7)
  wp_call_pure addProc


end Agar.Logic

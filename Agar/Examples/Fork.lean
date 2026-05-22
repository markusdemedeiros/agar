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

@[expose] public section

/-! # Fork example programs

* `progForkUnit`  — single auxiliary thread running `skip`.
* `progForkAlloc` — auxiliary thread does a self-contained alloc/free
                     round-trip; main falls through.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

/-! ## `progForkUnit` — fork `skip`, fall through to `Val.unit` -/

def unitProc : Proc where
  params := []
  body   := Stmt.skip

def progForkUnit : Program where
  procs := fun n => if n = "unitProc" then some unitProc else none
  main  := Stmt.fork "unitProc" []

theorem progForkUnit_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progForkUnit n (Machine.initial progForkUnit) μ') :
    Machine.Adequate progForkUnit μ' Val.unit := by
  adequacy_with_heap_intro progForkUnit Val.unit
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "unitProc" [] unitProc [] [] Env.empty [] _ rfl rfl rfl
  isplitr
  · iintro !>
    wp_done
  · iintro !>
    wp_done


/-! ## `progForkAlloc` — forked thread does `alloc 7 ; free x` round-trip -/

def allocFreeProc : Proc where
  params := []
  body   := ags(
    x := alloc 7 ;
    free x
  )

def progForkAlloc : Program where
  procs := fun n => if n = "allocFreeProc" then some allocFreeProc else none
  main  := Stmt.fork "allocFreeProc" []

theorem progForkAlloc_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progForkAlloc n (Machine.initial progForkAlloc) μ') :
    Machine.Adequate progForkAlloc μ' Val.unit := by
  adequacy_with_heap_intro progForkAlloc Val.unit
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "allocFreeProc" [] allocFreeProc [] [] Env.empty [] _ rfl rfl rfl
  isplitr
  · iintro !>
    unfold allocFreeProc
    wp_steps
    wp_alloc_intro HP
    wp_steps
    wp_free HP
    wp_steps
    wp_done
  · iintro !>
    wp_done

end Agar.Logic

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

/-! ## First concurrent closed adequacy

`progForkUnit` spawns one auxiliary thread running a procedure `unitProc`
whose body is `skip`, then the main thread falls through. Both the
forked thread and the (post-fork) main thread are terminal value-threads
carrying `Val.unit`.

We pick `fork_post := emp`: the forked thread's WP obligation collapses
to `emp ⊢ wp ⟨skip, [], _, [], none⟩ (fun _ => emp)`, dischargeable by
`wp_value` at `Val.unit`.
-/

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
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progForkUnit ?_ n μ' htr
  intro _LC
  heap_adequacy_intro progForkUnit
  -- WP of `Thread.initial (fork "unitProc" [])`. Apply `wp_fork` with fork_post := emp.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "unitProc" [] unitProc [] [] Env.empty [] _ rfl rfl rfl
  isplitr
  · -- Forked thread: body = skip; bindParams [] [] = Env.empty.
    -- Goal: ▷ wp _ emp ⊤ ⟨skip, [], Env.empty, [], none⟩ (fun _ => emp).
    iintro !>
    wp_done
  · -- Parent's continuation: `⟨skip, [], Env.empty, [], none⟩` at value `Val.unit`.
    iintro !>
    wp_done


/-! ## Concurrent + heap closed adequacy

`progForkAlloc` combines fork with heap activity: main forks a thread
running `allocFreeProc` whose body is `x := alloc 7 ; free x`, then
falls through. Both threads terminate at `Val.unit`; the forked
thread's heap activity is self-contained (alloc then free), so it
admits `fork_post := emp`.
-/

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
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progForkAlloc ?_ n μ' htr
  intro _LC
  heap_adequacy_intro progForkAlloc
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "allocFreeProc" [] allocFreeProc [] [] Env.empty [] _ rfl rfl rfl
  isplitr
  · -- Forked thread: body = alloc "x" 7 ; free x.
    iintro !>
    unfold allocFreeProc
    wp_steps
    wp_alloc_intro HP
    wp_steps
    wp_free HP
    wp_steps
    wp_done
  · -- Parent continuation: terminal value-thread at Val.unit.
    iintro !>
    wp_done

end Agar.Logic

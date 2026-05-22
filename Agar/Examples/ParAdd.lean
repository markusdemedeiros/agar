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

/-! # Parallel disjoint-write example: resource splitting across forks

`progParAdd` allocates two disjoint heap cells `a` and `b`, then spawns
two threads:

* Thread 1 stores `1` into `a` (only).
* Thread 2 stores `1` into `b` (only).

The main thread falls through. Both forked procedures share a single
body (`writerProc`) parameterised by a single location `p`.

This complements `Examples.Fork`, where the spawned threads either do
nothing observable or perform a self-contained alloc/free round-trip
with `emp` as their precondition. Here each thread genuinely *consumes
a points-to* supplied by the parent, and the proof exhibits the
separation-conjunction split

```
  a ↦ 0 ∗ b ↦ 0  ⊣⊢  (a ↦ 0)  ∗  (b ↦ 0)
```

routing one half to each forked thread via successive `wp_fork` /
`isplitr` applications. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

/-- The shared writer procedure: stores `1` into its single location
parameter. -/
def writerProc : Proc where
  params := ["p"]
  body   := ags(
    store p 1
  )

/-- `progParAdd` — two disjoint allocations, two writer threads. -/
def progParAdd : Program where
  procs := fun n => if n = "writerProc" then some writerProc else none
  main  := ags(
    a := alloc 0 ;
    b := alloc 0 ;
    fork writerProc(a) ;
    fork writerProc(b)
  )

/-! ## Per-thread WP

`writerProc.body` with `env = bindParams ["p"] [Val.loc l]` and a
points-to `l ↦ v` in the spatial context closes at `fork_post = emp`.

The points-to is *consumed*: after the store the cell contains
`Val.int 1`, but the thread is terminal at that point and we discard
the updated resource via the `fun _ => emp` post. -/

private theorem writerProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (l : Loc) (v : Val) :
    iprop(points_to (GF := GF) (F := F) l v) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨writerProc.body, [],
          bindParams writerProc.params [Val.loc l],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro HP
  unfold writerProc
  wp_store HP
  iintro !> _HP
  wp_done

/-! ## Closed adequacy theorem

Closes at `Val.unit`; the point is the *resource split*: separating
conjunction routes HA and HB to disjoint forked threads. -/

theorem progParAdd_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progParAdd n (Machine.initial progParAdd) μ') :
    Machine.Adequate progParAdd μ' Val.unit := by
  adequacy_with_heap_intro progParAdd Val.unit
  wp_pures
  wp_alloc_intro HA
  wp_pures
  wp_alloc_intro HB
  wp_pures
  wp_fork_emp "writerProc" [Expr.var "a"] writerProc [Val.loc _]
    [Stmt.fork "writerProc" [Expr.var "b"]]
  isplitl [HA]
  · iintro !>
    iapply writerProc_wp_body
    iexact HA
  · iintro !>
    wp_pures
    wp_fork_emp "writerProc" [Expr.var "b"] writerProc [Val.loc _] []
    isplitl [HB]
    · iintro !>
      iapply writerProc_wp_body
      iexact HB
    · iintro !>
      wp_done

end Agar.Logic

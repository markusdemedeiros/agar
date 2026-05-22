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

/-! # Sequential push-pop round-trip on a single-cell stack

The smallest "stack is a stack" witness: push `7`, pop, return the
popped value. Spec: `result = Val.int 7`. Only true if pop recovers
what push stored — a queue or a "drop-pushes" implementation would
fail this. Single-threaded, no invariants; resources are owned
directly through the linear proof. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

/-- Node literal: `Val.struct [("v", v), ("nx", nx)]`. Stored at a single
heap cell. `nx` is `Val.int 0` for the bottom node, `Val.loc l` for a
link to node `l`. -/
def nodeExpr (v nx : Expr) : Expr :=
  Expr.mk [("v", v), ("nx", nx)]

/-- Push `7` then pop, returning the popped payload. -/
def progStackPushPop : Program where
  procs := fun _ => none
  main := ags(
    stk  := alloc 0 ;
    node := alloc #(nodeExpr (Expr.val (Val.int 7)) (Expr.val (Val.int 0))) ;
    store stk node ;
    top  := load stk ;
    n    := load top ;
    v    := #(Expr.proj (Expr.var "n") "v") ;
    nx   := #(Expr.proj (Expr.var "n") "nx") ;
    store stk nx ;
    free top ;
    return v
  )

theorem progStackPushPop_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progStackPushPop n
            (Machine.initial progStackPushPop) μ') :
    Machine.Adequate progStackPushPop μ' (Val.int 7) := by
  adequacy_with_heap_intro progStackPushPop (Val.int 7)
  wp_steps
  wp_alloc_intro HStk         -- stk ↦ Val.int 0
  wp_steps
  wp_alloc_intro HNode        -- node ↦ Val.struct [("v",7),("nx",0)]
  wp_steps
  wp_store_keep HStk          -- stk ↦ Val.loc node
  wp_steps
  wp_load_keep HStk
  wp_steps
  wp_load_keep HNode
  wp_steps
  wp_store_keep HStk          -- stk ↦ Val.int 0 (popped)
  wp_steps
  wp_free HNode
  wp_steps
  itrivial

/-! ## `progStackLifo` — two-element LIFO witness

Push `1`, push `2`, pop, pop, return the second pop's value. Spec:
`result = Val.int 1`. The second pop returns the bottom element only
under LIFO discipline — a FIFO queue would return `2` (the first
inserted), a multiset/bag would be unable to commit to either. -/

def progStackLifo : Program where
  procs := fun _ => none
  main := ags(
    stk := alloc 0 ;
    -- push 1
    n1  := alloc #(nodeExpr (Expr.val (Val.int 1)) (Expr.val (Val.int 0))) ;
    store stk n1 ;
    -- push 2 (next = n1)
    old := load stk ;
    n2  := alloc #(nodeExpr (Expr.val (Val.int 2)) (Expr.var "old")) ;
    store stk n2 ;
    -- pop top (= 2, discard)
    top2 := load stk ;
    s2   := load top2 ;
    nx2  := #(Expr.proj (Expr.var "s2") "nx") ;
    store stk nx2 ;
    free top2 ;
    -- pop again (= 1, return)
    top1 := load stk ;
    s1   := load top1 ;
    v1   := #(Expr.proj (Expr.var "s1") "v") ;
    nx1  := #(Expr.proj (Expr.var "s1") "nx") ;
    store stk nx1 ;
    free top1 ;
    return v1
  )

theorem progStackLifo_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progStackLifo n
            (Machine.initial progStackLifo) μ') :
    Machine.Adequate progStackLifo μ' (Val.int 1) := by
  adequacy_with_heap_intro progStackLifo (Val.int 1)
  wp_steps
  wp_alloc_intro HStk
  wp_steps
  wp_alloc_intro HN1            -- n1 ↦ struct {v=1, nx=0}
  wp_steps
  wp_store_keep HStk            -- stk ↦ Val.loc n1
  wp_steps
  wp_load_keep HStk             -- env old = Val.loc n1
  wp_steps
  wp_alloc_intro HN2            -- n2 ↦ struct {v=2, nx=Val.loc n1}
  wp_steps
  wp_store_keep HStk            -- stk ↦ Val.loc n2
  wp_steps
  wp_load_keep HStk
  wp_steps
  wp_load_keep HN2
  wp_steps
  wp_store_keep HStk            -- stk ↦ Val.loc n1
  wp_steps
  wp_free HN2
  wp_steps
  wp_load_keep HStk
  wp_steps
  wp_load_keep HN1
  wp_steps
  wp_store_keep HStk
  wp_steps
  wp_free HN1
  wp_steps
  itrivial

/-! ## `progStackReverse` — list reversal via two stacks

Pre-populate `src` with `[1, 2, 3]` (3 on top). Three iterations of
"pop src, push dst" transfer all elements. Because each transfer
removes the top of `src` and makes it the new top of `dst`, the
LIFO-flip composes into a reversal: after three transfers `dst` is
`[3, 2, 1]` from bottom to top, with `1` on top.

The driver loop is hand-unrolled (three explicit transfers) so the
proof stays sequential and avoids the abstract-stack-chain
infrastructure that a general while-loop reversal would need.

Spec: `Machine.Adequate progStackReverse μ' (Val.int 1)`. Only true if
the transfer correctly reverses — a "lose pushes" implementation would
read garbage from `dst`'s top, a FIFO would return `3`, and a stack
that erases values would fail outright. -/

def progStackReverse : Program where
  procs := fun _ => none
  main := ags(
    -- Build src = [1, 2, 3] (3 on top).
    src := alloc 0 ;
    a1  := alloc #(nodeExpr (Expr.val (Val.int 1)) (Expr.val (Val.int 0))) ;
    store src a1 ;
    o1  := load src ;
    a2  := alloc #(nodeExpr (Expr.val (Val.int 2)) (Expr.var "o1")) ;
    store src a2 ;
    o2  := load src ;
    a3  := alloc #(nodeExpr (Expr.val (Val.int 3)) (Expr.var "o2")) ;
    store src a3 ;
    -- dst = empty.
    dst := alloc 0 ;
    -- Transfer #1: pop src (value 3), push onto dst.
    t1  := load src ;
    s1  := load t1 ;
    v1  := #(Expr.proj (Expr.var "s1") "v") ;
    nx1 := #(Expr.proj (Expr.var "s1") "nx") ;
    store src nx1 ;
    free t1 ;
    d0  := load dst ;
    b1  := alloc #(nodeExpr (Expr.var "v1") (Expr.var "d0")) ;
    store dst b1 ;
    -- Transfer #2: pop src (value 2), push onto dst.
    t2  := load src ;
    s2  := load t2 ;
    v2  := #(Expr.proj (Expr.var "s2") "v") ;
    nx2 := #(Expr.proj (Expr.var "s2") "nx") ;
    store src nx2 ;
    free t2 ;
    d1  := load dst ;
    b2  := alloc #(nodeExpr (Expr.var "v2") (Expr.var "d1")) ;
    store dst b2 ;
    -- Transfer #3: pop src (value 1), push onto dst.
    t3  := load src ;
    s3  := load t3 ;
    v3  := #(Expr.proj (Expr.var "s3") "v") ;
    nx3 := #(Expr.proj (Expr.var "s3") "nx") ;
    store src nx3 ;
    free t3 ;
    d2  := load dst ;
    b3  := alloc #(nodeExpr (Expr.var "v3") (Expr.var "d2")) ;
    store dst b3 ;
    -- Observe top of dst — should be the value that was at the bottom
    -- of src (i.e., the first-pushed value, `1`).
    top := load dst ;
    s   := load top ;
    w   := #(Expr.proj (Expr.var "s") "v") ;
    return w
  )

theorem progStackReverse_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progStackReverse n
            (Machine.initial progStackReverse) μ') :
    Machine.Adequate progStackReverse μ' (Val.int 1) := by
  adequacy_with_heap_intro progStackReverse (Val.int 1)
  -- Build src.
  wp_steps; wp_alloc_intro HSrc
  wp_steps; wp_alloc_intro HA1
  wp_steps; wp_store_keep HSrc
  wp_steps; wp_load_keep HSrc
  wp_steps; wp_alloc_intro HA2
  wp_steps; wp_store_keep HSrc
  wp_steps; wp_load_keep HSrc
  wp_steps; wp_alloc_intro HA3
  wp_steps; wp_store_keep HSrc
  wp_steps; wp_alloc_intro HDst
  -- Transfer #1: pop a3 (value 3), push as b1 onto dst.
  wp_steps; wp_load_keep HSrc
  wp_steps; wp_load_keep HA3
  wp_steps
  wp_steps
  wp_steps; wp_store_keep HSrc
  wp_steps; wp_free HA3
  wp_steps; wp_load_keep HDst
  wp_steps; wp_alloc_intro HB1
  wp_steps; wp_store_keep HDst
  -- Transfer #2: pop a2 (value 2), push as b2.
  wp_steps; wp_load_keep HSrc
  wp_steps; wp_load_keep HA2
  wp_steps
  wp_steps
  wp_steps; wp_store_keep HSrc
  wp_steps; wp_free HA2
  wp_steps; wp_load_keep HDst
  wp_steps; wp_alloc_intro HB2
  wp_steps; wp_store_keep HDst
  -- Transfer #3: pop a1 (value 1), push as b3 onto dst.
  wp_steps; wp_load_keep HSrc
  wp_steps; wp_load_keep HA1
  wp_steps
  wp_steps
  wp_steps; wp_store_keep HSrc
  wp_steps; wp_free HA1
  wp_steps; wp_load_keep HDst
  wp_steps; wp_alloc_intro HB3
  wp_steps; wp_store_keep HDst
  -- Read top of dst.
  wp_steps; wp_load_keep HDst
  wp_steps; wp_load_keep HB3
  wp_steps
  wp_steps
  itrivial

end Agar.Logic

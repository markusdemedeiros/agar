module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Denotational
public import Agar.Operational.Composition

@[expose] public section

/-! # Shared definitions for the `rangeProd` composite example

This file holds the surface-syntax definitions (`prodBody`, `prodProg`,
`rangeProd`, `rangeProdCaller`, `rangeProdComposite3`,
`rangeProdValue`, `helper_post`) shared by the Route A showcase in
`Agar/Examples/ExternalSolver.lean`. Both the legacy operational
`safe_compose` route and the Route B `CalleeBridge` route have been
retired; only Route A remains.

The helper computes `a * (a+1) * … * (a+n-1)` where `n` is baked into
the helper proc (no variable-length loops in `PureStmt`). The composite
forks a worker that calls `rangeProd(5)`, then the main thread calls
`rangeProd(1)` itself and returns the result — bare-bones "two pure
helper calls in parallel" with no shared memory, no CAS, no spin. -/

namespace Agar
open Agar.Logic
namespace SimpleRangeProd

/-! ## The helper -/

/-- Loop body: `acc := acc * i ; i := i + 1`. -/
def prodBody : PureStmt :=
  .seq (.assign "acc" (.bin .mul (.var "acc") (.var "i")))
       (.assign "i" (.bin .add (.var "i") (.val (.int 1))))

/-- Full body PureStmt: `acc := 1 ; i := a ; forN n prodBody`. The
parameter `a` is bound by the caller via `bindParams`. -/
def prodProg (n : Nat) : PureStmt :=
  .seq (.assign "acc" (.val (.int 1)))
   (.seq (.assign "i" (.var "a"))
    (.forN n prodBody))

/-- `rangeProd n`: pure helper proc. Param `a` is the start; the loop
count `n` is baked at the proc level. -/
def rangeProd (n : Nat) : Proc where
  params := ["a"]
  body   := .seq (embed (prodProg n)) (.ret (.var "acc"))

/-- Closed-form: `a * (a+1) * … * (a+k-1)`. -/
def rangeProdValue (a : Int) : Nat → Int
  | 0     => 1
  | k + 1 => a * rangeProdValue (a + 1) k

/-- The helper-post: at vs = [int a], the return value is the closed
form `rangeProdValue a n`. -/
def helper_post (n : Nat) (vs : List Val) (v : Val) : Prop :=
  ∃ a : Int, vs = [Val.int a] ∧ v = Val.int (rangeProdValue a n)

/-! ## The composite -/

/-- Worker proc: a thin caller of `rangeProd`. -/
def rangeProdCaller : Proc where
  params := []
  body   :=
    .seq (.call "r" "rangeProd" [.val (.int 5)])
         (.ret (.var "r"))

/-- The composite program (pinned to `n = 3` so the program is fully
ground for adequacy): `fork rangeProdCaller; x := call rangeProd(1); ret x`. -/
def rangeProdComposite3 : Program where
  procs := fun name =>
    if name = "rangeProd" then some (rangeProd 3)
    else if name = "rangeProdCaller" then some rangeProdCaller
    else none
  main  :=
    .seq (.fork "rangeProdCaller" [])
     (.seq (.call "x" "rangeProd" [.val (.int 1)])
           (.ret (.var "x")))

end SimpleRangeProd
end Agar

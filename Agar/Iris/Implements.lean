module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Iris.Adequacy
public import Agar.Iris.Heap
public import Agar.Iris.Hoare
public import Agar.Iris.Tactics
public import Agar.Iris.Library
public import Agar.Examples.Recursion

@[expose] public section

/-! # `implements` — high-level specs tying closed adequacy to math functions

The `_closed` theorems in `Examples/` only ever conclude
`Machine.safe prog (· = v)` for some concrete `v`. They are low-level:
they speak about a single program at a time, and the connection between
the program and the mathematical function it computes is folklore —
only visible by reading the value `v` in the conclusion.

This file lifts that connection into a named predicate:
`Program.implementsUnary prog f`  says **"the program family `prog`,
parameterised by an input `n`, implements the function `f`"**.  The
unary / binary / nullary variants cover the closed-adequacy examples we
have: factorial, gcd/min/max, constant programs, etc.

Each predicate is universally quantified over the Iris model
(`{GF} [InvGpreS GF] [AgarGpreS GF F]`), exactly matching the context
each `_closed` theorem assumes, so an `_closed` theorem can be plugged
in directly with no additional metatheory.
-/

namespace Agar.Logic

open Iris Iris.BI Agar Agar.Examples

/-- A family of programs `prog : Nat → Program` *implements* the
function `f : Nat → Int` if every reachable machine state of
`prog n` is safe and its main thread, if terminated, returns
`Val.int (f n)`. -/
def Program.implementsUnary (prog : Nat → Program) (f : Nat → Int) : Prop :=
  ∀ {GF : BundledGFunctors.{0,0,0}} {F : Type} [UFraction F]
    [InvGpreS GF] [AgarGpreS GF F]
    (n : Nat),
      Machine.safe (prog n) (· = Val.int (f n))

/-- Binary version: `prog : Nat → Nat → Program` implements
`f : Nat → Nat → Int`. -/
def Program.implementsBinary (prog : Nat → Nat → Program)
    (f : Nat → Nat → Int) : Prop :=
  ∀ {GF : BundledGFunctors.{0,0,0}} {F : Type} [UFraction F]
    [InvGpreS GF] [AgarGpreS GF F]
    (a b : Nat),
      Machine.safe (prog a b) (· = Val.int (f a b))

/-- Nullary version: a closed `prog : Program` implements a constant
value `v : Val` (the canonical observation of the main thread's
return value). -/
def Program.implementsNullary (prog : Program) (v : Val) : Prop :=
  ∀ {GF : BundledGFunctors.{0,0,0}} {F : Type} [UFraction F]
    [InvGpreS GF] [AgarGpreS GF F],
      Machine.safe prog (· = v)

/-! ## Worked example: `progFactWith` implements `factorial`

`progFactWith n` mirrors the shape of the existing `progFact3` driver
but parameterises over the natural-number input `n`. The proof of
`progFactWith_implements_factorial` is a direct instantiation of the
universal Hoare spec `factProc_spec_gen` (the very same lemma that
both `fact_3_closed` and `progFact_closed` invoke). -/

/-- `progFactWith n` = `v := call fact(n); return v`, using the
recursive `Examples.fact` procedure.

The integer literal in `age(n)` is the Lean-bound `n` lifted into
the Agar expression syntax. -/
def progFactWith (n : Nat) : Program where
  procs := fun nm => if nm = "fact" then some Examples.fact else none
  main  := ags(
    v := call fact(#(Expr.val (Val.int (n : Int)))) ;
    return v
  )

/-- The implements theorem: `progFactWith` computes `factorial` for
every natural-number input. The proof is structurally identical to
`fact_3_closed`, just universally quantified over `n`. -/
theorem progFactWith_implements_factorial :
    Program.implementsUnary progFactWith (fun n => (factorial n : Int)) := by
  intro GF F _ _ _ n
  refine wp_safe_bupd (GF := GF) (progFactWith n) ?_
  start_closed_proof_with_heap progFactWith
  -- main = (v := call fact(n)) ; return v
  wp_step                     -- wp_seq
  iintro !>
  -- Apply the universal Löb spec at the input `n`, target var "v",
  -- argument literal `age(n)`, continuation `[return v]`.
  wp_apply_gen_call_spec factProc_spec_gen
    (fun nm => if nm = "fact" then some Examples.fact else none)
    (fun v => iprop(⌜(fun w : Val => w = Val.int (factorial n : Int)) v⌝))
    n "v" (Expr.val (Val.int (n : Int))) [ags(return v)] Env.empty []
  iintro !>
  -- Post-thread: ⟨return v, [], Env.empty.set "v" (.int (factorial n)), [], none⟩.
  unfold factProc_post
  wp_steps
  itrivial

/-! ## `progMaxWith` implements `max`

Binary instantiation against the non-recursive `maxProc`. Proof
follows the `max_5_3_closed` template (uses `wp_apply_binop_spec`,
the convenience tactic for non-recursive binary procedures with
three `▷` modalities). -/

/-- `progMaxWith a b` = `v := call maxProc(a, b); return v`, using
the Library `maxProc` procedure. -/
def progMaxWith (a b : Nat) : Program where
  procs := fun nm => if nm = "maxProc" then some maxProc else none
  main  := ags(
    v := call maxProc(#(Expr.val (Val.int (a : Int))),
                      #(Expr.val (Val.int (b : Int)))) ;
    return v
  )

/-- `progMaxWith` computes `Nat.max` for every pair of natural-number
inputs. The math model is `if a < b then b else a` lifted to `Int`. -/
theorem progMaxWith_implements_max :
    Program.implementsBinary progMaxWith
      (fun a b => (if (a : Int) < (b : Int) then (b : Int) else (a : Int))) := by
  intro GF F _ _ _ a b
  unfold Machine.safe Machine.safeFrom Machine.SafeTp
  intro steps μ' htr k t hget
  refine wp_strong_adequacy_bupd_pointwise (GF := GF)
    (φ := fun v => v = Val.int (if (a : Int) < (b : Int) then (b : Int) else (a : Int)))
    (progMaxWith a b) ?_ steps μ' htr k t hget
  start_closed_proof_with_heap progMaxWith
  wp_step
  iintro !>
  wp_apply_binop_spec maxProc_spec (a : Int) (b : Int) "v"
    (Expr.val (Val.int (a : Int))) (Expr.val (Val.int (b : Int)))
    [ags(return v)] Env.empty []
  iintro !> !> !>
  unfold maxProc_post
  simp
  wp_done

/-! ## `progSumWith` implements `sumNat`

Unary instantiation against the recursive `sumProc`. Proof mirrors
`progFactWith_implements_factorial` exactly — only the spec name and
the math model change. -/

/-- `progSumWith n` = `v := call sumProc(n); return v`, using the
Library `sumProc` procedure. -/
def progSumWith (n : Nat) : Program where
  procs := fun nm => if nm = "sumProc" then some sumProc else none
  main  := ags(
    v := call sumProc(#(Expr.val (Val.int (n : Int)))) ;
    return v
  )

/-- The implements theorem: `progSumWith` computes `sumNat`
(the triangular number `0 + 1 + ... + n`) for every input. -/
theorem progSumWith_implements_sumNat :
    Program.implementsUnary progSumWith (fun n => (sumNat n : Int)) := by
  intro GF F _ _ _ n
  refine wp_safe_bupd (GF := GF) (progSumWith n) ?_
  start_closed_proof_with_heap progSumWith
  wp_step
  iintro !>
  wp_apply_gen_call_spec sumProc_spec_gen
    (fun nm => if nm = "sumProc" then some sumProc else none)
    (fun v => iprop(⌜(fun w : Val => w = Val.int (sumNat n : Int)) v⌝))
    n "v" (Expr.val (Val.int (n : Int))) [ags(return v)] Env.empty []
  iintro !>
  unfold sumProc_post
  wp_steps
  itrivial

end Agar.Logic

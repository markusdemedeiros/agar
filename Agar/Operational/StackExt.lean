module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics

@[expose] public section

/-! # Stack-extension and `tstep` (Work-In-Progress)

`stackExt t extra` appends `extra` at the bottom of `t.stack`.

This module is the operational scaffold for the Iris-level
`wp_stack_push` lemma. The intended top-level lemma is
`tstep_stackExt_preserve` (stated but not yet proved):

  Every successful `tstep` on `t` that is **not** `.ret e` with empty
  `t.stack` lifts to a `tstep` on `stackExt t extra` with stack-extended
  post-state.

The exceptional `.ret`-empty case is the genuine divergence and is
handled at the Iris level using the value disjunct.

## Status

The proof requires case analysis on `Stmt × chosen × cont/stack` with
13 stmt arms. With the 2026-05-26 semantic refinement (implicit
fallthrough uses `t.result.getD .unit` instead of `.unit`), the
mathematical content is uniform — each case is mechanical — but Lean's
`match` reduction over `cont` and `stack ++ extra` doesn't auto-simplify
when one of those is a literal, requiring per-case manual rewriting.

This file establishes:
* `stackExt` and its simp lemmas (used throughout).
* `tstep_stackExt_assign`: a single-stmt worked example showing the
  idiom — `unfold tstep; split; cases; rfl`.

The per-stmt lemma collection for the remaining 12 forms is left for a
focused follow-up; structurally the same idiom works.
-/

namespace Agar
namespace BodyTraj

/-- Append `extra` to the bottom of `t.stack`. -/
def stackExt (t : Thread) (extra : List Frame) : Thread :=
  { t with stack := t.stack ++ extra }

@[simp] theorem stackExt_stmt   (t : Thread) (e : List Frame) :
    (stackExt t e).stmt = t.stmt := rfl
@[simp] theorem stackExt_cont   (t : Thread) (e : List Frame) :
    (stackExt t e).cont = t.cont := rfl
@[simp] theorem stackExt_env    (t : Thread) (e : List Frame) :
    (stackExt t e).env = t.env := rfl
@[simp] theorem stackExt_stack  (t : Thread) (e : List Frame) :
    (stackExt t e).stack = t.stack ++ e := rfl
@[simp] theorem stackExt_result (t : Thread) (e : List Frame) :
    (stackExt t e).result = t.result := rfl

/-- Worked-example per-stmt case: `.assign` preserves stack-extension. -/
theorem tstep_stackExt_assign
    (procs : Name → Option Proc) (m : Mem) (x : Name) (e : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame) (result : Option Val)
    (v : Val) (extra : List Frame)
    (h : Expr.eval env e = some v) :
    tstep procs none m (stackExt ⟨.assign x e, cont, env, stack, result⟩ extra)
      = some (m, stackExt ⟨.skip, cont, env.set x v, stack, result⟩ extra, none) := by
  unfold tstep stackExt
  simp [h]

end BodyTraj
end Agar

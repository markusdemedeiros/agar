module

public import Agar.Lang.Denotational

@[expose] public section

namespace Agar

/-! # Marquee example: non-recursive `square(n) := n * n` procedure.

We define a Agar procedure body that reads its input parameter `"n"`,
writes `n * n` into the local variable `"r"`, and is invoked by the
top-level program via `pcall`. The marquee theorem closes the loop:
the denotation of `callSquare m` from the empty environment matches
the math function `m * m`, and via `Machine.denote_iff` this lifts to
operational reachability on the multi-thread machine. -/

/-- Body of the `square` procedure. Expects parameter `"n"` to be
bound on entry; writes `"r" := n * n`. -/
def squareBody : PureStmt :=
  .assign "r" (.bin .mul (.var "n") (.var "n"))

/-- The top-level program that invokes `square(m)` and stores the
result in caller-side variable `"result"`. -/
def callSquare (m : Int) : PureStmt :=
  pcall [("n", .val (.int m))] squareBody "result" (.var "r")

/-- The final environment after the call: `"n" ↦ m`, `"r" ↦ m*m`,
`"result" ↦ m*m`. -/
def squareEnv (m : Int) : Env :=
  ((Env.empty.set "n" (.int m)).set "r" (.int (m * m))).set
    "result" (.int (m * m))

/-- **Marquee identity.** `denote (callSquare m) Env.empty` succeeds
with the final environment binding `"result"` to `m * m`. -/
theorem denote_callSquare (m : Int) :
    denote (callSquare m) Env.empty = (some (), squareEnv m) := by
  rw [callSquare, denote_pcall]
  -- assignAll: assigns "n" := m, succeeds with env₁ = empty.set "n" (.int m).
  show (match denote (assignAll [("n", .val (.int m))]) Env.empty with
        | (none, ρ') => (none, ρ')
        | (some _, ρ₁) =>
          match denote squareBody ρ₁ with
          | (none, ρ') => (none, ρ')
          | (some _, ρ₂) =>
            match Expr.eval ρ₂ (.var "r") with
            | none   => (none, ρ₂)
            | some v => (some (), ρ₂.set "result" v)) = _
  have hA : denote (assignAll [("n", .val (.int m))]) Env.empty
      = (some (), Env.empty.set "n" (.int m)) := by
    show denote (.seq (.assign "n" (.val (.int m))) (assignAll [])) Env.empty = _
    show (match denote (.assign "n" (.val (.int m))) Env.empty with
          | (none, ρ') => (none, ρ')
          | (some _, ρ') => denote (assignAll []) ρ') = _
    show (match denote (.assign "n" (.val (.int m))) Env.empty with
          | (none, ρ') => (none, ρ')
          | (some _, ρ') => denote .skip ρ') = _
    rfl
  rw [hA]
  -- Now denote squareBody on (empty.set "n" m).
  let ρ₁ : Env := Env.empty.set "n" (.int m)
  have hn : ρ₁ "n" = some (.int m) := by simp [ρ₁, Env.set]
  have hev : Expr.eval ρ₁ (.bin .mul (.var "n") (.var "n"))
      = some (.int (m * m)) := by
    show (do let v₁ ← ρ₁ "n"; let v₂ ← ρ₁ "n"; BinOp.eval .mul v₁ v₂) = _
    rw [hn]; rfl
  show (match denote squareBody ρ₁ with
        | (none, ρ') => (none, ρ')
        | (some _, ρ₂) =>
          match Expr.eval ρ₂ (.var "r") with
          | none   => (none, ρ₂)
          | some v => (some (), ρ₂.set "result" v)) = _
  have hB : denote squareBody ρ₁ = (some (), ρ₁.set "r" (.int (m * m))) := by
    show (match Expr.eval ρ₁ (.bin .mul (.var "n") (.var "n")) with
          | none   => (none, ρ₁)
          | some v => (some (), ρ₁.set "r" v)) = _
    rw [hev]
  rw [hB]
  -- Now evaluate (.var "r") in ρ₁.set "r" (m*m): yields some (.int (m*m)).
  let ρ₂ : Env := ρ₁.set "r" (.int (m * m))
  have hr : Expr.eval ρ₂ (.var "r") = some (.int (m * m)) := by
    show ρ₂ "r" = _
    simp [ρ₂, ρ₁, Env.set]
  show (match Expr.eval ρ₂ (.var "r") with
        | none   => (none, ρ₂)
        | some v => (some (), ρ₂.set "result" v)) = _
  rw [hr]
  -- Final env equality.
  show (some (), ρ₂.set "result" (.int (m * m))) = (some (), squareEnv m)
  rfl

/-- Worked instance: `square(7) = 49`. -/
example : (denote (callSquare 7) Env.empty).2 "result" = some (.int 49) := by
  rw [denote_callSquare]; rfl

/-- **Operational corollary.** Via `Machine.denote_iff`, the multi-thread
operational machine for `callSquare m` reaches the terminated
single-thread configuration with environment `squareEnv m`. -/
theorem Machine.callSquare_reaches_square (m : Int) :
    Machine.StepStar (programOf (callSquare m))
      (Machine.initial (programOf (callSquare m)))
      ⟨Mem.empty, [mkT .skip [] (squareEnv m)]⟩ :=
  (Machine.denote_iff (callSquare m) (squareEnv m)).mp (denote_callSquare m)

end Agar

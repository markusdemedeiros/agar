module

public import Agar.Lang.Denotational

@[expose] public section

namespace Agar

/-! # Marquee numeric example: Euclidean algorithm by subtraction.

We compute `Nat.gcd a b` via a fuel-bounded `while` loop in the pure
denotational fragment, and lift the denotational identity to an
operational reachability statement via `Machine.denote_iff`.

The Agar program holds two positive ints `"a"` and `"b"` and repeatedly
subtracts the smaller from the larger until they become equal. The
remaining common value is the gcd; the program then copies it into
`"result"`.

For the marquee statement we restrict to `0 < a ∧ 0 < b` (otherwise the
subtraction loop diverges). Fuel is taken to be `a + b`, which suffices
because each loop iteration strictly decreases `a + b`. -/

/-- Body of the gcd loop: if `a > b` decrement `a`, else decrement `b`. -/
def gcdBody : PureStmt :=
  .ite (.bin .lt (.var "b") (.var "a"))
    (.assign "a" (.bin .sub (.var "a") (.var "b")))
    (.assign "b" (.bin .sub (.var "b") (.var "a")))

/-- Full gcd program: initialise `"a"`, `"b"`, loop until equal, then
copy into `"result"`. -/
def gcdPure (a b : Nat) : PureStmt :=
  .seq (.assign "a" (.val (.int a)))
   (.seq (.assign "b" (.val (.int b)))
    (.seq (.while_ (a + b) (.un .not (.bin .eq (.var "a") (.var "b"))) gcdBody)
          (.assign "result" (.var "a"))))

/-- Environment after running `gcd` to fixed point. -/
def gcdEnv (a b : Nat) : Env :=
  ((Env.empty.set "a" (.int (Nat.gcd a b))).set "b" (.int (Nat.gcd a b))).set
    "result" (.int (Nat.gcd a b))

/-! ## Loop invariant: each iteration preserves `Nat.gcd`. -/

/-- Evaluate the loop guard `¬ (a = b)`. -/
theorem eval_guard (a b : Int) (ρ : Env)
    (ha : ρ "a" = some (.int a)) (hb : ρ "b" = some (.int b)) :
    Expr.eval ρ (.un .not (.bin .eq (.var "a") (.var "b")))
      = some (.bool (!(a == b))) := by
  show (do
    let v ← (do
      let v₁ ← ρ "a"
      let v₂ ← ρ "b"
      BinOp.eval .eq v₁ v₂)
    UnOp.eval .not v) = _
  rw [ha, hb]; rfl

/-- Evaluate the body guard `b < a`. -/
theorem eval_lt (a b : Int) (ρ : Env)
    (ha : ρ "a" = some (.int a)) (hb : ρ "b" = some (.int b)) :
    Expr.eval ρ (.bin .lt (.var "b") (.var "a"))
      = some (.bool (decide (b < a))) := by
  show (do
    let v₁ ← ρ "b"
    let v₂ ← ρ "a"
    BinOp.eval .lt v₁ v₂) = _
  rw [ha, hb]; rfl

/-- The "ab environment" abstracting our two-variable state. -/
def abEnv (a b : Int) : Env :=
  (Env.empty.set "a" (.int a)).set "b" (.int b)

theorem abEnv_a (a b : Int) : (abEnv a b) "a" = some (.int a) := by
  simp [abEnv, Env.set]

theorem abEnv_b (a b : Int) : (abEnv a b) "b" = some (.int b) := by
  simp [abEnv, Env.set]

/-- A single body step takes `(a, b)` with `a ≠ b` to either
`(a - b, b)` (when `b < a`) or `(a, b - a)` (when `¬ b < a`, i.e. `a < b`). -/
theorem denote_gcdBody (a b : Int) :
    denote gcdBody (abEnv a b)
      = if decide (b < a) then (some (), abEnv (a - b) b)
        else (some (), abEnv a (b - a)) := by
  show (match Expr.eval (abEnv a b) (.bin .lt (.var "b") (.var "a")) with
        | some (.bool true)  => denote _ (abEnv a b)
        | some (.bool false) => denote _ (abEnv a b)
        | _                  => (none, abEnv a b)) = _
  rw [eval_lt a b _ (abEnv_a a b) (abEnv_b a b)]
  by_cases hba : b < a
  · simp [hba]
    show (match Expr.eval (abEnv a b) (.bin .sub (.var "a") (.var "b")) with
          | none   => (none, abEnv a b)
          | some v => (some (), (abEnv a b).set "a" v))
        = (some (), abEnv (a - b) b)
    have hev : Expr.eval (abEnv a b) (.bin .sub (.var "a") (.var "b"))
        = some (Val.int (a - b)) := by
      show (do let v₁ ← (abEnv a b) "a"; let v₂ ← (abEnv a b) "b";
               BinOp.eval .sub v₁ v₂) = _
      rw [abEnv_a, abEnv_b]; rfl
    rw [hev]
    show (some (), (abEnv a b).set "a" (Val.int (a - b))) = (some (), abEnv (a - b) b)
    congr 1
    funext x
    by_cases hx : x = "a"
    · subst hx; simp [abEnv, Env.set]
    · by_cases hxb : x = "b"
      · subst hxb; simp [abEnv, Env.set, hx]
      · simp [abEnv, Env.set, hx, hxb]
  · simp [hba]
    show (match Expr.eval (abEnv a b) (.bin .sub (.var "b") (.var "a")) with
          | none   => (none, abEnv a b)
          | some v => (some (), (abEnv a b).set "b" v))
        = (some (), abEnv a (b - a))
    have hev : Expr.eval (abEnv a b) (.bin .sub (.var "b") (.var "a"))
        = some (Val.int (b - a)) := by
      show (do let v₁ ← (abEnv a b) "b"; let v₂ ← (abEnv a b) "a";
               BinOp.eval .sub v₁ v₂) = _
      rw [abEnv_a, abEnv_b]; rfl
    rw [hev]
    show (some (), (abEnv a b).set "b" (Val.int (b - a))) = (some (), abEnv a (b - a))
    congr 1
    funext x
    by_cases hxb : x = "b"
    · subst hxb; simp [abEnv, Env.set]
    · simp [abEnv, Env.set, hxb]

/-! ## Connecting subtraction-loop to `Nat.gcd`. -/

/-- Symmetric form of `Nat.gcd_sub_self_left`. -/
theorem gcd_sub_left_eq (a b : Nat) (h : b ≤ a) :
    Nat.gcd (a - b) b = Nat.gcd a b :=
  Nat.gcd_sub_self_left h

theorem gcd_sub_right_eq (a b : Nat) (h : a ≤ b) :
    Nat.gcd a (b - a) = Nat.gcd a b := by
  rw [Nat.gcd_comm, Nat.gcd_sub_self_left h, Nat.gcd_comm]

/-- Loop invariant: with at least `a + b` fuel, the while loop terminates
in the configuration where `a = b = Nat.gcd a₀ b₀`, provided both
inputs start strictly positive. -/
theorem denote_gcd_loop :
    ∀ (n a b : Nat), 0 < a → 0 < b → a + b ≤ n →
      denote (.while_ n (.un .not (.bin .eq (.var "a") (.var "b"))) gcdBody)
             (abEnv a b)
        = (some (), abEnv (Nat.gcd a b) (Nat.gcd a b)) := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb hsum
      omega
  | succ k ih =>
      intro a b ha hb hsum
      rw [denote_while_succ]
      rw [eval_guard (a : Int) (b : Int) _ (abEnv_a _ _) (abEnv_b _ _)]
      by_cases hab : (a : Int) = b
      · -- guard `!(a == b)` is false: loop exits with `a = b`.
        have habN : a = b := by exact_mod_cast hab
        simp [hab]
        subst habN
        show (some (), abEnv (a : Int) a) = (some (), abEnv (Nat.gcd a a) (Nat.gcd a a))
        rw [Nat.gcd_self]
      · -- guard true: body runs once, then recurse with reduced fuel.
        have hne : ((a : Int) == (b : Int)) = false := by
          simp [hab]
        rw [hne]
        show denote (.seq gcdBody (.while_ k _ gcdBody)) (abEnv (a : Int) b) = _
        show (match denote gcdBody (abEnv (a : Int) b) with
              | (none, ρ')   => (none, ρ')
              | (some _, ρ') => denote (.while_ k _ gcdBody) ρ') = _
        rw [denote_gcdBody]
        by_cases hba : ((b : Int) < (a : Int))
        · simp [hba]
          have hbaN : b < a := by exact_mod_cast hba
          have hba_le : b ≤ a := Nat.le_of_lt hbaN
          have habN : a ≠ b := fun e => hab (by exact_mod_cast e)
          have hsub_pos : 0 < a - b := Nat.sub_pos_of_lt hbaN
          have hsum' : (a - b) + b ≤ k := by
            have : a + b = (a - b + b) + b := by omega
            omega
          have hcast : ((a : Int) - (b : Int)) = ((a - b : Nat) : Int) := by
            have := Nat.sub_add_cancel hba_le
            push_cast
            omega
          rw [hcast]
          rw [ih (a - b) b hsub_pos hb hsum']
          rw [gcd_sub_left_eq a b hba_le]
        · simp [hba]
          have hba' : ¬ b < a := fun h => hba (by exact_mod_cast h)
          have hab_lt : a < b := by
            have habN : a ≠ b := fun e => hab (by exact_mod_cast e)
            omega
          have hab_le : a ≤ b := Nat.le_of_lt hab_lt
          have hsub_pos : 0 < b - a := Nat.sub_pos_of_lt hab_lt
          have hsum' : a + (b - a) ≤ k := by
            have : a + b = a + ((b - a) + a) := by omega
            omega
          have hcast : ((b : Int) - (a : Int)) = ((b - a : Nat) : Int) := by
            push_cast; omega
          rw [hcast]
          rw [ih a (b - a) ha hsub_pos hsum']
          rw [gcd_sub_right_eq a b hab_le]

/-! ## Marquee theorem and operational corollary. -/

/-- **Marquee gcd identity.** With positive inputs, the denotation of
`gcdPure a b` terminates with `"result"` bound to `Nat.gcd a b`. -/
theorem denote_gcdPure (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    denote (gcdPure a b) Env.empty = (some (), gcdEnv a b) := by
  show (match denote (.assign "a" (.val (.int a))) Env.empty with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote _ ρ') = _
  show denote (.seq (.assign "b" (.val (.int b)))
              (.seq (.while_ (a + b) _ gcdBody) (.assign "result" (.var "a"))))
        (Env.empty.set "a" (.int a)) = _
  show (match denote (.assign "b" (.val (.int b)))
              (Env.empty.set "a" (.int a)) with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote _ ρ') = _
  show denote (.seq (.while_ (a + b) _ gcdBody) (.assign "result" (.var "a")))
        ((Env.empty.set "a" (.int a)).set "b" (.int b)) = _
  show (match denote (.while_ (a + b) _ gcdBody) (abEnv a b) with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote (.assign "result" (.var "a")) ρ') = _
  rw [denote_gcd_loop (a + b) a b ha hb (Nat.le_refl _)]
  show denote (.assign "result" (.var "a"))
        (abEnv ((Nat.gcd a b : Nat) : Int) ((Nat.gcd a b : Nat) : Int)) = _
  have heva : Expr.eval (abEnv ((Nat.gcd a b : Nat) : Int) ((Nat.gcd a b : Nat) : Int)) (.var "a")
      = some (.int (Nat.gcd a b)) := abEnv_a _ _
  simp only [denote, heva]
  -- Goal: (some (), (abEnv g g).set "result" (.int g)) = (some (), gcdEnv a b)
  show (some (), (abEnv ((Nat.gcd a b : Nat) : Int) ((Nat.gcd a b : Nat) : Int)).set
                    "result" (.int (Nat.gcd a b))) = (some (), gcdEnv a b)
  refine congrArg (Prod.mk _) ?_
  funext x
  by_cases hr : x = "result"
  · subst hr; simp [abEnv, gcdEnv, Env.set]
  · by_cases hb' : x = "b"
    · subst hb'; simp [abEnv, gcdEnv, Env.set, hr]
    · by_cases ha' : x = "a"
      · subst ha'; simp [abEnv, gcdEnv, Env.set, hr, hb']
      · simp [abEnv, gcdEnv, Env.set, hr, hb', ha']

/-- **Operational corollary.** Via `Machine.denote_iff`, the multi-thread
operational machine for `gcdPure a b` reaches the terminated
single-thread configuration whose environment binds `"result"` to
`Nat.gcd a b`. -/
theorem Machine.gcdPure_reaches_gcd (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Machine.StepStar (programOf (gcdPure a b))
      (Machine.initial (programOf (gcdPure a b)))
      ⟨Mem.empty, [mkT .skip [] (gcdEnv a b)]⟩ :=
  (Machine.denote_iff (gcdPure a b) (gcdEnv a b)).mp (denote_gcdPure a b ha hb)

/-- Worked instance: `gcdPure 12 18` produces `6` in `"result"`. -/
example : (denote (gcdPure 12 18) Env.empty).2 "result" = some (.int 6) := by
  rw [denote_gcdPure 12 18 (by decide) (by decide)]
  rfl

end Agar

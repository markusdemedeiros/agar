module

@[expose] public section

namespace Agar

abbrev Name := String
abbrev Loc  := Nat

inductive Val where
  | int    : Int → Val
  | bool   : Bool → Val
  | loc    : Loc → Val
  | unit   : Val
  | struct : List (Name × Val) → Val
  deriving Inhabited

-- Explicit structural equality on Val. We avoid `deriving BEq`
-- because the module system marks the generated `beq` opaque,
-- blocking val_beq_refl-style facts that downstream proofs need.
mutual
  def Val.beq : Val → Val → Bool
    | .int i, .int j => i == j
    | .bool a, .bool b => a == b
    | .loc l, .loc m => l == m
    | .unit, .unit => true
    | .struct fs, .struct gs => Val.beqFields fs gs
    | _, _ => false
  def Val.beqFields : List (Name × Val) → List (Name × Val) → Bool
    | [], [] => true
    | (n, v) :: r, (m, w) :: s => n == m && Val.beq v w && Val.beqFields r s
    | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

-- Reflexivity for the explicit Val equality. Unlike the derived BEq,
-- this is provable from outside the defining module.
mutual
  theorem val_beq_refl : ∀ v : Val, (v == v) = true
    | .int i => by show (i == i) = true; simp
    | .bool b => by show (b == b) = true; cases b <;> rfl
    | .loc l => by show (l == l) = true; simp
    | .unit => rfl
    | .struct fs => Val.beqFields_refl fs
  theorem Val.beqFields_refl :
      ∀ fs : List (Name × Val), Val.beqFields fs fs = true
    | [] => rfl
    | (n, v) :: r => by
        show (n == n && Val.beq v v && Val.beqFields r r) = true
        rw [show Val.beq v v = true from val_beq_refl v,
            Val.beqFields_refl r,
            show (n == n) = true from by simp]
        rfl
end

/-- Pointwise discriminator: any value distinct from `Val.int n` BEq-tests
to `false`. This is the contrapositive companion to `val_beq_refl`, used
to discharge the failure-side side condition of `wp_cas_*` whenever the
expected value is a specific integer. Lives here (next to `Val.beq`)
rather than in each example so that the 6+ specialised copies that
existed across `Examples/` can all reduce to a single named lemma. -/
theorem val_beq_int_false (n : Int) :
    ∀ v : Val, v ≠ Val.int n → (v == Val.int n) = false := by
  intro v hne
  cases v with
  | int i =>
      show (i == n) = false
      have : i ≠ n := fun h => hne (by cases h; rfl)
      simp [this]
  | bool _ => rfl
  | loc _ => rfl
  | unit => rfl
  | struct _ => rfl

inductive BinOp where
  | add | sub | mul | eq | lt | and | or
  deriving DecidableEq, Inhabited

inductive UnOp where
  | neg | not
  deriving DecidableEq, Inhabited

inductive Expr where
  | val  : Val → Expr
  | var  : Name → Expr
  | bin  : BinOp → Expr → Expr → Expr
  | un   : UnOp → Expr → Expr
  | mk   : List (Name × Expr) → Expr
  | proj : Expr → Name → Expr
  | upd  : Expr → Name → Expr → Expr

inductive Stmt where
  | skip    : Stmt
  | assign  : Name → Expr → Stmt
  | load    : Name → Expr → Stmt
  | store   : Expr → Expr → Stmt
  | alloc   : Name → Expr → Stmt
  | free    : Expr → Stmt
  | cas     : Name → Expr → Expr → Expr → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ite     : Expr → Stmt → Stmt → Stmt
  | whileDo : Expr → Stmt → Stmt
  | call    : Name → Name → List Expr → Stmt
  | ret     : Expr → Stmt
  | fork    : Name → List Expr → Stmt

structure Proc where
  params : List Name
  body   : Stmt

structure Program where
  procs : Name → Option Proc
  main  : Stmt

end Agar

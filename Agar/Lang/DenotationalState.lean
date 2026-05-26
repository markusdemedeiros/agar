module

public import Agar.Lang.Semantics
public import Agar.Lang.Denotational

@[expose] public section

namespace Agar

/-! # State-bearing denotation (heap-touching fragment)

This file extends `Agar.Lang.Denotational` to a fragment that touches
the heap. It defines:

* `StateStmt`: a structural pure terminating fragment extended with
  `.load / .store / .free / .cas / .alloc`.
* `denote_state`: total denotation `StateStmt → Env × Mem → Option Unit
  × Env × Mem`, structurally mirroring `denote` on shared cases and
  threading the `Mem` through heap operations.

No proofs yet — this is the data-type and denotation only. Soundness
(`denote_state_sound`: convergent denotation drives the operational
chain to terminate) lives in a follow-up. See `HYPOTHESIS.md` §8.10–§8.11
for the design context.

`.alloc` takes the location as a *deterministic* argument, threading a
`FreshSupply := Nat`-typed counter through the denotation. This matches
the operational `Machine.Step`'s existentially-quantified `chosen : Loc`
by binding `chosen := freshSupply` at the bridge level. -/

/-- The state-bearing pure terminating fragment. Extends `PureStmt`'s
shape with heap operations. `.call / .fork / .ret` are excluded
(same as `PureStmt`). -/
inductive StateStmt where
  | skip   : StateStmt
  | assign : Name → Expr → StateStmt
  | seq    : StateStmt → StateStmt → StateStmt
  | ite    : Expr → StateStmt → StateStmt → StateStmt
  | repeat : Nat → StateStmt → StateStmt
  | forN   : Nat → StateStmt → StateStmt
  /-- Fuel-bounded `while`. -/
  | while_ : Nat → Expr → StateStmt → StateStmt
  /-- `load x e`: evaluate `e` to a `.loc l`, set `x := m.load l`. -/
  | load   : Name → Expr → StateStmt
  /-- `store eL eV`: evaluate both, update `eL`'s pointee to `eV`'s value. -/
  | store  : Expr → Expr → StateStmt
  /-- `free e`: evaluate to `.loc l`, free the slot. -/
  | free   : Expr → StateStmt
  /-- `cas x eL eO eN`: evaluate, compare-and-set; `x` records the
  pre-swap value. -/
  | cas    : Name → Expr → Expr → Expr → StateStmt
  /-- `alloc x e`: allocate at the *next* slot from the fresh supply
  with value `Expr.eval e`. -/
  | alloc  : Name → Expr → StateStmt

/-- A `StatePack` bundles the components threaded through `denote_state`:
local env, memory, and a fresh-location supply. -/
structure StatePack where
  env    : Env
  mem    : Mem
  fresh  : Nat
  deriving Inhabited

abbrev StateDenot := StateM StatePack (Option Unit)

/-- `iter_st` is the state-bearing analogue of `iter`. -/
def iter_st (body : StateDenot) : Nat → StateDenot
  | 0,     p => (some (), p)
  | n + 1, p =>
      match body p with
      | (none, p')   => (none, p')
      | (some _, p') => iter_st body n p'

/-- `iterWhile_st` is the state-bearing analogue of `iterWhile`. -/
def iterWhile_st (g : Env → Option Val) (body : StateDenot) : Nat → StateDenot
  | 0,     p => (none, p)
  | n + 1, p =>
      match g p.env with
      | some (.bool true) =>
          match body p with
          | (none, p')   => (none, p')
          | (some _, p') => iterWhile_st g body n p'
      | some (.bool false) => (some (), p)
      | _ => (none, p)

/-- **State-bearing denotation.** Same shape as `denote` on shared
cases; the heap operations consume/produce `Mem` via the `StatePack`. -/
def denote_state : StateStmt → StateDenot
  | .skip          => fun p => (some (), p)
  | .assign x e    => fun p =>
      match Expr.eval p.env e with
      | none   => (none, p)
      | some v => (some (), { p with env := p.env.set x v })
  | .seq s₁ s₂     => fun p =>
      match denote_state s₁ p with
      | (none, p')   => (none, p')
      | (some _, p') => denote_state s₂ p'
  | .ite e s₁ s₂   => fun p =>
      match Expr.eval p.env e with
      | some (.bool true)  => denote_state s₁ p
      | some (.bool false) => denote_state s₂ p
      | _                  => (none, p)
  | .repeat n s    => iter_st (denote_state s) n
  | .forN n s      => iter_st (denote_state s) n
  | .while_ n g s  => iterWhile_st (fun ρ => Expr.eval ρ g) (denote_state s) n
  | .load x e      => fun p =>
      match Expr.eval p.env e with
      | some (.loc l) =>
          match p.mem.load l with
          | some w => (some (), { p with env := p.env.set x w })
          | none   => (none, p)
      | _ => (none, p)
  | .store eL eV   => fun p =>
      match Expr.eval p.env eL, Expr.eval p.env eV with
      | some (.loc l), some v =>
          match p.mem.store l v with
          | some m' => (some (), { p with mem := m' })
          | none    => (none, p)
      | _, _ => (none, p)
  | .free e        => fun p =>
      match Expr.eval p.env e with
      | some (.loc l) =>
          match p.mem.free l with
          | some m' => (some (), { p with mem := m' })
          | none    => (none, p)
      | _ => (none, p)
  | .cas x eL eO eN => fun p =>
      match Expr.eval p.env eL, Expr.eval p.env eO, Expr.eval p.env eN with
      | some (.loc l), some vO, some vN =>
          match p.mem.load l with
          | none     => (none, p)
          | some cur =>
              if cur == vO then
                match p.mem.store l vN with
                | some m' => (some (),
                    { p with env := p.env.set x cur, mem := m' })
                | none    => (none, p)
              else
                (some (), { p with env := p.env.set x cur })
      | _, _, _ => (none, p)
  | .alloc x e     => fun p =>
      match Expr.eval p.env e with
      | none   => (none, p)
      | some v =>
          -- Deterministic: allocate at the next fresh slot, bump supply.
          let l := p.fresh
          match p.mem.alloc l v with
          | some m' => (some (),
              { env := p.env.set x (.loc l), mem := m', fresh := l + 1 })
          | none    =>
              -- The slot is already occupied; the fresh supply was
              -- desynchronised from the actual heap. This is the
              -- denotation's "stuck" case for alloc, paralleling
              -- `none` from `Mem.alloc`.
              (none, p)

/-! ## Sanity simp lemmas

Direct reductions for `denote_state` on the leaf and one-step
constructors. The control-flow constructors (seq/ite/repeat/forN/while_)
already reduce by `simp [denote_state]`. -/

@[simp] theorem denote_state_skip (p : StatePack) :
    denote_state .skip p = (some (), p) := rfl

@[simp] theorem denote_state_assign (x : Name) (e : Expr) (p : StatePack) :
    denote_state (.assign x e) p =
      (match Expr.eval p.env e with
       | none   => (none, p)
       | some v => (some (), { p with env := p.env.set x v })) := rfl

@[simp] theorem denote_state_forN_zero (s : StateStmt) (p : StatePack) :
    denote_state (.forN 0 s) p = (some (), p) := rfl

theorem denote_state_forN_succ (n : Nat) (s : StateStmt) (p : StatePack) :
    denote_state (.forN (n+1) s) p = denote_state (.seq s (.forN n s)) p := by
  show iter_st (denote_state s) (n+1) p = _
  simp only [denote_state, iter_st]

@[simp] theorem denote_state_while_zero (g : Expr) (s : StateStmt) (p : StatePack) :
    denote_state (.while_ 0 g s) p = (none, p) := rfl

theorem denote_state_while_succ (n : Nat) (g : Expr) (s : StateStmt) (p : StatePack) :
    denote_state (.while_ (n+1) g s) p =
      match Expr.eval p.env g with
      | some (.bool true)  => denote_state (.seq s (.while_ n g s)) p
      | some (.bool false) => (some (), p)
      | _ => (none, p) := by
  show iterWhile_st (fun ρ => Expr.eval ρ g) (denote_state s) (n + 1) p = _
  unfold iterWhile_st
  rcases hev : Expr.eval p.env g with _ | v
  · rfl
  · cases v <;> (first | rfl | (next b => cases b <;> rfl))

/-! ## Embedding into operational `Stmt`

`embed_state` is the state-aware analogue of `embed`. On the shared
constructors it mirrors `embed`; on the heap-touching constructors it
maps directly to the corresponding `Stmt` form (which already exists,
since `Stmt` has full heap-touching syntax). -/

def embed_state : StateStmt → Stmt
  | .skip          => .skip
  | .assign x e    => .assign x e
  | .seq s₁ s₂     => .seq (embed_state s₁) (embed_state s₂)
  | .ite e s₁ s₂   => .ite e (embed_state s₁) (embed_state s₂)
  | .repeat n s    => unroll (embed_state s) n
  | .forN n s      => unroll (embed_state s) n
  | .while_ n g s  => unrollW g (embed_state s) n
  | .load x e      => .load x e
  | .store eL eV   => .store eL eV
  | .free e        => .free e
  | .cas x eL eO eN => .cas x eL eO eN
  | .alloc x e     => .alloc x e

/-! ## Smoke-test shape

The presence of a worked example was helpful in shaking out
signatures; the equation itself requires `Mem.ext`-style unfolding
because `Mem` is bundled with a `notFull` witness, so post-alloc-and-
free equality is not `rfl`. Deferred to the soundness file. -/

end Agar

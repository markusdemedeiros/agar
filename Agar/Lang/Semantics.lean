module

public import Agar.Lang.Syntax
public import Agar.Lang.SimpAttr

@[expose] public section

namespace Agar

/-! ## Environments -/

abbrev Env := Name → Option Val

@[agar_eval] def Env.empty : Env := fun _ => none

@[agar_eval] def Env.set (ρ : Env) (x : Name) (v : Val) : Env :=
  fun y => if y = x then some v else ρ y

@[agar_eval] def bindParams : List Name → List Val → Env
  | [], []         => Env.empty
  | n :: ns, v :: vs => (bindParams ns vs).set n v
  | _, _           => Env.empty

/-! ## Field operations on struct values -/

namespace Fields

@[agar_eval] def proj : List (Name × Val) → Name → Option Val
  | [], _ => none
  | (n, v) :: fs, m => if n = m then some v else proj fs m

@[agar_eval] def upd : List (Name × Val) → Name → Val → Option (List (Name × Val))
  | [], _, _ => none
  | (n, v) :: fs, m, w =>
      if n = m then some ((n, w) :: fs)
      else (upd fs m w).map (fun fs' => (n, v) :: fs')

end Fields

/-! ## Operator semantics -/

@[agar_eval] def BinOp.eval : BinOp → Val → Val → Option Val
  | .add, .int a,  .int b  => some (.int (a + b))
  | .sub, .int a,  .int b  => some (.int (a - b))
  | .mul, .int a,  .int b  => some (.int (a * b))
  | .eq,  a,       b       => some (.bool (a == b))
  | .lt,  .int a,  .int b  => some (.bool (decide (a < b)))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or,  .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

@[agar_eval] def UnOp.eval : UnOp → Val → Option Val
  | .neg, .int a  => some (.int (-a))
  | .not, .bool a => some (.bool (!a))
  | _, _ => none

/-! ## Expression evaluation -/

mutual
  @[agar_eval] def Expr.eval (ρ : Env) : Expr → Option Val
    | .val v        => some v
    | .var x        => ρ x
    | .bin op e₁ e₂ => do
        let v₁ ← Expr.eval ρ e₁
        let v₂ ← Expr.eval ρ e₂
        BinOp.eval op v₁ v₂
    | .un op e      => do
        let v ← Expr.eval ρ e
        UnOp.eval op v
    | .mk fs        => do
        let vs ← Expr.evalFields ρ fs
        some (.struct vs)
    | .proj e f     => do
        match (← Expr.eval ρ e) with
        | .struct fs => Fields.proj fs f
        | _          => none
    | .upd e f e'   => do
        let v ← Expr.eval ρ e
        let w ← Expr.eval ρ e'
        match v with
        | .struct fs => (Fields.upd fs f w).map Val.struct
        | _          => none

  @[agar_eval] def Expr.evalFields (ρ : Env) :
      List (Name × Expr) → Option (List (Name × Val))
    | [] => some []
    | (n, e) :: rest => do
        let v ← Expr.eval ρ e
        let r ← Expr.evalFields ρ rest
        some ((n, v) :: r)
end

@[agar_eval] def evalArgs (ρ : Env) : List Expr → Option (List Val)
  | []      => some []
  | e :: es => do
      let v ← Expr.eval ρ e
      let vs ← evalArgs ρ es
      some (v :: vs)

/-! ## Heap

A Agar heap is a partial function `Loc → Option Val` packaged with a
classical "infinitely many slots are unallocated" witness. The witness
is what lets `alloc` always pick a fresh location operationally, and
what the Iris ghost-state side relies on when discharging `wp_alloc`. -/

structure Mem where
  fn       : Loc → Option Val
  /-- For every cutoff `N`, there is still some `l ≥ N` with nothing
  stored there. This is the cofinite-cosupport invariant; allocating,
  storing, or freeing one slot all preserve it. -/
  notFull  : ∀ N : Loc, ∃ l, N ≤ l ∧ fn l = none

instance : CoeFun Mem (fun _ => Loc → Option Val) := ⟨Mem.fn⟩

namespace Mem

@[ext] theorem ext {m₁ m₂ : Mem} (h : ∀ l, m₁.fn l = m₂.fn l) : m₁ = m₂ := by
  cases m₁; cases m₂; congr; funext l; exact h l

def empty : Mem :=
  ⟨fun _ => none, fun N => ⟨N, Nat.le_refl _, rfl⟩⟩

instance : Inhabited Mem := ⟨empty⟩

@[reducible] def load (m : Mem) (l : Loc) : Option Val := m.fn l

/-- `l` is fresh in `m` when nothing is mapped there. -/
def fresh (m : Mem) (l : Loc) : Prop := m.fn l = none

/-- There is always *some* fresh location — direct corollary of `notFull`. -/
theorem exists_fresh (m : Mem) : ∃ l, m.fresh l := by
  obtain ⟨l, _, h⟩ := m.notFull 0
  exact ⟨l, h⟩

/-- Altering one slot of a cofinite-cosupport heap preserves the
invariant: pick a fresh location strictly above the altered one. -/
theorem notFull_update {fn : Loc → Option Val}
    (hwf : ∀ N : Loc, ∃ l, N ≤ l ∧ fn l = none) (k : Loc) (ov : Option Val) :
    ∀ N : Loc, ∃ l, N ≤ l ∧
      (fun l' => if l' = k then ov else fn l') l = none := by
  intro N
  obtain ⟨l, hN, hl⟩ := hwf (max N (k + 1))
  have ⟨hN', hk'⟩ := Nat.max_le.mp hN
  have hne : l ≠ k := Nat.ne_of_gt hk'
  exact ⟨l, hN', by simp [hne, hl]⟩

/-- Pointwise update — the underlying primitive for the three heap ops.
The `notFull` invariant is preserved by `notFull_update`. -/
def update (m : Mem) (l : Loc) (ov : Option Val) : Mem :=
  ⟨fun l' => if l' = l then ov else m.fn l', notFull_update m.notFull l ov⟩

@[simp] theorem update_fn (m : Mem) (l : Loc) (ov : Option Val) (l' : Loc) :
    (m.update l ov).fn l' = if l' = l then ov else m.fn l' := rfl

/-- Allocate at a *caller-chosen* location. Succeeds only if `l` is fresh. -/
def alloc (m : Mem) (l : Loc) (v : Val) : Option Mem :=
  match m.fn l with
  | some _ => none
  | none   => some (m.update l (some v))

/-- Replace the value at an already-allocated location. -/
def store (m : Mem) (l : Loc) (v : Val) : Option Mem :=
  match m.fn l with
  | some _ => some (m.update l (some v))
  | none   => none

/-- Remove a location from the heap; fails if it wasn't allocated. -/
def free (m : Mem) (l : Loc) : Option Mem :=
  match m.fn l with
  | some _ => some (m.update l none)
  | none   => none

end Mem

/-! ## Threads and the machine -/

structure Frame where
  retVar : Name
  cont   : List Stmt
  env    : Env

/-- A thread carries its statement, queued continuation, locals,
call stack, and — once it has executed a top-level `return e` — the
returned value. Threads that fall through to `skip` without an explicit
`return` have `result = none`, which the WP machinery interprets as the
implicit unit return. -/
structure Thread where
  stmt   : Stmt
  cont   : List Stmt
  env    : Env
  stack  : List Frame
  result : Option Val := none

def Thread.initial (s : Stmt) : Thread :=
  { stmt := s, cont := [], env := Env.empty, stack := [], result := none }

def Thread.terminated (t : Thread) : Bool :=
  match t.stmt, t.cont, t.stack with
  | .skip, [], [] => true
  | _, _, _       => false

/-- The value of a fully-terminated thread.

* `t` is terminated and `t.result = some v`: a top-level `return e`
  fired, the value is `v`.
* `t` is terminated and `t.result = none`: the thread fell through, the
  value is `Val.unit`.
* `t` is not terminated: there is no value yet. -/
def Thread.toValue (t : Thread) : Option Val :=
  match t.stmt, t.cont, t.stack with
  | .skip, [], [] => some (t.result.getD .unit)
  | _, _, _       => none

structure Machine where
  mem     : Mem
  threads : List Thread

def Machine.initial (p : Program) : Machine :=
  { mem := Mem.empty, threads := [Thread.initial p.main] }

/-! ## Per-thread small step

Returns `none` if the thread is stuck or terminated (no step). On success,
returns the new memory, the updated thread, and optionally a spawned thread
from `fork`.
-/

abbrev StepResult := Mem × Thread × Option Thread

def callFrom (procs : Name → Option Proc) (m : Mem) (t : Thread)
    (retVar : Name) (cont : List Stmt) (f : Name) (args : List Expr) :
    Option StepResult :=
  match procs f, evalArgs t.env args with
  | some proc, some vs =>
      if vs.length = proc.params.length then
        let frame : Frame := ⟨retVar, cont, t.env⟩
        some (m,
          { stmt  := proc.body
            cont  := []
            env   := bindParams proc.params vs
            stack := frame :: t.stack },
          none)
      else none
  | _, _ => none

def doReturn (m : Mem) (t : Thread) (v : Val) : StepResult :=
  match t.stack with
  | [] =>
      -- Top-level return: terminate the thread, recording `v` so the
      -- WP can observe it.
      (m, { stmt := .skip, cont := [], env := t.env, stack := [],
            result := some v }, none)
  | f :: rest =>
      let env' := f.env.set f.retVar v
      match f.cont with
      | s :: cs => (m, { stmt := s,    cont := cs, env := env', stack := rest }, none)
      | []      => (m, { stmt := .skip, cont := [], env := env', stack := rest }, none)

/-- `tstep` is parameterised by an *optional* fresh location:

* `chosen = none`  — the step must not be an `alloc`. Allocation requires a
  caller-supplied address; without one it cannot fire.
* `chosen = some l` — the step *must* be an `alloc` whose `l` is fresh in `m`.
  Every other statement requires `chosen = none` and is stuck otherwise.

This way the machine-level relation existentially quantifies the location for
allocation steps and supplies `none` for all others, modelling truly
nondeterministic allocation. -/
def tstep (procs : Name → Option Proc) (chosen : Option Loc)
    (m : Mem) (t : Thread) : Option StepResult :=
  match chosen, t.stmt with
  | some l, .alloc x e =>
      match Expr.eval t.env e with
      | none => none
      | some v =>
          match m.alloc l v with
          | none    => none
          | some m' =>
              some (m', { t with stmt := .skip, env := t.env.set x (.loc l) }, none)
  | some _, _          => none
  | none,   .alloc _ _ => none
  | none,   .skip =>
      match t.cont, t.stack with
      | s :: rest, _      => some (m, { t with stmt := s, cont := rest }, none)
      | [],        []     => none  -- terminated
      | [],        _ :: _ => some (doReturn m t .unit)
  | none, .seq s₁ s₂ =>
      some (m, { t with stmt := s₁, cont := s₂ :: t.cont }, none)
  | none, .assign x e =>
      match Expr.eval t.env e with
      | none   => none
      | some v => some (m, { t with stmt := .skip, env := t.env.set x v }, none)
  | none, .load x e =>
      match Expr.eval t.env e with
      | some (.loc l) =>
          match m.load l with
          | some w => some (m, { t with stmt := .skip, env := t.env.set x w }, none)
          | none   => none
      | _ => none
  | none, .store eL eV =>
      match Expr.eval t.env eL, Expr.eval t.env eV with
      | some (.loc l), some v =>
          match m.store l v with
          | some m' => some (m', { t with stmt := .skip }, none)
          | none    => none
      | _, _ => none
  | none, .free e =>
      match Expr.eval t.env e with
      | some (.loc l) =>
          match m.free l with
          | some m' => some (m', { t with stmt := .skip }, none)
          | none    => none
      | _ => none
  | none, .cas x eL eO eN =>
      match Expr.eval t.env eL, Expr.eval t.env eO, Expr.eval t.env eN with
      | some (.loc l), some vO, some vN =>
          match m.load l with
          | none     => none
          | some cur =>
              if cur == vO then
                match m.store l vN with
                | some m' =>
                    some (m', { t with stmt := .skip, env := t.env.set x cur }, none)
                | none    => none
              else
                some (m, { t with stmt := .skip, env := t.env.set x cur }, none)
      | _, _, _ => none
  | none, .ite e s₁ s₂ =>
      match Expr.eval t.env e with
      | some (.bool true)  => some (m, { t with stmt := s₁ }, none)
      | some (.bool false) => some (m, { t with stmt := s₂ }, none)
      | _ => none
  | none, .whileDo e s =>
      some (m, { t with stmt := .ite e (.seq s (.whileDo e s)) .skip }, none)
  | none, .call x f args =>
      callFrom procs m t x t.cont f args
  | none, .ret e =>
      match Expr.eval t.env e with
      | none   => none
      | some v => some (doReturn m t v)
  | none, .fork f args =>
      match procs f, evalArgs t.env args with
      | some proc, some vs =>
          if vs.length = proc.params.length then
            let spawned : Thread :=
              { stmt  := proc.body
                cont  := []
                env   := bindParams proc.params vs
                stack := [] }
            some (m, { t with stmt := .skip }, some spawned)
          else none
      | _, _ => none

/-! ## Machine step (thread-pool interleaving)

We model thread selection nondeterministically via an inductive relation.
Per-thread stepping is deterministic given a thread index *and* an
`Option Loc` for nondeterministic allocation. The relation existentially
quantifies the chosen location, so any fresh address is a valid alloc step.
-/

inductive Machine.Step (p : Program) : Machine → Machine → Prop where
  | step
      (i : Nat) (chosen : Option Loc)
      (t t' : Thread) (sp : Option Thread) (m m' : Mem)
      (threads : List Thread)
      (hi : threads[i]? = some t)
      (hstep : tstep p.procs chosen m t = some (m', t', sp)) :
      Machine.Step p
        ⟨m, threads⟩
        ⟨m', threads.set i t' ++ sp.toList⟩

/-! ## Halting

The machine halts when `main` (thread 0) has terminated. Other threads may
still exist; they are abandoned.
-/

def Machine.halted (μ : Machine) : Bool :=
  match μ.threads with
  | t :: _ => t.terminated
  | []     => true

/-! # Reduction equations for `tstep`

`tstep` is one giant pattern match on `(chosen, t.stmt)`. The lemmas
below give one reduction equation per statement form, so downstream
WP-rule proofs don't have to unfold the entire match. Each is proved by
`unfold tstep; simp [...]`.

Naming convention: `tstep_<stmt>` for the positive equation,
`tstep_<stmt>_inv` for the inversion-style "only-step" equation that WP
rules use to extract determinism.
-/

section TstepEq

variable (procs : Name → Option Proc)

/-! ## skip / cont / sequencing -/

theorem tstep_skip_cons (m : Mem) (s : Stmt) (rest : List Stmt)
    (env : Env) (stack : List Frame) :
    tstep procs none m ⟨.skip, s :: rest, env, stack, none⟩
      = some (m, ⟨s, rest, env, stack, none⟩, none) := by
  unfold tstep; simp

theorem tstep_skip_frame (m : Mem) (env : Env) (f : Frame) (stack : List Frame) :
    tstep procs none m ⟨.skip, [], env, f :: stack, none⟩
      = some (doReturn m ⟨.skip, [], env, f :: stack, none⟩ .unit) := by
  unfold tstep; simp

theorem tstep_seq (m : Mem) (s₁ s₂ : Stmt) (cont : List Stmt)
    (env : Env) (stack : List Frame) :
    tstep procs none m ⟨.seq s₁ s₂, cont, env, stack, none⟩
      = some (m, ⟨s₁, s₂ :: cont, env, stack, none⟩, none) := by
  unfold tstep; simp

/-! ## Pure local statements -/

theorem tstep_assign (m : Mem) (x : Name) (e : Expr) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some v) :
    tstep procs none m ⟨.assign x e, cont, env, stack, none⟩
      = some (m, ⟨.skip, cont, env.set x v, stack, none⟩, none) := by
  unfold tstep; simp [heval]

theorem tstep_ite_true (m : Mem) (e : Expr) (s₁ s₂ : Stmt)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some (.bool true)) :
    tstep procs none m ⟨.ite e s₁ s₂, cont, env, stack, none⟩
      = some (m, ⟨s₁, cont, env, stack, none⟩, none) := by
  unfold tstep; simp [heval]

theorem tstep_ite_false (m : Mem) (e : Expr) (s₁ s₂ : Stmt)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some (.bool false)) :
    tstep procs none m ⟨.ite e s₁ s₂, cont, env, stack, none⟩
      = some (m, ⟨s₂, cont, env, stack, none⟩, none) := by
  unfold tstep; simp [heval]

theorem tstep_whileDo (m : Mem) (e : Expr) (s : Stmt)
    (cont : List Stmt) (env : Env) (stack : List Frame) :
    tstep procs none m ⟨.whileDo e s, cont, env, stack, none⟩
      = some (m, ⟨.ite e (.seq s (.whileDo e s)) .skip, cont, env, stack, none⟩, none) := by
  unfold tstep; simp

/-! ## Heap-touching statements -/

theorem tstep_load (m : Mem) (x : Name) (e : Expr) (l : Loc) (w : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some (.loc l)) (hl : m l = some w) :
    tstep procs none m ⟨.load x e, cont, env, stack, none⟩
      = some (m, ⟨.skip, cont, env.set x w, stack, none⟩, none) := by
  unfold tstep; simp [heval, Mem.load, hl]

theorem tstep_store (m : Mem) (eL eV : Expr) (l : Loc) (v : Val) (m' : Mem)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heL : Expr.eval env eL = some (.loc l)) (heV : Expr.eval env eV = some v)
    (hst : m.store l v = some m') :
    tstep procs none m ⟨.store eL eV, cont, env, stack, none⟩
      = some (m', ⟨.skip, cont, env, stack, none⟩, none) := by
  unfold tstep; simp [heL, heV, hst]

theorem tstep_alloc (m m' : Mem) (l : Loc) (x : Name) (e : Expr) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some v) (hal : m.alloc l v = some m') :
    tstep procs (some l) m ⟨.alloc x e, cont, env, stack, none⟩
      = some (m', ⟨.skip, cont, env.set x (.loc l), stack, none⟩, none) := by
  unfold tstep; simp [heval, hal]

theorem tstep_free (m m' : Mem) (e : Expr) (l : Loc)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some (.loc l)) (hfr : m.free l = some m') :
    tstep procs none m ⟨.free e, cont, env, stack, none⟩
      = some (m', ⟨.skip, cont, env, stack, none⟩, none) := by
  unfold tstep; simp [heval, hfr]

theorem tstep_cas_succ (m m' : Mem) (x : Name) (eL eO eN : Expr)
    (l : Loc) (vO vN cur : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (hl : m l = some cur) (heq : (cur == vO) = true)
    (hst : m.store l vN = some m') :
    tstep procs none m ⟨.cas x eL eO eN, cont, env, stack, none⟩
      = some (m', ⟨.skip, cont, env.set x cur, stack, none⟩, none) := by
  unfold tstep; simp [heL, heO, heN, Mem.load, hl, heq, hst]

theorem tstep_cas_fail (m : Mem) (x : Name) (eL eO eN : Expr)
    (l : Loc) (vO vN cur : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (hl : m l = some cur) (hne : (cur == vO) = false) :
    tstep procs none m ⟨.cas x eL eO eN, cont, env, stack, none⟩
      = some (m, ⟨.skip, cont, env.set x cur, stack, none⟩, none) := by
  unfold tstep; simp [heL, heO, heN, Mem.load, hl, hne]

/-! ## Call and return -/

theorem tstep_call (m : Mem) (x f : Name) (args : List Expr) (proc : Proc)
    (vs : List Val) (cont : List Stmt) (env : Env) (stack : List Frame)
    (hproc : procs f = some proc) (hargs : evalArgs env args = some vs)
    (harity : vs.length = proc.params.length) :
    tstep procs none m ⟨.call x f args, cont, env, stack, none⟩
      = some (m,
          ⟨proc.body, [], bindParams proc.params vs,
            ⟨x, cont, env⟩ :: stack, none⟩, none) := by
  unfold tstep callFrom; simp [hproc, hargs, harity]

theorem tstep_ret (m : Mem) (e : Expr) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (heval : Expr.eval env e = some v) :
    tstep procs none m ⟨.ret e, cont, env, stack, none⟩
      = some (doReturn m ⟨.ret e, cont, env, stack, none⟩ v) := by
  unfold tstep; simp [heval]

/-! ## Fork -/

theorem tstep_fork (m : Mem) (f : Name) (args : List Expr) (proc : Proc)
    (vs : List Val) (cont : List Stmt) (env : Env) (stack : List Frame)
    (hproc : procs f = some proc) (hargs : evalArgs env args = some vs)
    (harity : vs.length = proc.params.length) :
    tstep procs none m ⟨.fork f args, cont, env, stack, none⟩
      = some
          (m, ⟨.skip, cont, env, stack, none⟩,
            some ⟨proc.body, [], bindParams proc.params vs, [], none⟩) := by
  unfold tstep; simp [hproc, hargs, harity]

end TstepEq

end Agar

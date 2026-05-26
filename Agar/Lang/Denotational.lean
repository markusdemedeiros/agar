module

public import Agar.Lang.Semantics
public import Agar.Lang.SimpAttr

@[expose] public section

namespace Agar

/-! ## Pure terminating fragment: heap-free, call-free, loop-free. -/

inductive PureStmt where
  | skip   : PureStmt
  | assign : Name → Expr → PureStmt
  | seq    : PureStmt → PureStmt → PureStmt
  | ite    : Expr → PureStmt → PureStmt → PureStmt
  | repeat : Nat → PureStmt → PureStmt
  | forN   : Nat → PureStmt → PureStmt
  /-- Fuel-bounded `while`. The first `Nat` bounds the number of loop
  iterations; running out of fuel produces `none`. -/
  | while_ : Nat → Expr → PureStmt → PureStmt

/-! ## Denotation -/

abbrev Denot := StateM Env (Option Unit)

def iter (body : Denot) : Nat → Denot
  | 0,     ρ => (some (), ρ)
  | n + 1, ρ =>
      match body ρ with
      | (none, ρ')   => (none, ρ')
      | (some _, ρ') => iter body n ρ'

/-- Fuel-bounded loop driver. At each step, evaluate the guard:
* If `some (.bool true)` and we still have fuel, run the body and recurse
  with one fewer fuel unit.
* If `some (.bool false)`, terminate successfully (loop exit).
* Otherwise (non-bool guard, or out of fuel), fail.

Fuel `0` always fails — mirroring the operationally-stuck base case
chosen for `embed`. -/
def iterWhile (g : Env → Option Val) (body : Denot) : Nat → Denot
  | 0,     ρ => (none, ρ)
  | n + 1, ρ =>
      match g ρ with
      | some (.bool true) =>
          match body ρ with
          | (none, ρ')   => (none, ρ')
          | (some _, ρ') => iterWhile g body n ρ'
      | some (.bool false) => (some (), ρ)
      | _ => (none, ρ)

def denote : PureStmt → Denot
  | .skip          => fun ρ => (some (), ρ)
  | .assign x e    => fun ρ =>
      match Expr.eval ρ e with
      | none   => (none, ρ)
      | some v => (some (), ρ.set x v)
  | .seq s₁ s₂     => fun ρ =>
      match denote s₁ ρ with
      | (none, ρ')   => (none, ρ')
      | (some _, ρ') => denote s₂ ρ'
  | .ite e s₁ s₂   => fun ρ =>
      match Expr.eval ρ e with
      | some (.bool true)  => denote s₁ ρ
      | some (.bool false) => denote s₂ ρ
      | _                  => (none, ρ)
  | .repeat n s    => iter (denote s) n
  | .forN n s      => iter (denote s) n
  | .while_ n g s  => iterWhile (fun ρ => Expr.eval ρ g) (denote s) n

@[simp] theorem denote_skip (ρ : Env) : denote .skip ρ = (some (), ρ) := rfl

@[simp] theorem denote_forN_zero (s : PureStmt) (ρ : Env) :
    denote (.forN 0 s) ρ = (some (), ρ) := rfl

theorem denote_forN_succ (n : Nat) (s : PureStmt) (ρ : Env) :
    denote (.forN (n+1) s) ρ = denote (.seq s (.forN n s)) ρ := by
  show iter (denote s) (n+1) ρ = _
  simp only [denote, iter]

/-! ### `denote_norm` simp set

These lemmas rewrite `denote (constructor …) ρ` into its plain
match-on-result form, suitable for `simp only [denote_norm, …]` to
walk an entire `PureStmt` tree without leaving stray `denote` calls.

Use case: bridging `denote prog` to a hand-written `StateM Env (Option
Unit)` monadic mirror, where the mirror exposes the same match
structure for `mvcgen`. -/

attribute [denote_norm] denote_skip denote_forN_zero

@[denote_norm] theorem denote_assign_eq (x : Name) (e : Expr) (ρ : Env) :
    denote (.assign x e) ρ =
      (match Expr.eval ρ e with
       | none   => (none, ρ)
       | some v => (some (), ρ.set x v)) := rfl

@[denote_norm] theorem denote_seq_eq (s₁ s₂ : PureStmt) (ρ : Env) :
    denote (.seq s₁ s₂) ρ =
      (match denote s₁ ρ with
       | (none, ρ')   => (none, ρ')
       | (some _, ρ') => denote s₂ ρ') := rfl

@[denote_norm] theorem denote_ite_eq (e : Expr) (s₁ s₂ : PureStmt) (ρ : Env) :
    denote (.ite e s₁ s₂) ρ =
      (match Expr.eval ρ e with
       | some (.bool true)  => denote s₁ ρ
       | some (.bool false) => denote s₂ ρ
       | _                  => (none, ρ)) := rfl

@[denote_norm] theorem denote_forN_succ_eq (n : Nat) (s : PureStmt) (ρ : Env) :
    denote (.forN (n+1) s) ρ =
      (match denote s ρ with
       | (none, ρ')   => (none, ρ')
       | (some _, ρ') => denote (.forN n s) ρ') := by
  rw [denote_forN_succ]; rfl

@[simp] theorem denote_while_zero (g : Expr) (s : PureStmt) (ρ : Env) :
    denote (.while_ 0 g s) ρ = (none, ρ) := rfl

/-- **Loop unfolding.** With at least one fuel unit, `while_` matches the
operational unfolding through the guard: if the guard is `true`, the body
runs once and we recurse with one fewer fuel unit; if `false`, we
terminate successfully; otherwise we fail. -/
theorem denote_while_succ (n : Nat) (g : Expr) (s : PureStmt) (ρ : Env) :
    denote (.while_ (n+1) g s) ρ =
      match Expr.eval ρ g with
      | some (.bool true)  => denote (.seq s (.while_ n g s)) ρ
      | some (.bool false) => (some (), ρ)
      | _ => (none, ρ) := by
  show iterWhile (fun ρ => Expr.eval ρ g) (denote s) (n + 1) ρ = _
  unfold iterWhile
  rcases hev : Expr.eval ρ g with _ | v
  · rfl
  · cases v <;> (first | rfl | (next b => cases b <;> rfl))

/-- Worked example: two sequenced assignments. -/
example :
    denote (.seq (.assign "x" (.val (.int 5)))
                 (.assign "y" (.var "x"))) Env.empty
      = (some (), (Env.empty.set "x" (.int 5)).set "y" (.int 5)) := by
  rfl

/-! ## Monadic denotation (`mvcgen`-friendly twin)

`denoteM` is a `do`-block re-presentation of `denote`. It exists so that
specs about pure programs can be stated against a shape `mvcgen` can
walk — `denote` itself uses explicit pattern matching, which `mvcgen`
cannot traverse.

The bridge between the two, and the rest of the operational/triple
plumbing, is built incrementally in follow-up commits. -/

/-- `n`-fold execution of `body` over the placeholder list `List.replicate n ()`.
Using `forIn` (rather than direct recursion) lets `Std.Do`'s `Spec.forIn_list`
fire under `mvcgen`. Equivalent to the recursive form via `iterM_succ`. -/
def iterM (body : StateM Env (Option Unit)) (n : Nat) :
    StateM Env (Option Unit) :=
  forIn (List.replicate n ()) (some ()) (fun _ acc =>
    match acc with
    | none   => pure (.done none)
    | some _ => do
        match ← body with
        | none   => pure (.done none)
        | some _ => pure (.yield (some ())))

def iterWhileM (g : Env → Option Val) (body : StateM Env (Option Unit)) :
    Nat → StateM Env (Option Unit)
  | 0     => pure none
  | n + 1 => do
      let ρ ← get
      match g ρ with
      | some (.bool true) => do
          match ← body with
          | none   => pure none
          | some _ => iterWhileM g body n
      | some (.bool false) => pure (some ())
      | _ => pure none

def denoteM : PureStmt → StateM Env (Option Unit)
  | .skip          => pure (some ())
  | .assign x e    => do
      let ρ ← get
      match Expr.eval ρ e with
      | none   => pure none
      | some v => do set (ρ.set x v); pure (some ())
  | .seq s₁ s₂     => do
      match ← denoteM s₁ with
      | none   => pure none
      | some _ => denoteM s₂
  | .ite e s₁ s₂   => do
      let ρ ← get
      match Expr.eval ρ e with
      | some (.bool true)  => denoteM s₁
      | some (.bool false) => denoteM s₂
      | _                  => pure none
  | .repeat n s    => iterM (denoteM s) n
  | .forN n s      => iterM (denoteM s) n
  | .while_ n g s  => iterWhileM (fun ρ => Expr.eval ρ g) (denoteM s) n

/-! ### `denoteM_norm` simp set

Monadic analogues of the `denote_norm` lemmas. Each rewrites
`denoteM (constructor …)` into its `do`-block / bind form, exposing the
shape `mvcgen` walks. -/

@[simp, denoteM_norm] theorem denoteM_skip :
    denoteM .skip = pure (some ()) := rfl

@[simp, denoteM_norm] theorem denoteM_assign (x : Name) (e : Expr) :
    denoteM (.assign x e) =
      (do
        let ρ ← get
        match Expr.eval ρ e with
        | none   => pure none
        | some v => do set (ρ.set x v); pure (some ())) := rfl

@[simp, denoteM_norm] theorem denoteM_seq (s₁ s₂ : PureStmt) :
    denoteM (.seq s₁ s₂) =
      (do
        match ← denoteM s₁ with
        | none   => pure none
        | some _ => denoteM s₂) := rfl

@[simp, denoteM_norm] theorem denoteM_ite (e : Expr) (s₁ s₂ : PureStmt) :
    denoteM (.ite e s₁ s₂) =
      (do
        let ρ ← get
        match Expr.eval ρ e with
        | some (.bool true)  => denoteM s₁
        | some (.bool false) => denoteM s₂
        | _                  => pure none) := rfl

@[simp, denoteM_norm] theorem denoteM_repeat (n : Nat) (s : PureStmt) :
    denoteM (.repeat n s) = iterM (denoteM s) n := rfl

@[simp, denoteM_norm] theorem denoteM_forN (n : Nat) (s : PureStmt) :
    denoteM (.forN n s) = iterM (denoteM s) n := rfl

@[simp, denoteM_norm] theorem denoteM_while (n : Nat) (g : Expr) (s : PureStmt) :
    denoteM (.while_ n g s) =
      iterWhileM (fun ρ => Expr.eval ρ g) (denoteM s) n := rfl

@[simp, denoteM_norm] theorem iterM_zero (body : StateM Env (Option Unit)) :
    iterM body 0 = pure (some ()) := by
  show forIn (List.replicate 0 ()) (some ()) _ = _
  simp [List.replicate]

@[denoteM_norm] theorem iterM_succ (body : StateM Env (Option Unit)) (n : Nat) :
    iterM body (n+1) =
      (do
        match ← body with
        | none   => pure none
        | some _ => iterM body n) := by
  show iterM body (n+1) = _
  unfold iterM
  rw [List.replicate_succ, List.forIn_cons]
  funext ρ
  simp only [bind, StateT.bind, pure, StateT.pure]
  cases body ρ with
  | mk o ρ' => cases o <;> rfl

@[simp, denoteM_norm] theorem iterWhileM_zero
    (g : Env → Option Val) (body : StateM Env (Option Unit)) :
    iterWhileM g body 0 = pure none := rfl

@[denoteM_norm] theorem iterWhileM_succ
    (g : Env → Option Val) (body : StateM Env (Option Unit)) (n : Nat) :
    iterWhileM g body (n+1) =
      (do
        let ρ ← get
        match g ρ with
        | some (.bool true) => do
            match ← body with
            | none   => pure none
            | some _ => iterWhileM g body n
        | some (.bool false) => pure (some ())
        | _ => pure none) := rfl

/-! ## Embedding into `Stmt` -/

def unroll (body : Stmt) : Nat → Stmt
  | 0     => .skip
  | n + 1 => .seq body (unroll body n)

/-- Bounded operational unrolling of a `while` loop. Fuel `0` is a
definitely-stuck `.call` to a procedure that does not exist (the
`programOf` table is `noProcs`), making the operational and denotational
"out of fuel" cases agree. -/
def unrollW (g : Expr) (body : Stmt) : Nat → Stmt
  | 0     => .call "_no_var_" "_no_proc_" []
  | n + 1 => .ite g (.seq body (unrollW g body n)) .skip

def embed : PureStmt → Stmt
  | .skip        => .skip
  | .assign x e  => .assign x e
  | .seq s₁ s₂   => .seq (embed s₁) (embed s₂)
  | .ite e s₁ s₂ => .ite e (embed s₁) (embed s₂)
  | .repeat n s  => unroll (embed s) n
  | .forN n s    => unroll (embed s) n
  | .while_ n g s => unrollW g (embed s) n

/-! ## Small-step closure on pure threads: empty procedure table, `Mem.empty`. -/

def noProcs : Name → Option Proc := fun _ => none

def pstep (t : Thread) : Option Thread :=
  match tstep noProcs none Mem.empty t with
  | some (_, t', _) => some t'
  | none            => none

inductive PureSteps : Thread → Thread → Prop where
  | refl  : PureSteps t t
  | step  : pstep t = some t' → PureSteps t' t'' → PureSteps t t''

theorem PureSteps.trans :
    PureSteps t₁ t₂ → PureSteps t₂ t₃ → PureSteps t₁ t₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem PureSteps.single (h : pstep t = some t') : PureSteps t t' :=
  .step h .refl

/-- Thread with statement `s`, queued continuation `cs`, env `ρ`, empty stack. -/
def mkT (s : Stmt) (cs : List Stmt) (ρ : Env) : Thread :=
  { stmt := s, cont := cs, env := ρ, stack := [], result := none }

@[simp] theorem mkT_skip_step (cs : List Stmt) (ρ : Env) (s' : Stmt) :
    pstep (mkT .skip (s' :: cs) ρ) = some (mkT s' cs ρ) := rfl

@[simp] theorem mkT_seq_step (a b : Stmt) (cs : List Stmt) (ρ : Env) :
    pstep (mkT (.seq a b) cs ρ) = some (mkT a (b :: cs) ρ) := rfl

@[simp] theorem mkT_assign_step (x : Name) (e : Expr) (cs : List Stmt) (ρ : Env) :
    pstep (mkT (.assign x e) cs ρ) =
      (Expr.eval ρ e).map (fun v => mkT .skip cs (ρ.set x v)) := by
  simp [pstep, tstep, mkT]
  cases Expr.eval ρ e <;> rfl

@[simp] theorem mkT_ite_step (e : Expr) (s₁ s₂ : Stmt) (cs : List Stmt) (ρ : Env) :
    pstep (mkT (.ite e s₁ s₂) cs ρ) =
      match Expr.eval ρ e with
      | some (.bool true)  => some (mkT s₁ cs ρ)
      | some (.bool false) => some (mkT s₂ cs ρ)
      | _                  => none := by
  simp [pstep, tstep, mkT]
  rcases h : Expr.eval ρ e with _ | v
  · rfl
  · cases v <;> try rfl
    rename_i b; cases b <;> rfl

/-! ## Marquee theorem: successful denotation drives `embed` to `skip`. -/

theorem denote_sound (s : PureStmt) :
    ∀ (cs : List Stmt) (ρ ρ' : Env),
      denote s ρ = (some (), ρ') →
      PureSteps (mkT (embed s) cs ρ) (mkT .skip cs ρ') := by
  induction s with
  | skip =>
      intro cs ρ ρ' h
      simp [denote] at h
      obtain ⟨_, rfl⟩ := h
      exact .refl
  | assign x e =>
      intro cs ρ ρ' h
      simp [denote] at h
      split at h
      · cases h
      · rename_i v heq
        cases h
        exact .single (by simp [embed, heq])
  | seq s₁ s₂ ih₁ ih₂ =>
      intro cs ρ ρ' h
      simp only [denote] at h
      rcases h₁ : denote s₁ ρ with ⟨o₁, ρ₁⟩
      rw [h₁] at h
      cases o₁ with
      | none => cases h
      | some =>
          simp only at h
          have step₁ : pstep (mkT (.seq (embed s₁) (embed s₂)) cs ρ)
              = some (mkT (embed s₁) (embed s₂ :: cs) ρ) := by simp
          refine .step step₁ ?_
          have hs₁ := ih₁ (embed s₂ :: cs) ρ ρ₁ h₁
          have hpop : pstep (mkT .skip (embed s₂ :: cs) ρ₁)
              = some (mkT (embed s₂) cs ρ₁) := by simp
          refine hs₁.trans (.step hpop ?_)
          exact ih₂ cs ρ₁ ρ' h
  | ite e s₁ s₂ ih₁ ih₂ =>
      intro cs ρ ρ' h
      simp only [denote] at h
      split at h
      · rename_i hb
        have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
            = some (mkT (embed s₁) cs ρ) := by simp [hb]
        exact .step step₁ (ih₁ cs ρ ρ' h)
      · rename_i hb
        have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
            = some (mkT (embed s₂) cs ρ) := by simp [hb]
        exact .step step₁ (ih₂ cs ρ ρ' h)
      · cases h
  | «repeat» n s ih =>
      show ∀ cs ρ ρ', iter (denote s) n ρ = (some (), ρ') →
        PureSteps (mkT (unroll (embed s) n) cs ρ) (mkT .skip cs ρ')
      induction n with
      | zero =>
          intro cs ρ ρ' h
          simp [iter] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs ρ ρ' h
          show PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) _
          simp only [iter] at h
          rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => cases h
          | some =>
              simp only at h
              have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
                  = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) ρ ρ₁ h₁
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs ρ₁ ρ' h
  | forN n s ih =>
      show ∀ cs ρ ρ', iter (denote s) n ρ = (some (), ρ') →
        PureSteps (mkT (unroll (embed s) n) cs ρ) (mkT .skip cs ρ')
      induction n with
      | zero =>
          intro cs ρ ρ' h
          simp [iter] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs ρ ρ' h
          show PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) _
          simp only [iter] at h
          rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => cases h
          | some =>
              simp only at h
              have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
                  = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) ρ ρ₁ h₁
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs ρ₁ ρ' h
  | while_ n g s ih =>
      show ∀ cs ρ ρ', denote (.while_ n g s) ρ = (some (), ρ') →
        PureSteps (mkT (unrollW g (embed s) n) cs ρ) (mkT .skip cs ρ')
      induction n with
      | zero =>
          intro cs ρ ρ' h
          rw [denote_while_zero] at h
          cases h
      | succ k ihk =>
          intro cs ρ ρ' h
          show PureSteps (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ) _
          rw [denote_while_succ] at h
          split at h
          · rename_i hb
            -- guard true: ite picks the seq branch
            simp only [denote] at h
            rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
            rw [h₁] at h
            cases o₁ with
            | none => cases h
            | some =>
                simp only at h
                have stepIte : pstep (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ)
                    = some (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ) := by
                  simp [hb]
                refine .step stepIte ?_
                have stepSeq : pstep (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ)
                    = some (mkT (embed s) (unrollW g (embed s) k :: cs) ρ) := by simp
                refine .step stepSeq ?_
                have hs₁ := ih (unrollW g (embed s) k :: cs) ρ ρ₁ h₁
                have hpop : pstep (mkT .skip (unrollW g (embed s) k :: cs) ρ₁)
                    = some (mkT (unrollW g (embed s) k) cs ρ₁) := by simp
                refine hs₁.trans (.step hpop ?_)
                exact ihk cs ρ₁ ρ' h
          · rename_i hb
            -- guard false: ite picks the skip branch
            have hρ : ρ = ρ' := by
              have := congrArg Prod.snd h; simpa using this
            subst hρ
            have stepIte : pstep (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ)
                = some (mkT .skip cs ρ) := by simp [hb]
            exact .step stepIte .refl
          · cases h

/-- Generalised soundness: arbitrary trailing `stack` and `result` are carried
through unchanged by the embed trajectory. -/
theorem denote_sound_general (s : PureStmt) :
    ∀ (cs : List Stmt) (ρ ρ' : Env)
      (stack : List Frame) (result : Option Val),
      denote s ρ = (some (), ρ') →
      PureSteps ⟨embed s, cs, ρ, stack, result⟩
                ⟨.skip, cs, ρ', stack, result⟩ := by
  induction s with
  | skip =>
      intro cs ρ ρ' stack result h
      simp [denote] at h
      obtain ⟨_, rfl⟩ := h
      exact .refl
  | assign x e =>
      intro cs ρ ρ' stack result h
      simp [denote] at h
      split at h
      · cases h
      · rename_i v heq
        cases h
        refine .single ?_
        show pstep ⟨.assign x e, cs, ρ, stack, result⟩ = _
        simp [pstep, tstep, heq]
  | seq s₁ s₂ ih₁ ih₂ =>
      intro cs ρ ρ' stack result h
      simp only [denote] at h
      rcases h₁ : denote s₁ ρ with ⟨o₁, ρ₁⟩
      rw [h₁] at h
      cases o₁ with
      | none => cases h
      | some =>
          simp only at h
          have step₁ : pstep ⟨.seq (embed s₁) (embed s₂), cs, ρ, stack, result⟩
              = some ⟨embed s₁, embed s₂ :: cs, ρ, stack, result⟩ := rfl
          refine .step step₁ ?_
          have hs₁ := ih₁ (embed s₂ :: cs) ρ ρ₁ stack result h₁
          have hpop : pstep ⟨(.skip : Stmt), embed s₂ :: cs, ρ₁, stack, result⟩
              = some ⟨embed s₂, cs, ρ₁, stack, result⟩ := rfl
          refine hs₁.trans (.step hpop ?_)
          exact ih₂ cs ρ₁ ρ' stack result h
  | ite e s₁ s₂ ih₁ ih₂ =>
      intro cs ρ ρ' stack result h
      simp only [denote] at h
      split at h
      · rename_i hb
        have step₁ : pstep ⟨.ite e (embed s₁) (embed s₂), cs, ρ, stack, result⟩
            = some ⟨embed s₁, cs, ρ, stack, result⟩ := by
          show (match tstep noProcs none Mem.empty
                  ⟨.ite e (embed s₁) (embed s₂), cs, ρ, stack, result⟩ with
                | some (_, t', _) => some t' | none => none) = _
          simp [tstep, hb]
        exact .step step₁ (ih₁ cs ρ ρ' stack result h)
      · rename_i hb
        have step₁ : pstep ⟨.ite e (embed s₁) (embed s₂), cs, ρ, stack, result⟩
            = some ⟨embed s₂, cs, ρ, stack, result⟩ := by
          show (match tstep noProcs none Mem.empty
                  ⟨.ite e (embed s₁) (embed s₂), cs, ρ, stack, result⟩ with
                | some (_, t', _) => some t' | none => none) = _
          simp [tstep, hb]
        exact .step step₁ (ih₂ cs ρ ρ' stack result h)
      · cases h
  | «repeat» n s ih =>
      show ∀ cs ρ ρ' stack result, iter (denote s) n ρ = (some (), ρ') →
        PureSteps ⟨unroll (embed s) n, cs, ρ, stack, result⟩
                  ⟨.skip, cs, ρ', stack, result⟩
      induction n with
      | zero =>
          intro cs ρ ρ' stack result h
          simp [iter] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs ρ ρ' stack result h
          show PureSteps ⟨.seq (embed s) (unroll (embed s) k), cs, ρ, stack, result⟩ _
          simp only [iter] at h
          rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => cases h
          | some =>
              simp only at h
              have step₁ : pstep ⟨.seq (embed s) (unroll (embed s) k), cs, ρ, stack, result⟩
                  = some ⟨embed s, unroll (embed s) k :: cs, ρ, stack, result⟩ := rfl
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) ρ ρ₁ stack result h₁
              have hpop : pstep ⟨(.skip : Stmt), unroll (embed s) k :: cs, ρ₁, stack, result⟩
                  = some ⟨unroll (embed s) k, cs, ρ₁, stack, result⟩ := rfl
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs ρ₁ ρ' stack result h
  | forN n s ih =>
      show ∀ cs ρ ρ' stack result, iter (denote s) n ρ = (some (), ρ') →
        PureSteps ⟨unroll (embed s) n, cs, ρ, stack, result⟩
                  ⟨.skip, cs, ρ', stack, result⟩
      induction n with
      | zero =>
          intro cs ρ ρ' stack result h
          simp [iter] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs ρ ρ' stack result h
          show PureSteps ⟨.seq (embed s) (unroll (embed s) k), cs, ρ, stack, result⟩ _
          simp only [iter] at h
          rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => cases h
          | some =>
              simp only at h
              have step₁ : pstep ⟨.seq (embed s) (unroll (embed s) k), cs, ρ, stack, result⟩
                  = some ⟨embed s, unroll (embed s) k :: cs, ρ, stack, result⟩ := rfl
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) ρ ρ₁ stack result h₁
              have hpop : pstep ⟨(.skip : Stmt), unroll (embed s) k :: cs, ρ₁, stack, result⟩
                  = some ⟨unroll (embed s) k, cs, ρ₁, stack, result⟩ := rfl
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs ρ₁ ρ' stack result h
  | while_ n g s ih =>
      show ∀ cs ρ ρ' stack result, denote (.while_ n g s) ρ = (some (), ρ') →
        PureSteps ⟨unrollW g (embed s) n, cs, ρ, stack, result⟩
                  ⟨.skip, cs, ρ', stack, result⟩
      induction n with
      | zero =>
          intro cs ρ ρ' stack result h
          rw [denote_while_zero] at h
          cases h
      | succ k ihk =>
          intro cs ρ ρ' stack result h
          show PureSteps ⟨.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip, cs, ρ, stack, result⟩ _
          rw [denote_while_succ] at h
          split at h
          · rename_i hb
            simp only [denote] at h
            rcases h₁ : denote s ρ with ⟨o₁, ρ₁⟩
            rw [h₁] at h
            cases o₁ with
            | none => cases h
            | some =>
                simp only at h
                have stepIte : pstep ⟨.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip, cs, ρ, stack, result⟩
                    = some ⟨.seq (embed s) (unrollW g (embed s) k), cs, ρ, stack, result⟩ := by
                  show (match tstep noProcs none Mem.empty
                          ⟨.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip, cs, ρ, stack, result⟩ with
                        | some (_, t', _) => some t' | none => none) = _
                  simp [tstep, hb]
                refine .step stepIte ?_
                have stepSeq : pstep ⟨.seq (embed s) (unrollW g (embed s) k), cs, ρ, stack, result⟩
                    = some ⟨embed s, unrollW g (embed s) k :: cs, ρ, stack, result⟩ := rfl
                refine .step stepSeq ?_
                have hs₁ := ih (unrollW g (embed s) k :: cs) ρ ρ₁ stack result h₁
                have hpop : pstep ⟨(.skip : Stmt), unrollW g (embed s) k :: cs, ρ₁, stack, result⟩
                    = some ⟨unrollW g (embed s) k, cs, ρ₁, stack, result⟩ := rfl
                refine hs₁.trans (.step hpop ?_)
                exact ihk cs ρ₁ ρ' stack result h
          · rename_i hb
            have hρ : ρ = ρ' := by
              have := congrArg Prod.snd h; simpa using this
            subst hρ
            have stepIte : pstep ⟨.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip, cs, ρ, stack, result⟩
                = some ⟨.skip, cs, ρ, stack, result⟩ := by
              show (match tstep noProcs none Mem.empty
                      ⟨.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip, cs, ρ, stack, result⟩ with
                    | some (_, t', _) => some t' | none => none) = _
              simp [tstep, hb]
            exact .step stepIte .refl
          · cases h

/-- From an initial thread for `embed s`, we reach the terminal thread with env
`(denote s ρ).2`. -/
theorem denote_initial_sound (s : PureStmt) (ρ ρ' : Env)
    (h : denote s ρ = (some (), ρ')) :
    PureSteps (mkT (embed s) [] ρ) (mkT .skip [] ρ') :=
  denote_sound s [] ρ ρ' h

/-! ## Soundness for `denoteM`

`denoteM_sound` is the monadic analogue of `denote_sound`: a successful
`denoteM` outcome drives the embedded operational thread to `.skip` at
the same final environment. Proof mirrors `denote_sound` constructor by
constructor; the `denoteM`-side reduction uses a small bag of
`StateT`-internal unfolders (`bind`, `StateT.bind`, `StateT.get`,
`StateT.set`, `StateT.pure`) to bring each case into pair form. -/

theorem denoteM_sound (s : PureStmt) :
    ∀ (cs : List Stmt) (ρ ρ' : Env),
      denoteM s ρ = (some (), ρ') →
      PureSteps (mkT (embed s) cs ρ) (mkT .skip cs ρ') := by
  induction s with
  | skip =>
      intro cs ρ ρ' h
      simp [denoteM] at h
      obtain ⟨_, rfl⟩ := h
      exact .refl
  | assign x e =>
      intro cs ρ ρ' h
      simp only [denoteM, bind, StateT.bind, get, getThe, MonadStateOf.get,
                 StateT.get, StateT.set, set, MonadStateOf.set,
                 pure, StateT.pure] at h
      rcases hev : Expr.eval ρ e with _ | v
      · rw [hev] at h; cases h
      · rw [hev] at h; cases h
        exact .single (by simp [embed, hev])
  | seq s₁ s₂ ih₁ ih₂ =>
      intro cs ρ ρ' h
      simp only [denoteM, bind, StateT.bind] at h
      rcases h₁ : denoteM s₁ ρ with ⟨o₁, ρ₁⟩
      rw [h₁] at h
      cases o₁ with
      | none => simp [pure, StateT.pure] at h; cases h
      | some =>
          simp only at h
          have step₁ : pstep (mkT (.seq (embed s₁) (embed s₂)) cs ρ)
              = some (mkT (embed s₁) (embed s₂ :: cs) ρ) := by simp
          refine .step step₁ ?_
          have hs₁ := ih₁ (embed s₂ :: cs) ρ ρ₁ h₁
          have hpop : pstep (mkT .skip (embed s₂ :: cs) ρ₁)
              = some (mkT (embed s₂) cs ρ₁) := by simp
          refine hs₁.trans (.step hpop ?_)
          exact ih₂ cs ρ₁ ρ' h
  | ite e s₁ s₂ ih₁ ih₂ =>
      intro cs ρ ρ' h
      simp only [denoteM, bind, StateT.bind, get, getThe, MonadStateOf.get,
                 StateT.get, pure, StateT.pure] at h
      rcases hev : Expr.eval ρ e with _ | v
      · rw [hev] at h; cases h
      · rw [hev] at h
        cases v with
        | bool b =>
            cases b with
            | true =>
                have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
                    = some (mkT (embed s₁) cs ρ) := by simp [hev]
                exact .step step₁ (ih₁ cs ρ ρ' h)
            | false =>
                have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
                    = some (mkT (embed s₂) cs ρ) := by simp [hev]
                exact .step step₁ (ih₂ cs ρ ρ' h)
        | _ => cases h
  | «repeat» n s ih =>
      show ∀ cs ρ ρ', iterM (denoteM s) n ρ = (some (), ρ') →
        PureSteps (mkT (unroll (embed s) n) cs ρ) (mkT .skip cs ρ')
      induction n with
      | zero =>
          intro cs ρ ρ' h
          simp [iterM_zero, pure, StateT.pure] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs ρ ρ' h
          show PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) _
          rw [iterM_succ] at h
          simp only [bind, StateT.bind] at h
          rcases h₁ : denoteM s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => simp [pure, StateT.pure] at h; cases h
          | some =>
              simp only at h
              have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
                  = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) ρ ρ₁ h₁
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs ρ₁ ρ' h
  | forN n s ih =>
      show ∀ cs ρ ρ', iterM (denoteM s) n ρ = (some (), ρ') →
        PureSteps (mkT (unroll (embed s) n) cs ρ) (mkT .skip cs ρ')
      induction n with
      | zero =>
          intro cs ρ ρ' h
          simp [iterM_zero, pure, StateT.pure] at h
          obtain ⟨_, rfl⟩ := h
          exact .refl
      | succ k ihk =>
          intro cs ρ ρ' h
          show PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) _
          rw [iterM_succ] at h
          simp only [bind, StateT.bind] at h
          rcases h₁ : denoteM s ρ with ⟨o₁, ρ₁⟩
          rw [h₁] at h
          cases o₁ with
          | none => simp [pure, StateT.pure] at h; cases h
          | some =>
              simp only at h
              have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
                  = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
              refine .step step₁ ?_
              have hs₁ := ih (unroll (embed s) k :: cs) ρ ρ₁ h₁
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              refine hs₁.trans (.step hpop ?_)
              exact ihk cs ρ₁ ρ' h
  | while_ n g s ih =>
      show ∀ cs ρ ρ', iterWhileM (fun ρ => Expr.eval ρ g) (denoteM s) n ρ = (some (), ρ') →
        PureSteps (mkT (unrollW g (embed s) n) cs ρ) (mkT .skip cs ρ')
      induction n with
      | zero =>
          intro cs ρ ρ' h
          simp [iterWhileM_zero, pure, StateT.pure] at h
          cases h
      | succ k ihk =>
          intro cs ρ ρ' h
          show PureSteps (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ) _
          rw [iterWhileM_succ] at h
          simp only [bind, StateT.bind, get, getThe, MonadStateOf.get,
                     StateT.get, pure, StateT.pure] at h
          rcases hev : Expr.eval ρ g with _ | v
          · rw [hev] at h; cases h
          · rw [hev] at h
            cases v with
            | bool b =>
                cases b with
                | true =>
                    simp only [bind, StateT.bind] at h
                    rcases h₁ : denoteM s ρ with ⟨o₁, ρ₁⟩
                    rw [h₁] at h
                    cases o₁ with
                    | none => simp [pure, StateT.pure] at h; cases h
                    | some =>
                        simp only at h
                        have stepIte : pstep (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ)
                            = some (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ) := by
                          simp [hev]
                        refine .step stepIte ?_
                        have stepSeq : pstep (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ)
                            = some (mkT (embed s) (unrollW g (embed s) k :: cs) ρ) := by simp
                        refine .step stepSeq ?_
                        have hs₁ := ih (unrollW g (embed s) k :: cs) ρ ρ₁ h₁
                        have hpop : pstep (mkT .skip (unrollW g (embed s) k :: cs) ρ₁)
                            = some (mkT (unrollW g (embed s) k) cs ρ₁) := by simp
                        refine hs₁.trans (.step hpop ?_)
                        exact ihk cs ρ₁ ρ' h
                | false =>
                    have hρ : ρ = ρ' := by
                      have := congrArg Prod.snd h; simpa using this
                    subst hρ
                    have stepIte : pstep (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ)
                        = some (mkT .skip cs ρ) := by simp [hev]
                    exact .step stepIte .refl
            | _ => cases h

/-- Worked example: `repeat 3 (x := x + 1)` starting from `x = 0` ends with `x = 3`. -/
example :
    let r := denote (.repeat 3 (.assign "x" (.bin .add (.var "x") (.val (.int 1)))))
                   (Env.empty.set "x" (.int 0))
    r.1 = some () ∧ r.2 "x" = some (.int 3) := by
  refine ⟨rfl, rfl⟩

/-- Monadic analogue of `denote_initial_sound`. -/
theorem denoteM_initial_sound (s : PureStmt) (ρ ρ' : Env)
    (h : denoteM s ρ = (some (), ρ')) :
    PureSteps (mkT (embed s) [] ρ) (mkT .skip [] ρ') :=
  denoteM_sound s [] ρ ρ' h

/-- Monadic analogue of `denote_some_pure_steps`. -/
theorem denoteM_some_pure_steps (s : PureStmt) (cs : List Stmt) (ρ ρ' : Env)
    (h : denoteM s ρ = (some (), ρ')) :
    PureSteps (mkT (embed s) cs ρ) (mkT .skip cs ρ') :=
  denoteM_sound s cs ρ ρ' h

/-! ## Bridge to the multi-thread machine. -/

/-- Local refl-trans closure of `Machine.Step`, kept here to avoid pulling in the
Iris adequacy module. -/
inductive Machine.StepStar (p : Program) : Machine → Machine → Prop where
  | refl  (μ : Machine) : Machine.StepStar p μ μ
  | step  {μ μ' μ'' : Machine} (h₁ : Machine.Step p μ μ')
          (h₂ : Machine.StepStar p μ' μ'') : Machine.StepStar p μ μ''

theorem Machine.StepStar.trans {p : Program} {μ₁ μ₂ μ₃ : Machine} :
    Machine.StepStar p μ₁ μ₂ → Machine.StepStar p μ₂ μ₃ →
    Machine.StepStar p μ₁ μ₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- Package a `PureStmt` as a `Program`: no procedures, `main := embed s`. -/
def programOf (s : PureStmt) : Program where
  procs := noProcs
  main  := embed s

/-! ### Memory independence of `pstep`. -/

/-- A successful `pstep t` lifts to `tstep noProcs none m t` for any `m`, with the
same successor thread and unchanged heap. -/
theorem pstep_machine_indep (t t' : Thread)
    (h : pstep t = some t') (m : Mem) :
    tstep noProcs none m t = some (m, t', none) := by
  unfold pstep at h
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  cases stmt with
  | skip =>
      simp [tstep] at h
      cases cont with
      | nil =>
          cases stack with
          | nil => cases h
          | cons f rest =>
              simp [tstep, doReturn] at h ⊢
              cases hc : f.cont <;> simp [hc] at h ⊢ <;> (cases h; rfl)
      | cons s rest => cases h; simp [tstep]
  | seq a b => cases h; simp [tstep]
  | assign x e =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e <;> simp [hev] at h ⊢
      cases h; rfl
  | ite e s₁ s₂ =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          cases v <;> simp [hev] at h ⊢
          rename_i b; cases b <;> simp at h ⊢ <;> (cases h; rfl)
  | alloc x e => simp [tstep] at h
  | load x e =>
      simp [tstep, Mem.load, Mem.empty] at h
      cases hev : Expr.eval env e <;> simp [hev] at h
      rename_i v; cases v <;> simp at h
  | store eL eV =>
      simp [tstep, Mem.store, Mem.empty] at h
      cases hL : Expr.eval env eL <;> simp [hL] at h
      cases hV : Expr.eval env eV <;> simp [hV] at h
      rename_i v _; cases v <;> simp at h
  | free e =>
      simp [tstep, Mem.free, Mem.empty] at h
      cases hev : Expr.eval env e <;> simp [hev] at h
      rename_i v; cases v <;> simp at h
  | cas x eL eO eN =>
      simp [tstep, Mem.load, Mem.empty] at h
      cases hL : Expr.eval env eL <;> simp [hL] at h
      cases hO : Expr.eval env eO <;> simp [hO] at h
      cases hN : Expr.eval env eN <;> simp [hN] at h
      rename_i v _ _; cases v <;> simp at h
  | whileDo e s => cases h; simp [tstep]
  | call x f args => simp [tstep, callFrom, noProcs] at h
  | ret e =>
      simp [tstep] at h ⊢
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          simp [hev] at h ⊢
          unfold doReturn at h ⊢
          cases stack with
          | nil => cases h; rfl
          | cons f rest =>
              cases hc : f.cont <;> simp [hc] at h ⊢ <;> (cases h; rfl)
  | fork f args => simp [tstep, noProcs] at h

/-- Lift one pure step to one `Machine.Step` of the single-threaded machine. -/
theorem pstep_to_Machine_Step (s : PureStmt) (m : Mem) (t t' : Thread)
    (h : pstep t = some t') :
    Machine.Step (programOf s) ⟨m, [t]⟩ ⟨m, [t']⟩ := by
  have hts : tstep (programOf s).procs none m t = some (m, t', none) :=
    pstep_machine_indep t t' h m
  exact Machine.Step.step (p := programOf s)
    (i := 0) (chosen := none) (t := t) (t' := t') (sp := none)
    (m := m) (m' := m) (threads := [t]) (hi := rfl) (hstep := hts)

/-- Lift `PureSteps` to the single-threaded machine's refl-trans closure. -/
theorem liftPureSteps (s : PureStmt) (m : Mem) :
    ∀ {t t' : Thread}, PureSteps t t' →
      Machine.StepStar (programOf s) ⟨m, [t]⟩ ⟨m, [t']⟩ := by
  intro t t' h
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
      exact .step (pstep_to_Machine_Step s m _ _ hs) ih

/-- **Bridge theorem.** Successful denotation drives `programOf s` from its
initial machine to a single-thread halt at env `ρ'`. -/
theorem Machine.denote_sound (s : PureStmt) (ρ' : Env)
    (h : denote s Env.empty = (some (), ρ')) :
    Machine.StepStar (programOf s) (Machine.initial (programOf s))
      ⟨Mem.empty, [mkT .skip [] ρ']⟩ := by
  have hinit : Machine.initial (programOf s) =
      ⟨Mem.empty, [mkT (embed s) [] Env.empty]⟩ := rfl
  rw [hinit]
  exact liftPureSteps s Mem.empty (denote_initial_sound s Env.empty ρ' h)

/-! ## Capstone: closed-form safety from the denotational pillar. -/

/-- **Capstone corollary.** Successful denotation yields a reachable machine state
with the main thread terminated at the denotational final environment. -/
theorem PureStmt.closed_safe (s : PureStmt) (ρ' : Env)
    (h : denote s Env.empty = (some (), ρ')) :
    ∃ μ : Machine,
      Machine.StepStar (programOf s) (Machine.initial (programOf s)) μ ∧
      ∃ t, μ.threads = t :: [] ∧ t.terminated = true ∧ t.env = ρ' := by
  refine ⟨⟨Mem.empty, [mkT .skip [] ρ']⟩, Machine.denote_sound s ρ' h,
    mkT .skip [] ρ', rfl, ?_, rfl⟩
  rfl

/-- WP-style variant: from `(denote s Env.empty).1 = some ()` we get safety. -/
theorem PureStmt.closed_safe_of_success (s : PureStmt)
    (h : (denote s Env.empty).1 = some ()) :
    ∃ μ : Machine,
      Machine.StepStar (programOf s) (Machine.initial (programOf s)) μ ∧
      ∃ t ∈ μ.threads, t.terminated = true := by
  have hpair : denote s Env.empty = (some (), (denote s Env.empty).2) := by
    rcases hr : denote s Env.empty with ⟨o, ρ⟩
    rw [hr] at h
    cases o
    · cases h
    · rfl
  obtain ⟨μ, hstep, t, hts, htm, _⟩ :=
    PureStmt.closed_safe s (denote s Env.empty).2 hpair
  refine ⟨μ, hstep, t, ?_, htm⟩
  rw [hts]; exact List.mem_singleton.mpr rfl

/-! ## Reverse direction (adequacy): operational termination ⇒ denotational agreement. -/

/-- A thread on which `pstep` returns `none` is operationally stuck. -/
def pstuck (t : Thread) : Prop := pstep t = none

/-- The terminal skip-thread is stuck (`pstep` cannot fire). -/
theorem pstep_skip_empty (ρ : Env) : pstep (mkT .skip [] ρ) = none := by
  simp [pstep, tstep, mkT]

/-- `pstep` is a function, hence trivially deterministic. -/
theorem pstep_det {t t₁ t₂ : Thread} (h₁ : pstep t = some t₁)
    (h₂ : pstep t = some t₂) : t₁ = t₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- Confluence to a stuck state under deterministic `pstep`: any two stuck
endpoints reachable from `t` coincide. -/
theorem PureSteps.stuck_unique {t t_a t_b : Thread}
    (ha : PureSteps t t_a) (hsa : pstuck t_a)
    (hb : PureSteps t t_b) (hsb : pstuck t_b) :
    t_a = t_b := by
  induction ha generalizing t_b with
  | refl =>
      cases hb with
      | refl => rfl
      | step hs _ =>
          unfold pstuck at hsa; rw [hsa] at hs; cases hs
  | step hs _ ih =>
      cases hb with
      | refl =>
          unfold pstuck at hsb; rw [hsb] at hs; cases hs
      | step hs' hb' =>
          have := pstep_det hs hs'
          subst this
          exact ih hsa hb' hsb

/-- A successful `pstep` from a skip with empty cont/stack is impossible. -/
theorem not_pstep_skip_empty (ρ : Env) (t' : Thread)
    (h : pstep (mkT .skip [] ρ) = some t') : False := by
  rw [pstep_skip_empty] at h; cases h

/-- Helper: if denote produces `some`, embed reaches skip with original frame
intact (specialisation of `denote_sound` for the terminating case). -/
theorem denote_some_pure_steps (s : PureStmt) (cs : List Stmt) (ρ ρ' : Env)
    (h : denote s ρ = (some (), ρ')) :
    PureSteps (mkT (embed s) cs ρ) (mkT .skip cs ρ') :=
  denote_sound s cs ρ ρ' h

/-- When `denote s ρ` fails, the embed of `s` (with any continuation `cs`) drives
the machine to a stuck thread whose statement is **not** `.skip` — a stuck error
state, never the terminal. -/
theorem denote_none_stuck (s : PureStmt) :
    ∀ (cs : List Stmt) (ρ : Env) (r : Env),
      denote s ρ = (none, r) →
      ∃ t_stuck, PureSteps (mkT (embed s) cs ρ) t_stuck ∧ pstuck t_stuck ∧
        t_stuck.stmt ≠ .skip := by
  induction s with
  | skip =>
      intro cs ρ r h; simp [denote] at h
      cases h
  | assign x e =>
      intro cs ρ r h
      simp [denote] at h
      split at h
      · rename_i heq
        refine ⟨mkT (.assign x e) cs ρ, .refl, ?_, ?_⟩
        · simp [pstuck, pstep, tstep, mkT, heq]
        · simp [mkT]
      · cases h
  | seq s₁ s₂ ih₁ ih₂ =>
      intro cs ρ r h
      simp only [denote] at h
      generalize hde : denote s₁ ρ = res at h
      rcases res with ⟨o₁, ρ₁⟩
      have step₁ : pstep (mkT (.seq (embed s₁) (embed s₂)) cs ρ)
          = some (mkT (embed s₁) (embed s₂ :: cs) ρ) := by simp
      cases o₁ with
      | none =>
          cases h
          obtain ⟨t_stk, hst, hsk, hne⟩ := ih₁ (embed s₂ :: cs) ρ r hde
          exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
      | some =>
          simp only at h
          obtain ⟨t_stk, hst, hsk, hne⟩ := ih₂ cs ρ₁ r h
          have h_to_skip := denote_some_pure_steps s₁ (embed s₂ :: cs) ρ ρ₁ hde
          have hpop : pstep (mkT .skip (embed s₂ :: cs) ρ₁)
              = some (mkT (embed s₂) cs ρ₁) := by simp
          exact ⟨t_stk, .step step₁ (h_to_skip.trans (.step hpop hst)), hsk, hne⟩
  | ite e s₁ s₂ ih₁ ih₂ =>
      intro cs ρ r h
      simp only [denote] at h
      split at h
      · rename_i hb
        obtain ⟨t_stk, hst, hsk, hne⟩ := ih₁ cs ρ r h
        have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
            = some (mkT (embed s₁) cs ρ) := by simp [hb]
        exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
      · rename_i hb
        obtain ⟨t_stk, hst, hsk, hne⟩ := ih₂ cs ρ r h
        have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
            = some (mkT (embed s₂) cs ρ) := by simp [hb]
        exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
      · rename_i hb
        refine ⟨mkT (.ite e (embed s₁) (embed s₂)) cs ρ, .refl, ?_, ?_⟩
        · simp [pstuck, mkT_ite_step]
        · simp [mkT]
  | «repeat» n s ih =>
      show ∀ cs ρ r, iter (denote s) n ρ = (none, r) →
        ∃ t_stuck, PureSteps (mkT (unroll (embed s) n) cs ρ) t_stuck ∧
          pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
      induction n with
      | zero =>
          intro cs ρ r h; simp [iter] at h; cases h
      | succ k ihk =>
          intro cs ρ r h
          show ∃ t_stuck, PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) t_stuck ∧
            pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
          simp only [iter] at h
          generalize hde : denote s ρ = res at h
          rcases res with ⟨o₁, ρ₁⟩
          have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
              = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
          cases o₁ with
          | none =>
              cases h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ih (unroll (embed s) k :: cs) ρ r hde
              exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
          | some =>
              simp only at h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ihk cs ρ₁ r h
              have h_to_skip := denote_some_pure_steps s (unroll (embed s) k :: cs) ρ ρ₁ hde
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              exact ⟨t_stk, .step step₁ (h_to_skip.trans (.step hpop hst)), hsk, hne⟩
  | forN n s ih =>
      show ∀ cs ρ r, iter (denote s) n ρ = (none, r) →
        ∃ t_stuck, PureSteps (mkT (unroll (embed s) n) cs ρ) t_stuck ∧
          pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
      induction n with
      | zero =>
          intro cs ρ r h; simp [iter] at h; cases h
      | succ k ihk =>
          intro cs ρ r h
          show ∃ t_stuck, PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) t_stuck ∧
            pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
          simp only [iter] at h
          generalize hde : denote s ρ = res at h
          rcases res with ⟨o₁, ρ₁⟩
          have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
              = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
          cases o₁ with
          | none =>
              cases h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ih (unroll (embed s) k :: cs) ρ r hde
              exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
          | some =>
              simp only at h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ihk cs ρ₁ r h
              have h_to_skip := denote_some_pure_steps s (unroll (embed s) k :: cs) ρ ρ₁ hde
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              exact ⟨t_stk, .step step₁ (h_to_skip.trans (.step hpop hst)), hsk, hne⟩
  | while_ n g s ih =>
      show ∀ cs ρ r, denote (.while_ n g s) ρ = (none, r) →
        ∃ t_stuck, PureSteps (mkT (unrollW g (embed s) n) cs ρ) t_stuck ∧
          pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
      induction n with
      | zero =>
          intro cs ρ r _h
          -- embed at fuel 0 is the stuck `.call _no_var_ _no_proc_ []`.
          refine ⟨mkT (.call "_no_var_" "_no_proc_" []) cs ρ, .refl, ?_, ?_⟩
          · simp [pstuck, pstep, tstep, callFrom, noProcs, mkT]
          · simp [mkT]
      | succ k ihk =>
          intro cs ρ r h
          show ∃ t_stuck,
            PureSteps (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ) t_stuck
              ∧ pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
          rw [denote_while_succ] at h
          split at h
          · rename_i hb
            -- guard true: ite steps to seq, then body, then recursion
            simp only [denote] at h
            generalize hde : denote s ρ = res at h
            rcases res with ⟨o₁, ρ₁⟩
            have stepIte : pstep (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ)
                = some (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ) := by simp [hb]
            have stepSeq : pstep (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ)
                = some (mkT (embed s) (unrollW g (embed s) k :: cs) ρ) := by simp
            cases o₁ with
            | none =>
                cases h
                obtain ⟨t_stk, hst, hsk, hne⟩ := ih (unrollW g (embed s) k :: cs) ρ r hde
                exact ⟨t_stk, .step stepIte (.step stepSeq hst), hsk, hne⟩
            | some =>
                simp only at h
                obtain ⟨t_stk, hst, hsk, hne⟩ := ihk cs ρ₁ r h
                have h_to_skip := denote_some_pure_steps s (unrollW g (embed s) k :: cs) ρ ρ₁ hde
                have hpop : pstep (mkT .skip (unrollW g (embed s) k :: cs) ρ₁)
                    = some (mkT (unrollW g (embed s) k) cs ρ₁) := by simp
                refine ⟨t_stk, ?_, hsk, hne⟩
                exact .step stepIte (.step stepSeq (h_to_skip.trans (.step hpop hst)))
          · -- guard false: denote = (some (), ρ), contradiction with h
            cases h
          · rename_i hNotTrue hNotFalse
            -- guard non-bool / fail: the ite itself is stuck.
            refine ⟨mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ, .refl, ?_, ?_⟩
            · unfold pstuck
              rw [mkT_ite_step]
              cases hev : Expr.eval ρ g with
              | none => rfl
              | some v =>
                  cases v <;> try rfl
                  next b =>
                    cases b
                    · exact (hNotFalse hev).elim
                    · exact (hNotTrue hev).elim
            · simp [mkT]

/-- **Completeness** (reverse direction at empty continuation). If from
`mkT (embed s) [] ρ` we PureStep-reach the terminal `mkT .skip [] ρ'`, then
`denote s ρ = (some (), ρ')`. -/
theorem denote_complete (s : PureStmt) (ρ ρ' : Env)
    (hps : PureSteps (mkT (embed s) [] ρ) (mkT .skip [] ρ')) :
    denote s ρ = (some (), ρ') := by
  have htermB : pstuck (mkT .skip [] ρ') := by simp [pstuck, pstep_skip_empty]
  rcases hr : denote s ρ with ⟨o, ρ_d⟩
  rcases o with _ | u
  · -- none case
    exfalso
    obtain ⟨t_stk, hst, hsk, hne⟩ := denote_none_stuck s [] ρ ρ_d hr
    have heq := PureSteps.stuck_unique hst hsk hps htermB
    apply hne
    have := congrArg Thread.stmt heq
    simpa [mkT] using this
  · -- some () case
    cases u
    have hps_fwd := denote_some_pure_steps s [] ρ ρ_d hr
    have htermA : pstuck (mkT .skip [] ρ_d) := by simp [pstuck, pstep_skip_empty]
    have heq := PureSteps.stuck_unique hps_fwd htermA hps htermB
    have hρ : ρ_d = ρ' := by
      have := congrArg Thread.env heq
      simpa [mkT] using this
    subst hρ; rfl

/-! ## Reverse direction for `denoteM` -/

/-- Monadic analogue of `denote_none_stuck`. -/
theorem denoteM_none_stuck (s : PureStmt) :
    ∀ (cs : List Stmt) (ρ : Env) (r : Env),
      denoteM s ρ = (none, r) →
      ∃ t_stuck, PureSteps (mkT (embed s) cs ρ) t_stuck ∧ pstuck t_stuck ∧
        t_stuck.stmt ≠ .skip := by
  induction s with
  | skip =>
      intro cs ρ r h
      simp [denoteM, pure, StateT.pure] at h
      cases h
  | assign x e =>
      intro cs ρ r h
      simp only [denoteM, bind, StateT.bind, get, getThe, MonadStateOf.get,
                 StateT.get, StateT.set, set, MonadStateOf.set,
                 pure, StateT.pure] at h
      rcases hev : Expr.eval ρ e with _ | v
      · refine ⟨mkT (.assign x e) cs ρ, .refl, ?_, ?_⟩
        · simp [pstuck, pstep, tstep, mkT, hev]
        · simp [mkT]
      · rw [hev] at h; cases h
  | seq s₁ s₂ ih₁ ih₂ =>
      intro cs ρ r h
      simp only [denoteM, bind, StateT.bind] at h
      generalize hde : denoteM s₁ ρ = res at h
      rcases res with ⟨o₁, ρ₁⟩
      have step₁ : pstep (mkT (.seq (embed s₁) (embed s₂)) cs ρ)
          = some (mkT (embed s₁) (embed s₂ :: cs) ρ) := by simp
      cases o₁ with
      | none =>
          simp [pure, StateT.pure] at h
          cases h
          obtain ⟨t_stk, hst, hsk, hne⟩ := ih₁ (embed s₂ :: cs) ρ r hde
          exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
      | some =>
          simp only at h
          obtain ⟨t_stk, hst, hsk, hne⟩ := ih₂ cs ρ₁ r h
          have h_to_skip := denoteM_some_pure_steps s₁ (embed s₂ :: cs) ρ ρ₁ hde
          have hpop : pstep (mkT .skip (embed s₂ :: cs) ρ₁)
              = some (mkT (embed s₂) cs ρ₁) := by simp
          exact ⟨t_stk, .step step₁ (h_to_skip.trans (.step hpop hst)), hsk, hne⟩
  | ite e s₁ s₂ ih₁ ih₂ =>
      intro cs ρ r h
      simp only [denoteM, bind, StateT.bind, get, getThe, MonadStateOf.get,
                 StateT.get, pure, StateT.pure] at h
      rcases hev : Expr.eval ρ e with _ | v
      · rw [hev] at h
        refine ⟨mkT (.ite e (embed s₁) (embed s₂)) cs ρ, .refl, ?_, ?_⟩
        · simp [pstuck, mkT_ite_step, hev]
        · simp [mkT]
      · rw [hev] at h
        cases v with
        | bool b =>
            cases b with
            | true =>
                obtain ⟨t_stk, hst, hsk, hne⟩ := ih₁ cs ρ r h
                have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
                    = some (mkT (embed s₁) cs ρ) := by simp [hev]
                exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
            | false =>
                obtain ⟨t_stk, hst, hsk, hne⟩ := ih₂ cs ρ r h
                have step₁ : pstep (mkT (.ite e (embed s₁) (embed s₂)) cs ρ)
                    = some (mkT (embed s₂) cs ρ) := by simp [hev]
                exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
        | _ =>
            refine ⟨mkT (.ite e (embed s₁) (embed s₂)) cs ρ, .refl, ?_, ?_⟩
            · simp [pstuck, mkT_ite_step, hev]
            · simp [mkT]
  | «repeat» n s ih =>
      show ∀ cs ρ r, iterM (denoteM s) n ρ = (none, r) →
        ∃ t_stuck, PureSteps (mkT (unroll (embed s) n) cs ρ) t_stuck ∧
          pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
      induction n with
      | zero =>
          intro cs ρ r h; simp [iterM_zero, pure, StateT.pure] at h
          cases h
      | succ k ihk =>
          intro cs ρ r h
          show ∃ t_stuck, PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) t_stuck ∧
            pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
          rw [iterM_succ] at h
          simp only [bind, StateT.bind] at h
          generalize hde : denoteM s ρ = res at h
          rcases res with ⟨o₁, ρ₁⟩
          have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
              = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
          cases o₁ with
          | none =>
              simp [pure, StateT.pure] at h
              cases h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ih (unroll (embed s) k :: cs) ρ r hde
              exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
          | some =>
              simp only at h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ihk cs ρ₁ r h
              have h_to_skip := denoteM_some_pure_steps s (unroll (embed s) k :: cs) ρ ρ₁ hde
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              exact ⟨t_stk, .step step₁ (h_to_skip.trans (.step hpop hst)), hsk, hne⟩
  | forN n s ih =>
      show ∀ cs ρ r, iterM (denoteM s) n ρ = (none, r) →
        ∃ t_stuck, PureSteps (mkT (unroll (embed s) n) cs ρ) t_stuck ∧
          pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
      induction n with
      | zero =>
          intro cs ρ r h; simp [iterM_zero, pure, StateT.pure] at h
          cases h
      | succ k ihk =>
          intro cs ρ r h
          show ∃ t_stuck, PureSteps (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ) t_stuck ∧
            pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
          rw [iterM_succ] at h
          simp only [bind, StateT.bind] at h
          generalize hde : denoteM s ρ = res at h
          rcases res with ⟨o₁, ρ₁⟩
          have step₁ : pstep (mkT (.seq (embed s) (unroll (embed s) k)) cs ρ)
              = some (mkT (embed s) (unroll (embed s) k :: cs) ρ) := by simp
          cases o₁ with
          | none =>
              simp [pure, StateT.pure] at h
              cases h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ih (unroll (embed s) k :: cs) ρ r hde
              exact ⟨t_stk, .step step₁ hst, hsk, hne⟩
          | some =>
              simp only at h
              obtain ⟨t_stk, hst, hsk, hne⟩ := ihk cs ρ₁ r h
              have h_to_skip := denoteM_some_pure_steps s (unroll (embed s) k :: cs) ρ ρ₁ hde
              have hpop : pstep (mkT .skip (unroll (embed s) k :: cs) ρ₁)
                  = some (mkT (unroll (embed s) k) cs ρ₁) := by simp
              exact ⟨t_stk, .step step₁ (h_to_skip.trans (.step hpop hst)), hsk, hne⟩
  | while_ n g s ih =>
      show ∀ cs ρ r, iterWhileM (fun ρ => Expr.eval ρ g) (denoteM s) n ρ = (none, r) →
        ∃ t_stuck, PureSteps (mkT (unrollW g (embed s) n) cs ρ) t_stuck ∧
          pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
      induction n with
      | zero =>
          intro cs ρ r _h
          refine ⟨mkT (.call "_no_var_" "_no_proc_" []) cs ρ, .refl, ?_, ?_⟩
          · simp [pstuck, pstep, tstep, callFrom, noProcs, mkT]
          · simp [mkT]
      | succ k ihk =>
          intro cs ρ r h
          show ∃ t_stuck,
            PureSteps (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ) t_stuck
              ∧ pstuck t_stuck ∧ t_stuck.stmt ≠ .skip
          rw [iterWhileM_succ] at h
          simp only [bind, StateT.bind, get, getThe, MonadStateOf.get,
                     StateT.get, pure, StateT.pure] at h
          rcases hev : Expr.eval ρ g with _ | v
          · rw [hev] at h
            refine ⟨mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ, .refl, ?_, ?_⟩
            · simp [pstuck, mkT_ite_step, hev]
            · simp [mkT]
          · rw [hev] at h
            cases v with
            | bool b =>
                cases b with
                | true =>
                    simp only [bind, StateT.bind] at h
                    generalize hde : denoteM s ρ = res at h
                    rcases res with ⟨o₁, ρ₁⟩
                    have stepIte : pstep (mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ)
                        = some (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ) := by simp [hev]
                    have stepSeq : pstep (mkT (.seq (embed s) (unrollW g (embed s) k)) cs ρ)
                        = some (mkT (embed s) (unrollW g (embed s) k :: cs) ρ) := by simp
                    cases o₁ with
                    | none =>
                        simp [pure, StateT.pure] at h
                        cases h
                        obtain ⟨t_stk, hst, hsk, hne⟩ := ih (unrollW g (embed s) k :: cs) ρ r hde
                        exact ⟨t_stk, .step stepIte (.step stepSeq hst), hsk, hne⟩
                    | some =>
                        simp only at h
                        obtain ⟨t_stk, hst, hsk, hne⟩ := ihk cs ρ₁ r h
                        have h_to_skip := denoteM_some_pure_steps s (unrollW g (embed s) k :: cs) ρ ρ₁ hde
                        have hpop : pstep (mkT .skip (unrollW g (embed s) k :: cs) ρ₁)
                            = some (mkT (unrollW g (embed s) k) cs ρ₁) := by simp
                        refine ⟨t_stk, ?_, hsk, hne⟩
                        exact .step stepIte (.step stepSeq (h_to_skip.trans (.step hpop hst)))
                | false => cases h
            | _ =>
                refine ⟨mkT (.ite g (.seq (embed s) (unrollW g (embed s) k)) .skip) cs ρ, .refl, ?_, ?_⟩
                · simp [pstuck, mkT_ite_step, hev]
                · simp [mkT]

/-- Monadic analogue of `denote_complete`. -/
theorem denoteM_complete (s : PureStmt) (ρ ρ' : Env)
    (hps : PureSteps (mkT (embed s) [] ρ) (mkT .skip [] ρ')) :
    denoteM s ρ = (some (), ρ') := by
  have htermB : pstuck (mkT .skip [] ρ') := by simp [pstuck, pstep_skip_empty]
  rcases hr : denoteM s ρ with ⟨o, ρ_d⟩
  rcases o with _ | u
  · exfalso
    obtain ⟨t_stk, hst, hsk, hne⟩ := denoteM_none_stuck s [] ρ ρ_d hr
    have heq := PureSteps.stuck_unique hst hsk hps htermB
    apply hne
    have := congrArg Thread.stmt heq
    simpa [mkT] using this
  · cases u
    have hps_fwd := denoteM_some_pure_steps s [] ρ ρ_d hr
    have htermA : pstuck (mkT .skip [] ρ_d) := by simp [pstuck, pstep_skip_empty]
    have heq := PureSteps.stuck_unique hps_fwd htermA hps htermB
    have hρ : ρ_d = ρ' := by
      have := congrArg Thread.env heq
      simpa [mkT] using this
    subst hρ; rfl

/-! ### Reflecting Machine.StepStar into PureSteps for `programOf s`. -/

/-- Generic inversion: a `Machine.Step` from `⟨m, threads⟩` to `μ'` factors
as one `tstep` of some thread in the pool. -/
theorem Machine.Step.invert {p : Program} {m : Mem} {threads : List Thread} {μ' : Machine}
    (h : Machine.Step p ⟨m, threads⟩ μ') :
    ∃ i chosen t t' sp m', threads[i]? = some t ∧
      tstep p.procs chosen m t = some (m', t', sp) ∧
      μ' = ⟨m', threads.set i t' ++ sp.toList⟩ := by
  cases h with
  | step i chosen t t' sp m m' threads hi hstep =>
    exact ⟨i, chosen, t, t', sp, m', hi, hstep, rfl⟩

/-- A single `Machine.Step` of `programOf s` from `⟨Mem.empty, [t]⟩` to
`⟨Mem.empty, [t']⟩` corresponds to one `pstep`. -/
theorem Machine_Step_pure (s : PureStmt) (t t' : Thread)
    (h : Machine.Step (programOf s)
            ⟨Mem.empty, [t]⟩ ⟨Mem.empty, [t']⟩) :
    pstep t = some t' := by
  obtain ⟨i, chosen, t₀, t₁, sp, m', hi, hstep, hμ'⟩ := h.invert
  -- From hi : [t][i]? = some t₀, get i = 0 and t₀ = t.
  have hi0 : i = 0 := by
    rcases i with _ | i'
    · rfl
    · simp at hi
  subst hi0
  simp at hi
  subst hi
  -- From hμ' : ⟨Mem.empty, [t']⟩ = ⟨m', [t].set 0 t₁ ++ sp.toList⟩,
  -- extract m' = Mem.empty and the threads equation.
  have hμ_mem : m' = Mem.empty := by
    have := congrArg Machine.mem hμ'.symm
    simpa using this
  -- Threads eq: [t'] vs t₁ :: sp.toList. Use it later by case on sp.
  have hμ_thr0 : ([t] : List Thread).set 0 t₁ ++ sp.toList = [t'] := by
    have := congrArg Machine.threads hμ'
    -- this : ⟨Mem.empty, [t']⟩.threads = ⟨m', _⟩.threads
    exact this.symm
  subst hμ_mem
  -- Case-split on chosen.
  cases hch : chosen with
  | none =>
      rw [hch] at hstep
      -- pstep is tstep noProcs none Mem.empty t = some (Mem.empty, t₁, sp).
      -- We need pstep t = some t'. Use hstep and the threads equation.
      have hsp : sp = none := by
        cases sp with
        | none => rfl
        | some sp' => simp at hμ_thr0
      subst hsp
      simp at hμ_thr0
      subst hμ_thr0
      unfold pstep
      rw [show (programOf s).procs = noProcs from rfl] at hstep
      rw [hstep]
  | some l =>
      rw [hch] at hstep
      -- The alloc branch produces m' ≠ Mem.empty (it allocates a fresh slot).
      exfalso
      -- Drill into tstep with chosen = some l. Only stmt = .alloc proceeds.
      unfold tstep at hstep
      obtain ⟨stmt, cont, env, stack, result⟩ := t
      cases stmt <;> simp at hstep
      -- only .alloc case survives
      rename_i x e
      cases hev : Expr.eval env e with
      | none => simp [hev] at hstep
      | some v =>
          simp [hev] at hstep
          cases hal : Mem.empty.alloc l v with
          | none => simp [hal] at hstep
          | some m'' =>
              simp [hal] at hstep
              -- hstep gives m' = m'' and (stuff).
              -- m'' = (Mem.empty).update l (some v). It has a non-none slot at l.
              -- Meanwhile m' = Mem.empty (from hμ_mem). So Mem.empty = m'' is a contradiction.
              -- But wait we already subst'd m' = Mem.empty. So hstep yields m'' = Mem.empty.
              -- Extract first component.
              obtain ⟨hm, _⟩ := hstep
              -- m'' is alloc'd at l: (m''.fn l) = some v. But (Mem.empty.fn l) = none.
              -- We have hal : Mem.empty.alloc l v = some m''. By def, m'' = update Mem.empty l (some v).
              have hm''_l : m''.fn l = some v := by
                unfold Mem.alloc at hal
                simp [Mem.empty] at hal
                subst hal
                simp [Mem.update]
              have : Mem.empty.fn l = some v := by rw [← hm]; exact hm''_l
              simp [Mem.empty] at this

/-! ### Embed-shape invariant on threads. -/

/-- The statements appearing in `embed`'s image — these are heap-free,
call-free, fork-free, and `alloc`-free. -/
inductive EmbedShape : Stmt → Prop where
  | skip   : EmbedShape .skip
  | assign : ∀ x e, EmbedShape (.assign x e)
  | seq    : ∀ s₁ s₂, EmbedShape s₁ → EmbedShape s₂ → EmbedShape (.seq s₁ s₂)
  | ite    : ∀ e s₁ s₂, EmbedShape s₁ → EmbedShape s₂ → EmbedShape (.ite e s₁ s₂)
  /-- Stuck `call` to an unknown procedure: used as the operational
  representation of "out of fuel" in `unrollW`. -/
  | callStuck : ∀ x f args, EmbedShape (.call x f args)

theorem unroll_embedShape (body : Stmt) (h : EmbedShape body) :
    ∀ n, EmbedShape (unroll body n)
  | 0     => .skip
  | n + 1 => .seq _ _ h (unroll_embedShape body h n)

theorem unrollW_embedShape (g : Expr) (body : Stmt) (h : EmbedShape body) :
    ∀ n, EmbedShape (unrollW g body n)
  | 0     => .callStuck _ _ _
  | n + 1 => .ite _ _ _ (.seq _ _ h (unrollW_embedShape g body h n)) .skip

theorem embed_embedShape (s : PureStmt) : EmbedShape (embed s) := by
  induction s with
  | skip => exact .skip
  | assign x e => exact .assign x e
  | seq s₁ s₂ ih₁ ih₂ => exact .seq _ _ ih₁ ih₂
  | ite e s₁ s₂ ih₁ ih₂ => exact .ite _ _ _ ih₁ ih₂
  | «repeat» n s ih => exact unroll_embedShape _ ih n
  | forN n s ih => exact unroll_embedShape _ ih n
  | while_ n g s ih => exact unrollW_embedShape g (embed s) ih n

/-- An invariant on threads: the current `stmt` and every queued cont entry are
embed-shaped, and the stack is empty (no call frames). -/
structure ThreadEmbed (t : Thread) : Prop where
  stmt  : EmbedShape t.stmt
  cont  : ∀ s ∈ t.cont, EmbedShape s
  stack : t.stack = []
  result : t.result = none

theorem mkT_embed_inv (s : PureStmt) (ρ : Env) :
    ThreadEmbed (mkT (embed s) [] ρ) where
  stmt := embed_embedShape s
  cont := by intro s hs; cases hs
  stack := rfl
  result := rfl

/-- `pstep` preserves `ThreadEmbed`. -/
theorem pstep_preserves_embed {t t' : Thread} (he : ThreadEmbed t)
    (h : pstep t = some t') : ThreadEmbed t' := by
  unfold pstep at h
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  have hst := he.stmt
  have hco := he.cont
  have hsk := he.stack
  have hre := he.result
  simp at hsk hre
  subst hsk; subst hre
  cases hst with
  | skip =>
      -- t.stmt = .skip. tstep noProcs none Mem.empty ⟨.skip, cont, env, [], none⟩.
      cases cont with
      | nil =>
          simp [tstep] at h
      | cons s rest =>
          simp [tstep] at h
          rcases h with ⟨rfl⟩
          refine ⟨?_, ?_, rfl, rfl⟩
          · exact hco s (by simp)
          · intro c hc; exact hco c (by simp [hc])
  | assign x e =>
      simp [tstep] at h
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          simp [hev] at h
          rcases h with ⟨rfl⟩
          exact ⟨.skip, hco, rfl, rfl⟩
  | seq s₁ s₂ h₁ h₂ =>
      simp [tstep] at h
      rcases h with ⟨rfl⟩
      refine ⟨h₁, ?_, rfl, rfl⟩
      intro c hc
      cases hc with
      | head => exact h₂
      | tail _ hc' => exact hco c hc'
  | ite e s₁ s₂ h₁ h₂ =>
      simp [tstep] at h
      cases hev : Expr.eval env e with
      | none => simp [hev] at h
      | some v =>
          cases v <;> simp [hev] at h
          rename_i b; cases b <;> simp at h
          · rcases h with ⟨rfl⟩; exact ⟨h₂, hco, rfl, rfl⟩
          · rcases h with ⟨rfl⟩; exact ⟨h₁, hco, rfl, rfl⟩
  | callStuck x f args =>
      -- noProcs makes `.call` stuck, so pstep returns none — vacuous.
      exfalso
      simp [tstep, callFrom, noProcs] at h

/-- Every `Machine.Step` from a single-thread embed-shaped configuration with
empty memory lands in the same shape — and is exactly a `pstep`. -/
theorem machineStep_pure_embed (s : PureStmt) (t : Thread) (he : ThreadEmbed t) (μ' : Machine)
    (h : Machine.Step (programOf s) ⟨Mem.empty, [t]⟩ μ') :
    ∃ t', μ' = ⟨Mem.empty, [t']⟩ ∧ pstep t = some t' ∧ ThreadEmbed t' := by
  obtain ⟨i, chosen, t₀, t₁, sp, m', hi, hstep, hμ'⟩ := h.invert
  have hi0 : i = 0 := by
    rcases i with _ | i'
    · rfl
    · simp at hi
  subst hi0
  simp at hi
  subst hi
  have hst := he.stmt
  have hco := he.cont
  have hsk := he.stack
  have hre := he.result
  -- Derive memory and threads constraints from hμ' lazily; first analyse chosen + stmt.
  have hps : pstep t = some t₁ ∧ m' = Mem.empty ∧ sp = none := by
    obtain ⟨stmt, cont, env, stack, result⟩ := t
    simp at hsk hre
    subst hsk; subst hre
    cases hch : chosen with
    | some l =>
        rw [hch] at hstep
        exfalso
        -- chosen = some l only succeeds on .alloc; embed has no .alloc.
        cases hst <;> simp [tstep] at hstep
    | none =>
        rw [hch] at hstep
        -- chosen = none. Case on stmt.
        cases hst with
        | skip =>
            cases cont with
            | nil => simp [tstep] at hstep
            | cons sh rest =>
                simp [tstep] at hstep
                rcases hstep with ⟨hm, ht₁, hsp⟩
                refine ⟨?_, hm.symm, hsp.symm⟩
                unfold pstep; simp [tstep, ← ht₁]
        | assign x e =>
            simp [tstep] at hstep
            cases hev : Expr.eval env e with
            | none => simp [hev] at hstep
            | some v =>
                simp [hev] at hstep
                rcases hstep with ⟨hm, ht₁, hsp⟩
                refine ⟨?_, hm.symm, hsp.symm⟩
                unfold pstep; simp [tstep, hev, ← ht₁]
        | seq a b ha hb =>
            simp [tstep] at hstep
            rcases hstep with ⟨hm, ht₁, hsp⟩
            refine ⟨?_, hm.symm, hsp.symm⟩
            unfold pstep; simp [tstep, ← ht₁]
        | ite e a b ha hb =>
            simp [tstep] at hstep
            cases hev : Expr.eval env e with
            | none => simp [hev] at hstep
            | some v =>
                cases v <;> simp [hev] at hstep
                rename_i bv
                cases bv <;> simp at hstep <;>
                  · rcases hstep with ⟨hm, ht₁, hsp⟩
                    refine ⟨?_, hm.symm, hsp.symm⟩
                    unfold pstep; simp [tstep, hev, ← ht₁]
        | callStuck x f args =>
            exfalso
            simp [tstep, callFrom] at hstep
            rw [show (programOf s).procs = noProcs from rfl] at hstep
            simp [noProcs] at hstep
  obtain ⟨hp, hm, hsp_eq⟩ := hps
  subst hm; subst hsp_eq
  refine ⟨t₁, ?_, hp, ?_⟩
  · -- μ' = ⟨Mem.empty, [t].set 0 t₁ ++ none.toList⟩ = ⟨Mem.empty, [t₁]⟩.
    rw [hμ']; simp
  · exact pstep_preserves_embed he hp

theorem machineStepStar_to_PureSteps (s : PureStmt) :
    ∀ {μ μ' : Machine}, Machine.StepStar (programOf s) μ μ' →
      ∀ t t', ThreadEmbed t → μ = ⟨Mem.empty, [t]⟩ → μ' = ⟨Mem.empty, [t']⟩ →
        PureSteps t t' := by
  intro μ μ' h
  induction h with
  | refl _ =>
      intro t t' _ hμ hμ'
      rw [hμ] at hμ'
      have : [t] = [t'] := by
        have := congrArg Machine.threads hμ'
        simpa using this
      have ht : t = t' := by injection this
      subst ht; exact .refl
  | step hs _ ih =>
      intro t t' he hμ hμ'
      subst hμ
      obtain ⟨t_mid, hmid, hpstep, he'⟩ := machineStep_pure_embed s t he _ hs
      have hrest := ih t_mid t' he' hmid hμ'
      exact .step hpstep hrest

/-- **Reverse adequacy.** If the multi-thread machine reaches the terminal
configuration with thread environment `ρ'`, then `denote s Env.empty` agrees
on `ρ'`. This is the converse to `Machine.denote_sound`. -/
theorem Machine.exec_sound (s : PureStmt) (ρ' : Env) :
    Machine.StepStar (programOf s) (Machine.initial (programOf s))
      ⟨Mem.empty, [mkT .skip [] ρ']⟩ →
    denote s Env.empty = (some (), ρ') := by
  intro hsteps
  apply denote_complete s Env.empty ρ'
  have hinit : Machine.initial (programOf s) =
      ⟨Mem.empty, [mkT (embed s) [] Env.empty]⟩ := rfl
  rw [hinit] at hsteps
  exact machineStepStar_to_PureSteps s hsteps _ _ (mkT_embed_inv s Env.empty) rfl rfl

/-- **Bidirectional marquee adequacy.** The denotational evaluator returns
`(some (), ρ')` from the empty environment iff the multi-thread operational
machine reaches the terminated single-thread configuration with environment
`ρ'`. This packages `Machine.denote_sound` and `Machine.exec_sound` into one
iff. -/
theorem Machine.denote_iff (s : PureStmt) (ρ' : Env) :
    denote s Env.empty = (some (), ρ') ↔
      Machine.StepStar (programOf s) (Machine.initial (programOf s))
        ⟨Mem.empty, [mkT .skip [] ρ']⟩ :=
  ⟨Machine.denote_sound s ρ', Machine.exec_sound s ρ'⟩

/-- **Existential reachability corollary.** The denotation succeeds (returns
`some ()`) iff the operational machine can reach some terminated single-thread
configuration. This is the "denotation halts iff operationally reaches a
terminated state" packaging. -/
theorem Machine.exec_complete_safe (s : PureStmt) :
    (∃ ρ', denote s Env.empty = (some (), ρ')) ↔
      ∃ ρ', Machine.StepStar (programOf s) (Machine.initial (programOf s))
        ⟨Mem.empty, [mkT .skip [] ρ']⟩ :=
  ⟨fun ⟨ρ', h⟩ => ⟨ρ', (Machine.denote_iff s ρ').mp h⟩,
   fun ⟨ρ', h⟩ => ⟨ρ', (Machine.denote_iff s ρ').mpr h⟩⟩

/-! ## Marquee numeric example: `forN n` sums `1 + 2 + … + n`.

The denotation of a Gauss-sum loop matches the closed form `gauss n` (which
is `∑_{j<n} (j+1)`), and via `Machine.denote_iff` this lifts to a closed
operational reachability statement. -/

/-- Loop body: `s := s + i; i := i + 1`. -/
def sumBody : PureStmt :=
  .seq (.assign "s" (.bin .add (.var "s") (.var "i")))
       (.assign "i" (.bin .add (.var "i") (.val (.int 1))))

/-- Full Gauss program: zero `s`, set `i := 1`, then accumulate `n` times. -/
def sumProg (n : Nat) : PureStmt :=
  .seq (.assign "s" (.val (.int 0)))
   (.seq (.assign "i" (.val (.int 1)))
    (.forN n sumBody))

/-- Post-loop env after some Gauss iterations. -/
def gaussEnv (s₀ i₀ : Int) : Env :=
  (Env.empty.set "s" (.int s₀)).set "i" (.int i₀)

/-- Closed-form `∑_{j<n} (j+1)`. -/
def gauss : Nat → Int
  | 0     => 0
  | n + 1 => gauss n + (n + 1 : Nat)

/-- Eval `.bin add (.var x) (.var y)` when both vars hold ints. -/
theorem eval_add_vars (ρ : Env) (x y : Name) (a b : Int)
    (hx : ρ x = some (Val.int a)) (hy : ρ y = some (Val.int b)) :
    Expr.eval ρ (Expr.bin .add (.var x) (.var y)) = some (Val.int (a + b)) := by
  show (do let v₁ ← ρ x; let v₂ ← ρ y; BinOp.eval .add v₁ v₂) = _
  rw [hx, hy]; rfl

/-- Eval `.bin add (.var x) (.val (.int c))`. -/
theorem eval_add_var_const (ρ : Env) (x : Name) (a c : Int)
    (hx : ρ x = some (Val.int a)) :
    Expr.eval ρ (Expr.bin .add (.var x) (.val (.int c)))
      = some (Val.int (a + c)) := by
  show (do let v₁ ← ρ x; let v₂ ← some (Val.int c); BinOp.eval .add v₁ v₂) = _
  rw [hx]; rfl

/-- One step of the Gauss loop body: from `(s, i)` to `(s + i, i + 1)`. -/
theorem denote_sumBody (s₀ i₀ : Int) :
    denote sumBody (gaussEnv s₀ i₀)
      = (some (), gaussEnv (s₀ + i₀) (i₀ + 1)) := by
  have hs : (gaussEnv s₀ i₀) "s" = some (.int s₀) := by
    simp [gaussEnv, Env.set]
  have hi : (gaussEnv s₀ i₀) "i" = some (.int i₀) := by
    simp [gaussEnv, Env.set]
  have he1 := eval_add_vars (gaussEnv s₀ i₀) "s" "i" s₀ i₀ hs hi
  have hi' : ((gaussEnv s₀ i₀).set "s" (Val.int (s₀ + i₀))) "i"
              = some (Val.int i₀) := by simp [gaussEnv, Env.set]
  have he2 := eval_add_var_const ((gaussEnv s₀ i₀).set "s" (Val.int (s₀ + i₀)))
              "i" i₀ 1 hi'
  simp only [sumBody, denote, he1, he2]
  congr 1
  funext y
  by_cases hyi : y = "i"
  · subst hyi; simp [gaussEnv, Env.set]
  · by_cases hys : y = "s"
    · subst hys; simp [gaussEnv, Env.set, hyi]
    · simp [gaussEnv, Env.set, hyi, hys]

/-- Sum of consecutive integers `start, start+1, …, start+k-1`. -/
def sumFrom (start : Int) : Nat → Int
  | 0     => 0
  | k + 1 => start + sumFrom (start + 1) k

theorem sumFrom_succ_right (a : Int) :
    ∀ k, sumFrom a (k + 1) = sumFrom a k + (a + k) := by
  intro k
  induction k generalizing a with
  | zero => show a + 0 = 0 + (a + 0); omega
  | succ j ihj =>
      show a + sumFrom (a + 1) (j + 1) = (a + sumFrom (a + 1) j) + (a + ((j : Int) + 1))
      rw [ihj (a + 1)]
      have : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by push_cast; rfl
      omega

/-- General loop invariant. -/
theorem denote_forN_sumBody_general :
    ∀ (k : Nat) (s₀ i₀ : Int),
      denote (.forN k sumBody) (gaussEnv s₀ i₀)
        = (some (), gaussEnv (s₀ + sumFrom i₀ k) (i₀ + k)) := by
  intro k
  induction k with
  | zero =>
      intro s₀ i₀
      show (some (), gaussEnv s₀ i₀)
        = (some (), gaussEnv (s₀ + sumFrom i₀ 0) (i₀ + ((0 : Nat) : Int)))
      have h1 : s₀ + sumFrom i₀ 0 = s₀ := by show s₀ + 0 = s₀; omega
      have h2 : i₀ + ((0 : Nat) : Int) = i₀ := by simp
      rw [h1, h2]
  | succ k ih =>
      intro s₀ i₀
      rw [denote_forN_succ]
      show (match denote sumBody (gaussEnv s₀ i₀) with
            | (none, ρ')   => (none, ρ')
            | (some _, ρ') => denote (.forN k sumBody) ρ')
          = (some (), gaussEnv (s₀ + sumFrom i₀ (k + 1)) (i₀ + (k + 1 : Nat)))
      rw [denote_sumBody]
      show denote (.forN k sumBody) (gaussEnv (s₀ + i₀) (i₀ + 1)) = _
      rw [ih (s₀ + i₀) (i₀ + 1)]
      have h1 : s₀ + sumFrom i₀ (k + 1) = (s₀ + i₀) + sumFrom (i₀ + 1) k := by
        show s₀ + (i₀ + sumFrom (i₀ + 1) k) = _; omega
      have h2 : i₀ + ((k + 1 : Nat) : Int) = (i₀ + 1) + (k : Nat) := by
        have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by push_cast; rfl
        omega
      rw [h1, h2]

/-- `sumFrom 1 n = gauss n`. -/
theorem sumFrom_one_eq_gauss (n : Nat) : sumFrom 1 n = gauss n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [sumFrom_succ_right 1 k, ih]
      show gauss k + (1 + (k : Int)) = gauss k + ((k + 1 : Nat) : Int)
      have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by push_cast; rfl
      omega

/-- **Marquee Gauss identity.** The denotation of `sumProg n` from the empty
environment terminates with `"s" ↦ gauss n` and `"i" ↦ n + 1`. -/
theorem denote_sumProg (n : Nat) :
    denote (sumProg n) Env.empty
      = (some (), gaussEnv (gauss n) (n + 1)) := by
  show denote (.seq (.assign "s" (.val (.int 0)))
              (.seq (.assign "i" (.val (.int 1)))
                    (.forN n sumBody))) Env.empty = _
  show (match denote (.assign "s" (.val (.int 0))) Env.empty with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote _ ρ') = _
  show denote (.seq (.assign "i" (.val (.int 1))) (.forN n sumBody))
        (Env.empty.set "s" (.int 0)) = _
  show (match denote (.assign "i" (.val (.int 1)))
              (Env.empty.set "s" (.int 0)) with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote (.forN n sumBody) ρ') = _
  show denote (.forN n sumBody)
        ((Env.empty.set "s" (.int 0)).set "i" (.int 1)) = _
  show denote (.forN n sumBody) (gaussEnv 0 1) = _
  rw [denote_forN_sumBody_general n 0 1, sumFrom_one_eq_gauss]
  congr 1
  show gaussEnv (0 + gauss n) (1 + (n : Int)) = gaussEnv (gauss n) ((n : Int) + 1)
  have h1 : (0 : Int) + gauss n = gauss n := by omega
  have h2 : (1 : Int) + (n : Int) = (n : Int) + 1 := by omega
  rw [h1, h2]

/-- Worked instance: `sumProg 10` accumulates to `55` in `"s"`. -/
example :
    (denote (sumProg 10) Env.empty).2 "s" = some (.int 55) := by
  rw [denote_sumProg]; rfl

/-- **Operational corollary.** Via `Machine.denote_iff`, the multi-thread
operational machine for `sumProg n` reaches the terminated single-thread
configuration whose environment binds `"s"` to the Gauss closed form. -/
theorem Machine.sumProg_reaches_gauss (n : Nat) :
    Machine.StepStar (programOf (sumProg n))
      (Machine.initial (programOf (sumProg n)))
      ⟨Mem.empty, [mkT .skip [] (gaussEnv (gauss n) (n + 1))]⟩ :=
  (Machine.denote_iff (sumProg n) (gaussEnv (gauss n) (n + 1))).mp
    (denote_sumProg n)

/-! ## Marquee numeric example: `forN n` computes `∏_{i=a}^{b-1} i`.

This mirrors the Gauss-sum setup above, but:
* The loop body multiplies instead of adds.
* The starting value of the counter `i` is read from a variable `"a"`
  (rather than a constant `1`), and the loop bound is supplied externally
  by the caller as `(b - a).toNat`. The caller sets up `"a"` and `"b"`
  in the environment beforehand (e.g. via `bindParams`). -/

/-- Loop body: `s := s * i; i := i + 1`. -/
def productBody : PureStmt :=
  .seq (.assign "s" (.bin .mul (.var "s") (.var "i")))
       (.assign "i" (.bin .add (.var "i") (.val (.int 1))))

/-- Full product program: set `s := 1`, set `i := a` (reading from env),
then accumulate the body `n` times. The caller supplies
`n := (b - a).toNat` and an environment with `"a"` and `"b"` bound. -/
def productProg (n : Nat) : PureStmt :=
  .seq (.assign "s" (.val (.int 1)))
   (.seq (.assign "i" (.var "a"))
    (.forN n productBody))

/-- Post-loop env: `"a"`, `"b"`, `"s"`, `"i"` bound (in that order, so
later sets shadow earlier ones for repeated names). -/
def productEnv (a b s₀ i₀ : Int) : Env :=
  ((((Env.empty.set "a" (.int a)).set "b" (.int b)).set
    "s" (.int s₀)).set "i" (.int i₀))

/-- Closed-form product `start * (start+1) * … * (start+k-1)`. -/
def productFrom (start : Int) : Nat → Int
  | 0     => 1
  | k + 1 => start * productFrom (start + 1) k

/-- Closed-form `∏_{i=a}^{b-1} i`. When `b ≤ a` this is `1` (empty
product), because `(b - a).toNat = 0`. -/
def rangeProd (a b : Int) : Int := productFrom a (b - a).toNat

/-- Eval `.bin mul (.var x) (.var y)` when both vars hold ints. -/
theorem eval_mul_vars (ρ : Env) (x y : Name) (a b : Int)
    (hx : ρ x = some (Val.int a)) (hy : ρ y = some (Val.int b)) :
    Expr.eval ρ (Expr.bin .mul (.var x) (.var y)) = some (Val.int (a * b)) := by
  show (do let v₁ ← ρ x; let v₂ ← ρ y; BinOp.eval .mul v₁ v₂) = _
  rw [hx, hy]; rfl

/-- One step of the product loop body:
from `(s, i)` to `(s * i, i + 1)`. -/
theorem denote_productBody (a b s₀ i₀ : Int) :
    denote productBody (productEnv a b s₀ i₀)
      = (some (), productEnv a b (s₀ * i₀) (i₀ + 1)) := by
  have hs : (productEnv a b s₀ i₀) "s" = some (.int s₀) := by
    simp [productEnv, Env.set]
  have hi : (productEnv a b s₀ i₀) "i" = some (.int i₀) := by
    simp [productEnv, Env.set]
  have he1 := eval_mul_vars (productEnv a b s₀ i₀) "s" "i" s₀ i₀ hs hi
  have hi' : ((productEnv a b s₀ i₀).set "s" (Val.int (s₀ * i₀))) "i"
              = some (Val.int i₀) := by simp [productEnv, Env.set]
  have he2 := eval_add_var_const ((productEnv a b s₀ i₀).set
                "s" (Val.int (s₀ * i₀))) "i" i₀ 1 hi'
  simp only [productBody, denote, he1, he2]
  congr 1
  funext y
  by_cases hyi : y = "i"
  · subst hyi; simp [productEnv, Env.set]
  · by_cases hys : y = "s"
    · subst hys; simp [productEnv, Env.set, hyi]
    · simp [productEnv, Env.set, hyi, hys]

theorem productFrom_succ_right (a : Int) :
    ∀ k, productFrom a (k + 1) = productFrom a k * (a + k) := by
  intro k
  induction k generalizing a with
  | zero => show a * 1 = 1 * (a + 0); simp
  | succ j ihj =>
      show a * productFrom (a + 1) (j + 1)
            = (a * productFrom (a + 1) j) * (a + ((j : Int) + 1))
      rw [ihj (a + 1)]
      have hj : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by push_cast; rfl
      -- LHS = a * (productFrom (a+1) j * (a+1+j))
      -- RHS = (a * productFrom (a+1) j) * (a+j+1)
      -- Use associativity and the fact that (a+1)+j = a+(j+1).
      have hcomm : (a + 1) + (j : Int) = a + ((j : Int) + 1) := by omega
      rw [hcomm, Int.mul_assoc]

/-- General loop invariant: after `k` iterations from `(s₀, i₀)`, the
accumulator is `s₀ * productFrom i₀ k` and the counter is `i₀ + k`. -/
theorem denote_forN_productBody_general :
    ∀ (k : Nat) (a b s₀ i₀ : Int),
      denote (.forN k productBody) (productEnv a b s₀ i₀)
        = (some (), productEnv a b (s₀ * productFrom i₀ k) (i₀ + k)) := by
  intro k
  induction k with
  | zero =>
      intro a b s₀ i₀
      show (some (), productEnv a b s₀ i₀)
        = (some (), productEnv a b
            (s₀ * productFrom i₀ 0) (i₀ + ((0 : Nat) : Int)))
      have h1 : s₀ * productFrom i₀ 0 = s₀ := by show s₀ * 1 = s₀; simp
      have h2 : i₀ + ((0 : Nat) : Int) = i₀ := by simp
      rw [h1, h2]
  | succ k ih =>
      intro a b s₀ i₀
      rw [denote_forN_succ]
      show (match denote productBody (productEnv a b s₀ i₀) with
            | (none, ρ')   => (none, ρ')
            | (some _, ρ') => denote (.forN k productBody) ρ')
          = (some (), productEnv a b
              (s₀ * productFrom i₀ (k + 1)) (i₀ + (k + 1 : Nat)))
      rw [denote_productBody]
      show denote (.forN k productBody)
              (productEnv a b (s₀ * i₀) (i₀ + 1)) = _
      rw [ih a b (s₀ * i₀) (i₀ + 1)]
      have h1 : s₀ * productFrom i₀ (k + 1)
                  = (s₀ * i₀) * productFrom (i₀ + 1) k := by
        show s₀ * (i₀ * productFrom (i₀ + 1) k) = _
        rw [← Int.mul_assoc]
      have h2 : i₀ + ((k + 1 : Nat) : Int) = (i₀ + 1) + (k : Nat) := by
        have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by push_cast; rfl
        omega
      rw [h1, h2]

/-- **Marquee product identity.** From an env binding `"a" ↦ a, "b" ↦ b`,
the denotation of `productProg (b - a).toNat` terminates with
`"s" ↦ rangeProd a b` and `"i" ↦ a + (b - a).toNat`. -/
theorem denote_productProg (a b : Int) :
    denote (productProg (b - a).toNat)
        ((Env.empty.set "a" (.int a)).set "b" (.int b))
      = (some (), productEnv a b (rangeProd a b) (a + ((b - a).toNat : Int))) := by
  show denote (.seq (.assign "s" (.val (.int 1)))
              (.seq (.assign "i" (.var "a"))
                    (.forN (b - a).toNat productBody)))
              ((Env.empty.set "a" (.int a)).set "b" (.int b)) = _
  -- Step `s := 1`.
  show (match denote (.assign "s" (.val (.int 1)))
              ((Env.empty.set "a" (.int a)).set "b" (.int b)) with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote _ ρ') = _
  show denote (.seq (.assign "i" (.var "a"))
                    (.forN (b - a).toNat productBody))
        (((Env.empty.set "a" (.int a)).set "b" (.int b)).set
          "s" (.int 1)) = _
  -- Step `i := a` (reads `"a"` from the env).
  have ha :
      (((Env.empty.set "a" (.int a)).set "b" (.int b)).set
        "s" (.int 1)) "a" = some (.int a) := by
    simp [Env.set]
  show (match denote (.assign "i" (.var "a"))
              (((Env.empty.set "a" (.int a)).set "b" (.int b)).set
                "s" (.int 1)) with
        | (none, ρ')   => (none, ρ')
        | (some _, ρ') => denote (.forN (b - a).toNat productBody) ρ') = _
  simp only [denote, Expr.eval, ha]
  show denote (.forN (b - a).toNat productBody)
        ((((Env.empty.set "a" (.int a)).set "b" (.int b)).set
            "s" (.int 1)).set "i" (.int a)) = _
  show denote (.forN (b - a).toNat productBody) (productEnv a b 1 a) = _
  rw [denote_forN_productBody_general (b - a).toNat a b 1 a]
  congr 1
  show productEnv a b (1 * productFrom a (b - a).toNat) (a + ((b - a).toNat : Int))
    = productEnv a b (rangeProd a b) (a + ((b - a).toNat : Int))
  have h1 : 1 * productFrom a (b - a).toNat = rangeProd a b := by
    show 1 * rangeProd a b = rangeProd a b
    rw [Int.one_mul]
  rw [h1]

/-! ## Non-recursive procedure calls (inline)

We add procedure calls as a *smart constructor* over the existing
`PureStmt` grammar: a `pcall` is a sequence of parameter-binding
assignments, followed by the procedure body, followed by an assignment
of the caller's "out" variable from a return-value expression evaluated
in the post-body environment.

This is strictly non-recursive — the body is a fixed `PureStmt` value
provided at construction time and cannot reference the call itself —
and inherits `embed`, `denote_sound`, `denote_complete`,
`Machine.denote_iff`, and all related theorems automatically through
the existing `seq`/`assign` cases. -/

/-- Bind a list of `(formal, actualExpr)` pairs by emitting a chain of
`.assign formal actualExpr` statements. Each binding sees the previous
ones in scope (left-to-right). -/
def assignAll : List (Name × Expr) → PureStmt
  | []             => .skip
  | (x, e) :: rest => .seq (.assign x e) (assignAll rest)

/-- **Non-recursive inline procedure call.** Bind parameters from
caller-side expressions, run the body, then write `retExpr` (evaluated
in the post-body environment) into the caller's `out` variable. -/
def pcall (params : List (Name × Expr)) (body : PureStmt)
    (out : Name) (retExpr : Expr) : PureStmt :=
  .seq (assignAll params) (.seq body (.assign out retExpr))

/-- Denotational unfolding of `pcall`. -/
theorem denote_pcall (params : List (Name × Expr)) (body : PureStmt)
    (out : Name) (retExpr : Expr) (ρ : Env) :
    denote (pcall params body out retExpr) ρ =
      (match denote (assignAll params) ρ with
       | (none, ρ') => (none, ρ')
       | (some _, ρ₁) =>
         match denote body ρ₁ with
         | (none, ρ') => (none, ρ')
         | (some _, ρ₂) =>
           match Expr.eval ρ₂ retExpr with
           | none   => (none, ρ₂)
           | some v => (some (), ρ₂.set out v)) := by
  show (match denote (assignAll params) ρ with
        | (none, ρ') => (none, ρ')
        | (some _, ρ₁) => denote (.seq body (.assign out retExpr)) ρ₁) =
      (match denote (assignAll params) ρ with
       | (none, ρ') => (none, ρ')
       | (some _, ρ₁) =>
         match denote body ρ₁ with
         | (none, ρ') => (none, ρ')
         | (some _, ρ₂) =>
           match Expr.eval ρ₂ retExpr with
           | none   => (none, ρ₂)
           | some v => (some (), ρ₂.set out v))
  rcases h1 : denote (assignAll params) ρ with ⟨o1, ρ1⟩
  cases o1 with
  | none => rfl
  | some =>
      show denote (.seq body (.assign out retExpr)) ρ1 =
        (match denote body ρ1 with
         | (none, ρ') => (none, ρ')
         | (some _, ρ₂) =>
           match Expr.eval ρ₂ retExpr with
           | none   => (none, ρ₂)
           | some v => (some (), ρ₂.set out v))
      show (match denote body ρ1 with
            | (none, ρ') => (none, ρ')
            | (some _, ρ') => denote (.assign out retExpr) ρ') = _
      rcases h2 : denote body ρ1 with ⟨o2, ρ2⟩
      cases o2 with
      | none => rfl
      | some => rfl

/-! ## Pure helpers: bridging denotational reasoning to `Machine.safe`

A `PureHelper` packages a `PureStmt` body with a *return expression* read
off the post-state. The compiled `main := embed body ; ret retExpr`
actually fires a top-level `return`, so the operational machine
terminates with `Thread.toValue = some v` for a non-trivial `v` — and a
value-postcondition `φ : Val → Prop` is no longer collapsed to
`φ Val.unit`. -/

/-- Body plus a final return expression. -/
structure PureHelper where
  body : PureStmt
  ret  : Expr

/-- The helper's compiled `main`: run the body, then return `ret`. -/
def PureHelper.main (h : PureHelper) : Stmt :=
  .seq (embed h.body) (.ret h.ret)

/-- Package a helper as a self-contained program: no procedures. -/
def programOfHelper (h : PureHelper) : Program where
  procs := noProcs
  main  := h.main

/-- Denotation lifted to a `Val`: run the body, then read `ret` in the
post-environment. `none` propagates a stuck body or an ill-typed `ret`. -/
def denoteHelper (h : PureHelper) (ρ₀ : Env) : Option Val :=
  match denote h.body ρ₀ with
  | (some _, ρ') => Expr.eval ρ' h.ret
  | (none,   _)  => none

/-- Monadic analogue of `denoteHelper`. Same shape over `denoteM`. -/
def denoteHelperM (h : PureHelper) (ρ₀ : Env) : Option Val :=
  match denoteM h.body ρ₀ with
  | (some _, ρ') => Expr.eval ρ' h.ret
  | (none,   _)  => none

end Agar

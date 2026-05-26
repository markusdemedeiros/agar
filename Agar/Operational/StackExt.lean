module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics

@[expose] public section

/-! # Stack-extension and `tstep`

`stackExt t extra` appends `extra` at the bottom of `t.stack`. The
key operational lemma `tstep_stackExt_preserve` says: every successful
`tstep` on `t` that is **not** `.ret e` with empty `t.stack` lifts to
a `tstep` on `stackExt t extra` whose post-state has `extra` appended.

The exceptional `.ret`-empty case is the divergence and is handled at
the Iris level via the value disjunct.
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

theorem tstep_stackExt_preserve
    (procs : Name → Option Proc) (chosen : Option Loc) (m : Mem)
    (t : Thread) (extra : List Frame)
    (m' : Mem) (t' : Thread) (sp : Option Thread)
    (h_step : tstep procs chosen m t = some (m', t', sp))
    (h_not_top_ret : ∀ e, t.stmt = .ret e → t.stack ≠ []) :
    tstep procs chosen m (stackExt t extra)
      = some (m', stackExt t' extra, sp) := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  simp only [stackExt] at h_not_top_ret ⊢
  match chosen, stmt with
  -- chosen = some _ : only .alloc is reachable; rule out the rest
  | some _, .skip       => simp [tstep] at h_step
  | some _, .seq _ _    => simp [tstep] at h_step
  | some _, .assign _ _ => simp [tstep] at h_step
  | some _, .load _ _   => simp [tstep] at h_step
  | some _, .store _ _  => simp [tstep] at h_step
  | some _, .free _     => simp [tstep] at h_step
  | some _, .cas _ _ _ _ => simp [tstep] at h_step
  | some _, .ite _ _ _  => simp [tstep] at h_step
  | some _, .whileDo _ _ => simp [tstep] at h_step
  | some _, .call _ _ _ => simp [tstep] at h_step
  | some _, .ret _      => simp [tstep] at h_step
  | some _, .fork _ _   => simp [tstep] at h_step
  | none, .alloc _ _    => simp [tstep] at h_step
  -- alloc with chosen = some l
  | some _, .alloc x e =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · cases h_step
      · split at h_step
        · cases h_step
        · cases h_step; rfl
  -- pure cases with no inner match
  | none, .seq _ _ =>
      simp only [tstep] at h_step ⊢; cases h_step; rfl
  | none, .whileDo _ _ =>
      simp only [tstep] at h_step ⊢; cases h_step; rfl
  | none, .assign _ _ =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · cases h_step
      · cases h_step; rfl
  | none, .load _ _ =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · split at h_step
        · cases h_step; rfl
        · cases h_step
      · cases h_step
  | none, .store _ _ =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · split at h_step
        · cases h_step; rfl
        · cases h_step
      · cases h_step
  | none, .free _ =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · split at h_step
        · cases h_step; rfl
        · cases h_step
      · cases h_step
  | none, .cas _ _ _ _ =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · split at h_step
        · cases h_step
        · split at h_step
          · split at h_step
            · cases h_step; simp_all
            · cases h_step
          · cases h_step; simp_all
      · cases h_step
  | none, .ite _ _ _ =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · cases h_step; rfl
      · cases h_step; rfl
      · cases h_step
  | none, .call x f args =>
      simp only [tstep, callFrom] at h_step ⊢
      split at h_step
      · split at h_step
        · cases h_step; simp_all
        · cases h_step
      · cases h_step
  | none, .fork f args =>
      simp only [tstep] at h_step ⊢
      split at h_step
      · split at h_step
        · cases h_step; simp_all
        · cases h_step
      · cases h_step
  | none, .ret e =>
      have hstk : stack ≠ [] := h_not_top_ret e rfl
      simp only [tstep] at h_step ⊢
      split at h_step
      · cases h_step
      · simp only [doReturn] at h_step ⊢
        match stack, hstk with
        | f :: rest, _ =>
            simp only [List.cons_append] at h_step ⊢
            cases h_cont : f.cont with
            | nil => simp only [h_cont] at h_step ⊢; cases h_step; rfl
            | cons _ _ => simp only [h_cont] at h_step ⊢; cases h_step; rfl
  | none, .skip =>
      simp only [tstep] at h_step ⊢
      match cont, stack with
      | s :: rest, _ =>
          cases h_step; rfl
      | [], [] =>
          cases h_step
      | [], f :: rest =>
          simp only [doReturn] at h_step ⊢
          simp only [List.cons_append] at h_step ⊢
          cases h_cont : f.cont with
          | nil => simp only [h_cont] at h_step ⊢; cases h_step; rfl
          | cons _ _ => simp only [h_cont] at h_step ⊢; cases h_step; rfl

/-- **Inversion** of `tstep_stackExt_preserve`. If `stackExt t extra` steps
to `(m', t'', sp)` and `t` is neither terminated nor `.ret`-with-empty-stack,
then the step lifts back to a step on `t` whose post is `stackExt t0 extra`.

Proven by exhibiting a `t0` from a forward step on `t` (constructed by
case analysis), invoking `tstep_stackExt_preserve` to get a canonical
form `some (m', stackExt t0 extra, sp)` for the extended step, and then
chaining with the hypothesis via determinism. -/
theorem tstep_stackExt_invert
    (procs : Name → Option Proc) (chosen : Option Loc) (m : Mem)
    (t : Thread) (extra : List Frame)
    (m' : Mem) (t'' : Thread) (sp : Option Thread)
    (h_step : tstep procs chosen m (stackExt t extra) = some (m', t'', sp))
    (h_not_top_ret : ∀ e, t.stmt = .ret e → t.stack ≠ [])
    (h_not_term : t.terminated = false) :
    ∃ t0, t'' = stackExt t0 extra ∧
          tstep procs chosen m t = some (m', t0, sp) := by
  match h_t : tstep procs chosen m t with
  | some (m1, t0, sp1) =>
      have h_pres := tstep_stackExt_preserve procs chosen m t extra m1 t0 sp1
        h_t h_not_top_ret
      have h_eq : some (m', t'', sp) = some (m1, stackExt t0 extra, sp1) :=
        h_step.symm.trans h_pres
      simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
      refine ⟨t0, h_eq.2.1, ?_⟩
      rw [h_eq.1, h_eq.2.2]
  | none =>
      exfalso
      obtain ⟨stmt, cont, env, stack, result⟩ := t
      simp only [stackExt] at h_step
      simp only at h_not_top_ret
      -- For stack-independent cases (everything except .skip-empty-cont
      -- and .ret), `tstep` on `t` and on `stackExt t extra` agree on
      -- success/failure, so `h_t = none ∧ h_step = some` is contradictory
      -- — checked by `simp_all` after fully unfolding tstep.
      match chosen, stmt with
      | some _, .skip => simp [tstep] at h_step
      | some _, .seq _ _ => simp [tstep] at h_step
      | some _, .assign _ _ => simp [tstep] at h_step
      | some _, .load _ _ => simp [tstep] at h_step
      | some _, .store _ _ => simp [tstep] at h_step
      | some _, .free _ => simp [tstep] at h_step
      | some _, .cas _ _ _ _ => simp [tstep] at h_step
      | some _, .ite _ _ _ => simp [tstep] at h_step
      | some _, .whileDo _ _ => simp [tstep] at h_step
      | some _, .call _ _ _ => simp [tstep] at h_step
      | some _, .ret _ => simp [tstep] at h_step
      | some _, .fork _ _ => simp [tstep] at h_step
      | none, .alloc _ _ => simp [tstep] at h_step
      | some _, .alloc x e =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all)
      | none, .seq _ _ => simp [tstep] at h_t
      | none, .whileDo _ _ => simp [tstep] at h_t
      | none, .assign _ _ =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all
      | none, .load _ _ =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all)
      | none, .store _ _ =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all)
      | none, .free _ =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all)
      | none, .cas _ _ _ _ =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all <;>
              (split at h_t <;> split at h_step <;> simp_all <;>
                (split at h_t <;> split at h_step <;> simp_all)))
      | none, .ite _ _ _ =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all
      | none, .call x f args =>
          simp only [tstep, callFrom] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all)
      | none, .fork f args =>
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (split at h_t <;> split at h_step <;> simp_all)
      | none, .ret e =>
          have hstk : stack ≠ [] := h_not_top_ret e rfl
          simp only [tstep] at h_t h_step
          split at h_t <;> split at h_step <;> simp_all <;>
            (cases stack
             · exact hstk rfl
             · simp [doReturn] at h_t)
      | none, .skip =>
          simp only [tstep] at h_t h_step
          match cont, stack with
          | _ :: _, _ => cases h_t
          | [], [] => exact absurd h_not_term (by simp [Thread.terminated])
          | [], _ :: _ => cases h_t

end BodyTraj
end Agar

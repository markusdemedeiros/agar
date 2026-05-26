module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Operational.Composition
public import Agar.Operational.StackExt
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap

@[expose] public section

/-! # Stack-push Iris lemma

`wp_stack_push`: a wp on `t` whose post fires a continuation wp at the
post-doReturn state lifts to a wp on `stackExt t (frame :: rest)`.

This is the Iris-level counterpart of `tstep_stackExt_preserve`. The
proof is by Löb induction; case analysis splits on:

* HW value disjunct (`t.toValue = some v`): the extended thread steps
  exactly one `.skip` fall-through that fires `doReturn`, landing at
  `postDoReturnThread frame rest v`.
* HW step disjunct: handled by lifting each step on the extended thread
  back to a step on `t` (via `tstep_stackExt_preserve`), then applying
  the IH under the `▷`. The exceptional `.ret e` / empty-stack case is
  handled in line: the extended thread steps to `postDoReturn` while
  `t` itself steps to a terminated thread; we re-enter the value
  disjunct of the inner wp.
-/

namespace Agar
open Agar.Logic
namespace BodyTraj

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

section
variable {GF : BundledGFunctors.{0,0,0}}
variable {F : Type _} [UFraction F]
variable [InvGS_gen false GF] [AgarG GF F]

theorem stackExt_terminated_false (t : Thread) (frame : Frame) (rest : List Frame) :
    (stackExt t (frame :: rest)).terminated = false := by
  unfold Thread.terminated stackExt
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  cases stmt <;> cases cont <;> cases stack <;> rfl

theorem toValue_some_inv {t : Thread} {v : Val} (h : t.toValue = some v) :
    t.stmt = .skip ∧ t.cont = [] ∧ t.stack = [] ∧ v = t.result.getD .unit := by
  unfold Thread.toValue at h
  split at h <;> simp_all

/-- Step on a terminated `stackExt` thread: lands at `postDoReturnThread`. -/
theorem tstep_stackExt_terminated
    (procs : Name → Option Proc) (m : Mem)
    (env : Env) (result : Option Val) (frame : Frame) (rest : List Frame)
    (v : Val) (hv : v = result.getD .unit) :
    tstep procs none m (stackExt ⟨.skip, [], env, [], result⟩ (frame :: rest))
      = some (m, postDoReturnThread frame rest v, none) := by
  subst hv
  simp only [tstep, stackExt, doReturn, postDoReturnThread, List.nil_append]
  cases frame.cont <;> rfl

/-- Determinism for the terminated-stackExt step: any `tstep` from this
state lands at `postDoReturnThread`. -/
theorem tstep_stackExt_terminated_det
    (procs : Name → Option Proc) (m : Mem)
    (env : Env) (result : Option Val) (frame : Frame) (rest : List Frame)
    (v : Val) (hv : v = result.getD .unit)
    {chosen : Option Loc} {m'' : Mem} {t'' : Thread} {sp : Option Thread}
    (h : tstep procs chosen m
          (stackExt ⟨.skip, [], env, [], result⟩ (frame :: rest))
          = some (m'', t'', sp)) :
    m'' = m ∧ t'' = postDoReturnThread frame rest v ∧ sp = none := by
  cases chosen with
  | some _ => simp [tstep, stackExt] at h
  | none =>
      rw [tstep_stackExt_terminated procs m env result frame rest v hv] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- **Stack-push wp lemma: callee-frame embedding for `wp`.**

This is the Iris-level analogue of "extending a safe thread's stack
preserves safety, threading the saved frame's continuation through to
the post." Concretely: take a wp on `t` (where `t` thinks it's running
standalone with an empty stack) whose post says "when `t` terminates
with value `v`, the rest of the trace at `postDoReturnThread frame rest v`
is itself safe," and produce a wp on `stackExt t (frame :: rest)` (the
same thread but with a caller frame embedded at the bottom of its stack).

**Where it sits in the Route A bridge.** This is step 3 of
`wp_callee_routeA`. The pipeline so far:
* `completeness_open` gives a wp on the helper running standalone
  (empty stack, the helper's `.ret` terminates the thread).
* `wp_wand` reshapes the post from the operational spec into the
  caller's continuation wp.
* **`wp_stack_push` (this lemma)** then embeds the helper into a frame:
  the helper's `.ret` no longer terminates — it `doReturn`s into the
  caller's continuation, which is exactly what `wp_call` leaves behind
  as a residual.

**Proof: Löb induction over `∀ t`.** Two cases off `wp_unfold`:

* *Value disjunct* (`t.toValue = some v`): the extended thread fires
  one `.skip` fall-through `doReturn` step landing at
  `postDoReturnThread`, and the caller's post fires.
* *Step disjunct*: each step on the extended thread is either lifted
  from a step on `t` (via `tstep_stackExt_preserve`) or is the
  exceptional `.ret e`-empty case in which the step lands directly at
  `postDoReturnThread`. In the `.ret`-empty case, `t`'s own step
  terminates `t`, and the IH applied to that terminated thread
  re-enters the value branch. The `.ret`-with-empty-stack wrinkle
  (HYPOTHESIS.md §8.5) is handled inline rather than via a separate
  operational coupling lemma. -/
theorem wp_stack_push
    (procs : Name → Option Proc) (fp : IProp GF)
    (frame : Frame) (rest : List Frame) (Φ : Val → IProp GF) (t : Thread) :
    wp procs fp ⊤ t
        (fun v => wp procs fp ⊤ (postDoReturnThread frame rest v) Φ)
    ⊢ wp procs fp ⊤ (stackExt t (frame :: rest)) Φ := by
  suffices key : (True : IProp GF) ⊢ iprop(∀ (t' : Thread),
      wp procs fp ⊤ t'
        (fun v => wp procs fp ⊤ (postDoReturnThread frame rest v) Φ) -∗
      wp procs fp ⊤ (stackExt t' (frame :: rest)) Φ) by
    exact BI.wand_entails
      (BI.true_intro.trans (key.trans (BI.forall_elim t)))
  apply BILoeb.loeb_weak
  iintro IH
  iintro %t' HW
  ihave HW' :=
    (equiv_iff.mp (wp_unfold procs fp ⊤ t' _)).mp $$ HW
  iapply (equiv_iff.mp
    (wp_unfold procs fp ⊤ (stackExt t' (frame :: rest)) Φ)).mpr
  iright
  isplitr
  · ipure_intro; exact stackExt_terminated_false t' frame rest
  iintro %m HS
  icases HW' with ⟨⟨%v, %htv, HΦ⟩ | ⟨%hnt, Hsteps⟩⟩
  · -- Value disjunct: t' terminated, single doReturn step.
    obtain ⟨hstm, hcont, hstk, hvres⟩ := toValue_some_inv htv
    obtain ⟨stmt, cont, env, stack, result⟩ := t'
    simp only at hstm hcont hstk
    subst hstm; subst hcont; subst hstk
    iapply fupd_mask_intro empty_subset
    iintro Hclose
    isplitr
    · ipure_intro
      refine ⟨m, postDoReturnThread frame rest v, none, none, ?_⟩
      exact tstep_stackExt_terminated procs m env result frame rest v hvres
    iintro !> %m'' %t'' %sp %hstep
    obtain ⟨chosen, hstep'⟩ := hstep
    obtain ⟨rfl, rfl, rfl⟩ :=
      tstep_stackExt_terminated_det procs m env result frame rest v hvres hstep'
    imod Hclose
    imod HΦ
    imodintro
    iframe HS HΦ
    iintro %ts %hsp; cases hsp
  · -- Step disjunct.
    -- Consume Hsteps first while we're still under |={⊤,∅}=>.
    imod Hsteps $$ HS with ⟨%hred, Hsteps'⟩
    -- Now goal: ⌜reducible (stackExt t')⌝ ∗ ▷ (∀ ... ={∅,⊤}=∗ ...) [no outer fupd].
    -- Re-open the fupd to ∅ via fupd_mask_intro: we land back at
    -- `|={⊤,∅}=> emp -∗ ⌜...⌝ ∗ ▷ ...` minus the inner emp via Hclose.
    -- Actually the goal here is the body of the outer fupd: a
    -- `⌜hred (stackExt t')⌝ ∗ ▷ (∀ ... ={∅,⊤}=∗ ...)`. Provide it directly.
    by_cases h_ret_empty : ∃ e, t'.stmt = .ret e ∧ t'.stack = []
    · -- Exceptional .ret-empty case.
      obtain ⟨eret, hstm, hstk⟩ := h_ret_empty
      obtain ⟨stmt, cont, env, stack, result⟩ := t'
      simp only at hstm hstk; subst hstm; subst hstk
      have ⟨v_eret, hv_eret⟩ : ∃ v, Expr.eval env eret = some v := by
        obtain ⟨m1, t1, sp1, chosen1, hstep1⟩ := hred
        cases chosen1 with
        | some _ => simp [tstep] at hstep1
        | none =>
            simp only [tstep] at hstep1
            split at hstep1
            · exact absurd hstep1 (by simp)
            · rename_i v heval
              exact ⟨v, heval⟩
      -- Build the extended-step witness.
      have hstep_ext_some :
          ∀ ch, tstep procs ch m (stackExt ⟨.ret eret, cont, env, [], result⟩
            (frame :: rest)) =
            if ch.isSome then none
            else some (m, postDoReturnThread frame rest v_eret, none) := by
        intro ch
        cases ch with
        | some _ => simp [tstep, stackExt]
        | none =>
            simp only [tstep, stackExt, hv_eret, doReturn,
              postDoReturnThread, List.nil_append, Option.isSome_none,
              Bool.false_eq_true, ↓reduceIte]
            cases frame.cont <;> rfl
      have h_stackExt_step :
          tstep procs none m (stackExt ⟨.ret eret, cont, env, [], result⟩
            (frame :: rest)) = some (m, postDoReturnThread frame rest v_eret, none) := by
        have := hstep_ext_some none
        simpa using this
      iapply fupd_mask_intro empty_subset
      iintro Hclose
      isplitr
      · ipure_intro
        exact ⟨m, postDoReturnThread frame rest v_eret, none, none, h_stackExt_step⟩
      iintro !> %m'' %t'' %sp %hstep_ext
      obtain ⟨chosen, hstep_ext'⟩ := hstep_ext
      have hch : chosen = none := by
        cases chosen with
        | some _ =>
            rw [hstep_ext_some] at hstep_ext'
            simp at hstep_ext'
        | none => rfl
      subst hch
      rw [hstep_ext_some] at hstep_ext'
      simp at hstep_ext'
      obtain ⟨hm_eq, ht_eq, hsp_eq⟩ := hstep_ext'
      subst hm_eq; subst ht_eq; subst hsp_eq
      -- Build the corresponding step on t' = (.ret eret, cont, env, [], result).
      have hstep_t' :
          thread_step procs m ⟨.ret eret, cont, env, [], result⟩
            m ⟨.skip, [], env, [], some v_eret⟩ none := by
        refine ⟨none, ?_⟩
        simp only [tstep, hv_eret, doReturn]
      imod Hclose
      imod Hsteps' $$ %m %(⟨.skip, [], env, [], some v_eret⟩ : Thread) %(none : Option Thread) %hstep_t' with ⟨HSm, HWt'', _⟩
      imodintro
      iframe HSm
      isplitl [HWt'']
      · ihave HWt''_unf :=
          (equiv_iff.mp (wp_unfold procs fp ⊤
            ⟨.skip, [], env, [], some v_eret⟩ _)).mp $$ HWt''
        icases HWt''_unf with ⟨⟨%v', %htv', HΦ'⟩ | ⟨%hnt', _⟩⟩
        · have hveq : v' = v_eret := by
            unfold Thread.toValue at htv'; simp_all
          subst hveq
          iapply (fupd_wp procs fp _ Φ)
          iexact HΦ'
        · exfalso
          unfold Thread.terminated at hnt'
          simp at hnt'
      iintro %ts %hsp; cases hsp
    · -- Non-exceptional: tstep_stackExt_invert applies.
      have h_not_top_ret : ∀ e, t'.stmt = .ret e → t'.stack ≠ [] := by
        intro e hret_e hstk_e
        exact h_ret_empty ⟨e, hret_e, hstk_e⟩
      iapply fupd_mask_intro empty_subset
      iintro Hclose
      isplitr
      · ipure_intro
        obtain ⟨m1, t1, sp1, chosen1, hstep1⟩ := hred
        refine ⟨m1, stackExt t1 (frame :: rest), sp1, chosen1, ?_⟩
        exact tstep_stackExt_preserve procs chosen1 m t' (frame :: rest)
          m1 t1 sp1 hstep1 h_not_top_ret
      iintro !> %m'' %t'' %sp %hstep_ext
      obtain ⟨chosen, hstep_ext'⟩ := hstep_ext
      have ⟨t0, ht''_eq, hstep_t0⟩ :=
        tstep_stackExt_invert procs chosen m t' (frame :: rest) m'' t'' sp
          hstep_ext' h_not_top_ret hnt
      subst ht''_eq
      have hstep_t0' : thread_step procs m t' m'' t0 sp := ⟨chosen, hstep_t0⟩
      imod Hclose
      imod Hsteps' $$ %m'' %t0 %sp %hstep_t0' with ⟨HSm', HWt0, HFork⟩
      imodintro
      iframe HSm' HFork
      iapply IH $$ %t0 HWt0

end
end BodyTraj
end Agar

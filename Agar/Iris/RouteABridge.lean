module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Denotational
public import Agar.Operational.Composition
public import Agar.Operational.StackExt
public import Agar.Operational.StrictHelper
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Completeness
public import Agar.Iris.StackPush

@[expose] public section

/-! # `RouteABridge` — generic, example-independent Route A bridge

The `wp_callee_routeA` theorem in `Agar/Examples/ExternalSolver.lean`
was originally written against the `rangeProdComposite3` composite and
the `helper_post_at` postcondition specific to that example. But its
body uses the composite **only** through three example-agnostic inputs:

1. `prog.heapFree`,
2. `(helper_init).heapFree`,
3. `Machine.SafeTp prog ⟨σ, [helper_init]⟩ φ`.

Everything else — `completeness_open`, `wp_wand`, `wp_stack_push` — is
generic Iris machinery. So we lift the bridge into a generic statement
parameterized over the composite `prog`, an arbitrary helper-init
thread `helper_init`, and an arbitrary pure post `φ`.

A new example wanting Route A dispatch supplies:
- its composite program,
- its helper's init thread,
- its helper's pure post,
- proofs of the three obligations above,
and gets back the same bridge shape `wp_callee_routeA` produced before.

The original `wp_callee_routeA` in `ExternalSolver.lean` is now a thin
specialization of this theorem (kept as a named restatement so external
consumers find it at the expected path). -/

namespace Agar.Logic
open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarG GF F] [InvGS_gen false GF]

/-! ## `wp` procs-irrelevance for strict helpers

The key observation that lets us bridge to a composite with heap-using
worker procs: a `StrictHelperThread` (no `.call`, no `.fork`, empty
stack) takes the same `tstep` under any procs table. So its `wp` is
also procs-irrelevant. We can therefore obtain a wp against `noProcs`
(which is trivially heap-free, so `completeness_open`'s procs-heap-free
hypothesis is vacuous), and then transport to a wp against the real
composite's procs table.

This is the Iris analogue of `SafeTp_procs_irrel_of_strict` on the
operational side. -/

/-- For a strict-helper thread, `tstep` yields the same result under
any procs table, and the post-step thread is still strict. We package
both facts to use inside the Löb step. -/
private theorem strict_tstep_irrel {t : Thread}
    (he : StrictHelperThread t)
    (procs1 procs2 : Name → Option Proc)
    (chosen : Option Loc) (m m' : Mem) (t' : Thread) (sp : Option Thread)
    (h : tstep procs1 chosen m t = some (m', t', sp)) :
    tstep procs2 chosen m t = some (m', t', sp) := by
  rw [tstep_strict_procs_irrel he procs2 procs1]; exact h

/-- Strict-helper threads' tsteps don't depend on the procs table —
so their `wp` doesn't either. We prove the entailment in one direction;
the other follows by symmetry. -/
theorem wp_procs_irrel_strict {t : Thread}
    (he : StrictHelperThread t)
    (procs1 procs2 : Name → Option Proc) (fork_post : IProp GF)
    (E : CoPset) (Φ : Val → IProp GF) :
    wp procs1 fork_post E t Φ ⊢ wp procs2 fork_post E t Φ := by
  suffices key : ⊢ (iprop(∀ (t' : Thread),
      (⌜StrictHelperThread t'⌝ →
        (wp procs1 fork_post E t' Φ -∗
          wp procs2 fork_post E t' Φ))) : IProp GF) by
    have s1 := key.trans (BI.forall_elim t)
    have hpure : (True : IProp GF) ⊢ iprop(⌜StrictHelperThread t⌝) :=
      BI.pure_intro he
    have s2 : (True : IProp GF) ⊢ iprop(
        wp procs1 fork_post E t Φ -∗
          wp procs2 fork_post E t Φ) :=
      (BI.and_intro s1 hpure).trans BI.imp_elim_l
    refine BI.wand_entails ?_
    exact s2
  iloeb as IH
  iintro %t' %he' HW
  ihave HW' :=
    (equiv_iff.mp (wp_unfold procs1 fork_post E t' Φ)).mp $$ HW
  iapply (equiv_iff.mp (wp_unfold procs2 fork_post E t' Φ)).mpr
  icases HW' with ⟨⟨%v, %hterm, HΦ⟩ | ⟨%hnt, Hsteps⟩⟩
  · ileft
    iexists v
    isplitr
    · ipure_intro; exact hterm
    · iexact HΦ
  · iright
    isplitr
    · ipure_intro; exact hnt
    iintro %m HS
    imod Hsteps $$ HS with ⟨%hred, HsRest⟩
    -- Reducibility under procs2 follows from procs-irrelevance.
    have hred2 : thread_reducible procs2 m t' := by
      obtain ⟨m'', t'', sp, chosen, hstep⟩ := hred
      exact ⟨m'', t'', sp, chosen,
        strict_tstep_irrel he' procs1 procs2 chosen m m'' t'' sp hstep⟩
    iapply fupd_mask_intro empty_subset
    iintro Hclose
    isplitr
    · ipure_intro; exact hred2
    iintro !> %m' %t'' %sp %hstep2
    imod Hclose
    -- Extract the chosen from procs2-step, then lift back to procs1.
    obtain ⟨chosen, hstep2_t⟩ := hstep2
    have hstep1_t : tstep procs1 chosen m t' = some (m', t'', sp) :=
      strict_tstep_irrel he' procs2 procs1 chosen m m' t'' sp hstep2_t
    -- Structural characterization: sp = none, m' = m, t'' strict.
    obtain ⟨_, hmm, hspn, he''⟩ := tstep_strict_characterise he' hstep1_t
    subst hmm
    subst hspn
    have hstep1 : thread_step procs1 m' t' m' t'' none := ⟨chosen, hstep1_t⟩
    imod HsRest $$ %m' %t'' %(none : Option Thread) %hstep1 with ⟨HSm', HWt', _HFork⟩
    imodintro
    iframe HSm'
    isplitl [HWt']
    · ihave IH_inst := IH $$ %t''
      iapply IH_inst
      · ipure_intro; exact he''
      · iexact HWt'
    · iintro %ts %hts; cases hts

end Agar.Logic

namespace Agar.Logic
open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarG GF F] [InvGS_gen false GF]

/-- Sentinel program used internally by the bridge: empty procs table,
trivial main. Heap-free by construction. -/
private def noProcsProg : Program where
  procs := noProcs
  main  := .skip

private theorem noProcsProg_procs_heapFree :
    ∀ name proc, noProcsProg.procs name = some proc → proc.heapFree := by
  intro name proc h
  simp [noProcsProg, noProcs] at h

/-- **Generic Route A bridge.** Given a composite program `prog`, a
strict-helper init thread `helper_init`, and a pure post `φ`, together
with a `SafeTp` witness for the helper under the composite's procs,
produce the wp at a `wp_call`-shaped callee-frame thread that runs the
helper with the caller's frame pushed onto its stack.

**No heap-freeness obligation on the composite's procs.** The bridge
internally invokes `completeness_open` against an empty procs table
(`noProcs`, trivially heap-free), then transports the resulting wp to
`prog.procs` via `wp_procs_irrel_strict`. Worker procs in the composite
may freely use heap operations.

This is exactly the residual that `wp_call` leaves behind — the
"caller obligation" parameter `Hcont` is the wp-continuation the
caller already has in hand.

`fork_post := iprop(True : IProp GF)` is uniform across the whole
Route A pipeline (it's what `completeness_open` produces); the caller
threads the same value at every `wp_fork` / `wp_call` site and at the
`wp_safe_bupd` existential. -/
theorem wp_callee_routeA_generic
    (prog : Program)
    (helper_init : Thread)
    (helper_init_HF : helper_init.heapFree)
    (helper_init_strict : StrictHelperThread helper_init)
    (helper_init_stack_nil : helper_init.stack = [])
    (φ : Val → Prop)
    (helper_safeTp : ∀ σ, Machine.SafeTp prog ⟨σ, [helper_init]⟩ φ)
    (callerFrame : Frame)
    (Φ : Val → IProp GF) :
    (∀ v, iprop(⌜φ v⌝ -∗
        wp prog.procs (iprop(True : IProp GF)) ⊤
          (BodyTraj.postDoReturnThread callerFrame [] v) Φ))
    ⊢ |={⊤}=> wp prog.procs (iprop(True : IProp GF)) ⊤
        ⟨helper_init.stmt, helper_init.cont, helper_init.env,
         callerFrame :: helper_init.stack, helper_init.result⟩ Φ := by
  iintro Hwand
  -- Convert helper safety under `prog` to safety under `noProcsProg`
  -- via the operational procs-irrelevance lift.
  have helper_safeTp_noProcs :
      ∀ σ, Machine.SafeTp noProcsProg ⟨σ, [helper_init]⟩ φ := by
    intro σ
    exact SafeTp_procs_irrel_of_strict (prog1 := prog) (prog2 := noProcsProg)
      helper_init_strict (helper_safeTp σ)
  -- 1. Standalone wp from completeness_open over noProcsProg.
  ihave Hopen :=
    completeness_open (prog := noProcsProg) (GF := GF) (F := F)
      (φ := φ)
      noProcsProg_procs_heapFree helper_init helper_init_HF
      helper_safeTp_noProcs
  imod Hopen with Hstandalone_np
  -- Transport across procs tables via wp_procs_irrel_strict.
  ihave Hstandalone :=
    wp_procs_irrel_strict helper_init_strict noProcsProg.procs prog.procs
      (iprop(True : IProp GF)) ⊤ _ $$ [Hstandalone_np]
  · iexact Hstandalone_np
  -- 2. Reshape post via wp_wand.
  ihave Hreshaped := wp_wand (GF := GF) prog.procs
    (iprop(True : IProp GF))
    (Φ := fun v => iprop(⌜φ v⌝ : IProp GF))
    (Ψ := fun v => wp prog.procs (iprop(True : IProp GF)) ⊤
            (BodyTraj.postDoReturnThread callerFrame [] v) Φ)
    helper_init $$ [Hstandalone Hwand]
  · isplitl [Hstandalone]
    · iexact Hstandalone
    · iintro %v Hpurev
      iapply Hwand $$ %v
      iexact Hpurev
  -- 3. Lift via wp_stack_push.
  imodintro
  have hgoal :
      BodyTraj.stackExt helper_init [callerFrame]
        = ({ stmt := helper_init.stmt, cont := helper_init.cont,
             env := helper_init.env, stack := callerFrame :: helper_init.stack,
             result := helper_init.result } : Thread) := by
    simp [BodyTraj.stackExt, helper_init_stack_nil]
  rw [← hgoal]
  iapply (BodyTraj.wp_stack_push prog.procs
    (iprop(True : IProp GF)) callerFrame [] Φ helper_init)
  iexact Hreshaped

end Agar.Logic

module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Iris.Std.CoPset
public import Iris.Std.Namespaces
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Delab
public import Agar.Iris.Heap

@[expose] public section


/-! # Boilerplate tactics for `Rules.lean`

Two macros factor out repetition that pervades the rule proofs:

* `wp_unfold_step` opens the step disjunct of `wp_unfold` (unfold +
  `or_intro_r` + `istart`).
* `wp_pure_det rw` discharges the determinism obligation of
  `wp_pure_step` by rewriting the operational equation. -/

namespace Agar.Logic

open Iris Iris.BI

/-- Open the step disjunct of `wp_unfold`. -/
scoped macro "wp_unfold_step" : tactic => `(tactic| (
  refine .trans ?_ (equiv_iff.mp (wp_unfold _ _ _ _ _)).mpr
  refine .trans ?_ BI.or_intro_r
  istart))

/-- Open the value disjunct of `wp_unfold`. -/
scoped macro "wp_unfold_value" : tactic => `(tactic| (
  refine .trans ?_ (equiv_iff.mp (wp_unfold _ _ _ _ _)).mpr
  refine .trans ?_ BI.or_intro_l))

/-- Discharge the determinism obligation in a `wp_pure_step` application
by rewriting with the supplied `tstep_*` equation. -/
scoped macro "wp_pure_det " "[" rs:Lean.Parser.Tactic.rwRule,* "]" : tactic =>
  `(tactic| (
    rintro m m'' t'' sp ⟨chosen, hstep⟩
    cases chosen with
    | some _ => simp [tstep] at hstep
    | none =>
        rw [$rs,*] at hstep
        first
        | (cases hstep; exact ⟨rfl, rfl, rfl⟩)
        | (simp only [doReturn] at hstep; cases hstep; exact ⟨rfl, rfl, rfl⟩)))

end Agar.Logic



/-! # WP rules for Agar

Mask-aware Hoare-style rules over the fancy-update WP. Each rule threads
the invariant mask `E : CoPset` through unchanged (no rule here opens or
closes invariants — that is the user's job via `inv_acc` etc.). Forked
threads run at `⊤`.

The step-rule shape inside `wp_unfold` is
`state_interp m ={E,∅}=∗ ⌜red⌝ ∗ ▷ ∀…, ⌜step⌝ ={∅,E}=∗ (…)`. Pure
rules just open the outer `={E,∅}=∗` with `fupd_mask_intro empty_subset`
(holding a closer `Hclose : |={∅,E}=> emp`), then `imod Hclose` after
the step to close back to `E`. Heap rules additionally lift the
points-to ghost update via `BIUpdateFUpdate.fupd_of_bupd` (transparent
through `imod`). -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-! ## Monotonicity in the post-condition

If `Φ` entails `Ψ` pointwise, then `wp _ _ _ Φ` entails `wp _ _ _ Ψ`.
Standard Iris result; proven by Löb induction over an internalised
universal claim, then specialised. The fork branch is unaffected: the
spawned thread's post is `fun _ => fork_post`, fixed across `Φ → Ψ`.
-/

theorem wp_mono (procs : Name → Option Proc) (fork_post : IProp GF)
    {Φ Ψ : Val → IProp GF} (h : ∀ v, Φ v ⊢ Ψ v) (t : Thread) :
    wp procs fork_post E t Φ ⊢ wp procs fork_post E t Ψ := by
  suffices key : (True : IProp GF) ⊢ iprop(∀ (t' : Thread),
      wp procs fork_post E t' Φ -∗ wp procs fork_post E t' Ψ) by
    exact BI.wand_entails
      (BI.true_intro.trans (key.trans (BI.forall_elim t)))
  apply BILoeb.loeb_weak
  iintro IH
  iintro %t' HW
  ihave HW' :=
    (equiv_iff.mp (wp_unfold procs fork_post E t' Φ)).mp $$ HW
  iapply (equiv_iff.mp (wp_unfold procs fork_post E t' Ψ)).mpr
  icases HW' with ⟨⟨%v, %hterm, HΦ⟩ | ⟨%hnt, Hsteps⟩⟩
  · ileft
    iexists v
    isplitr
    · ipure_intro; exact hterm
    · imod HΦ with HΦv
      imodintro
      iapply h v
      iexact HΦv
  · iright
    isplitr
    · ipure_intro; exact hnt
    iintro %m HS
    imod Hsteps $$ HS with ⟨%hred, HsRest⟩
    iapply fupd_mask_intro empty_subset
    iintro Hclose
    isplitr
    · ipure_intro; exact hred
    iintro !> %m' %t'' %sp %hstep
    imod Hclose
    imod HsRest $$ %m' %t'' %sp %hstep with ⟨HSm', HWt', HFork⟩
    imodintro
    iframe HSm' HFork
    iapply IH $$ %t'' HWt'

/-! ## Termination

If a thread has terminated, the WP collapses to the post-condition. -/

theorem wp_value (procs : Name → Option Proc) (fork_post : IProp GF)
    (t : Thread) (v : Val) (Φ : Val → IProp GF) (h : t.toValue = some v) :
    Φ v ⊢ wp procs fork_post E t Φ := by
  wp_unfold_value
  refine BI.exists_intro' v ?_
  istart
  iintro HΦ
  isplitr
  · ipure_intro; exact h
  · iintro !>; iexact HΦ

/-- Fancy-update-strengthened `wp_value`. The value branch of the WP
unfolds to `|={E}=> Φ v`, so it accepts a fupd-flavoured post directly
— useful when the resource we want to deliver (e.g. a freshly allocated
`inv N P`) only becomes available *after* a fupd. -/
theorem wp_value_fupd (procs : Name → Option Proc) (fork_post : IProp GF)
    (t : Thread) (v : Val) (Φ : Val → IProp GF) (h : t.toValue = some v) :
    iprop(|={E}=> Φ v) ⊢ wp procs fork_post E t Φ := by
  wp_unfold_value
  refine BI.exists_intro' v ?_
  istart
  iintro HΦ
  isplitr
  · ipure_intro; exact h
  · iexact HΦ

/-! ## Fancy-update absorption

The standard Iris `fupd_wp`: an outer fancy-update with mask `E` can be
absorbed into a `wp` at the same mask `E`. Proof: meta-level case-split
on `t.toValue`.

* `some v`: the WP collapses to the value branch `|={E}=> Φ v`; the two
  fupds at mask `E` chain via proofmode `imod`.
* `none`: `t.terminated = false`, deliver the step branch. Its outer
  `={E,∅}=∗` absorbs the ambient `|={E}=>` again via `imod` (fupd
  transitivity at the proofmode level). -/

private theorem toValue_none_of_terminated {t : Thread}
    (h : t.terminated = false) : t.toValue = none := by
  unfold Thread.terminated at h
  unfold Thread.toValue
  split at h <;> simp_all

private theorem terminated_false_of_toValue_none {t : Thread}
    (h : t.toValue = none) : t.terminated = false := by
  unfold Thread.toValue at h
  unfold Thread.terminated
  split at h <;> simp_all

theorem fupd_wp (procs : Name → Option Proc) (fork_post : IProp GF)
    (t : Thread) (Φ : Val → IProp GF) :
    iprop(|={E}=> wp procs fork_post E t Φ)
    ⊢ wp procs fork_post E t Φ := by
  istart
  iintro Hupd
  iapply (equiv_iff.mp (wp_unfold procs fork_post E t Φ)).mpr
  by_cases hterm : t.terminated = false
  · -- step branch
    iright
    isplitr
    · ipure_intro; exact hterm
    iintro %m HS
    imod Hupd with HW
    ihave HW' :=
      (equiv_iff.mp (wp_unfold procs fork_post E t Φ)).mp $$ HW
    icases HW' with ⟨⟨%v', %htv', _⟩ | ⟨_, Hsteps⟩⟩
    · rw [toValue_none_of_terminated hterm] at htv'
      cases htv'
    · iapply Hsteps $$ HS
  · -- value branch: t.terminated = true, so t.toValue = some _
    have hterm' : t.terminated = true := by
      cases h : t.terminated
      · exact absurd h hterm
      · rfl
    have ⟨v, hv⟩ : ∃ v, t.toValue = some v := by
      unfold Thread.toValue
      unfold Thread.terminated at hterm'
      split at hterm' <;> simp_all
    ileft
    iexists v
    isplitr
    · ipure_intro; exact hv
    · imod Hupd with HW
      ihave HW' :=
        (equiv_iff.mp (wp_unfold procs fork_post E t Φ)).mp $$ HW
      icases HW' with ⟨⟨%v', %htv', HΦ⟩ | ⟨%hnt, _⟩⟩
      · have hvv : some v = some v' := hv.symm.trans htv'
        cases hvv
        iexact HΦ
      · exact absurd hnt (by rw [hterm']; simp)

/-! ## Frame rule

Any resource `R` held alongside a `wp` can be threaded through to the
post-condition. Proved by Löb induction on a universally-quantified
internal entailment, exactly like `wp_mono`. -/

theorem wp_frame (procs : Name → Option Proc) (fork_post : IProp GF)
    (R : IProp GF) {Φ : Val → IProp GF} (t : Thread) :
    iprop(R ∗ wp procs fork_post E t Φ)
    ⊢ wp procs fork_post E t (fun v => iprop(R ∗ Φ v)) := by
  suffices key : (True : IProp GF) ⊢ iprop(∀ (t' : Thread),
      R ∗ wp procs fork_post E t' Φ -∗
        wp procs fork_post E t' (fun v => iprop(R ∗ Φ v))) by
    exact BI.wand_entails
      (BI.true_intro.trans (key.trans (BI.forall_elim t)))
  apply BILoeb.loeb_weak
  iintro IH
  iintro %t' ⟨HR, HW⟩
  ihave HW' :=
    (equiv_iff.mp (wp_unfold procs fork_post E t' Φ)).mp $$ HW
  iapply (equiv_iff.mp
    (wp_unfold procs fork_post E t' (fun v => iprop(R ∗ Φ v)))).mpr
  icases HW' with ⟨⟨%v, %hterm, HΦ⟩ | ⟨%hnt, Hsteps⟩⟩
  · ileft
    iexists v
    isplitr
    · ipure_intro; exact hterm
    · imod HΦ with HΦv
      imodintro
      iframe HR HΦv
  · iright
    isplitr
    · ipure_intro; exact hnt
    iintro %m HS
    imod Hsteps $$ HS with ⟨%hred, Hsteps'⟩
    iapply fupd_mask_intro empty_subset
    iintro Hclose
    isplitr
    · ipure_intro; exact hred
    iintro !> %m' %t'' %sp %hstep
    imod Hclose
    imod Hsteps' $$ %m' %t'' %sp %hstep with ⟨HSm', HWt', HFork⟩
    imodintro
    iframe HSm' HFork
    iapply IH $$ %t''
    iframe HR HWt'

/-! ## A pure-step combinator

`wp_pure_step` lets us derive a Hoare-style rule from a determinism
witness for a single thread step. It is the workhorse for assignments
and other purely local statement reductions that don't touch the heap.
-/

theorem wp_pure_step (procs : Name → Option Proc) (fork_post : IProp GF)
    (t t' : Thread) (Φ : Val → IProp GF)
    (hnt : t.terminated = false)
    (hred : ∀ m, ∃ m' sp, thread_step procs m t m' t' sp)
    (hdet : ∀ m m'' t'' sp, thread_step procs m t m'' t'' sp →
              m'' = m ∧ t'' = t' ∧ sp = none) :
    ▷ wp procs fork_post E t' Φ ⊢ wp procs fork_post E t Φ := by
  wp_unfold_step
  iintro HW
  isplitr
  · ipure_intro; exact hnt
  iintro %m HS
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    obtain ⟨m', sp, hstep⟩ := hred m
    exact ⟨m', t', sp, hstep⟩
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨rfl, rfl, rfl⟩ := hdet m m'' t'' sp hstep
  imod Hclose
  imodintro
  iframe HS HW
  iintro %ts %hsp; cases hsp

/-! ## Pure statement rules

Each rule discharges its determinism obligation by rewriting via the
corresponding `tstep_<stmt>` equation, leaving a `some _ = some _` that
inversion handles. Statements split on `chosen`: `some _` only ever
steps `.alloc`, so for non-alloc statements that case yields
`none = some _` after `simp [tstep]`.
-/

theorem wp_skip_cons (procs : Name → Option Proc) (fork_post : IProp GF)
    (s : Stmt) (rest : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF) :
    ▷ wp procs fork_post E ⟨s, rest, env, stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.skip, s :: rest, env, stack, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨s, rest, env, stack, none⟩)
  · rfl
  · intro m; exact ⟨m, none, none, tstep_skip_cons procs m s rest env stack⟩
  · wp_pure_det [tstep_skip_cons]

theorem wp_seq (procs : Name → Option Proc) (fork_post : IProp GF)
    (s₁ s₂ : Stmt) (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF) :
    ▷ wp procs fork_post E ⟨s₁, s₂ :: cont, env, stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.seq s₁ s₂, cont, env, stack, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨s₁, s₂ :: cont, env, stack, none⟩)
  · rfl
  · intro m; exact ⟨m, none, none, tstep_seq procs m s₁ s₂ cont env stack⟩
  · wp_pure_det [tstep_seq]

theorem wp_assign (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (e : Expr) (v : Val) (cont : List Stmt) (env : Env)
    (stack : List Frame) (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some v) :
    ▷ wp procs fork_post E ⟨.skip, cont, env.set x v, stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.assign x e, cont, env, stack, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨.skip, cont, env.set x v, stack, none⟩)
  · rfl
  · intro m
    exact ⟨m, none, none, tstep_assign procs m x e v cont env stack heval⟩
  · wp_pure_det [tstep_assign _ _ _ _ _ _ _ _ heval]

theorem wp_ite_true (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (s₁ s₂ : Stmt) (cont : List Stmt) (env : Env)
    (stack : List Frame) (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some (.bool true)) :
    ▷ wp procs fork_post E ⟨s₁, cont, env, stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.ite e s₁ s₂, cont, env, stack, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨s₁, cont, env, stack, none⟩)
  · rfl
  · intro m
    exact ⟨m, none, none, tstep_ite_true procs m e s₁ s₂ cont env stack heval⟩
  · wp_pure_det [tstep_ite_true _ _ _ _ _ _ _ _ heval]

theorem wp_ite_false (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (s₁ s₂ : Stmt) (cont : List Stmt) (env : Env)
    (stack : List Frame) (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some (.bool false)) :
    ▷ wp procs fork_post E ⟨s₂, cont, env, stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.ite e s₁ s₂, cont, env, stack, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨s₂, cont, env, stack, none⟩)
  · rfl
  · intro m
    exact ⟨m, none, none, tstep_ite_false procs m e s₁ s₂ cont env stack heval⟩
  · wp_pure_det [tstep_ite_false _ _ _ _ _ _ _ _ heval]

theorem wp_while (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (s : Stmt) (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF) :
    ▷ wp procs fork_post E
        ⟨.ite e (.seq s (.whileDo e s)) .skip, cont, env, stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.whileDo e s, cont, env, stack, none⟩ Φ := by
  apply wp_pure_step
    (t' := ⟨.ite e (.seq s (.whileDo e s)) .skip, cont, env, stack, none⟩)
  · rfl
  · intro m
    exact ⟨m, none, none, tstep_whileDo procs m e s cont env stack⟩
  · wp_pure_det [tstep_whileDo]

/-! ## Heap-touching statement rules

These follow the same template as the pure rules, but
* extract a pure fact from `heap_auth ∗ points_to …` via the framed
  read/lookup lemmas to discharge the reducibility obligation, and
* invoke the corresponding `heap_*` ghost-update to update the auth and
  produce the new points-to after the step.
-/

section Heap
variable {F : Type _} [UFraction F] [AgarG GF F]

theorem wp_load (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (e : Expr) (l : Loc) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some (.loc l)) :
    (points_to (GF := GF) (F := F) l v ∗
      ▷ (points_to l v -∗
          wp procs fork_post E ⟨.skip, cont, env.set x v, stack, none⟩ Φ))
    ⊢ wp procs fork_post E ⟨.load x e, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨HP, HK⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l v $$ [HS HP]
  · isplitl [HS] <;> iassumption
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m, ⟨.skip, cont, env.set x v, stack, none⟩, none, none, ?_⟩
    exact tstep_load procs m x e l v cont env stack heval hml
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_load _ _ _ _ _ _ _ _ _ heval hml] at hstep'
      cases hstep'
      imod Hclose
      imodintro
      iframe HS
      isplitl [HP HK]
      · iapply HK $$ HP
      · iintro %ts %hsp; cases hsp

theorem wp_store (procs : Name → Option Proc) (fork_post : IProp GF)
    (eL eV : Expr) (l : Loc) (vold v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (heL : Expr.eval env eL = some (.loc l))
    (heV : Expr.eval env eV = some v) :
    (points_to (GF := GF) (F := F) l vold ∗
      ▷ (points_to l v -∗ wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ))
    ⊢ wp procs fork_post E ⟨.store eL eV, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨HP, HK⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l vold $$ [HS HP]
  · isplitl [HS] <;> iassumption
  have hstore : m.store l v = some (m.update l (some v)) := by
    unfold Mem.store; rw [hml]
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m.update l (some v), ⟨.skip, cont, env, stack, none⟩, none, none, ?_⟩
    exact tstep_store procs m eL eV l v _ cont env stack heL heV hstore
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_store _ _ _ _ _ _ _ _ _ _ heL heV hstore] at hstep'
      cases hstep'
      imod Hclose
      imod heap_store (GF := GF) (F := F) hstore $$ [HS HP] with ⟨HS, HP⟩
      · isplitl [HS] <;> iassumption
      imodintro
      iframe HS
      isplitl [HP HK]
      · iapply HK $$ HP
      · iintro %ts %hsp; cases hsp

theorem wp_free (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (l : Loc) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some (.loc l)) :
    (points_to (GF := GF) (F := F) l v ∗
      ▷ wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
    ⊢ wp procs fork_post E ⟨.free e, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨HP, HK⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l v $$ [HS HP]
  · isplitl [HS] <;> iassumption
  have hfree : m.free l = some (m.update l none) := by
    unfold Mem.free; rw [hml]
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m.update l none, ⟨.skip, cont, env, stack, none⟩, none, none, ?_⟩
    exact tstep_free procs m _ e l cont env stack heval hfree
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_free _ _ _ _ _ _ _ _ heval hfree] at hstep'
      cases hstep'
      imod Hclose
      imod heap_free (GF := GF) (F := F) hfree $$ [HS HP] with HS
      · isplitl [HS] <;> iassumption
      imodintro
      iframe HS HK
      iintro %ts %hsp; cases hsp

/-! ### Allocation

The freshness witness lives in `Mem.notFull`, so `state_interp m` carries
it for free. Reducibility picks *any* fresh `l₀`; the universal post
`∀ l, l ↦ v -∗ wp …` is then specialised at whatever location the
adversary chose. The new points-to fragment comes from `heap_alloc`. -/

theorem wp_alloc (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (e : Expr) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some v) :
    (▷ ∀ (l : Loc), points_to (GF := GF) (F := F) l v -∗
          wp procs fork_post E ⟨.skip, cont, env.set x (.loc l), stack, none⟩ Φ)
    ⊢ wp procs fork_post E ⟨.alloc x e, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro HK
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  obtain ⟨l₀, hfresh⟩ := m.exists_fresh
  have halloc₀ : m.alloc l₀ v = some (m.update l₀ (some v)) := by
    unfold Mem.alloc; rw [show m.fn l₀ = none from hfresh]
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m.update l₀ (some v),
            ⟨.skip, cont, env.set x (.loc l₀), stack, none⟩, none, some l₀, ?_⟩
    exact tstep_alloc procs m _ l₀ x e v cont env stack heval halloc₀
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | none => simp [tstep] at hstep'
  | some l =>
      have hne : m.alloc l v ≠ none := fun h => by
        revert hstep'; unfold tstep; simp [heval, h]
      have ⟨m', halloc⟩ : ∃ m', m.alloc l v = some m' :=
        match h : m.alloc l v with
        | none    => absurd h hne
        | some m' => ⟨m', rfl⟩
      rw [tstep_alloc _ _ _ _ _ _ _ _ _ _ heval halloc] at hstep'
      cases hstep'
      imod Hclose
      imod heap_alloc (GF := GF) (F := F) halloc $$ HS with ⟨HS, HP⟩
      imodintro
      iframe HS
      isplitl [HK HP]
      · iapply HK $$ %l HP
      · iintro %ts %hsp; cases hsp

theorem wp_cas_fail (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (eL eO eN : Expr) (l : Loc) (vO vN cur : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (hne : (cur == vO) = false) :
    (points_to (GF := GF) (F := F) l cur ∗
      ▷ (points_to l cur -∗
          wp procs fork_post E ⟨.skip, cont, env.set x cur, stack, none⟩ Φ))
    ⊢ wp procs fork_post E ⟨.cas x eL eO eN, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨HP, HK⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l cur $$ [HS HP]
  · isplitl [HS] <;> iassumption
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m, ⟨.skip, cont, env.set x cur, stack, none⟩, none, none, ?_⟩
    exact tstep_cas_fail procs m x eL eO eN l vO vN cur cont env stack
      heL heO heN hml hne
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ heL heO heN hml hne]
        at hstep'
      cases hstep'
      imod Hclose
      imodintro
      iframe HS
      isplitl [HP HK]
      · iapply HK $$ HP
      · iintro %ts %hsp; cases hsp

theorem wp_cas_succ (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (eL eO eN : Expr) (l : Loc) (vO vN : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (heq : (vO == vO) = true) :
    (points_to (GF := GF) (F := F) l vO ∗
      ▷ (points_to l vN -∗
          wp procs fork_post E ⟨.skip, cont, env.set x vO, stack, none⟩ Φ))
    ⊢ wp procs fork_post E ⟨.cas x eL eO eN, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨HP, HK⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l vO $$ [HS HP]
  · isplitl [HS] <;> iassumption
  have hstore : m.store l vN = some (m.update l (some vN)) := by
    unfold Mem.store; rw [hml]
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m.update l (some vN), ⟨.skip, cont, env.set x vO, stack, none⟩,
             none, none, ?_⟩
    exact tstep_cas_succ procs m _ x eL eO eN l vO vN vO cont env stack
      heL heO heN hml heq hstore
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_cas_succ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            heL heO heN hml heq hstore]
        at hstep'
      cases hstep'
      imod Hclose
      imod heap_store (GF := GF) (F := F) hstore $$ [HS HP] with ⟨HS, HP⟩
      · isplitl [HS] <;> iassumption
      imodintro
      iframe HS
      isplitl [HP HK]
      · iapply HK $$ HP
      · iintro %ts %hsp; cases hsp

end Heap

/-- `skip` with empty cont but a pending stack frame: equivalent to
returning `unit` from the call. Two variants on `f.cont`. -/
theorem wp_skip_frame_cons (procs : Name → Option Proc) (fork_post : IProp GF)
    (env : Env) (rv : Name) (s : Stmt) (cs : List Stmt) (fenv : Env)
    (rest : List Frame) (Φ : Val → IProp GF) :
    ▷ wp procs fork_post E ⟨s, cs, fenv.set rv .unit, rest, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.skip, [], env, ⟨rv, s :: cs, fenv⟩ :: rest, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨s, cs, fenv.set rv .unit, rest, none⟩)
  · rfl
  · intro m
    refine ⟨m, none, none, ?_⟩
    rw [tstep_skip_frame]; rfl
  · wp_pure_det [tstep_skip_frame]

theorem wp_skip_frame_nil (procs : Name → Option Proc) (fork_post : IProp GF)
    (env : Env) (rv : Name) (fenv : Env) (rest : List Frame)
    (Φ : Val → IProp GF) :
    ▷ wp procs fork_post E ⟨.skip, [], fenv.set rv .unit, rest, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.skip, [], env, ⟨rv, [], fenv⟩ :: rest, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨.skip, [], fenv.set rv .unit, rest, none⟩)
  · rfl
  · intro m
    refine ⟨m, none, none, ?_⟩
    rw [tstep_skip_frame]; rfl
  · wp_pure_det [tstep_skip_frame]

/-! ## Procedures: call and (top-of-stack) return -/

/-- Return at the top of the stack: the thread terminates with the
returned value `v`, and the WP post-condition fires at that value. -/
theorem wp_ret_top (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (v : Val) (cont : List Stmt) (env : Env)
    (Φ : Val → IProp GF) (heval : Expr.eval env e = some v) :
    Φ v ⊢ wp procs fork_post E ⟨.ret e, cont, env, [], none⟩ Φ := by
  wp_unfold_step
  iintro HΦ
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m, ⟨.skip, [], env, [], some v⟩, none, none, ?_⟩
    rw [tstep_ret _ _ _ _ _ _ _ heval]; rfl
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_ret _ _ _ _ _ _ _ heval] at hstep'
      simp only [doReturn] at hstep'
      cases hstep'
      imod Hclose
      imodintro
      iframe HS
      isplitl [HΦ]
      · -- The terminated thread `⟨skip, [], env, [], some v⟩` has
        -- `toValue = some v`; chain into the value disjunct.
        iapply (equiv_iff.mp
          (wp_unfold procs fork_post E ⟨.skip, [], env, [], some v⟩ Φ)).mpr
        ileft
        iexists v
        isplitr
        · ipure_intro; rfl
        · imodintro; iexact HΦ
      · iintro %ts %hsp; cases hsp

/-- Return popping one frame with a non-empty continuation. -/
theorem wp_ret_pop_cons (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (v : Val) (cont : List Stmt) (env : Env)
    (rv : Name) (s : Stmt) (cs : List Stmt) (fenv : Env)
    (rest : List Frame) (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some v) :
    ▷ wp procs fork_post E ⟨s, cs, fenv.set rv v, rest, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.ret e, cont, env, ⟨rv, s :: cs, fenv⟩ :: rest, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨s, cs, fenv.set rv v, rest, none⟩)
  · rfl
  · intro m
    refine ⟨m, none, none, ?_⟩
    rw [tstep_ret _ _ _ _ _ _ _ heval]; rfl
  · wp_pure_det [tstep_ret _ _ _ _ _ _ _ heval]

/-- Return popping one frame with an empty continuation. -/
theorem wp_ret_pop_nil (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (v : Val) (cont : List Stmt) (env : Env)
    (rv : Name) (fenv : Env) (rest : List Frame)
    (Φ : Val → IProp GF) (heval : Expr.eval env e = some v) :
    ▷ wp procs fork_post E ⟨.skip, [], fenv.set rv v, rest, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.ret e, cont, env, ⟨rv, [], fenv⟩ :: rest, none⟩ Φ := by
  apply wp_pure_step (t' := ⟨.skip, [], fenv.set rv v, rest, none⟩)
  · rfl
  · intro m
    refine ⟨m, none, none, ?_⟩
    rw [tstep_ret _ _ _ _ _ _ _ heval]; rfl
  · wp_pure_det [tstep_ret _ _ _ _ _ _ _ heval]

theorem wp_call (procs : Name → Option Proc) (fork_post : IProp GF)
    (x f : Name) (args : List Expr) (proc : Proc) (vs : List Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (hproc : procs f = some proc) (hargs : evalArgs env args = some vs)
    (harity : vs.length = proc.params.length) :
    ▷ wp procs fork_post E
        ⟨proc.body, [], bindParams proc.params vs,
          ⟨x, cont, env⟩ :: stack, none⟩ Φ
    ⊢ wp procs fork_post E ⟨.call x f args, cont, env, stack, none⟩ Φ := by
  apply wp_pure_step
    (t' := ⟨proc.body, [], bindParams proc.params vs, ⟨x, cont, env⟩ :: stack, none⟩)
  · rfl
  · intro m
    exact ⟨m, none, none,
      tstep_call procs m x f args proc vs cont env stack hproc hargs harity⟩
  · wp_pure_det [tstep_call _ _ _ _ _ _ _ _ _ _ hproc hargs harity]

/-! ## Concurrency: `fork`

The forked thread's WP is verified with `fork_post` as its post-condition
(it does not affect the parent's post-condition). The parent continues
with `skip` queued onto its `cont`. -/

theorem wp_fork (procs : Name → Option Proc) (fork_post : IProp GF)
    (f : Name) (args : List Expr) (proc : Proc) (vs : List Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (hproc : procs f = some proc) (hargs : evalArgs env args = some vs)
    (harity : vs.length = proc.params.length) :
    (▷ wp procs fork_post CoPset.full
          ⟨proc.body, [], bindParams proc.params vs, [], none⟩ (fun _ => fork_post)) ∗
    (▷ wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
    ⊢ wp procs fork_post E ⟨.fork f args, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨HFork, HCont⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipure_intro
    refine ⟨m, ⟨.skip, cont, env, stack, none⟩,
      some ⟨proc.body, [], bindParams proc.params vs, [], none⟩, none, ?_⟩
    exact tstep_fork procs m f args proc vs cont env stack hproc hargs harity
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_fork _ _ _ _ _ _ _ _ _ hproc hargs harity] at hstep'
      cases hstep'
      imod Hclose
      imodintro
      iframe HS HCont
      iintro %ts %hsp
      cases hsp
      iexact HFork

end Agar.Logic



/-! # WP rules that open an invariant for one atomic heap op

These rules mirror `wp_load` / `wp_store` / `wp_cas_*` from `Rules`,
but instead of taking a bare `l ↦ v` as precondition they take
`inv N (∃ v, l ↦ v)` and open the invariant across the atomic heap
operation. The mask sequence inside the WP step is

```
  E  ─inv_acc─▶  E\↑N  ─fupd_mask_intro─▶  ∅
  …step…
  ∅  ─Hclose_eq─▶  E\↑N  ─Hclose_inv─▶  E
```

Reducibility needs `m.load l = some v` upfront, so we strip the `▷`
on the invariant body using `imod` (the body `∃ v, l ↦ v` is timeless;
`imod` over a fupd absorbs `◇`).
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}



section Heap

/-! ## Load opening an invariant

`inv N (∃ v, l ↦ v)` lets us read `l` and observe *some* value `v`.
The continuation gets the points-to and must hand it back. -/

theorem wp_load_inv (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (x : Name) (e : Expr) (l : Loc)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E)
    (heval : Expr.eval env e = some (.loc l)) :
    (inv N (iprop(∃ v : Val, points_to (GF := GF) (F := F) l v)) ∗
      ▷ iprop(∀ (v : Val),
          points_to (GF := GF) (F := F) l v -∗
            points_to (GF := GF) (F := F) l v ∗
              wp procs fork_post E ⟨.skip, cont, env.set x v, stack, none⟩ Φ))
    ⊢ wp procs fork_post E ⟨.load x e, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨#HI, HK⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  imod (inv_acc E N _ Hsub) $$ HI with ⟨>⟨%v, HP⟩, Hclose_inv⟩
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l v $$ [HS HP]
  · isplitl [HS] <;> iassumption
  iapply fupd_mask_intro empty_subset
  iintro Hclose_eq
  isplitr
  · ipure_intro
    refine ⟨m, ⟨.skip, cont, env.set x v, stack, none⟩, none, none, ?_⟩
    exact tstep_load procs m x e l v cont env stack heval hml
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_load _ _ _ _ _ _ _ _ _ heval hml] at hstep'
      cases hstep'
      imod Hclose_eq
      ispecialize HK $$ %v
      ihave ⟨HP, HW⟩ := HK $$ HP
      imod Hclose_inv $$ [HP] with _
      · inext; iexists v; iexact HP
      imodintro
      iframe HS HW
      iintro %ts %hsp; cases hsp

/-! ## Store opening an invariant -/

theorem wp_store_inv (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (eL eV : Expr) (l : Loc) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E)
    (heL : Expr.eval env eL = some (.loc l))
    (heV : Expr.eval env eV = some v) :
    (inv N (iprop(∃ v : Val, points_to (GF := GF) (F := F) l v)) ∗
      ▷ wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
    ⊢ wp procs fork_post E ⟨.store eL eV, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨#HI, HW⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  imod (inv_acc E N _ Hsub) $$ HI with ⟨>⟨%vold, HP⟩, Hclose_inv⟩
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l vold $$ [HS HP]
  · isplitl [HS] <;> iassumption
  have hstore : m.store l v = some (m.update l (some v)) := by
    unfold Mem.store; rw [hml]
  iapply fupd_mask_intro empty_subset
  iintro Hclose_eq
  isplitr
  · ipure_intro
    refine ⟨m.update l (some v), ⟨.skip, cont, env, stack, none⟩, none, none, ?_⟩
    exact tstep_store procs m eL eV l v _ cont env stack heL heV hstore
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_store _ _ _ _ _ _ _ _ _ _ heL heV hstore] at hstep'
      cases hstep'
      imod Hclose_eq
      imod heap_store (GF := GF) (F := F) hstore $$ [HS HP] with ⟨HS, HP⟩
      · isplitl [HS] <;> iassumption
      imod Hclose_inv $$ [HP] with _
      · inext; iexists v; iexact HP
      imodintro
      iframe HS HW
      iintro %ts %hsp; cases hsp

/-! ## Store atomic-triple form

This is the accessor / atomic-triple variant of `wp_store_inv`. The caller
picks an arbitrary invariant body `P` and supplies a fupd that consumes
`▷ P` (in mask `E ∖ ↑N`) to produce the current points-to plus a closing
continuation that takes the *updated* points-to (`l ↦ v`) and gives back
`▷ P` together with the unguarded WP for the continuation.

This lets clients change the invariant body across the store — needed for
release-store of a mutex, where the lock invariant body switches from
"held" to "free with token". -/

theorem wp_store_atomic (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (P : IProp GF) (eL eV : Expr)
    (l : Loc) (v : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E)
    (heL : Expr.eval env eL = some (.loc l))
    (heV : Expr.eval env eV = some v) :
    iprop(inv N P ∗
      ((▷ P) ={E \ ↑N}=∗
        ∃ vcur : Val, points_to (GF := GF) (F := F) l vcur ∗
          (points_to (GF := GF) (F := F) l v ={E \ ↑N}=∗ (▷ P) ∗
            wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)))
    ⊢ wp procs fork_post E ⟨.store eL eV, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨#HI, Hacc⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  imod (inv_acc E N _ Hsub) $$ HI with ⟨HPbody, Hclose_inv⟩
  imod Hacc $$ [HPbody] with ⟨%vcur, HP, Hclose_acc⟩
  · iexact HPbody
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l vcur $$ [HS HP]
  · isplitl [HS] <;> iassumption
  have hstore : m.store l v = some (m.update l (some v)) := by
    unfold Mem.store; rw [hml]
  iapply fupd_mask_intro empty_subset
  iintro Hclose_eq
  isplitr
  · ipure_intro
    refine ⟨m.update l (some v), ⟨.skip, cont, env, stack, none⟩, none, none, ?_⟩
    exact tstep_store procs m eL eV l v _ cont env stack heL heV hstore
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_store _ _ _ _ _ _ _ _ _ _ heL heV hstore] at hstep'
      cases hstep'
      imod Hclose_eq
      imod heap_store (GF := GF) (F := F) hstore $$ [HS HP] with ⟨HS, HP⟩
      · isplitl [HS] <;> iassumption
      imod Hclose_acc $$ [HP] with ⟨HPbody, HW⟩
      · iexact HP
      imod Hclose_inv $$ [HPbody] with _
      · iexact HPbody
      imodintro
      iframe HS HW
      iintro %ts %hsp; cases hsp

/-! ## Load atomic-triple form

This is the accessor / atomic-triple variant of `wp_load_inv`. The caller
picks an arbitrary invariant body `P` and supplies a fupd that consumes
`▷ P` (in mask `E ∖ ↑N`) to produce the current points-to plus a closing
continuation that takes back the *same* points-to (load doesn't change
the cell) and gives back `▷ P` together with the unguarded WP for the
continuation, with the local `x` bound to the loaded value `vcur`. -/

theorem wp_load_atomic (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (P : IProp GF) (eL : Expr) (l : Loc)
    (x : Name) (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E)
    (heL : Expr.eval env eL = some (.loc l)) :
    iprop(inv N P ∗
      ((▷ P) ={E \ ↑N}=∗
        ∃ vcur : Val, points_to (GF := GF) (F := F) l vcur ∗
          (points_to (GF := GF) (F := F) l vcur ={E \ ↑N}=∗ (▷ P) ∗
            wp procs fork_post E ⟨.skip, cont, env.set x vcur, stack, none⟩ Φ)))
    ⊢ wp procs fork_post E ⟨.load x eL, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨#HI, Hacc⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  imod (inv_acc E N _ Hsub) $$ HI with ⟨HPbody, Hclose_inv⟩
  imod Hacc $$ [HPbody] with ⟨%vcur, HP, Hclose_acc⟩
  · iexact HPbody
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l vcur $$ [HS HP]
  · isplitl [HS] <;> iassumption
  iapply fupd_mask_intro empty_subset
  iintro Hclose_eq
  isplitr
  · ipure_intro
    refine ⟨m, ⟨.skip, cont, env.set x vcur, stack, none⟩, none, none, ?_⟩
    exact tstep_load procs m x eL l vcur cont env stack heL hml
  iintro !> %m'' %t'' %sp %hstep
  obtain ⟨chosen, hstep'⟩ := hstep
  cases chosen with
  | some _ => simp [tstep] at hstep'
  | none =>
      rw [tstep_load _ _ _ _ _ _ _ _ _ heL hml] at hstep'
      cases hstep'
      imod Hclose_eq
      imod Hclose_acc $$ [HP] with ⟨HPbody, HW⟩
      · iexact HP
      imod Hclose_inv $$ [HPbody] with _
      · iexact HPbody
      imodintro
      iframe HS HW
      iintro %ts %hsp; cases hsp

/-! ## CAS opening an invariant

The continuation receives the *current* value `v` together with the
points-to. It must return the new points-to (either `l ↦ vN` on
success or `l ↦ v` on failure) and the WP continuation, where the
local variable `x` is bound to the value the heap held. -/

theorem wp_cas_inv (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (x : Name) (eL eO eN : Expr) (l : Loc) (vO vN : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (heq : (vO == vO) = true)
    (hne_of_ne : ∀ v, v ≠ vO → (v == vO) = false) :
    (inv N (iprop(∃ v : Val, points_to (GF := GF) (F := F) l v)) ∗
      ▷ wp procs fork_post E ⟨.skip, cont, env.set x vO, stack, none⟩ Φ ∗
      iprop(▷ (∀ (v : Val), ⌜v ≠ vO⌝ -∗
              wp procs fork_post E
                ⟨.skip, cont, env.set x v, stack, none⟩ Φ)))
    ⊢ wp procs fork_post E ⟨.cas x eL eO eN, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨#HI, Hsucc, Hfail⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  imod (inv_acc E N _ Hsub) $$ HI with ⟨>⟨%v, HP⟩, Hclose_inv⟩
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l v $$ [HS HP]
  · isplitl [HS] <;> iassumption
  iapply fupd_mask_intro empty_subset
  iintro Hclose_eq
  by_cases hvO : v = vO
  · -- Success branch.
    cases hvO
    have hstore : m.store l vN = some (m.update l (some vN)) := by
      unfold Mem.store; rw [hml]
    isplitr
    · ipure_intro
      refine ⟨m.update l (some vN), ⟨.skip, cont, env.set x vO, stack, none⟩,
              none, none, ?_⟩
      exact tstep_cas_succ procs m _ x eL eO eN l vO vN vO cont env stack
        heL heO heN hml heq hstore
    iintro !> %m'' %t'' %sp %hstep
    obtain ⟨chosen, hstep'⟩ := hstep
    cases chosen with
    | some _ => simp [tstep] at hstep'
    | none =>
        rw [tstep_cas_succ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              heL heO heN hml heq hstore] at hstep'
        cases hstep'
        imod Hclose_eq
        imod heap_store (GF := GF) (F := F) hstore $$ [HS HP] with ⟨HS, HP⟩
        · isplitl [HS] <;> iassumption
        imod Hclose_inv $$ [HP] with _
        · inext; iexists vN; iexact HP
        imodintro
        iframe HS
        iframe Hsucc
        iintro %ts %hsp; cases hsp
  · -- Failure branch.
    have hne : (v == vO) = false := hne_of_ne v hvO
    isplitr
    · ipure_intro
      refine ⟨m, ⟨.skip, cont, env.set x v, stack, none⟩, none, none, ?_⟩
      exact tstep_cas_fail procs m x eL eO eN l vO vN v cont env stack
        heL heO heN hml hne
    iintro !> %m'' %t'' %sp %hstep
    obtain ⟨chosen, hstep'⟩ := hstep
    cases chosen with
    | some _ => simp [tstep] at hstep'
    | none =>
        rw [tstep_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ heL heO heN hml hne]
          at hstep'
        cases hstep'
        imod Hclose_eq
        ispecialize Hfail $$ %v
        ihave HW := Hfail $$ %hvO
        imod Hclose_inv $$ [HP] with _
        · inext; iexists v; iexact HP
        imodintro
        iframe HS
        iframe HW
        iintro %ts %hsp; cases hsp

/-! ## CAS atomic-triple form

This is the accessor / atomic-triple variant of `wp_cas_inv`. Instead of
hard-wiring the invariant body to `∃ v, l ↦ v` and absorbing the open/close
internally, we let the caller pick an arbitrary body `P` and supply a fupd
that consumes `▷ P` (in mask `E ∖ ↑N`) to produce the points-to plus *both*
closing continuations — one for the success case (`vcur = vO`, return the
updated points-to) and one for the failure case (`vcur ≠ vO`, return the
unchanged points-to). Each closing continuation re-establishes `▷ P` and
the WP for the rest of the program.

This lets clients open an invariant whose body is a disjunction (e.g. a
lock that is either free with token or held), branch on which disjunct is
present, and re-close into the *other* disjunct after the CAS — exactly
what lock-ownership ghost-state proofs need. -/

theorem wp_cas_atomic (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (P : IProp GF) (x : Name) (eL eO eN : Expr)
    (l : Loc) (vO vN : Val)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E)
    (heL : Expr.eval env eL = some (.loc l))
    (heO : Expr.eval env eO = some vO) (heN : Expr.eval env eN = some vN)
    (heq : (vO == vO) = true)
    (hne_of_ne : ∀ v, v ≠ vO → (v == vO) = false) :
    iprop(inv N P ∗
      ((▷ P) ={E \ ↑N}=∗
        ∃ vcur : Val, points_to (GF := GF) (F := F) l vcur ∗
          ((⌜vcur = vO⌝ -∗ points_to (GF := GF) (F := F) l vN
                  ={E \ ↑N}=∗ (▷ P) ∗
                    wp procs fork_post E
                      ⟨.skip, cont, env.set x vO, stack, none⟩ Φ) ∗
            (⌜vcur ≠ vO⌝ -∗ points_to (GF := GF) (F := F) l vcur
                  ={E \ ↑N}=∗ (▷ P) ∗
                    wp procs fork_post E
                      ⟨.skip, cont, env.set x vcur, stack, none⟩ Φ))))
    ⊢ wp procs fork_post E ⟨.cas x eL eO eN, cont, env, stack, none⟩ Φ := by
  wp_unfold_step
  iintro ⟨#HI, Hacc⟩
  isplitr
  · ipure_intro; rfl
  iintro %m HS
  imod (inv_acc E N _ Hsub) $$ HI with ⟨HPbody, Hclose_inv⟩
  imod Hacc $$ [HPbody] with ⟨%vcur, HP, Hsucc, Hfail⟩
  · iexact HPbody
  ihave ⟨%hml, HS, HP⟩ :=
    heap_load_frame (GF := GF) (F := F) m l vcur $$ [HS HP]
  · isplitl [HS] <;> iassumption
  iapply fupd_mask_intro empty_subset
  iintro Hclose_eq
  by_cases hvO : vcur = vO
  · -- Success branch.
    cases hvO
    have hstore : m.store l vN = some (m.update l (some vN)) := by
      unfold Mem.store; rw [hml]
    isplitr
    · ipure_intro
      refine ⟨m.update l (some vN), ⟨.skip, cont, env.set x vO, stack, none⟩,
              none, none, ?_⟩
      exact tstep_cas_succ procs m _ x eL eO eN l vO vN vO cont env stack
        heL heO heN hml heq hstore
    iintro !> %m'' %t'' %sp %hstep
    obtain ⟨chosen, hstep'⟩ := hstep
    cases chosen with
    | some _ => simp [tstep] at hstep'
    | none =>
        rw [tstep_cas_succ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              heL heO heN hml heq hstore] at hstep'
        cases hstep'
        imod Hclose_eq
        imod heap_store (GF := GF) (F := F) hstore $$ [HS HP] with ⟨HS, HP⟩
        · isplitl [HS] <;> iassumption
        ihave Hsucc := Hsucc $$ %(rfl : vO = vO)
        imod Hsucc $$ [HP] with ⟨HPbody, HW⟩
        · iexact HP
        imod Hclose_inv $$ [HPbody] with _
        · iexact HPbody
        imodintro
        iframe HS
        iframe HW
        iintro %ts %hsp; cases hsp
  · -- Failure branch.
    have hne : (vcur == vO) = false := hne_of_ne vcur hvO
    isplitr
    · ipure_intro
      refine ⟨m, ⟨.skip, cont, env.set x vcur, stack, none⟩, none, none, ?_⟩
      exact tstep_cas_fail procs m x eL eO eN l vO vN vcur cont env stack
        heL heO heN hml hne
    iintro !> %m'' %t'' %sp %hstep
    obtain ⟨chosen, hstep'⟩ := hstep
    cases chosen with
    | some _ => simp [tstep] at hstep'
    | none =>
        rw [tstep_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ heL heO heN hml hne]
          at hstep'
        cases hstep'
        imod Hclose_eq
        ihave Hfail := Hfail $$ %hvO
        imod Hfail $$ [HP] with ⟨HPbody, HW⟩
        · iexact HP
        imod Hclose_inv $$ [HPbody] with _
        · iexact HPbody
        imodintro
        iframe HS
        iframe HW
        iintro %ts %hsp; cases hsp

/-! ## Note on derivability of `wp_cas_inv` from `wp_cas_atomic`

`wp_cas_atomic` is strictly *stronger* than `wp_cas_inv`: the closing
wands in the accessor return an unguarded `wp` (no leading `▷`), whereas
`wp_cas_inv` only assumes `▷ wp` for its success/failure continuations.
Re-deriving `wp_cas_inv` would require stripping a `▷` from those wps
without a step to consume it. The intended use of `wp_cas_atomic` is for
clients that *do* hold an unguarded wp by then (e.g. via prior ghost
moves that yield the post-state of a lock-acquire), which is precisely
what the existing `wp_cas_inv` cannot express. -/

end Heap

end Agar.Logic

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
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Algebra.ThreadpoolRA

@[expose] public section

/-! # Completeness scaffolding — heap-free fragment

Skeletal port of §3.2 of Hostert et al., *Completeness of Iris-Based
Program Logics*, to Agar.

What is provided here:

* `Stmt.heapFree` / `Thread.heapFree` / `Program.heapFree` —
  syntactic restrictions to programs that never use
  `load/store/alloc/free/cas`. Required because Agar's
  `state_interp = heap_auth` is exclusive and cannot coexist with the
  paper's "big-sep of all points-tos" inside the completeness
  invariant. For heap-free programs the operational memory stays at
  `Mem.empty`, sidestepping that conflict.
* `Icompl` — the completeness invariant. Records the existentially
  quantified thread-pool and the `SafeTp` witness, plus the
  threadpool-authority ghost map from
  `Agar/Iris/Algebra/ThreadpoolRA.lean`.

What is not (yet) provided:

* **Lemma 14** (per-thread completeness, `Icompl ∗ n ↪γ t ⊢ wp_⊤ t Φ`)
  by Löb induction.
* **Theorem 15** (top-level completeness, `safe → wp`).

The shape and obstacles are documented in `COMPLETENESS.md`.
-/

namespace Agar

/-! ## Heap-freeness predicates

A statement is heap-free if it never executes a heap operation
(`load`/`store`/`alloc`/`free`/`cas`). Recursive over the constructors;
the call/fork cases delegate to the surrounding `Program.heapFree`. -/

def Stmt.heapFree : Stmt → Prop
  | .skip          => True
  | .assign _ _    => True
  | .load _ _      => False
  | .store _ _     => False
  | .alloc _ _     => False
  | .free _        => False
  | .cas _ _ _ _   => False
  | .seq s₁ s₂     => s₁.heapFree ∧ s₂.heapFree
  | .ite _ s₁ s₂   => s₁.heapFree ∧ s₂.heapFree
  | .whileDo _ s   => s.heapFree
  | .call _ _ _    => True
  | .ret _         => True
  | .fork _ _      => True

def Proc.heapFree (p : Proc) : Prop := p.body.heapFree

def Frame.heapFree (f : Frame) : Prop :=
  ∀ s ∈ f.cont, s.heapFree

def Thread.heapFree (t : Thread) : Prop :=
  t.stmt.heapFree ∧ (∀ s ∈ t.cont, s.heapFree) ∧ (∀ f ∈ t.stack, f.heapFree)

def Program.heapFree (p : Program) : Prop :=
  p.main.heapFree ∧ ∀ name proc, p.procs name = some proc → proc.heapFree

theorem Thread.heapFree_initial (s : Stmt) (h : s.heapFree) :
    (Thread.initial s).heapFree :=
  ⟨h, fun _ hmem => by simp [Thread.initial] at hmem, fun _ hmem => by
    simp [Thread.initial] at hmem⟩

namespace Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

/-! ## Step preservation under heap-freeness

A heap-free thread cannot fire any heap-modifying `tstep` branch, so
the operational memory is unchanged across a step. We prove this by
case analysis on `t.stmt`; heap-modifying branches contradict
`heapFree`, and every other branch leaves `m` alone. -/

/-- The operational memory is unchanged by a step of a heap-free thread.
With `chosen = none` the `alloc` branch is excluded by the chooser; the
remaining heap-modifying branches (`load/store/free/cas`) are excluded
by `heapFree`. -/
theorem tstep_heapFree_mem_unchanged
    {procs : Name → Option Proc} {m : Mem} {t : Thread}
    {m' : Mem} {t' : Thread} {sp : Option Thread}
    (htf : t.heapFree)
    (h : tstep procs none m t = some (m', t', sp)) :
    m' = m := by
  have hsf : t.stmt.heapFree := htf.1
  unfold tstep at h
  -- The outer match is on (none, t.stmt); only the `none, _` rows fire.
  split at h
  · -- some, alloc: contradicts chosen = none.
    contradiction
  · -- some, _: same.
    contradiction
  · -- none, alloc: contradicts hsf.
    exact (by simp_all [Stmt.heapFree] : False).elim
  · -- none, skip
    split at h
    · cases h; rfl
    · contradiction
    · simp only [doReturn] at h
      split at h <;> first
        | contradiction
        | (cases h; rfl)
        | (split at h <;> (cases h; rfl))
  · -- none, seq
    cases h; rfl
  · -- none, assign
    split at h
    · contradiction
    · cases h; rfl
  · -- none, load: contradicts hsf
    exact (by simp_all [Stmt.heapFree] : False).elim
  · -- none, store
    exact (by simp_all [Stmt.heapFree] : False).elim
  · -- none, free
    exact (by simp_all [Stmt.heapFree] : False).elim
  · -- none, cas
    exact (by simp_all [Stmt.heapFree] : False).elim
  · -- none, ite
    split at h <;> first | contradiction | (cases h; rfl)
  · -- none, whileDo
    cases h; rfl
  · -- none, call
    unfold callFrom at h
    split at h <;> first
      | contradiction
      | (split at h <;> (try (cases h; rfl)) <;> contradiction)
  · -- none, ret
    split at h
    · contradiction
    · simp [doReturn] at h
      split at h
      · cases h; rfl
      · split at h <;> (cases h; rfl)
  · -- none, fork
    split at h
    · split at h
      · cases h; rfl
      · contradiction
    all_goals contradiction

/-! ## The completeness invariant `Icompl`

Mirrors §3.2 of the paper:

```
I_compl ≜ ∃ ē, σ. ⌜safe-tp_φ(ē, σ)⌝ ∗ •^γ ē ∗ ⊛_{(ℓ↦v)∈σ} ℓ ↦ v
```

For the heap-free fragment, `σ = Mem.empty` always, so the big-sep is
`emp` and drops out. The invariant reduces to thread-pool tracking
plus the safe-tp pure witness. -/

section Icompl
variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [InvGS_gen false GF]

/-- The (heap-free specialised) completeness invariant body. -/
def Icompl_pure (prog : Program) (φ : Val → Prop) (γ : GName) : IProp GF :=
  iprop(∃ ts : List Thread,
    ⌜Machine.SafeTp prog ⟨Mem.empty, ts⟩ φ⌝ ∗
    threadpool_auth (GF := GF) (F := F) γ ts)

end Icompl

/-! ## Heap-freeness: chosen-none and step-preservation helpers -/

/-- A successful step on a heap-free thread can never come from a non-`none`
chooser. Allocation is excluded by `heapFree`, and only `alloc` consumes a
`some _` chooser; so the chooser must be `none`. -/
theorem tstep_heapFree_chosen_none
    {procs : Name → Option Proc} {chosen : Option Loc} {m : Mem} {t : Thread}
    {r : Mem × Thread × Option Thread}
    (htf : t.heapFree)
    (h : tstep procs chosen m t = some r) :
    chosen = none := by
  have hsf : t.stmt.heapFree := htf.1
  cases chosen with
  | none => rfl
  | some l =>
      exfalso
      obtain ⟨stmt, cont, env, stack, result⟩ := t
      simp only at hsf
      cases stmt <;> unfold tstep at h
      all_goals first | cases h | (exact hsf.elim) | (split at h <;> cases h)

/-- One step of a heap-free thread produces a heap-free post-state thread.
The step uses `chosen = none` (forced by `tstep_heapFree_chosen_none`).
This is needed to maintain the Löb induction hypothesis. -/
theorem tstep_heapFree_preserves
    {procs : Name → Option Proc} {m : Mem} {t : Thread}
    {m' : Mem} {t' : Thread} {sp : Option Thread}
    (htf : t.heapFree)
    (hprog : ∀ name proc, procs name = some proc → proc.heapFree)
    (h : tstep procs none m t = some (m', t', sp)) :
    t'.heapFree ∧ (∀ ts, sp = some ts → ts.heapFree) := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  obtain ⟨hsf, hcf, hstk⟩ := htf
  simp only at hsf hcf hstk
  have noSp : sp = none → ∀ ts, sp = some ts → ts.heapFree := by
    intro hsp ts hts; rw [hsp] at hts; cases hts
  cases stmt with
  | skip =>
    simp only [tstep] at h
    cases cont with
    | cons s rest =>
      simp only at h; cases h
      refine ⟨⟨hcf s List.mem_cons_self, fun s' hs' => hcf s' (List.mem_cons_of_mem _ hs'),
        hstk⟩, noSp rfl⟩
    | nil =>
      cases stack with
      | nil => cases h
      | cons fr rest =>
        simp only [doReturn] at h
        have hfrm : fr.heapFree := hstk fr List.mem_cons_self
        cases hfreq : fr.cont with
        | nil =>
          rw [hfreq] at h; simp only at h; cases h
          refine ⟨⟨trivial, ?_, ?_⟩, noSp rfl⟩
          · intro s hs; cases hs
          · intro f' hf'; exact hstk f' (List.mem_cons_of_mem _ hf')
        | cons s cs =>
          rw [hfreq] at h; simp only at h; cases h
          refine ⟨⟨?_, ?_, ?_⟩, noSp rfl⟩
          · exact hfrm _ (by rw [hfreq]; exact List.mem_cons_self)
          · intro c hc; exact hfrm _ (by rw [hfreq]; exact List.mem_cons_of_mem _ hc)
          · intro f' hf'; exact hstk f' (List.mem_cons_of_mem _ hf')
  | assign x e =>
    simp only [tstep] at h
    split at h
    · contradiction
    · cases h; exact ⟨⟨trivial, hcf, hstk⟩, noSp rfl⟩
  | load _ _ => exact hsf.elim
  | store _ _ => exact hsf.elim
  | alloc _ _ => exact hsf.elim
  | free _ => exact hsf.elim
  | cas _ _ _ _ => exact hsf.elim
  | seq s₁ s₂ =>
    simp only [tstep] at h; cases h
    have hs : s₁.heapFree ∧ s₂.heapFree := hsf
    refine ⟨⟨hs.1, ?_, hstk⟩, noSp rfl⟩
    intro s hs'
    cases hs' with
    | head => exact hs.2
    | tail _ hs'' => exact hcf _ hs''
  | ite e s₁ s₂ =>
    simp only [tstep] at h
    have hs : s₁.heapFree ∧ s₂.heapFree := hsf
    split at h
    · cases h; exact ⟨⟨hs.1, hcf, hstk⟩, noSp rfl⟩
    · cases h; exact ⟨⟨hs.2, hcf, hstk⟩, noSp rfl⟩
    · contradiction
  | whileDo e s =>
    simp only [tstep] at h; cases h
    have hs : s.heapFree := hsf
    refine ⟨⟨?_, hcf, hstk⟩, noSp rfl⟩
    exact ⟨⟨hs, hs⟩, trivial⟩
  | call x f args =>
    simp only [tstep, callFrom] at h
    cases heqp : procs f with
    | none => rw [heqp] at h; cases h
    | some proc =>
      rw [heqp] at h
      cases heval : evalArgs env args with
      | none => rw [heval] at h; cases h
      | some vs =>
        rw [heval] at h
        change (if vs.length = proc.params.length then _ else _) = _ at h
        by_cases hlen : vs.length = proc.params.length
        · rw [if_pos hlen] at h; cases h
          have hpf : proc.heapFree := hprog _ _ heqp
          refine ⟨⟨hpf, ?_, ?_⟩, noSp rfl⟩
          · intro s hs; cases hs
          · intro fr hfr
            cases hfr with
            | head => intro s hs; exact hcf s hs
            | tail _ h' => exact hstk _ h'
        · rw [if_neg hlen] at h; cases h
  | ret e =>
    simp only [tstep] at h
    split at h
    · contradiction
    · simp only [doReturn] at h
      cases stack with
      | nil =>
        simp only at h; cases h
        refine ⟨⟨trivial, ?_, ?_⟩, noSp rfl⟩
        · intro s hs; cases hs
        · intro f' hf'; cases hf'
      | cons fr rest =>
        have hfrm : fr.heapFree := hstk fr List.mem_cons_self
        simp only at h
        cases hfreq : fr.cont with
        | nil =>
          rw [hfreq] at h; simp only at h; cases h
          refine ⟨⟨trivial, ?_, ?_⟩, noSp rfl⟩
          · intro s hs; cases hs
          · intro f' hf'; exact hstk f' (List.mem_cons_of_mem _ hf')
        | cons s cs =>
          rw [hfreq] at h; simp only at h; cases h
          refine ⟨⟨?_, ?_, ?_⟩, noSp rfl⟩
          · exact hfrm _ (by rw [hfreq]; exact List.mem_cons_self)
          · intro c hc; exact hfrm _ (by rw [hfreq]; exact List.mem_cons_of_mem _ hc)
          · intro f' hf'; exact hstk f' (List.mem_cons_of_mem _ hf')
  | fork f args =>
    simp only [tstep] at h
    cases heqp : procs f with
    | none => rw [heqp] at h; cases h
    | some proc =>
      rw [heqp] at h
      cases heval : evalArgs env args with
      | none => rw [heval] at h; cases h
      | some vs =>
        rw [heval] at h
        change (if vs.length = proc.params.length then _ else _) = _ at h
        by_cases hlen : vs.length = proc.params.length
        · rw [if_pos hlen] at h; cases h
          refine ⟨⟨trivial, hcf, hstk⟩, ?_⟩
          intro ts hts
          cases hts
          have hpf : proc.heapFree := hprog _ _ heqp
          refine ⟨hpf, ?_, ?_⟩
          · intro _ hh; cases hh
          · intro _ hh; cases hh
        · rw [if_neg hlen] at h; cases h

/-! ## m-independence of `tstep` for heap-free threads

For heap-free threads, `tstep` neither reads nor writes the operational
memory — it just threads `m` through unchanged. The next lemma proves
this substitution principle: if the step succeeds at `m₁`, the same
post-thread/spawn pair is produced when run at any `m₂`. This is the
load-bearing fact for `percomplete`'s step branch: `SafeTp.here` gives
reducibility at the invariant's pinned `Mem.empty`, and we transport
it to whichever `m` the `wp_pre` happens to hand us. -/

theorem tstep_heapFree_subst_m
    {procs : Name → Option Proc} {t : Thread} (htf : t.heapFree)
    {m₁ m₂ : Mem} {t' : Thread} {sp : Option Thread}
    (h : tstep procs none m₁ t = some (m₁, t', sp)) :
    tstep procs none m₂ t = some (m₂, t', sp) := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  have hsf : stmt.heapFree := htf.1
  cases stmt with
  | skip =>
    simp only [tstep] at h ⊢
    match hc : cont, h with
    | s :: rest, h => cases h; rfl
    | [], h =>
      match hstk : stack, h with
      | [], h => cases h
      | fr :: rest, h =>
        simp only [doReturn] at h ⊢
        match hfc : fr.cont, h with
        | [], h => cases h; rfl
        | s :: cs, h => cases h; rfl
  | assign x e =>
    simp only [tstep] at h ⊢
    match hev : Expr.eval env e, h with
    | none, h => cases h
    | some v, h => cases h; rfl
  | load _ _ => exact hsf.elim
  | store _ _ => exact hsf.elim
  | alloc _ _ => exact hsf.elim
  | free _ => exact hsf.elim
  | cas _ _ _ _ => exact hsf.elim
  | seq s₁ s₂ => simp only [tstep] at h ⊢; cases h; rfl
  | ite e s₁ s₂ =>
    simp only [tstep] at h ⊢
    match hev : Expr.eval env e, h with
    | none, h => cases h
    | some (.bool true), h => cases h; rfl
    | some (.bool false), h => cases h; rfl
    | some (.int _), h => cases h
    | some (.loc _), h => cases h
    | some .unit, h => cases h
    | some (.struct _), h => cases h
  | whileDo e s => simp only [tstep] at h ⊢; cases h; rfl
  | call x f args =>
    simp only [tstep, callFrom] at h ⊢
    match hpf : procs f, h with
    | none, h => cases h
    | some proc, h =>
      match hev : evalArgs env args, h with
      | none, h => cases h
      | some vs, h =>
        by_cases hlen : vs.length = proc.params.length
        · simp only [if_pos hlen] at h ⊢; cases h; rfl
        · simp only [if_neg hlen] at h; cases h
  | ret e =>
    simp only [tstep] at h ⊢
    match hev : Expr.eval env e, h with
    | none, h => cases h
    | some v, h =>
      simp only [doReturn] at h ⊢
      cases stack with
      | nil =>
        simp only at h ⊢; cases h; rfl
      | cons fr rest =>
        simp only at h ⊢
        cases hfc : fr.cont with
        | nil =>
          rw [hfc] at h; simp only at h ⊢; cases h; rfl
        | cons s cs =>
          rw [hfc] at h; simp only at h ⊢; cases h; rfl
  | fork f args =>
    simp only [tstep] at h ⊢
    match hpf : procs f, h with
    | none, h => cases h
    | some proc, h =>
      match hev : evalArgs env args, h with
      | none, h => cases h
      | some vs, h =>
        by_cases hlen : vs.length = proc.params.length
        · simp only [if_pos hlen] at h ⊢; cases h; rfl
        · simp only [if_neg hlen] at h; cases h

/-- m-independent reducibility for heap-free threads. -/
theorem thread_reducible_heapFree_subst_m
    {procs : Name → Option Proc} {t : Thread} (htf : t.heapFree)
    {m₁ m₂ : Mem} (h : thread_reducible procs m₁ t) :
    thread_reducible procs m₂ t := by
  obtain ⟨m₁', t', sp, chosen, hstep⟩ := h
  have hchosen : chosen = none := tstep_heapFree_chosen_none htf hstep
  subst hchosen
  have hm' : m₁' = m₁ := tstep_heapFree_mem_unchanged htf hstep
  subst hm'
  exact ⟨m₂, t', sp, none, tstep_heapFree_subst_m htf hstep⟩

/-! ## Helpers around `Thread.toValue` / `terminated` -/

theorem Thread.toValue_of_terminated' {t : Thread} (h : t.terminated = true) :
    ∃ v, t.toValue = some v := by
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  unfold Thread.terminated at h
  unfold Thread.toValue
  cases stmt <;> (try cases h)
  all_goals (cases cont <;> (try cases h))
  all_goals (cases stack <;> (try cases h))
  exact ⟨_, rfl⟩

theorem Thread.terminated_false_of_toValue_none {t : Thread}
    (h : t.toValue = none) : t.terminated = false := by
  unfold Thread.toValue at h
  unfold Thread.terminated
  split at h <;> simp_all

theorem Thread.terminated_of_toValue {t : Thread} {v : Val}
    (h : t.toValue = some v) : t.terminated = true := by
  unfold Thread.toValue at h
  unfold Thread.terminated
  split at h <;> simp_all

/-! ## Per-thread completeness post

The post-condition used by Lemma 14 and consumed by Theorem 15: a
thread terminating with value `v` has its ghost-map slot updated to a
terminal thread whose `toValue` is `v`. -/

section PostDef

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F]

/-- The percomplete post-condition. -/
@[reducible] def percomplete_post (γ : GName) (n : Nat) : Val → IProp GF :=
  fun v => iprop(∃ t' : Thread, thread_at (GF := GF) (F := F) γ n t' ∗
                                  ⌜t'.toValue = some v⌝)

/-- The post-weakening wand target: from any value `v`, the
post-condition implies the user-facing `⌜φ v⌝`. -/
def post_weaken_wand (γ : GName) (φ : Val → Prop) : IProp GF :=
  iprop(∀ (v : Val), percomplete_post (GF := GF) (F := F) γ 0 v -∗
                       ⌜φ v⌝)

end PostDef

/-! ## `wp_wand`: iprop-level post weakening

Iris' `wp_wand` lifts an iprop wand `∀ v, Φ v -∗ Ψ v` through a WP, in
contrast to `wp_mono` which only accepts a Lean-level pointwise
entailment. Provable by Löb induction over a generalised thread index,
in the same shape as `wp_mono`.

This is what `Theorem 15` uses to weaken `percomplete`'s output post
into the paper-shape `⌜φ v⌝`. -/

section WpWand

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF] [StateInterp GF]
variable {E : CoPset}

theorem wp_wand (procs : Name → Option Proc) (fork_post : IProp GF)
    {Φ Ψ : Val → IProp GF} (t : Thread) :
    iprop(wp procs fork_post E t Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢
      wp procs fork_post E t Ψ := by
  suffices key : (True : IProp GF) ⊢ iprop(∀ (t' : Thread),
      wp procs fork_post E t' Φ ∗ (∀ v, Φ v -∗ Ψ v) -∗
        wp procs fork_post E t' Ψ) by
    exact BI.wand_entails
      (BI.true_intro.trans (key.trans (BI.forall_elim t)))
  apply BILoeb.loeb_weak
  iintro IH
  iintro %t' ⟨HW, Hwand⟩
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
      iapply Hwand $$ %v
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
    iapply IH $$ %t''
    iframe HWt' Hwand

/-- Fupd-variant of `wp_wand`. The wand may produce a fupd of the new
post, which is absorbed via the value-branch's `|={E}=>` shape. -/
theorem wp_wand_fupd (procs : Name → Option Proc) (fork_post : IProp GF)
    {Φ Ψ : Val → IProp GF} (t : Thread) :
    iprop(wp procs fork_post E t Φ ∗ (∀ v, Φ v -∗ |={E}=> Ψ v)) ⊢
      wp procs fork_post E t Ψ := by
  suffices key : (True : IProp GF) ⊢ iprop(∀ (t' : Thread),
      wp procs fork_post E t' Φ ∗ (∀ v, Φ v -∗ |={E}=> Ψ v) -∗
        wp procs fork_post E t' Ψ) by
    exact BI.wand_entails
      (BI.true_intro.trans (key.trans (BI.forall_elim t)))
  apply BILoeb.loeb_weak
  iintro IH
  iintro %t' ⟨HW, Hwand⟩
  ihave HW' :=
    (equiv_iff.mp (wp_unfold procs fork_post E t' Φ)).mp $$ HW
  iapply (equiv_iff.mp (wp_unfold procs fork_post E t' Ψ)).mpr
  icases HW' with ⟨⟨%v, %hterm, HΦ⟩ | ⟨%hnt, Hsteps⟩⟩
  · ileft
    iexists v
    isplitr
    · ipure_intro; exact hterm
    · imod HΦ with HΦv
      ihave HΨ := Hwand $$ %v HΦv
      imod HΨ with HΨv
      imodintro
      iexact HΨv
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
    iapply IH $$ %t''
    iframe HWt' Hwand

end WpWand

/-! ## `icompl_pure_lookup`: pure-fact extraction from the invariant

Shared infrastructure for the two consumers `weaken_post` and
`percomplete`. From `▷ Icompl_pure ∗ thread_at γ n t`, extract the
pure conclusion that some `ts` exists with `SafeTp` for it and
`ts[n]? = some t` — while preserving the inputs for later use.

The conclusion is wrapped in `|={E}=>` because pure-fact extraction
from `▷` proceeds via `Timeless` + `⋄`, which is absorbed cleanly
inside a fancy update. Both consumers will already be in a fupd
context (opened invariants), so this shape is convenient. -/

section IcomplLookup

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [InvGS_gen false GF]

/-- Pre-built Lean-level entailment that unfolds `▷ Icompl_pure` into
the existential form, so the proof-mode steps don't need to fight the
`Icompl_pure` definition. -/
private theorem icompl_pure_unfold_later
    {prog : Program} {φ : Val → Prop} (γ : GName) :
    iprop(▷ Icompl_pure (GF := GF) (F := F) prog φ γ) ⊢
      iprop(∃ ts : List Thread,
              ▷ (⌜Machine.SafeTp prog ⟨Mem.empty, ts⟩ φ⌝ ∗
                  threadpool_auth (GF := GF) (F := F) γ ts)) := by
  unfold Icompl_pure
  exact (later_exists (α := List Thread)
    (Φ := fun ts => iprop(⌜Machine.SafeTp prog ⟨Mem.empty, ts⟩ φ⌝ ∗
            threadpool_auth (GF := GF) (F := F) γ ts))).mpr

theorem icompl_pure_lookup
    {E : CoPset}
    {prog : Program} {φ : Val → Prop} {γ : GName} {n : Nat} {t : Thread} :
    iprop(▷ Icompl_pure (GF := GF) (F := F) prog φ γ ∗
          thread_at (GF := GF) (F := F) γ n t) ⊢
      iprop(|={E}=>
        ∃ ts : List Thread,
          ⌜Machine.SafeTp prog ⟨Mem.empty, ts⟩ φ ∧ ts[n]? = some t⌝ ∗
          ▷ threadpool_auth (GF := GF) (F := F) γ ts ∗
          thread_at (GF := GF) (F := F) γ n t) := by
  istart
  iintro ⟨HIbody, Hn⟩
  -- Unfold the invariant body into the post-later-commuted form.
  ihave HIbody2 := icompl_pure_unfold_later γ $$ HIbody
  icases HIbody2 with ⟨%ts, HIbody3⟩
  -- HIbody3 : ▷ (⌜SafeTp ⟨Mem.empty, ts⟩ φ⌝ ∗ threadpool_auth γ ts)
  ihave HIbody4 := BI.later_sep.mp $$ HIbody3
  icases HIbody4 with ⟨Hsafe_l, Hauth_l⟩
  -- Extract the pure SafeTp via timelessness + fupd absorption.
  imod Hsafe_l with %hsafe
  -- Push thread_at under ▷ to combine with Hauth_l. Both will be
  -- extracted via timeless inside the surrounding fupd at the end.
  ihave Hn_l := (BI.later_intro (P := iprop(thread_at (GF := GF) (F := F) γ n t)))
                  $$ Hn
  -- Combine into a single ▷-block, apply framed lookup under ▷.
  have combine_lookup : iprop(▷ threadpool_auth (GF := GF) (F := F) γ ts ∗
                              ▷ thread_at (GF := GF) (F := F) γ n t) ⊢
      iprop(▷ ⌜ts[n]? = some t⌝ ∗
            ▷ threadpool_auth (GF := GF) (F := F) γ ts ∗
            ▷ thread_at (GF := GF) (F := F) γ n t) := by
    refine .trans BI.later_sep.mpr ?_
    refine .trans (BI.later_mono (threadpool_lookup_frame γ ts n t)) ?_
    refine .trans BI.later_sep.mp ?_
    refine BI.sep_mono .rfl ?_
    exact BI.later_sep.mp
  ihave Hpacked := combine_lookup $$ [Hauth_l Hn_l]
  · isplitl [Hauth_l]
    · iexact Hauth_l
    · iexact Hn_l
  icases Hpacked with ⟨Hpure_l, Hauth_l', Hn_l'⟩
  imod Hpure_l with %hlk
  imod Hn_l' with Hn'
  -- Build the conclusion.
  iapply fupd_intro
  iexists ts
  isplitr
  · ipure_intro; exact ⟨hsafe, hlk⟩
  isplitl [Hauth_l']
  · iexact Hauth_l'
  · iexact Hn'

/-- A terminated thread is not reducible (its `tstep` returns `none`). -/
theorem thread_terminated_not_reducible
    {procs : Name → Option Proc} {m : Mem} {t : Thread}
    (h : t.terminated = true) : ¬ thread_reducible procs m t := by
  rintro ⟨m', t'', sp, chosen, hstep⟩
  obtain ⟨stmt, cont, env, stack, result⟩ := t
  unfold Thread.terminated at h
  -- Only the `skip, [], []` form is terminated; any other gives `false = true`.
  cases stmt <;> first | cases h | skip
  case skip =>
    cases cont <;> first | cases h | skip
    case nil =>
      cases stack <;> first | cases h | skip
      case nil =>
        -- Now tstep with chosen=none, skip, [], [] is none.
        cases chosen <;> simp [tstep] at hstep

/-! ## `weaken_post`: deriving `⌜φ v⌝` from the invariant at index 0

Combines `icompl_pure_lookup` + `Machine.SafeTp.here` at index 0 + the
contradiction "terminated thread is not reducible" to extract `φ v`
from the threadpool fragment at the main thread's slot. This is the
post-weakening wand consumed by Theorem 15 via `wp_wand_fupd`. -/

section Weaken
variable [AgarG GF F]

theorem weaken_post_proof
    {prog : Program} {φ : Val → Prop} (γ : GName) (N : Namespace) :
    inv N (Icompl_pure (GF := GF) (F := F) prog φ γ) ⊢
      iprop(∀ (v : Val), percomplete_post (GF := GF) (F := F) γ 0 v -∗
              |={⊤}=> ⌜φ v⌝) := by
  istart
  iintro #HI
  iintro %v
  iintro Hpost
  -- Hpost : ∃ t', thread_at γ 0 t' ∗ ⌜t'.toValue = some v⌝
  icases Hpost with ⟨%t', Hn, %hv⟩
  -- Open the invariant.
  imod (inv_acc (⊤ : CoPset) N _ (fun _ _ => CoPset.mem_full)) $$ HI
    with ⟨HIbody, Hclose⟩
  -- Use icompl_pure_lookup to derive ⌜SafeTp ∧ ts[0]? = some t'⌝.
  imod (icompl_pure_lookup (E := ⊤ \ ↑N)) $$ [HIbody Hn]
    with ⟨%ts, %hSL, Hauth_l, Hn'⟩
  · isplitl [HIbody]
    · iexact HIbody
    · iexact Hn
  obtain ⟨hsafe, hlk⟩ := hSL
  -- Apply SafeTp.here at index 0.
  have hvr := Machine.SafeTp.here hsafe (k := 0) (t := t')
                (show (⟨Mem.empty, ts⟩ : Machine).threads[0]? = some t' from hlk)
  -- Extract φ v from the value-disjunct (reducibility contradicts hv).
  have hφ : φ v := by
    rcases hvr with ⟨v', hv', himpl⟩ | hred
    · -- v' = v from hv and hv'.
      have heq : v = v' := by rw [hv] at hv'; injection hv'
      subst heq; exact himpl rfl
    · -- t' is terminated (toValue = some v), so it can't be reducible.
      exact absurd hred
        (thread_terminated_not_reducible (Thread.terminated_of_toValue hv))
  -- Close the invariant.
  imod Hclose $$ [Hauth_l]
  · -- Need ▷ Icompl_pure prog φ γ.
    inext
    unfold Icompl_pure
    iexists ts
    isplitr
    · ipure_intro; exact hsafe
    · iexact Hauth_l
  imodintro
  ipure_intro; exact hφ

end Weaken

end IcomplLookup

/-! ## Theorem 15: completeness modulo Lemma 14

Allocates the heap, threadpool ghost map, and completeness invariant;
applies the (hypothesized) per-thread completeness lemma at the main
thread; weakens the resulting WP post via `wp_wand` to deliver the
paper-shape `⌜φ v⌝` post.

Lemma 14 is taken as a hypothesis. The post-weakening from
`percomplete_post γ 0 v` to `⌜φ v⌝` is left as a wand parameter
`weaken_post`, since it requires the same `▷`-commutation machinery as
Lemma 14's step case. With both Lemma 14 and `weaken_post` discharged,
Theorem 15 follows by the allocation + bookkeeping below. -/

/-! ## `percomplete`: Lemma 14 (per-thread completeness, heap-free)

The Löb induction. Given the completeness invariant + a threadpool
fragment for the current thread, derive its WP with `percomplete_post`
as the value-post. The proof case-splits on whether the thread is
terminated (value branch — trivial via `Hn` and `Thread.toValue`) or
about to step (step branch).

The step branch uses every helper we've built:
* `icompl_pure_lookup` to extract `ts`, `SafeTp`, and `ts[n']? = some t'`
* `Machine.SafeTp.here` + `thread_terminated_not_reducible` to derive
  reducibility at `Mem.empty`
* `thread_reducible_heapFree_subst_m` to transport to the wp's `m`
* `tstep_heapFree_{chosen_none, mem_unchanged, subst_m, preserves}` to
  validate and normalise the step
* `threadpool_update` (no fork) / `threadpool_insert` (fork) to update
  the ghost map
* `Machine.SafeTp.step_closed` to update the safety witness
* The Löb IH to recurse on the new parent thread (and the new child for
  fork). -/

section PerCompleteSec
open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarG GF F] [InvGS_gen false GF]

theorem percomplete
    {prog : Program} {φ : Val → Prop} (hpf : prog.heapFree)
    (γ : GName) (N : Namespace)
    (n : Nat) (t : Thread) (htf : t.heapFree) :
    inv N (Icompl_pure (GF := GF) (F := F) prog φ γ) ∗
    thread_at (GF := GF) (F := F) γ n t ⊢
      wp prog.procs (iprop(True : IProp GF)) ⊤ t
        (percomplete_post (GF := GF) (F := F) γ n) := by
  -- Internalise (n, t, t.heapFree) as iprop quantifiers for Löb.
  suffices key : ⊢ (iprop(
      ∀ (n' : Nat), (∀ (t' : Thread), (⌜t'.heapFree⌝ →
        (inv N (Icompl_pure (GF := GF) (F := F) prog φ γ) -∗
        (thread_at (GF := GF) (F := F) γ n' t' -∗
        wp prog.procs (iprop(True : IProp GF)) ⊤ t'
          (percomplete_post (GF := GF) (F := F) γ n')))))) : IProp GF) by
    have s1 := (key.trans (BI.forall_elim n)).trans (BI.forall_elim t)
    have hpure : (True : IProp GF) ⊢ iprop(⌜t.heapFree⌝) := BI.pure_intro htf
    have s2 : (True : IProp GF) ⊢ iprop(
        inv N (Icompl_pure (GF := GF) (F := F) prog φ γ) -∗
        thread_at (GF := GF) (F := F) γ n t -∗
        wp prog.procs (iprop(True : IProp GF)) ⊤ t
          (percomplete_post (GF := GF) (F := F) γ n)) :=
      (BI.and_intro s1 hpure).trans BI.imp_elim_l
    refine BI.wand_entails ?_
    exact s2.trans BI.wand_curry.1
  iloeb as IH
  iintro %n' %t' %htf' #HI Hn
  iapply (equiv_iff.mp (wp_unfold prog.procs (iprop(True : IProp GF)) ⊤ t'
    (percomplete_post (GF := GF) (F := F) γ n'))).mpr
  by_cases hterm : t'.terminated = true
  · -- Value case.
    obtain ⟨v, hv⟩ : ∃ v, t'.toValue = some v :=
      Thread.toValue_of_terminated' hterm
    ileft
    iexists v
    isplitr
    · ipure_intro; exact hv
    · imodintro
      iexists t'
      isplitl [Hn]
      · iexact Hn
      · ipure_intro; exact hv
  · -- Step case.
    iright
    have hntn : t'.terminated = false := by
      cases h : t'.terminated <;> simp_all
    isplitr
    · ipure_intro; exact hntn
    iintro %m HS
    -- Open the invariant, extract pure facts.
    imod (inv_acc (⊤ : CoPset) N _ (fun _ _ => CoPset.mem_full)) $$ HI
      with ⟨HIbody, Hclose_inv⟩
    imod (icompl_pure_lookup (E := ⊤ \ ↑N)) $$ [HIbody Hn]
      with ⟨%ts, %hSL, Hauth_l, Hn_re⟩
    · isplitl [HIbody]
      · iexact HIbody
      · iexact Hn
    obtain ⟨hsafe, hlk⟩ := hSL
    -- Derive reducibility at Mem.empty, then transport to m.
    have hvr := Machine.SafeTp.here hsafe (k := n') (t := t')
                  (show (⟨Mem.empty, ts⟩ : Machine).threads[n']? = some t' from hlk)
    have hred_empty : thread_reducible prog.procs Mem.empty t' := by
      rcases hvr with ⟨v, hv', _⟩ | hred
      · have : t'.terminated = true := Thread.terminated_of_toValue hv'
        exact absurd this (by rw [hntn]; simp)
      · exact hred
    have hred_m : thread_reducible prog.procs m t' :=
      thread_reducible_heapFree_subst_m htf' hred_empty
    -- Mask shift to ∅.
    iapply fupd_mask_intro empty_subset
    iintro Hclose_mask
    isplitr
    · ipure_intro; exact hred_m
    iintro !> %m'' %t'' %sp %hstep
    -- Validate the step: chosen = none, m'' = m, transport to Mem.empty.
    obtain ⟨chosen, htstep⟩ := hstep
    have hchosen : chosen = none := tstep_heapFree_chosen_none htf' htstep
    subst hchosen
    have hm_un : m'' = m := tstep_heapFree_mem_unchanged htf' htstep
    subst hm_un
    have htstep_empty : tstep prog.procs none Mem.empty t' =
        some (Mem.empty, t'', sp) :=
      tstep_heapFree_subst_m htf' htstep
    -- New SafeTp via step_closed.
    have hsafe' : Machine.SafeTp prog
        ⟨Mem.empty, ts.set n' t'' ++ sp.toList⟩ φ := by
      refine Machine.SafeTp.step_closed hsafe ?_
      exact Machine.Step.step n' none t' t'' sp Mem.empty Mem.empty ts hlk
        htstep_empty
    -- Heap-free preservation on the post-step thread + spawn.
    have hpf_procs : ∀ name proc, prog.procs name = some proc → proc.heapFree :=
      hpf.2
    have hpreserved := tstep_heapFree_preserves htf' hpf_procs htstep
    have htf'' : t''.heapFree := hpreserved.1
    have htf_sp : ∀ ts_c, sp = some ts_c → ts_c.heapFree := hpreserved.2
    -- Close the ∅-mask shift.
    imod Hclose_mask
    -- Update the threadpool ghost map for the parent step.
    imod (threadpool_update γ ts n' t' t'' hlk) $$ [Hauth_l Hn_re]
      with ⟨Hauth', Hn'⟩
    · isplitl [Hauth_l]
      · iexact Hauth_l
      · iexact Hn_re
    -- Branch on fork.
    cases hsp_eq : sp with
    | none =>
      -- Pure-step case: no fork.
      have hts_eq : ts.set n' t'' ++ Option.toList none = ts.set n' t'' := by
        simp [Option.toList]
      rw [hsp_eq, hts_eq] at hsafe'
      -- Re-close the invariant with the new ts.
      imod (Hclose_inv) $$ [Hauth']
      · inext
        unfold Icompl_pure
        iexists (ts.set n' t'')
        isplitr
        · ipure_intro; exact hsafe'
        · iexact Hauth'
      imodintro
      iframe HS
      isplitl [Hn']
      · -- Apply IH at (n', t'').
        ihave IH_inst := IH $$ %n' %t''
        iapply IH_inst
        · ipure_intro; exact htf''
        · iexact HI
        · iexact Hn'
      · iintro %ts_c %hsp_c
        cases hsp_c
    | some t_child =>
      -- Fork case: also insert the child.
      have htf_child : t_child.heapFree := htf_sp t_child hsp_eq
      have hts_eq : ts.set n' t'' ++ Option.toList (some t_child)
                  = ts.set n' t'' ++ [t_child] := by
        simp [Option.toList]
      rw [hsp_eq, hts_eq] at hsafe'
      -- Insert child into threadpool ghost.
      imod (threadpool_insert γ (ts.set n' t'') t_child) $$ Hauth'
        with ⟨Hauth'', Hchild⟩
      -- Re-close the invariant with the new ts.
      imod (Hclose_inv) $$ [Hauth'']
      · inext
        unfold Icompl_pure
        iexists (ts.set n' t'' ++ [t_child])
        isplitr
        · ipure_intro; exact hsafe'
        · iexact Hauth''
      imodintro
      iframe HS
      isplitl [Hn']
      · ihave IH_inst := IH $$ %n' %t''
        iapply IH_inst
        · ipure_intro; exact htf''
        · iexact HI
        · iexact Hn'
      · iintro %ts_c %hsp_c
        cases hsp_c
        -- Forked-thread WP with post `fun _ => True`. Apply IH at the
        -- new index, weaken via wp_wand with a trivial wand.
        iapply wp_wand prog.procs (iprop(True : IProp GF))
          (Φ := percomplete_post (GF := GF) (F := F) γ
                  (ts.set n' t'').length)
          (Ψ := fun _ => iprop(True : IProp GF))
          t_child
        isplitl [Hchild]
        · ihave IH_inst := IH $$ %(ts.set n' t'').length %t_child
          iapply IH_inst
          · ipure_intro; exact htf_child
          · iexact HI
          · iexact Hchild
        · iintro %v _
          itrivial

end PerCompleteSec

section Theorem15

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF]

/-- **Theorem 15 (Completeness) — modulo Lemma 14 and the
post-weakening wand.** From `∀ σ, Machine.safeFrom prog σ φ` we
construct a closed Iris derivation of
`wp_⊤ (Thread.initial prog.main) {v. ⌜φ v⌝}`, allocating the heap,
threadpool, and completeness invariant along the way.

Two hypotheses encapsulate the remaining work:
* `percomplete` — Lemma 14: per-thread completeness for heap-free
  threads.
* `weaken_post` — the post-weakening wand: from the threadpool
  fragment and the SafeTp witness in the invariant, derive `⌜φ v⌝`
  at the value. Both reduce to the same `▷`-extraction technique. -/
theorem completeness_modulo_lemma14
    {prog : Program} {φ : Val → Prop} (hpf : prog.heapFree)
    (hs : ∀ σ, Machine.safeFrom prog σ φ)
    (percomplete : ∀ [_LC : InvGS_gen false GF] [_G : AgarG GF F]
        (γ : GName) (N : Namespace) (n : Nat) (t : Thread), t.heapFree →
        inv N (Icompl_pure (GF := GF) (F := F) prog φ γ) ∗
        thread_at (GF := GF) (F := F) γ n t ⊢
          wp prog.procs (iprop(True : IProp GF)) ⊤ t
            (percomplete_post γ n))
    (weaken_post : ∀ [_LC : InvGS_gen false GF] [_G : AgarG GF F]
        (γ : GName) (N : Namespace),
        inv N (Icompl_pure (GF := GF) (F := F) prog φ γ) ⊢
          iprop(∀ (v : Val),
            percomplete_post (GF := GF) (F := F) γ 0 v -∗
              |={⊤}=> ⌜φ v⌝)) :
    ∀ [_LC : InvGS_gen false GF],
      ⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
        state_interp (GF := GF) Mem.empty ∗
        wp prog.procs fork_post ⊤ (Thread.initial prog.main)
          (fun v => iprop(⌜φ v⌝ : IProp GF)) := by
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, Hheap⟩
  -- G : AgarG GF F, Hheap : heap_auth Mem.empty
  letI : AgarG GF F := G
  -- Allocate threadpool.
  imod (threadpool_init (GF := GF) (F := F) (Thread.initial prog.main))
    with ⟨%γ, Hpool⟩
  icases Hpool with ⟨Hauth, Hn⟩
  -- Establish initial SafeTp witness.
  have hsafe_init : Machine.SafeTp prog
      ⟨Mem.empty, [Thread.initial prog.main]⟩ φ := hs Mem.empty
  -- Pre-build the invariant body.
  have build_body : iprop(threadpool_auth (GF := GF) (F := F) γ
                          [Thread.initial prog.main]) ⊢
      iprop(Icompl_pure (GF := GF) (F := F) prog φ γ) := by
    unfold Icompl_pure
    istart
    iintro Hauth
    iexists [Thread.initial prog.main]
    isplitr
    · ipure_intro; exact hsafe_init
    · iexact Hauth
  ihave HIbody := build_body $$ Hauth
  -- Lift to ▷ (needed by inv_alloc).
  ihave HIbody_later := (BI.later_intro (P := iprop(Icompl_pure (GF := GF) (F := F)
                                                    prog φ γ))) $$ HIbody
  -- Allocate the invariant.
  imod (inv_alloc nroot (⊤ : CoPset) _) $$ HIbody_later with HI
  ihave #HI := HI
  -- Apply percomplete at (0, Thread.initial prog.main).
  have hmain_hf : (Thread.initial prog.main).heapFree :=
    Thread.heapFree_initial prog.main hpf.1
  ihave Hwp := percomplete γ nroot 0 (Thread.initial prog.main) hmain_hf
    $$ [HI Hn]
  · isplitl [HI] <;> iassumption
  -- Weaken the post via the wand to ⌜φ v⌝.
  ihave Hwand := weaken_post γ nroot $$ HI
  ihave Hfinal := wp_wand_fupd (GF := GF) prog.procs (iprop(True : IProp GF))
    (Φ := percomplete_post γ 0)
    (Ψ := fun v => iprop(⌜φ v⌝ : IProp GF))
    (Thread.initial prog.main) $$ [Hwp Hwand]
  · isplitl [Hwp]
    · iexact Hwp
    · iexact Hwand
  -- Provide existentials and close.
  iapply fupd_intro
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists (iprop(True : IProp GF))
  isplitl [Hheap]
  · iexact Hheap
  · iexact Hfinal

end Theorem15

/-! ## Theorem 15: Completeness (full statement)

Specialises `completeness_modulo_lemma14` by discharging the two
hypotheses with the proven `percomplete` (Lemma 14) and
`weaken_post_proof`. The conclusion is in Iris-Lean fupd shape — to
match `wp_safe_bupd`'s bupd shape, the caller can lift via
`BIUpdate.bupd_fupd` (bupd ⊆ fupd) or instantiate adequacy with the
fupd form. -/

section Theorem15Full
open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
  [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF]

/-- **Theorem 15 (Completeness, full).** From `∀ σ, Machine.safeFrom
prog σ φ` for a heap-free program, produce a closed Iris derivation of
`wp_⊤ (Thread.initial prog.main) {v. ⌜φ v⌝}` over freshly-allocated
heap and threadpool ghost state. -/
theorem completeness
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F]
    [TpGpreS GF F] [AgarGpreS GF F] [InvGpreS GF]
    {prog : Program} {φ : Val → Prop} (hpf : prog.heapFree)
    (hs : ∀ σ, Machine.safeFrom prog σ φ) :
    ∀ [_LC : InvGS_gen false GF],
      ⊢ |={⊤}=> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
        state_interp (GF := GF) Mem.empty ∗
        wp prog.procs fork_post ⊤ (Thread.initial prog.main)
          (fun v => iprop(⌜φ v⌝ : IProp GF)) := by
  apply completeness_modulo_lemma14 (GF := GF) (F := F) hpf hs
  · intro _ _ γ N n t htf
    exact percomplete hpf γ N n t htf
  · intro _ _ γ N
    exact weaken_post_proof γ N

end Theorem15Full

end Logic
end Agar

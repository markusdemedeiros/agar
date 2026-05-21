module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import Iris.Std.CoPset
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd
public import Iris.BI.BigOp.BigSepList
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Heap

@[expose] public section

/-! # Adequacy of the Agar WP

The final theorem `wp_strong_adequacy` connects the threadwise `wp` to
actual machine-level guarantees over `Machine.StepStarN` (the n-step
closure of `Machine.Step`, including forks):

1. **per-thread safety** — every thread in the reachable pool is either
   terminated or reducible (no thread is ever stuck), and
2. **main-thread postcondition** — if the main thread (position 0)
   terminated with value `v`, then `φ v` (a pure `Val → Prop`).

The proof factors through three pieces:

* `wp_step_sound` — unfolds the WP once, exchanging a `thread_step`
  for a `|={⊤}[∅]▷=> (state_interp m' ∗ wp t' Φ ∗ fork-witness)`.
* `pool_wp` — the thread-pool invariant: position 0 carries `Φ`, every
  other thread carries `(fun _ => fork_post)`. `wp_machine_step_sound`
  preserves it across one `Machine.Step` (forks append the new thread
  via `bigSepL_append`).
* `pool_safe` / `pool_main_post` — extract the pure per-thread safety
  and main-thread postcondition from `pool_wp` at termination.

Soundness routes through `step_fupdN_soundness_no_lc'` from upstream
`Iris.Instances.Lib.FUpd`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

/-- n-step closure of `Machine.Step` (full step relation, including
forks). -/
inductive Machine.StepStarN (p : Program) :
    Nat → Machine → Machine → Prop where
  | refl (μ : Machine) : Machine.StepStarN p 0 μ μ
  | step {n : Nat} {μ μ' μ'' : Machine}
      (h1 : Machine.Step p μ μ')
      (h2 : Machine.StepStarN p n μ' μ'') :
      Machine.StepStarN p n.succ μ μ''

/-! ## The single-step soundness lemma -/

section StepSound

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF] [StateInterp GF]
variable (procs : Name → Option Proc) (fork_post : IProp GF)

/-- Single-step soundness: if `t` is *not yet terminated* (i.e. takes a
real step `thread_step`), then `state_interp m ∗ wp t Φ` plus the
operational step witness produce a step-fupd to the post-step state
interpretation, post-step WP, and (possibly) a forked-thread WP. -/
theorem wp_step_sound
    (m m' : Mem) (t t' : Thread) (sp : Option Thread)
    (Φ : Val → IProp GF) (hstep : thread_step procs m t m' t' sp) :
    state_interp (GF := GF) m ∗ wp procs fork_post CoPset.full t Φ ⊢
      iprop(|={⊤}[∅]▷=>
        (state_interp m' ∗ wp procs fork_post CoPset.full t' Φ ∗
          (∀ (ts : Thread), ⌜sp = some ts⌝ -∗
             wp procs fork_post CoPset.full ts (fun _ => fork_post)))) := by
  -- Unfold the WP and pick the step branch.
  istart
  iintro ⟨HS, HW⟩
  ihave HW' := (equiv_iff.mp (wp_unfold procs fork_post CoPset.full t Φ)).mp $$ HW
  icases HW' with ⟨⟨%v, %hterm, _⟩ | ⟨%hnt, Hsteps⟩⟩
  · -- Terminated thread cannot step — contradicts `hstep`.
    exfalso
    obtain ⟨chosen, hstep''⟩ := hstep
    obtain ⟨stmt, cont, env, stack, result⟩ := t
    -- `t.toValue = some v` forces stmt = .skip, cont = [], stack = [].
    unfold Thread.toValue at hterm
    -- Now hterm is a match expression on (stmt, cont, stack); only the
    -- (skip, [], []) arm gives `some _`, so all other arms force `cases hterm`.
    -- We just need to discharge that one terminal arm by stepping `tstep`.
    cases stmt <;> (try cases hterm)
    all_goals (cases cont <;> (try cases hterm))
    all_goals (cases stack <;> (try cases hterm))
    -- Only (skip, [], []) survives. Now step is impossible.
    cases chosen with
    | some l => simp [tstep] at hstep''
    | none => simp [tstep] at hstep''
  · -- Non-terminated case: feed the step.
    -- `Hsteps : ∀ m, state_interp m ={⊤,∅}=∗`
    --          `⌜red⌝ ∗ ▷ ∀ …, ⌜step⌝ ={∅,⊤}=∗ …`.
    -- Goal: `|={⊤}[∅]▷=> (state_interp m' ∗ wp t' Φ ∗ Fork)`
    --     = `|={⊤,∅}=> ▷ |={∅,⊤}=> (…)`.
    ispecialize Hsteps $$ %m
    imod Hsteps $$ HS with ⟨_, HsRest⟩
    imodintro
    iintro !>
    iapply HsRest $$ %m' %t' %sp %hstep

end StepSound

/-! ## Step-fupd tower helpers and termination extraction -/

section AdequacyHelpers

/-! ### Step-fupd tower monotonicity

A small generic helper: applying a single entailment `P ⊢ Q` inside the
innermost layer of an n-step-fupd tower is monotone. -/

variable {GF : BundledGFunctors.{0,0,0}} [InvGS_gen false GF]

private theorem step_fupdN_mono_inner (n : Nat) {P Q : IProp GF} (h : P ⊢ Q) :
    Nat.repeat (fun R => iprop(|={⊤}[∅]▷=> R)) n P ⊢
    Nat.repeat (fun R => iprop(|={⊤}[∅]▷=> R)) n Q := by
  induction n with
  | zero => simpa [Nat.repeat] using h
  | succ n IH =>
      simp only [Nat.repeat]
      refine BIFUpdate.mono ?_
      refine BI.later_mono ?_
      refine BIFUpdate.mono ?_
      exact IH

/-- Absorb an inner `|={⊤}=>` payload into an n-step-fupd tower, provided
the tower has at least one layer. (For n = 0 the tower is the bare payload
and no absorption is possible without exiting the BI.) -/
private theorem step_fupdN_absorb_inner_fupd (k : Nat) {P : IProp GF} :
    Nat.repeat (fun R => iprop(|={⊤}[∅]▷=> R)) k.succ iprop(|={⊤}=> P) ⊢
    Nat.repeat (fun R => iprop(|={⊤}[∅]▷=> R)) k.succ P := by
  induction k with
  | zero =>
      simp only [Nat.repeat]
      -- Goal: `|={⊤,∅}=> ▷ |={∅,⊤}=> |={⊤}=> P ⊢ |={⊤,∅}=> ▷ |={∅,⊤}=> P`.
      refine BIFUpdate.mono (BI.later_mono ?_)
      -- Goal: `|={∅,⊤}=> |={⊤}=> P ⊢ |={∅,⊤}=> P`.
      exact BIFUpdate.trans
  | succ j IH =>
      simp only [Nat.repeat]
      -- Outer layer matches; apply IH inside.
      refine BIFUpdate.mono (BI.later_mono (BIFUpdate.mono ?_))
      -- Goal: `tower (j+1) (|={⊤}=> P) ⊢ tower (j+1) P`.
      exact IH


/-! ### Terminated-value extraction

When the thread is terminated, the WP collapses to a fancy update on `Φ v`. -/

variable [StateInterp GF]

private theorem wp_terminated_extract
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (t : Thread) (v : Val) (φ : Val → Prop)
    (hterm : t.toValue = some v) :
    wp procs fork_post CoPset.full t (fun v => iprop(⌜φ v⌝ : IProp GF)) ⊢
      iprop(|={⊤}=> ⌜φ v⌝) := by
  istart
  iintro HW
  ihave HW' := (equiv_iff.mp
    (wp_unfold procs fork_post CoPset.full t (fun v => iprop(⌜φ v⌝)))).mp $$ HW
  icases HW' with ⟨⟨%w, %hterm', Hφ⟩ | ⟨%hnt, _⟩⟩
  · have hwv : w = v := by
      have heq := hterm'.symm.trans hterm
      cases heq; rfl
    subst hwv
    iexact Hφ
  · exfalso
    -- `hnt : t.terminated = false` contradicts `t.toValue = some v`.
    have hT : t.toValue = none := by
      unfold Thread.terminated at hnt
      unfold Thread.toValue
      split at hnt
      · cases hnt
      · rfl
    rw [hT] at hterm
    cases hterm

end AdequacyHelpers

/-! ## Strong adequacy: per-thread safety + main postcondition

The pool invariant `pool_wp` is a big separating conjunction over the
thread list, where index `0` (main) carries the user-supplied
postcondition `Φ` and every other index carries the generic forked
postcondition `fun _ => fork_post`. All threads run at mask `⊤`.

The resulting theorem gives:

1. **Per-thread safety**: every thread in the final pool is either
   terminated or reducible (no stuck threads anywhere).
2. **Main postcondition**: if the main thread (index 0) has terminated
   with value `v`, then `φ v`.
-/

section StrongAdequacy

open Iris.BI.BigSepL

variable {GF : BundledGFunctors.{0,0,0}} [InvGS_gen false GF] [StateInterp GF]

/-- Per-thread WP for the pool: index 0 uses `Φ`, others use `(fun _ => fp)`. -/
def pool_post (fp : IProp GF) (Φ : Val → IProp GF) (k : Nat) : Val → IProp GF :=
  if k = 0 then Φ else fun _ => fp

/-- Pool invariant: every thread of `μ.threads` is at WP with its
appropriate postcondition, at mask `⊤`. -/
def pool_wp (procs : Name → Option Proc) (fp : IProp GF)
    (μ : Machine) (Φ : Val → IProp GF) : IProp GF :=
  iprop([∗list] k ↦ t ∈ μ.threads, wp procs fp CoPset.full t (pool_post fp Φ k))

/-! ### Safety extraction for a single thread

From a thread's WP at mask `⊤` together with the state interpretation,
we can extract under fupd the disjunction "terminated ∨ reducible",
while preserving the resources. -/

variable (procs : Name → Option Proc) (fp : IProp GF)

/-- Per-thread safety (pure-only conclusion): from `state_interp m` and a
WP for `t` we get, under `|={⊤,∅}=∗`, the pure disjunction
"terminated ∨ reducible". This form is what `fupd_plainly_keep_l` needs
to extract the pure fact while keeping the original resources around. -/
theorem wp_safe_pure (m : Mem) (t : Thread) (Φ : Val → IProp GF) :
    state_interp (GF := GF) m ∗ wp procs fp CoPset.full t Φ ⊢
      iprop(|={⊤,∅}=> ⌜t.terminated = true ∨ thread_reducible procs m t⌝) := by
  istart
  iintro ⟨HS, HW⟩
  ihave HW' := (equiv_iff.mp (wp_unfold procs fp CoPset.full t Φ)).mp $$ HW
  icases HW' with ⟨⟨%v, %hterm, _HΦ⟩ | ⟨%_hnt, Hsteps⟩⟩
  · -- Terminated branch: `t.toValue = some v` ⇒ `t.terminated = true`.
    have hT : t.terminated = true := by
      unfold Thread.toValue at hterm
      unfold Thread.terminated
      split <;> simp_all
    iapply fupd_mask_intro empty_subset
    iintro _Hclose
    ipure_intro; exact Or.inl hT
  · -- Reducible branch: apply Hsteps to extract `⌜red⌝`.
    ispecialize Hsteps $$ %m
    imod Hsteps $$ HS with ⟨%hred, _Hrest⟩
    ipure_intro; exact Or.inr hred

/-! ### Pool safety: every thread of `μ.threads` is terminated or reducible.

We iterate `wp_safe_pure` over the thread list using
`BIFUpdatePlainly.fupd_plainly_keep_l` to extract pure safety facts one
thread at a time while preserving the resources. -/

/-- Helper: a one-thread version of `keep_l`. From `state_interp m ∗ wp t`
we get under `|={⊤}=>` both the pure safety fact and the original
resources back. (Sep-form: useful in term-mode combinators.) -/
private theorem wp_safe_keep_sep (m : Mem) (t : Thread) (Φ' : Val → IProp GF) :
    state_interp (GF := GF) m ∗ wp procs fp CoPset.full t Φ' ⊢
      iprop(|={⊤}=>
        ⌜t.terminated = true ∨ thread_reducible procs m t⌝ ∗
        (state_interp m ∗ wp procs fp CoPset.full t Φ')) := by
  -- Step 1: prove the closed-form wand
  --   `⊢ (state_interp m ∗ wp) ={⊤,∅}=∗ ■ ⌜term ∨ red⌝`.
  -- Closed-form wand: from R = state_interp m ∗ wp, we have
  --   ⊢ R ={⊤,∅}=∗ ■ ⌜p⌝.
  -- Equivalently as an entailment from emp:
  have hwand :
      (BI.emp : IProp GF) ⊢
        iprop((state_interp m ∗ wp procs fp CoPset.full t Φ') ={⊤,∅}=∗
              ■ ⌜t.terminated = true ∨ thread_reducible procs m t⌝) := by
    refine BI.wand_intro' ?_
    refine .trans BI.sep_elim_l ?_
    refine .trans (wp_safe_pure procs fp m t Φ') ?_
    exact BIFUpdate.mono BI.plainly_pure.mpr
  refine .trans ?_
    (BIFUpdatePlainly.fupd_plainly_keep_l (PROP := IProp GF) ⊤ ∅
      iprop(⌜t.terminated = true ∨ thread_reducible procs m t⌝)
      iprop(state_interp m ∗ wp procs fp CoPset.full t Φ'))
  refine .trans BI.emp_sep.mpr ?_
  exact BI.sep_mono hwand .rfl

/-- Pool safety (generic): from `state_interp m` and *any* big-sep of
WPs (with arbitrary postconditions), extract the pure conjunction that
every thread is terminated or reducible. -/
theorem pool_safe_generic (m : Mem) (ts : List Thread)
    (Ψ : Nat → Val → IProp GF) :
    state_interp (GF := GF) m ∗
        iprop([∗list] k ↦ t ∈ ts, wp procs fp CoPset.full t (Ψ k)) ⊢
      iprop(|={⊤}=>
        ⌜∀ t ∈ ts, t.terminated = true ∨ thread_reducible procs m t⌝) := by
  induction ts generalizing Ψ with
  | nil =>
      istart
      iintro _H
      imodintro
      ipure_intro
      intro t ht; cases ht
  | cons th rest IH =>
      istart
      iintro ⟨HS, Hpool⟩
      ihave Hpool' := bigSepL_cons.mp $$ Hpool
      icases Hpool' with ⟨Hhead, Htail⟩
      -- We bring HS and Hhead together and apply `wp_safe_keep_sep` via term mode.
      -- Use `ihave PAT : TYPE $$ spat` syntax to discharge a subgoal.
      ihave Hsafe : iprop(|={⊤}=>
          ⌜th.terminated = true ∨ thread_reducible procs m th⌝ ∗
          (state_interp m ∗ wp procs fp CoPset.full th (Ψ 0)))
        $$ [HS Hhead]
      · -- Subgoal: prove the assertion using HS and Hhead as resources.
        istop
        exact wp_safe_keep_sep procs fp m th (Ψ 0)
      imod Hsafe with ⟨%hth, HS, _Hhead⟩
      ihave Hrec : iprop(|={⊤}=>
          ⌜∀ t ∈ rest, t.terminated = true ∨ thread_reducible procs m t⌝)
        $$ [HS Htail]
      · istop
        exact BI.sep_comm.mp.trans (IH (Ψ := fun k => Ψ (k+1)))
      imod Hrec with %hrest
      imodintro
      ipure_intro
      intro t ht
      cases ht with
      | head _ => exact hth
      | tail _ ht' => exact hrest _ ht'

/-- Pool safety specialised to `pool_wp`. -/
theorem pool_safe (m : Mem) (μ : Machine) (Φ : Val → IProp GF) :
    state_interp (GF := GF) m ∗ pool_wp procs fp μ Φ ⊢
      iprop(|={⊤}=>
        ⌜∀ t ∈ μ.threads, t.terminated = true ∨ thread_reducible procs m t⌝) := by
  unfold pool_wp
  exact pool_safe_generic procs fp m μ.threads (pool_post fp Φ)

/-! ### Main-thread postcondition extraction

If the main thread (index 0 in the pool) has terminated with value `v`,
the pool invariant lets us extract `Φ v` under a fancy update. The proof
peels off the head WP from the big-sep and reuses `wp_terminated_extract`. -/

/-- If the pool is non-empty and its head has `toValue = some v`, extract
the main thread's post-condition. -/
theorem pool_main_post (μ : Machine) (Φ : Val → IProp GF)
    (v : Val) (φ : Val → Prop) (Hpost : Φ = fun v => iprop(⌜φ v⌝ : IProp GF))
    (th : Thread) (rest : List Thread)
    (hts : μ.threads = th :: rest) (hterm : th.toValue = some v) :
    pool_wp procs fp μ Φ ⊢ iprop(|={⊤}=> ⌜φ v⌝) := by
  subst Hpost
  unfold pool_wp
  rw [hts]
  refine .trans bigSepL_cons.mp ?_
  refine .trans BI.sep_elim_l ?_
  -- Goal: wp procs fp ⊤ th (pool_post fp ⌜φ⌝ 0) ⊢ |={⊤}=> ⌜φ v⌝.
  -- `pool_post fp ⌜φ⌝ 0` reduces to `⌜φ⌝` via the if-then-else.
  -- Bridge to `wp_terminated_extract`.
  have hpost0 : (pool_post fp (fun v => iprop(⌜φ v⌝ : IProp GF)) 0)
                  = (fun v => iprop(⌜φ v⌝ : IProp GF)) := by
    unfold pool_post; simp
  rw [hpost0]
  exact wp_terminated_extract procs fp th v φ hterm

/-! ### Trace bridging: a no-fork machine step preserves the pool invariant

We restrict to traces where no `fork` ever fires (the spawned-thread
component is always `none`). Under this restriction the pool's *length*
is preserved across `Machine.Step`, so we can use `bigSepL_lookup_acc` to
focus the WP of the stepped thread, apply `wp_step_sound`, and
reassemble the updated pool.

This is strictly stronger than the existing `ThreadStepN`-based
`wp_adequacy`: it covers full multi-thread *interleavings* of the
existing pool, just not the spawn of new threads. -/

/-! ### Machine-step soundness

We now drop the no-fork restriction. The proof template is the same as
`wp_machine_step_sound_nofork`, but in the fork case we additionally
consume the fork witness from the WP step branch and append the spawned
thread's WP to the pool via `bigSepL_snoc`. -/

/-- Single-step machine soundness, full version (allowing forks). -/
theorem wp_machine_step_sound (p : Program) (μ μ' : Machine)
    (Φ : Val → IProp GF)
    (hstep : Machine.Step p μ μ') :
    state_interp (GF := GF) μ.mem ∗ pool_wp p.procs fp μ Φ ⊢
      iprop(|={⊤}[∅]▷=>
        (state_interp μ'.mem ∗ pool_wp p.procs fp μ' Φ)) := by
  cases hstep with
  | step i chosen t t' sp m m' threads hi hstep =>
  unfold pool_wp
  -- Focus the i-th thread's WP via `bigSepL_lookup_acc`.
  istart
  iintro ⟨HS, Hpool⟩
  ihave Hpool' :=
    (bigSepL_lookup_acc (l := threads) (i := i) (x := t) hi).mp $$ Hpool
  icases Hpool' with ⟨Hi, Hreassem⟩
  -- Apply `wp_step_sound` to step thread `i` from `t` to `t'`.
  have hthread_step : thread_step p.procs m t m' t' sp := ⟨chosen, hstep⟩
  ihave Hstepped : iprop(|={⊤}[∅]▷=>
      (state_interp (GF := GF) m' ∗
        wp p.procs fp CoPset.full t' (pool_post fp Φ i) ∗
        (∀ (ts : Thread), ⌜sp = some ts⌝ -∗
           wp p.procs fp CoPset.full ts (fun _ => fp))))
    $$ [HS Hi]
  · istop
    exact wp_step_sound p.procs fp m m' t t' sp (pool_post fp Φ i) hthread_step
  imod Hstepped with HStepped
  imodintro
  inext
  imod HStepped with ⟨HS, HW', Hfork⟩
  imodintro
  -- We now branch on whether `sp` is `none` (no fork) or `some ts` (fork).
  -- In either case we must produce
  --   pool_wp p.procs fp ⟨m', threads.set i t' ++ sp.toList⟩ Φ
  -- from `Hreassem` (giving pool_wp over `threads.set i t'`) plus, if
  -- forked, the WP of `ts` from `Hfork`.
  cases hsp : sp with
  | none =>
    -- No fork: pool is `threads.set i t' ++ [] = threads.set i t'`.
    -- This reduces to the nofork case.
    simp only [Option.toList_none, List.append_nil]
    iframe HS
    iapply Hreassem $$ %t'
    iexact HW'
  | some ts =>
    -- Fork: new pool is `threads.set i t' ++ [ts]`.
    -- The post-condition for the appended thread is `fun _ => fp`, which
    -- equals `pool_post fp Φ threads.length` since `threads.length ≥ 1`.
    have hlen_pos : threads.length ≥ 1 := by
      have hlt : i < threads.length :=
        (List.getElem?_eq_some_iff.mp hi).1
      omega
    have hset_len : (threads.set i t').length = threads.length :=
      List.length_set ..
    have hpp_tail : pool_post fp Φ (threads.set i t').length = (fun _ => fp) := by
      rw [hset_len]
      unfold pool_post
      have hne : threads.length ≠ 0 := by omega
      simp [hne]
    -- Specialise the fork witness `Hfork : ∀ ts, ⌜sp = some ts⌝ -∗ wp ts (fun _ => fp)`
    -- at `ts`, using `hsp : sp = some ts`.
    iframe HS
    -- Rewrite `sp.toList = [ts]` and bigSepL_append.
    simp only [Option.toList_some]
    iapply bigSepL_append.mpr
    -- Goal: `([∗list] threads.set i t', wp _ (pool_post fp Φ k)) ∗
    --        ([∗list] [ts], wp _ (pool_post fp Φ (k + (set i t').length)))`.
    isplitl [HW' Hreassem]
    · -- Use reassem with t' to produce the main bigsep.
      iapply Hreassem $$ %t'
      iexact HW'
    · -- Singleton bigsep over [ts]: shift index is `0 + (set i t').length`.
      iapply bigSepL_singleton.mpr
      -- Goal: `wp p.procs fp ⊤ ts (pool_post fp Φ (0 + (set i t').length))`.
      -- Specialise Hfork at ts.
      ihave Hts : iprop(wp p.procs fp CoPset.full ts (fun _ => fp)) $$ [Hfork]
      · iapply Hfork $$ %ts %rfl
      -- Convert Hts to the required postcondition.
      have heqfun : (0 + (threads.set i t').length) ≠ 0 := by
        rw [hset_len, Nat.zero_add]; omega
      have hpp0 : pool_post fp Φ (0 + (threads.set i t').length) = (fun _ => fp) := by
        unfold pool_post
        rw [if_neg heqfun]
      rw [hpp0]
      iexact Hts

/-- n-step soundness of `Machine.StepStarN`: a step-fupd tower of height
n connects the initial and final `state_interp ∗ pool_wp`. -/
theorem wp_machine_steps_sound (p : Program) (Φ : Val → IProp GF) :
    ∀ (n : Nat) (μ μ' : Machine),
      Machine.StepStarN p n μ μ' →
      state_interp (GF := GF) μ.mem ∗ pool_wp p.procs fp μ Φ ⊢
        Nat.repeat (fun Q => iprop(|={⊤}[∅]▷=> Q)) n
          iprop(state_interp μ'.mem ∗ pool_wp p.procs fp μ' Φ) := by
  intro n
  induction n with
  | zero =>
      intro μ μ' htr
      cases htr
      simp [Nat.repeat]
  | succ n IH =>
      intro μ μ' htr
      cases htr with
      | step h1 h2 =>
        rename_i μ₁
        simp only [Nat.repeat]
        refine .trans (wp_machine_step_sound (fp := fp) p μ μ₁ Φ h1) ?_
        refine BIFUpdate.mono (BI.later_mono (BIFUpdate.mono ?_))
        exact IH μ₁ μ' h2

end StrongAdequacy

/-! ## Final strong adequacy theorem

Under any `Machine.StepStarN p n` trace from the initial machine, we get
*both* per-thread safety and the main postcondition. -/

section StrongAdequacyMain

open Iris.BI.BigSepL

/-- The initial machine `pool_wp` is just the main thread's `wp`: the
pool list has length 1 and position 0 gets the user-supplied `Φ`. -/
private theorem pool_init_iso
    {GF : BundledGFunctors.{0,0,0}} [InvGS_gen false GF] [StateInterp GF]
    (procs : Name → Option Proc) (fp : IProp GF) (s : Stmt)
    (Φ : Val → IProp GF) :
    iprop(state_interp (GF := GF) Mem.empty ∗
      wp procs fp CoPset.full (Thread.initial s) Φ) ⊢
    iprop(state_interp (GF := GF) Mem.empty ∗
      pool_wp procs fp ⟨Mem.empty, [Thread.initial s]⟩ Φ) := by
  refine BI.sep_mono .rfl ?_
  show iprop(wp _ _ _ _ _) ⊢
    iprop([∗list] k ↦ t ∈ [Thread.initial s],
      wp procs fp CoPset.full t (pool_post fp Φ k))
  refine .trans ?_ bigSepL_singleton.mpr
  have h0 : pool_post fp Φ 0 = Φ := by unfold pool_post; simp
  rw [h0]
  exact .rfl

/-- Boilerplate skeleton: given the hypothesis `H` and an inner
entailment producing a step-fupd tower of height `n` over `⌜P⌝` from
the initial `state_interp ∗ pool_wp`, conclude `P` purely. -/
private theorem adequacy_skeleton
    {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF]
    (p : Program) (φ : Val → Prop) (n : Nat) (P : Prop)
    (H : ∀ [_LC : InvGS_gen false GF],
         ⊢ ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
             state_interp (GF := GF) Mem.empty ∗
               wp p.procs fork_post CoPset.full (Thread.initial p.main)
                 (fun v => iprop(⌜φ v⌝ : IProp GF)))
    (body : ∀ [_LC : InvGS_gen false GF] (_Hsi : StateInterp GF) (fp : IProp GF),
              iprop(state_interp (GF := GF) Mem.empty ∗
                pool_wp p.procs fp (Machine.initial p)
                  (fun v => iprop(⌜φ v⌝ : IProp GF))) ⊢
              Nat.repeat (fun Q => iprop(|={⊤}[∅]▷=> Q)) n
                iprop(|={⊤}=> ⌜P⌝)) :
    P := by
  refine Iris.pure_soundness (PROP := IProp GF) ?_
  -- Pick the soundness primitive based on n: for n = 0, `fupd_soundness_no_lc`
  -- gives a fupd at ⊤; for n ≥ 1, `step_fupdN_soundness_no_lc'` gives a tower
  -- whose innermost layer is `|={⊤}=> _`, which we then absorb.
  cases n with
  | zero =>
      refine BI.true_intro.trans (fupd_soundness_no_lc
        (GF := GF) (m := 0) (E1 := ⊤) (E2 := ⊤) ?_)
      intro _LC
      refine BI.wand_intro' (BI.sep_elim_l.trans ?_)
      refine BI.true_intro.trans ((H (_LC := _LC)).trans ?_)
      refine BI.exists_elim fun SI_inst => ?_
      refine BI.exists_elim fun fp => ?_
      refine (pool_init_iso (GF := GF) p.procs fp p.main _).trans ?_
      have := body (_LC := _LC) SI_inst fp
      simpa using this
  | succ k =>
      refine BI.true_intro.trans (step_fupdN_soundness_no_lc'
        (GF := GF) (n := k.succ) (m := 0) ?_)
      intro LC
      refine BI.wand_intro' (BI.sep_elim_l.trans ?_)
      refine BI.true_intro.trans ((H (_LC := LC)).trans ?_)
      refine BI.exists_elim fun SI_inst => ?_
      refine BI.exists_elim fun fp => ?_
      refine (pool_init_iso (GF := GF) p.procs fp p.main _).trans ?_
      refine (body (_LC := LC) SI_inst fp).trans ?_
      exact step_fupdN_absorb_inner_fupd k

/-- **Strong adequacy.** Under any `Machine.StepStarN p n` trace from
the initial machine: every thread in the reached pool is terminated or
reducible, and if the main thread (position 0) terminated with value
`v`, then `φ v`. -/
theorem wp_strong_adequacy
    {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF]
    (p : Program) (φ : Val → Prop)
    (H : ∀ [_LC : InvGS_gen false GF],
         ⊢ ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
             state_interp (GF := GF) Mem.empty ∗
               wp p.procs fork_post CoPset.full (Thread.initial p.main)
                 (fun v => iprop(⌜φ v⌝ : IProp GF)))
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN p n (Machine.initial p) μ') :
    (∀ t ∈ μ'.threads, t.terminated = true ∨ thread_reducible p.procs μ'.mem t) ∧
    (∀ (th : Thread) (rest : List Thread), μ'.threads = th :: rest →
      ∀ v, th.toValue = some v → φ v) := by
  refine ⟨?_, ?_⟩
  -- Per-thread safety
  · refine adequacy_skeleton p φ n _ H ?_
    intro _LC SI_inst fp
    refine .trans (wp_machine_steps_sound
      (GF := GF) (fp := fp) p _ n (Machine.initial p) μ' htr) ?_
    refine step_fupdN_mono_inner n ?_
    exact pool_safe (GF := GF) p.procs fp μ'.mem μ' _
  -- Main postcondition
  · intro th rest hts v hterm
    refine adequacy_skeleton p φ n _ H ?_
    intro _LC SI_inst fp
    refine .trans (wp_machine_steps_sound
      (GF := GF) (fp := fp) p _ n (Machine.initial p) μ' htr) ?_
    refine step_fupdN_mono_inner n ?_
    exact .trans (BI.sep_elim_r.trans
      (pool_main_post (GF := GF)
        p.procs fp μ' (fun v => iprop(⌜φ v⌝ : IProp GF)) v φ rfl
        th rest hts hterm)) .rfl

/-! ## Bupd-allowed variant

Adequacy entry points that need to *allocate* initial ghost state (e.g.
the heap-auth via `heap_init`) cannot supply a closed `⊢ ∃ Hsi fp, …`
hypothesis: the `Hsi` typeclass field itself depends on a ghost name
that only exists *under* a `|==>`. The variant below accepts that form
by absorbing the leading bupd into the first fupd of the soundness
tower. -/

section StrongAdequacyBupd

open Iris.BI.BigSepL

private theorem adequacy_skeleton_bupd
    {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF]
    (p : Program) (φ : Val → Prop) (n : Nat) (P : Prop)
    (H : ∀ [_LC : InvGS_gen false GF],
         ⊢ |==> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
             state_interp (GF := GF) Mem.empty ∗
               wp p.procs fork_post CoPset.full (Thread.initial p.main)
                 (fun v => iprop(⌜φ v⌝ : IProp GF)))
    (body : ∀ [_LC : InvGS_gen false GF] (_Hsi : StateInterp GF) (fp : IProp GF),
              iprop(state_interp (GF := GF) Mem.empty ∗
                pool_wp p.procs fp (Machine.initial p)
                  (fun v => iprop(⌜φ v⌝ : IProp GF))) ⊢
              Nat.repeat (fun Q => iprop(|={⊤}[∅]▷=> Q)) n
                iprop(|={⊤}=> ⌜P⌝)) :
    P := by
  refine Iris.pure_soundness (PROP := IProp GF) ?_
  -- We use `step_fupdN_soundness_no_lc'` at level n (same as the non-bupd
  -- variant), then absorb the leading `|==>` from `H` into the first
  -- fupd of the tower. We split on `n` to keep the inner-layer absorption
  -- well-typed.
  cases n with
  | zero =>
      refine BI.true_intro.trans (fupd_soundness_no_lc
        (GF := GF) (m := 0) (E1 := ⊤) (E2 := ⊤) ?_)
      intro _LC
      refine BI.wand_intro' (BI.sep_elim_l.trans ?_)
      refine BI.true_intro.trans ((H (_LC := _LC)).trans ?_)
      -- `|==> X ⊢ |={⊤}=> X` via `fupd_of_bupd`, then ∃-elim and finish.
      refine .trans (BIUpdateFUpdate.fupd_of_bupd (E := ⊤)) ?_
      refine .trans (BIFUpdate.mono ?_) BIFUpdate.trans
      refine BI.exists_elim fun SI_inst => ?_
      refine BI.exists_elim fun fp => ?_
      refine (pool_init_iso (GF := GF) p.procs fp p.main _).trans ?_
      have := body (_LC := _LC) SI_inst fp
      simpa using this
  | succ k =>
      refine BI.true_intro.trans (step_fupdN_soundness_no_lc'
        (GF := GF) (n := k.succ) (m := 0) ?_)
      intro LC
      refine BI.wand_intro' (BI.sep_elim_l.trans ?_)
      refine BI.true_intro.trans ((H (_LC := LC)).trans ?_)
      -- Goal: |==> ∃... ⊢ tower(k+1)(|={⊤}=> ⌜P⌝).
      -- Convert `|==>` to `|={⊤}=>` and absorb into the outer `|={⊤,∅}=>`.
      refine .trans (BIUpdateFUpdate.fupd_of_bupd (E := ⊤)) ?_
      simp only [Nat.repeat]
      refine .trans (BIFUpdate.mono ?_) BIFUpdate.trans
      refine BI.exists_elim fun SI_inst => ?_
      refine BI.exists_elim fun fp => ?_
      refine (pool_init_iso (GF := GF) p.procs fp p.main _).trans ?_
      refine (body (_LC := LC) SI_inst fp).trans ?_
      exact step_fupdN_absorb_inner_fupd k

/-- Strong adequacy, bupd-allowing variant: the initial `state_interp ∗
wp` may live under a `|==>` so the caller can allocate ghost state. -/
theorem wp_strong_adequacy_bupd
    {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF]
    (p : Program) (φ : Val → Prop)
    (H : ∀ [_LC : InvGS_gen false GF],
         ⊢ |==> ∃ (_Hsi : StateInterp GF) (fork_post : IProp GF),
             state_interp (GF := GF) Mem.empty ∗
               wp p.procs fork_post CoPset.full (Thread.initial p.main)
                 (fun v => iprop(⌜φ v⌝ : IProp GF)))
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN p n (Machine.initial p) μ') :
    (∀ t ∈ μ'.threads, t.terminated = true ∨ thread_reducible p.procs μ'.mem t) ∧
    (∀ (th : Thread) (rest : List Thread), μ'.threads = th :: rest →
      ∀ v, th.toValue = some v → φ v) := by
  refine ⟨?_, ?_⟩
  · refine adequacy_skeleton_bupd p φ n _ H ?_
    intro _LC SI_inst fp
    refine .trans (wp_machine_steps_sound
      (GF := GF) (fp := fp) p _ n (Machine.initial p) μ' htr) ?_
    refine step_fupdN_mono_inner n ?_
    exact pool_safe (GF := GF) p.procs fp μ'.mem μ' _
  · intro th rest hts v hterm
    refine adequacy_skeleton_bupd p φ n _ H ?_
    intro _LC SI_inst fp
    refine .trans (wp_machine_steps_sound
      (GF := GF) (fp := fp) p _ n (Machine.initial p) μ' htr) ?_
    refine step_fupdN_mono_inner n ?_
    exact .trans (BI.sep_elim_r.trans
      (pool_main_post (GF := GF)
        p.procs fp μ' (fun v => iprop(⌜φ v⌝ : IProp GF)) v φ rfl
        th rest hts hterm)) .rfl

end StrongAdequacyBupd

end StrongAdequacyMain

/-! ## Named adequacy predicates

The strong-adequacy theorems above conclude with an ad-hoc conjunction of
per-thread safety and a main-thread postcondition. The predicates below
package those two clauses (and their conjunction) under stable names so
client `_closed` theorems can state their conclusion as
`Machine.Adequate prog μ' v` rather than spelling out the conjunction.

These are plain `def`s that reduce *definitionally* to the same conjunction
returned by `wp_strong_adequacy[_bupd]`, so an `unfold` at the start of a
`_closed` proof is the only adjustment needed. -/

/-- **Safety.** Every thread in `μ` is either terminated or reducible
under `procs` and `μ.mem`. -/
def Machine.Safe (procs : Name → Option Proc) (μ : Machine) : Prop :=
  ∀ t ∈ μ.threads, t.terminated = true ∨ thread_reducible procs μ.mem t

/-- **Main-thread postcondition.** If the main thread of `μ` has
terminated to a `Val`, that value is `v`. -/
def Machine.MainReturns (μ : Machine) (v : Val) : Prop :=
  ∀ (th : Thread) (rest : List Thread), μ.threads = th :: rest →
    ∀ v', th.toValue = some v' → v' = v

/-- **Combined adequacy.** Safety of the whole pool together with the
main-thread postcondition. This is the canonical conclusion of every
`_closed` theorem in the examples. -/
def Machine.Adequate (prog : Program) (μ : Machine) (v : Val) : Prop :=
  Machine.Safe prog.procs μ ∧ Machine.MainReturns μ v

end Agar.Logic

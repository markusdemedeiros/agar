module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Std.Namespaces
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.WpSpin

@[expose] public section

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

/-! # `progTicketLock` — single-thread ticket-lock mechanism demo

A single-thread program that exercises BOTH cells of a textbook
ticket-lock (`next` for ticket issuance, `now` for current-turn) with
the canonical mechanism:

* **acquire** = (FAA-via-CAS-loop on `next` to claim `myTicket = next`
  and bump `next`) followed by (spin on `now == myTicket`);
* **release** = (load `now`, store `now + 1`).

```
main :=
  next  := alloc 0 ;
  now   := alloc 0 ;
  doneA := 0 ;
  while doneA = 0 do (                       -- FAA via CAS loop
    t := load next ;
    r := cas next t (t + 1) ;
    if r = t then doneA := 1 else skip
  ) ;
  doneB := 0 ;
  while doneB = 0 do (                       -- spin on now == myTicket
    nv := load now ;
    if nv = t then doneB := 1 else skip
  ) ;
  rn := load now ;                           -- release
  store now (rn + 1)
```

Both cells are GENUINELY USED:
* `next` is loaded into `t`, then atomically bumped from `0` to `1`
  via `cas next 0 1` in the FAA-via-CAS pattern;
* `now` is read in the spin loop and incremented in release.

### Scope statement

Multi-thread Hoare specs `{{ is_lock γ N next now R }} acquire {{ … }}`
and `{{ is_lock γ N next now R ∗ locked γ ∗ R }} release {{ emp }}`,
quantifying over arbitrary `procs`/`fork_post`/`E`, with a disjunctive
invariant tracking issued-vs-served tickets, are NOT closed here — a
prior session attempt collapsed under the spin-Löb/invariant
interaction (the `next`-loop and `now`-loop each need to thread their
IHs through a disjunctive invariant whose disjuncts depend on the
ghost-counter state). This file documents the achievable shape: a
closed safety proof (`progTicketLock_closed`) of a single-thread head
program that runs through both `acquire` and `release` exactly once
using the mechanism above. Single-threaded ⇒ the CAS succeeds on its
first attempt and the spin exits on its first iteration; both loops
are dispatched by `wp_spin_invariant` with a disjunctive `I` whose
left disjunct holds at the initial env and right disjunct holds after
the body fires.

### What's verified

`progTicketLock_closed : Machine.Adequate progTicketLock μ' Val.unit`.
Safety + `Val.unit` termination of the head thread; every `cas`,
`load`, `store` is discharged by a real Iris WP rule against a real
`points_to`. -/

/-- The single-thread ticket-lock demonstrator program. -/
def progTicketLock : Program where
  procs := fun _ => none
  main  := ags(
    next := alloc 0 ;
    now  := alloc 0 ;
    doneA := 0 ;
    { while doneA = 0 do {
        t := load next ;
        r := cas next t (t + 1) ;
        if r = t then doneA := 1 else skip
      }
    } ;
    doneB := 0 ;
    { while doneB = 0 do {
        nv := load now ;
        if nv = t then doneB := 1 else skip
      }
    } ;
    rn := load now ;
    store now (rn + 1)
  )

theorem progTicketLock_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progTicketLock n
            (Machine.initial progTicketLock) μ') :
    Machine.Adequate progTicketLock μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progTicketLock ?_ n μ' htr
  start_closed_proof_with_heap progTicketLock
  -- main: alloc next ; alloc now ; doneA:=0 ; whileA ; doneB:=0 ; whileB ;
  --       rn:=load now ; store now (rn+1)
  wp_step; iintro !>
  iapply wp_alloc _ _ _ _ _ _ _ _ _ (by agar_eval)
  iintro !> %lNext HPnext
  wp_step; iintro !>
  wp_step; iintro !>
  iapply wp_alloc _ _ _ _ _ _ _ _ _ (by agar_eval)
  iintro !> %lNow HPnow
  wp_step; iintro !>
  wp_step; iintro !>
  wp_step; iintro !>                            -- doneA := 0
  wp_step; iintro !>
  wp_step; iintro !>
  -- ====== LOOP A: FAA-via-CAS on `next` ======
  -- I env disjunction:
  --   LEFT  : next ↦ 0 ∗ now ↦ 0 ∗ "doneA"=0, "next"=lNext, "now"=lNow.
  --   RIGHT : next ↦ 1 ∗ now ↦ 0 ∗ "doneA"=1, "t"=0, "next"=lNext, "now"=lNow.
  -- In both cases the guard (doneA=0) evaluates to some Boolean.
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := fun env =>
      iprop(
        (points_to (GF := GF) (F := F) lNext (Val.int 0) ∗
         points_to (GF := GF) (F := F) lNow (Val.int 0) ∗
         ⌜env "next" = some (Val.loc lNext) ∧
           env "now" = some (Val.loc lNow) ∧
           env "doneA" = some (Val.int 0)⌝)
        ∨
        (points_to (GF := GF) (F := F) lNext (Val.int 1) ∗
         points_to (GF := GF) (F := F) lNow (Val.int 0) ∗
         ⌜env "next" = some (Val.loc lNext) ∧
           env "now" = some (Val.loc lNow) ∧
           env "doneA" = some (Val.int 1) ∧
           env "t" = some (Val.int 0)⌝)))
    _
    (HGuard := fun env => ?HGuardA)
    (HBody := fun env => ?HBodyA)
    (HExit := fun env => ?HExitA))
  case HGuardA =>
    -- Both disjuncts yield a definite guard value.
    istart
    iintro HI
    icases HI with (⟨HPn, HPnw, %hL⟩ | ⟨HPn, HPnw, %hR⟩)
    · isplitl [HPn HPnw]
      · ileft; iframe HPn; iframe HPnw; ipure_intro; exact hL
      ipure_intro
      refine ⟨true, ?_⟩
      show (env "doneA").bind _ = _
      rw [hL.2.2]
      rfl
    · isplitl [HPn HPnw]
      · iright; iframe HPn; iframe HPnw; ipure_intro; exact hR
      ipure_intro
      refine ⟨false, ?_⟩
      show (env "doneA").bind _ = _
      rw [hR.2.2.1]
      rfl
  case HBodyA =>
    -- Guard is true ⇒ we're in the LEFT disjunct (in the RIGHT disjunct
    -- doneA is bound to 1 ⇒ guard is false ⇒ contradiction).
    iintro ⟨HIH, ⟨%hgtrue, HI⟩⟩
    icases HI with (⟨HPn, HPnw, %hL⟩ | ⟨HPn, HPnw, %hR⟩)
    · -- LEFT disjunct: env "next" = some lNext, env "now" = some lNow, doneA = 0.
      obtain ⟨hnext, hnow, _⟩ := hL
      iapply wp_seq; iintro !>
      wp_load_direct HPn (by exact hnext)
      wp_step; iintro !>
      wp_step; iintro !>
      iapply wp_cas_succ (GF := GF) (F := F)
        (vO := Val.int 0) (vN := Val.int 1)
        (heL := by
          show (env.set "t" (Val.int 0)) "next" = some (Val.loc lNext)
          simp [Env.set]; exact hnext)
        (heO := by
          show (env.set "t" (Val.int 0)) "t" = some (Val.int 0)
          simp [Env.set])
        (heN := by agar_eval)
        (heq := by decide)
      iframe HPn
      iintro !> HPn
      wp_step; iintro !>
      iapply wp_ite_true (heval := by agar_eval)
      iintro !>
      wp_step; iintro !>
      wp_step; iintro !>
      ihave HIH := HIH $$ %(((env.set "t" (Val.int 0)).set "r" (Val.int 0)).set "doneA" (Val.int 1))
      iapply HIH
      iright
      iframe HPn
      iframe HPnw
      ipure_intro
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Env.set]; exact hnext
      · simp [Env.set]; exact hnow
      · simp [Env.set]
      · simp [Env.set]
    -- RIGHT disjunct: doneA = 1 ⇒ guard false ⇒ contradicts hgtrue.
    exfalso
    revert hgtrue
    show (env "doneA").bind _ = _ → _
    rw [hR.2.2.1]
    intro h; injection h with h; injection h with h; cases h
  case HExitA =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with (⟨_HPn, _HPnw, %hL⟩ | ⟨HPn, HPnw, %hR⟩)
    · -- LEFT: doneA=0, guard would be true, contradiction.
      exfalso
      revert hgfalse
      show (env "doneA").bind _ = _ → _
      rw [hL.2.2]
      intro h; injection h with h; injection h with h; cases h
    -- RIGHT: HPn : next ↦ 1, HPnw : now ↦ 0, hR : env "t"=some 0, env "now"=some lNow.
    obtain ⟨_hnext, hnow, _, ht⟩ := hR
    -- Continuation: doneB := 0 ; whileB ; rn := load now ; store now (rn+1)
    wp_step; iintro !>                          -- skip_cons
    wp_step; iintro !>                          -- wp_seq
    wp_step; iintro !>                          -- wp_assign (doneB := 0)
    wp_step; iintro !>                          -- skip_cons
    wp_step; iintro !>                          -- wp_seq (expose whileB)
    -- ====== LOOP B: spin on now == t ======
    -- I' env := now ↦ 0 ∗ "now"=lNow ∗ "t"=0 ∗ (env "doneB" ∈ {some 0, some 1}).
    iapply (wp_spin_invariant _ _ _ _ _ _ _
      (I := fun env =>
        iprop(
          (points_to (GF := GF) (F := F) lNow (Val.int 0) ∗
           ⌜env "now" = some (Val.loc lNow) ∧
             env "t" = some (Val.int 0) ∧
             env "doneB" = some (Val.int 0)⌝)
          ∨
          (points_to (GF := GF) (F := F) lNow (Val.int 0) ∗
           ⌜env "now" = some (Val.loc lNow) ∧
             env "doneB" = some (Val.int 1)⌝)))
      _
      (HGuard := fun env => ?HGuardB)
      (HBody := fun env => ?HBodyB)
      (HExit := fun env => ?HExitB))
    case HGuardB =>
      istart
      iintro HI
      icases HI with (⟨HPnw, %hL⟩ | ⟨HPnw, %hR⟩)
      · isplitl [HPnw]
        · ileft; iframe HPnw; ipure_intro; exact hL
        ipure_intro; refine ⟨true, ?_⟩
        show (env "doneB").bind _ = _
        rw [hL.2.2]; rfl
      · isplitl [HPnw]
        · iright; iframe HPnw; ipure_intro; exact hR
        ipure_intro; refine ⟨false, ?_⟩
        show (env "doneB").bind _ = _
        rw [hR.2]; rfl
    case HBodyB =>
      iintro ⟨HIH, ⟨%hgtrue, HI⟩⟩
      icases HI with (⟨HPnw, %hL⟩ | ⟨HPnw, %hR⟩)
      · -- LEFT: env "now"=lNow, env "t"=0, env "doneB"=0.
        obtain ⟨hnow, ht, _⟩ := hL
        iapply wp_seq; iintro !>
        wp_load_direct HPnw (by exact hnow)
        wp_step; iintro !>
        iapply wp_ite_true
          (heval := by
            show Expr.eval _ _ = _
            simp [Expr.eval, Env.set, BinOp.eval]
            rw [ht]
            rfl)
        iintro !>
        wp_step; iintro !>
        wp_step; iintro !>
        ihave HIH := HIH $$ %((env.set "nv" (Val.int 0)).set "doneB" (Val.int 1))
        iapply HIH
        iright
        iframe HPnw
        ipure_intro
        refine ⟨?_, ?_⟩
        · simp [Env.set]; exact hnow
        · simp [Env.set]
      -- RIGHT: doneB = 1 ⇒ guard false ⇒ contradicts hgtrue.
      exfalso
      revert hgtrue
      show (env "doneB").bind _ = _ → _
      rw [hR.2]; intro h; injection h with h; injection h with h; cases h
    case HExitB =>
      iintro ⟨%hgfalse, HI⟩
      icases HI with (⟨_HPnw, %hL⟩ | ⟨HPnw, %hR⟩)
      · exfalso
        revert hgfalse
        show (env "doneB").bind _ = _ → _
        rw [hL.2.2]; intro h; injection h with h; injection h with h; cases h
      obtain ⟨hnow, _⟩ := hR
      -- Continuation: rn := load now ; store now (rn+1)
      wp_step; iintro !>
      wp_step; iintro !>
      wp_load_direct HPnw (by exact hnow)
      wp_step; iintro !>
      iapply wp_store (GF := GF) (F := F)
        (heL := by
          show (env.set "rn" (Val.int 0)) "now" = _
          simp [Env.set]; exact hnow)
        (heV := by agar_eval)
      iframe HPnw
      iintro !> _HPnw
      wp_done
    · -- Initial I' at the env entering loop B.
      -- env here is `((env_after_loopA).set "doneB" (Val.int 0))`-ish.
      -- Use LEFT disjunct: now ↦ 0 ∗ pure(now=lNow, t=0, doneB=0).
      ileft
      iframe HPnw
      ipure_intro
      refine ⟨?_, ?_, ?_⟩
      · show Env.set _ _ _ "now" = _; simp [Env.set]; exact hnow
      · show Env.set _ _ _ "t" = _; simp [Env.set]; exact ht
      · show Env.set _ _ _ "doneB" = _; simp [Env.set]
  · -- Initial I at the env entering loop A. LEFT disjunct.
    ileft
    iframe HPnext
    iframe HPnow
    ipure_intro
    refine ⟨?_, ?_, ?_⟩
    all_goals (show Env.set _ _ _ _ = _; simp [Env.set])

end Agar.Logic

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

`progTicketLock_closed : Machine.Adequate progTicketLock μ' (Val.int 1)`.
Safety + functional correctness: every terminating run returns
`Val.int 1`, the post-release counter value. Every `cas`, `load`,
`store` is discharged by a real Iris WP rule against a real
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
    store now (rn + 1) ;
    return (rn + 1)
  )

theorem progTicketLock_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progTicketLock n
            (Machine.initial progTicketLock) μ') :
    Machine.Adequate progTicketLock μ' (Val.int 1) := by
  adequacy_with_heap_intro progTicketLock (Val.int 1)
  wp_pures
  wp_alloc_intro lNext HPnext
  wp_pures
  wp_alloc_intro lNow HPnow
  wp_pures_no_loop
  -- LOOP A: FAA-via-CAS on `next`. LEFT = ticket unclaimed; RIGHT = claimed.
  -- Single-threaded, so we hold the points-to inside `I` directly (no `inv`).
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
    istart
    iintro HI
    icases HI with (⟨HPn, HPnw, %hL⟩ | ⟨HPn, HPnw, %hR⟩)
    · isplitl [HPn HPnw]
      · ileft; iframe HPn; iframe HPnw; ipure_intro; exact hL
      ipure_intro
      refine ⟨true, ?_⟩; simp [agar_eval, hL.2.2]; rfl
    · isplitl [HPn HPnw]
      · iright; iframe HPn; iframe HPnw; ipure_intro; exact hR
      ipure_intro
      refine ⟨false, ?_⟩; simp [agar_eval, hR.2.2.1]; rfl
  case HBodyA =>
    iintro ⟨HIH, ⟨%hgtrue, HI⟩⟩
    icases HI with (⟨HPn, HPnw, %hL⟩ | ⟨HPn, HPnw, %hR⟩)
    · obtain ⟨hnext, hnow, _⟩ := hL
      wp_lstep
      wp_load_direct HPn (by exact hnext)
      wp_lstep
      wp_lstep
      iapply wp_cas_succ (GF := GF) (F := F)
        (vO := Val.int 0) (vN := Val.int 1)
        (heL := by simpa [agar_eval] using hnext)
        (heO := by agar_eval)
        (heN := by agar_eval)
        (heq := by decide)
      iframe HPn
      iintro !> HPn
      wp_lstep
      iapply wp_ite_true (heval := by agar_eval)
      iintro !>
      wp_lstep
      wp_lstep
      ihave HIH := HIH $$ %(((env.set "t" (Val.int 0)).set "r" (Val.int 0)).set "doneA" (Val.int 1))
      iapply HIH
      iright
      iframe HPn
      iframe HPnw
      ipure_intro
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [agar_eval] using hnext
      · simpa [agar_eval] using hnow
      · agar_eval
      · agar_eval
    -- RIGHT disjunct: doneA = 1 contradicts hgtrue (`doneA = 0` evaluates false).
    exfalso
    simp [agar_eval, hR.2.2.1] at hgtrue
    exact absurd hgtrue (by decide)
  case HExitA =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with (⟨_HPn, _HPnw, %hL⟩ | ⟨HPn, HPnw, %hR⟩)
    · exact absurd hgfalse (by simp [agar_eval, hL.2.2]; decide)
    obtain ⟨_hnext, hnow, _, ht⟩ := hR
    wp_pures_no_loop
    -- LOOP B: spin on `now == t`. LEFT = pre-check; RIGHT = checked.
    -- `now` stays at 0 throughout; protocol state lives in `doneB`.
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
      · -- LEFT: doneB = 0 ⇒ guard is true.
        isplitl [HPnw]
        · ileft; iframe HPnw; ipure_intro; exact hL
        ipure_intro; refine ⟨true, ?_⟩
        simp [agar_eval, hL.2.2]; rfl
      · -- RIGHT: doneB = 1 ⇒ guard is false.
        isplitl [HPnw]
        · iright; iframe HPnw; ipure_intro; exact hR
        ipure_intro; refine ⟨false, ?_⟩
        simp [agar_eval, hR.2]; rfl
    case HBodyB =>
      iintro ⟨HIH, ⟨%hgtrue, HI⟩⟩
      icases HI with (⟨HPnw, %hL⟩ | ⟨HPnw, %hR⟩)
      · obtain ⟨hnow, ht, _⟩ := hL
        wp_lstep
        wp_load_direct HPnw (by exact hnow)
        wp_lstep
        -- Loaded `nv = 0`; `t = 0` from LEFT, so guard `t = nv` is true.
        iapply wp_ite_true (heval := by simp [agar_eval, ht]; rfl)
        iintro !>
        wp_lstep
        wp_lstep
        ihave HIH := HIH $$ %((env.set "nv" (Val.int 0)).set "doneB" (Val.int 1))
        iapply HIH
        iright
        iframe HPnw
        ipure_intro
        refine ⟨?_, ?_⟩
        · simpa [agar_eval] using hnow
        · agar_eval
      -- RIGHT disjunct has `doneB = 1`, contradicting hgtrue.
      exfalso
      simp [agar_eval, hR.2] at hgtrue
      exact absurd hgtrue (by decide)
    case HExitB =>
      iintro ⟨%hgfalse, HI⟩
      icases HI with (⟨_HPnw, %hL⟩ | ⟨HPnw, %hR⟩)
      · exact absurd hgfalse (by simp [agar_eval, hL.2.2]; decide)
      obtain ⟨hnow, _⟩ := hR
      wp_pures
      wp_load_direct HPnw (by exact hnow)
      wp_lstep
      wp_lstep
      iapply wp_store (GF := GF) (F := F)
        (heL := by simpa [agar_eval] using hnow)
        (heV := by agar_eval)
      iframe HPnw
      iintro !> _HPnw
      wp_lstep
      iapply (wp_ret_top _ _ (Expr.bin BinOp.add (Expr.var "rn") (Expr.val (Val.int 1)))
        (Val.int 1) [] _ _ (heval := by agar_eval))
      ipure_intro; rfl
    · ileft
      iframe HPnw
      ipure_intro
      refine ⟨?_, ?_, ?_⟩
      · simpa [agar_eval] using hnow
      · simpa [agar_eval] using ht
      · agar_eval
  · ileft
    iframe HPnext
    iframe HPnow
    ipure_intro
    refine ⟨?_, ?_, ?_⟩ <;> agar_eval

end Agar.Logic

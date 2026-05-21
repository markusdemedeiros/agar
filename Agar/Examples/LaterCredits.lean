module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Instances.Lib.LaterCredits

@[expose] public section

/-! # Later-credit demo

This file demonstrates *use* of Iris later credits (`£ n`) in isolation
from Agar's program logic. The rest of the Agar development imports
`InvGS_gen`, which extends `LcGS`, so credits are *available* in every
closed proof; until now they were always discarded (`intro _LC`). This
file shows the canonical credit-spending pattern: trading one credit for
one `▷`-strip, and iterating that to handle `n` laters with `n` credits.

The core API used (from `Iris.Instances.Lib.LaterCredits`):
* `£ n`             — own `n` later credits.
* `lc_split`        — `£ (n + m) ⊣⊢ £ n ∗ £ m`.
* `lc_succ`         — `£ (.succ n) ⊣⊢ £ 1 ∗ £ n`.
* `le_upd_later`    — `£ 1 -∗ ▷ P -∗ |==£> P`. *The* credit-spending lemma.
* `lc_soundness`    — closes a plain goal by allocating `m` credits.

All proofs are sorry-free and avoid Löb induction; the recursion is on
the credit budget, not on a guarded fixpoint.
-/

namespace Agar.Examples.LaterCredits

open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors}

section CreditSpending

variable [LcGS GF]

/-- **Canonical credit-spending step.** With one later credit, we can
strip a single `▷` and produce `|==£> P`. -/
theorem strip_one_later (P : IProp GF) :
    ⊢ £ 1 -∗ ▷ P -∗ |==£> P := by
  iintro Hc HP
  iapply le_upd_later $$ Hc HP

/-- **Two credits strip two laters.** No Löb: the recursion is on the
credit budget. -/
theorem strip_two_laters (P : IProp GF) :
    ⊢ £ 2 -∗ ▷ ▷ P -∗ |==£> P := by
  iintro Hc HP
  -- Peel the credit bag into two singletons.
  ihave ⟨Hc1, Hc2⟩ := (lc_split (n := 1) (m := 1)).mp $$ Hc
  -- Spend the first credit to strip the outer ▷.
  imod le_upd_later $$ Hc1 HP with HP
  -- Spend the second credit to strip the inner ▷.
  iapply le_upd_later $$ Hc2 HP

/-- **Bounded iteration: `n` credits strip `n` laters.** Induction on
the credit budget. With `£ n` in hand we can convert `▷^[n] P` into
`|==£> P` for *any* `P`. -/
theorem strip_n_laters (n : Nat) (P : IProp GF) :
    ⊢ £ n -∗ ▷^[n] P -∗ |==£> P := by
  induction n with
  | zero =>
    -- `▷^[0] P` is definitionally `P`; introduce the update modality.
    show ⊢ £ 0 -∗ P -∗ |==£> P
    iintro _ HP
    iapply le_upd_intro $$ HP
  | succ k IH =>
    -- Unfold `▷^[k+1] P` to `▷ ▷^[k] P`.
    show ⊢ £ (k+1) -∗ ▷ ▷^[k] P -∗ |==£> P
    iintro Hc HP
    -- Split off one credit; recurse with the remaining `k`.
    ihave ⟨Hc1, Hck⟩ := lc_succ.mp $$ Hc
    -- Spend `Hc1` to strip the outer `▷`.
    imod le_upd_later $$ Hc1 HP with HP
    -- Now `HP : ▷^[k] P`; recurse on the credit budget.
    iapply IH $$ Hck HP

end CreditSpending

section Soundness

variable [LcGpreS GF]

/-- **Closing soundness via credits.** For any pure proposition `φ`,
if we can derive `⌜φ⌝` after spending `n` credits, then `⌜φ⌝` holds —
and hence `φ`. This is `lc_soundness` instantiated at a pure goal,
showing that the credit-spending pipeline composes through the
soundness theorem. -/
theorem pure_via_credits (n : Nat) (φ : Prop)
    (H : ∀ [_LC : LcGS GF], ⊢@{IProp GF} £ n -∗ |==£> ⌜φ⌝) :
    ⊢@{IProp GF} ⌜φ⌝ :=
  lc_soundness (GF := GF) n (P := iprop(⌜φ⌝)) (fun {_} => H)

end Soundness

end Agar.Examples.LaterCredits

module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Heap
public import Agar.Iris.Rules
public import Agar.Iris.Tactics

@[expose] public section

/-! # Atomic-triple proof-mode combinators

`wp_cas_atomic_split` fuses the recurring 5-line opening for a CAS over
a disjunctive shared invariant:

```
iapply wp_cas_atomic (P := P) (vO := vO) (vN := vN) (Hsub := ...) ...
iframe HI
iintro HP
ihave HP := BI.later_or.mp $$ HP
icases HP with <pat>
```

The combinator handles everything except the user-specific `icases`
pattern (which depends on the *shape* of the disjuncts of `P`). This
covers the TOP-1 boilerplate site identified in the audit
(see `TACTICS.md`).

### Shape restriction

The tactic assumes the invariant body `P` is of the form `Pl ∨ Pr` so
that `BI.later_or.mp` applies. Non-disjunctive invariants (or
disjunctions nested under quantifiers/separating-conjunctions) need a
custom opening. Tri-disjunct bodies (`A ∨ B ∨ C` parsed as
`A ∨ (B ∨ C)`) require nested patterns `(>a | (>b | >c))`.
-/

namespace Agar.Logic

open Iris Iris.BI

/-- `wp_cas_atomic_split HI P vO vN hne with pat`:

* `HI`  — name of the persistent invariant hypothesis in the IPM
  context (the `inv N P` fragment, typically demoted via `#HI`).
* `P`   — the invariant body (a disjunction `Pl ∨ Pr`).
* `vO`, `vN` — the CAS expected / new values.
* `hne` — discriminator term `∀ v, v ≠ vO → (v == vO) = false`.
* `pat` — `icases` pattern for splitting the (later-stripped)
  disjunctive body, e.g. `(⟨>HLk, >HOwn, %vc, >HC⟩ | >HLk1)`.

Applies `wp_cas_atomic`, frames the invariant via `HI`, introduces the
accessor body as `HP`, commutes `▷` across the top-level `∨`, and runs
`icases HP with pat`. Leaves the user with one subgoal per disjunct,
with `▷` already stripped from each timeless sub-conjunct mentioned in
the pattern. The CAS namespace is fixed to `nroot` and `Hsub` to the
`CoPset.full` discharger, matching the Mutex-style invocation pattern.

Side conditions `heL`, `heO`, `heN` are discharged via `agar_eval` and
`heq` via `decide`. Other shapes (different namespace, partial
invariant masks) require the raw `iapply wp_cas_atomic`. -/
scoped syntax "wp_cas_atomic_split " ident ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max " with " icasesPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wp_cas_atomic_split $hi:ident $P:term $vO:term $vN:term
                                  $hne:term with $pat:icasesPat) => do
      let hiSel : Lean.TSyntax `selPat ← `(selPat| $hi:ident)
      `(tactic| (
        iapply wp_cas_atomic (N := nroot)
          (P := $P) (vO := $vO) (vN := $vN)
          (Hsub := by
            first | (rw [nclose_root]) | exact (fun _ _ => CoPset.mem_full))
          (heL := by agar_eval) (heO := by agar_eval) (heN := by agar_eval)
          (heq := by first | decide | rfl)
          (hne_of_ne := $hne)
        iframe $hiSel
        iintro HP
        ihave HP := BI.later_or.mp $$ HP
        icases HP with $pat))

/-! ## `cas_dead` — discharge a dead CAS wand

After opening the disjunctive invariant via `wp_cas_atomic_split` under
a specific disjunct, ONE of the two wands the CAS rule hands you is
ALWAYS dead:

* opened under the disjunct whose heap value equals `vO` — the
  *failure* wand requires `vcur ≠ vO` and is unreachable;
* opened under the disjunct whose heap value differs from `vO` — the
  *success* wand requires `vcur = vO` and is unreachable.

The dead-wand discharge always has the same shape: introduce the
side-condition (`hne : vcur ≠ vO` or `heq : vcur = vO`), throw the
remaining post-CAS resource, and close `False` from the side-condition
against the disjunct's heap value (a concrete `Val.int n` or `Val.loc l`).
`cas_dead` packs all five concrete discharge patterns that appear across
the examples folder into one tactic:

* `exact absurd rfl hne` — fail wand, value chosen = vO
* `injection heq with h; omega` — succ wand, Val.int n ≠ Val.int 0
* `cases heq` — succ wand, Val.loc l ≠ Val.int 0
* `Val.noConfusion heq …` — succ wand, Val.int n ≠ Val.int m

Reader sees `cas_dead` and knows the branch is the unreachable one. -/
scoped macro "cas_dead" : tactic => `(tactic|
  first
  | (iintro %hne _; exact absurd rfl hne)
  | (iintro %heq _; exfalso; injection heq with h; omega)
  | (iintro %heq _; exfalso; cases heq)
  | (iintro %heq _; exact Val.noConfusion heq (fun h => absurd h (by decide))))

/-! ## `inv_close_left` / `inv_close_right` — close a CAS wand by
re-establishing one disjunct of the invariant

The "live" wand of a `wp_cas_atomic_split` open is the one that
actually fires under the chosen disjunct. Its body always starts the
same four-line incantation:

```
iintro %_ HX              -- consume the side-condition; HX is the heap after the wand
imodintro                 -- commit the fupd
isplitl [HX]              -- send HX to close the invariant; keep the wp continuation
· inext; ileft; iexact HX -- (or iright)
```

The maneuver names a single move: "close the invariant in the LEFT
(resp. RIGHT) disjunct with `HX`." The remaining wp goal — whatever
the caller does next, whether `wp_done`, a critical section, or a
release-store — is left to the caller, so the tactic composes both for
terminal closes (single-CAS workers) and for in-flight closes (a
mutex's `acquire` leaves the critical section as the residual wp).

Single-resource form only — disjuncts that bundle ghosts
(`Counter.lean`, `Mutex.lean`) or existential witnesses
(`TreiberPush.lean`) still need a manual `iframe`/`iexists` dance.
A variadic generalisation would be possible but the multi-resource
cases are too few to motivate it. -/

scoped macro "inv_close_left " h:ident : tactic => `(tactic|
  (iintro %_ $h:ident
   imodintro
   isplitl [$h:ident]
   · inext; ileft; iexact $h:ident))

scoped macro "inv_close_right " h:ident : tactic => `(tactic|
  (iintro %_ $h:ident
   imodintro
   isplitl [$h:ident]
   · inext; iright; iexact $h:ident))

/-! ## `cas_succeed_with` / `cas_fail_with` — name the protocol decision

After `wp_cas_atomic_split` opens a disjunct, the next four lines tell
which side of the CAS will fire under the chosen disjunct:

```
imodintro            -- commit the fupd
iexists VX           -- announce the heap value we just opened with
iframe HY            -- frame the heap fragment
isplitl []           -- route resources for succ-live (LEFT goal = succ wand)
   -- ... or ...
isplitr              -- route resources for fail-live (RIGHT goal = fail wand)
```

`isplitr` is literally `isplitl []` (see `Iris/ProofMode/Tactics/Split`),
so the only semantic content of these four lines is "given the open we
chose, the CAS will *succeed* (resp. *fail*) here." Name that decision:

* `cas_succeed_with VX HY` — opened on the disjunct that holds VX, so
  the cell *equals* the expected vO and the CAS succeeds. First subgoal
  is the live succ-wand; second is the dead fail-wand (`cas_dead`).
* `cas_fail_with VX HY` — opened on the disjunct that holds VX where
  VX ≠ vO, so the CAS fails. First subgoal is the dead succ-wand; second
  is the live fail-wand.

This is the simple form — no extra spatial resources to route to either
side. Sites that hold ghost resources (`Counter.lean`, `Mutex.lean`)
still use the explicit `isplitl [Hauth Hfrag]` so the ghosts flow into
the live wand. -/

scoped macro "cas_succeed_with" ppSpace vX:term:max ppSpace hY:ident : tactic =>
  `(tactic| (imodintro; iexists $vX; iframe $hY:ident; isplitl []))

scoped macro "cas_fail_with" ppSpace vX:term:max ppSpace hY:ident : tactic =>
  `(tactic| (imodintro; iexists $vX; iframe $hY:ident; isplitr))

/-! ## `wp_load_atomic_open` — atomic load through the canonical
existential-points-to invariant

When the shared invariant body is just `∃ v, l ↦ v` (the simplest
shape — no ghost, no constraint), every atomic load goes through the
same twelve-line dance:

```
iapply wp_load_atomic (GF := …) (F := …) (N := nroot)
  (P := iprop(∃ v : Val, points_to (GF := …) (F := …) _ v))
  (Hsub := by rw [nclose_root]) (heL := heL_fact)
iframe HI
iintro >⟨%vcur, HP⟩          -- accessor: open inv, ▷-strip into vcur + l↦vcur
imodintro
iexists vcur
isplitl [HP]
· iexact HP                  -- give the load the heap fragment
iintro HP                    -- closing wand: get the heap back unchanged
imodintro
isplitl [HP]
· inext; iexists vcur; iexact HP   -- re-close inv with same vcur
```

The whole sequence is mechanical for this body shape — only `HI`
(the persistent invariant) and `heL` (the `Expr.eval env eL = some
(.loc l)` fact) carry semantic content. `wp_load_atomic_open HI heL`
names the move.

After the tactic, the local `vcur : Val` is in scope (its actual value
unknown beyond the invariant's existential) and the env has the load's
target bound to `vcur`. The caller continues with whatever the program
does next.

Body shapes other than `∃ v, l ↦ v` (Readback's `∃ v, l↦v ∗ ⌜v ∈ S⌝`,
ghost-augmented bodies, …) still need the raw `iapply wp_load_atomic`. -/

scoped syntax "wp_load_atomic_open" ppSpace ident ppSpace term : tactic
set_option hygiene false in
scoped macro_rules
  | `(tactic| wp_load_atomic_open $hi:ident $heL:term) => `(tactic| (
      iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
        (P := iprop(∃ v : Val, points_to (GF := GF) (F := F) _ v))
        (Hsub := by rw [nclose_root])
        (heL := $heL)
      iframe $hi:ident
      iintro >⟨%vcur, HP⟩
      imodintro
      iexists vcur
      isplitl [HP]
      · iexact HP
      iintro HP
      imodintro
      isplitl [HP]
      · inext; iexists vcur; iexact HP))

end Agar.Logic

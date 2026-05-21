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

end Agar.Logic

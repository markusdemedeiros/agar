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

@[expose] public section

/-! # Agar proof-mode tactics

`wp_step` inspects the head `Stmt` of the WP goal and applies the
appropriate rule from `Rules.lean`, discharging trivial side
conditions. For pure non-eval rules the user is left with the
post-step `▷` premise; for heap rules they are left with the
points-to obligation; for the eval-bearing rules the `heval`
side-condition is dispatched via `agar_eval`.
-/

namespace Agar.Logic

open Iris Iris.BI

/-- A `simp`-driven discharger for `Expr.eval … = some _` side
conditions arising in the `wp_*` rules. -/
scoped macro "agar_eval" : tactic => `(tactic|
  first
  | rfl
  | (simp [agar_eval]; done)
  | (simp [agar_eval]; rfl))

/-- One pure step. Picks the rule by head-`Stmt` match and discharges
any `heval`/decidable guard side condition. Leaves the continuation
under a `▷` as the remaining goal. -/
scoped macro "wp_step" : tactic => `(tactic|
  first
  | iapply wp_skip_cons
  | iapply wp_seq
  | (iapply wp_assign; · agar_eval)
  | (iapply wp_ite_true;  · agar_eval)
  | (iapply wp_ite_false; · agar_eval)
  | iapply wp_while
  | (iapply wp_ret_top; · agar_eval)
  | iapply wp_skip_frame_cons
  | iapply wp_skip_frame_nil
  | (iapply wp_ret_pop_cons; · agar_eval)
  | (iapply wp_ret_pop_nil;  · agar_eval)
  | iapply wp_call _ _ _ _ _ _ _ _ _ _ _ rfl (by agar_eval) rfl
  | iapply wp_fork _ _ _ _ _ _ _ _ _ _ rfl (by agar_eval) rfl)

/-- Close a terminal WP goal:
* `return e` at the top of the stack via `wp_ret_top` (eval via `agar_eval`);
* a value thread via `wp_value` (defaulting the value to `Val.unit`).

After picking a closer, try to fully discharge a leftover `⌜v = v⌝` /
`⌜True⌝` obligation via `ipure_intro; rfl` (or `trivial`), or an `emp`
residual (as arises with `fork_post := emp` on a forked terminal thread)
via `iemp_intro`. -/
scoped macro "wp_done" : tactic => `(tactic|
  ((first
    | (iapply wp_ret_top; · agar_eval)
    | (iapply wp_value _ _ _ Val.unit _ rfl)
    | iapply wp_value)
   <;> try (first
            | iemp_intro
            | (ipure_intro
               <;> first
                   | rfl
                   | trivial
                   | (show _ = _; rfl)
                   | (simp; done)))))

/-- Chain `wp_step` until it stops making progress, stripping `▷`
modalities before, between, and after pure steps via `iintro !>`.

Terminal-safe: when no `wp_step` alternative applies (e.g. the head is a
value thread `⟨skip, [], _, [], none⟩`) the loop stops cleanly instead
of forcing `wp_fork` and erroring out. -/
scoped macro "wp_steps" : tactic => `(tactic|
  (try iintro !>
   try wp_step
   repeat (first | (iintro !>; wp_step) | wp_step)
   try iintro !>))

/-- One *pure* step. Strictly more restrictive than `wp_step`: only the
rules that do not require user input or unification with external data
(no `wp_call`, `wp_fork`, `wp_ret_*`). Specifically tries — in order:

* `wp_skip_cons` (advance past a leading `skip`);
* `wp_seq` (split a `;`);
* `wp_assign` (with `agar_eval` discharging the eval side condition);
* `wp_ite_true` / `wp_ite_false` (only when the guard reduces concretely);
* `wp_while` (one unfolding);
* `wp_skip_frame_cons` / `wp_skip_frame_nil` (frame skip on return-to-skip).

Stops cleanly (`fail`s) if the head statement is not a pure step — the
caller should then invoke a more specific tactic (`wp_call`,
`wp_load HP`, `wp_ret`, etc.). -/
scoped macro "wp_pure_step" : tactic => `(tactic|
  first
  | iapply wp_skip_cons
  | iapply wp_seq
  | (iapply wp_assign; · agar_eval)
  | (iapply wp_ite_true;  · agar_eval)
  | (iapply wp_ite_false; · agar_eval)
  | iapply wp_while
  | iapply wp_skip_frame_cons
  | iapply wp_skip_frame_nil)

/-- Chain `wp_pure_step` until it stops making progress. Mirrors
`wp_steps` but uses only the *pure* rule fragment, so it never tries to
fire `wp_call`/`wp_fork`/`wp_ret_*`. This is what TACTICS.md calls
`wp_pures`: take whatever pure steps are available and stop when we hit
something that needs user input (a heap op, a `call`, a `ret`, or an
`ite` whose guard doesn't reduce).

Terminal-safe: stops cleanly when no pure rule applies. Strips `▷`
modalities between successive steps via `iintro !>`. -/
scoped macro "wp_pures" : tactic => `(tactic|
  (try iintro !>
   try wp_pure_step
   repeat (first | (iintro !>; wp_pure_step) | wp_pure_step)
   try iintro !>))

/-! ## Local proof-mode helpers

iris-lean now ships its own `iframe` tactic (since
[#378](https://github.com/leanprover-community/iris-lean/pull/378)), so
we no longer define a local syntactic version. The native `iframe`
inspects the goal and the spatial context, handles either side of a
separating conjunction, and recurses appropriately. -/

/-- `itrivial` discharges "obvious" IPM goals: a spatial assumption, an
`emp` goal, or a pure goal closable by `rfl`/`trivial`/`decide`. -/
scoped macro "itrivial" : tactic => `(tactic|
  first
  | iassumption
  | iemp_intro
  | (ipure_intro <;> first | rfl | trivial | decide))

/-! ## Heap-step variants

Each takes a `points_to` term from the IPM context and leaves the
post-step obligation. -/

/-- `wp_load HP` consumes `HP : l ↦ v` and leaves the post-step
obligation with `HP` re-introduced under `▷`. -/
scoped syntax "wp_load " ident : tactic
macro_rules
  | `(tactic| wp_load $h:ident) => `(tactic| (
      iapply wp_load _ _ _ _ _ _ _ _ _ _ (by agar_eval)
      isplitl [$h]
      iexact $h))

/-- `wp_store HP` consumes `HP : l ↦ vold`. -/
scoped syntax "wp_store " ident : tactic
macro_rules
  | `(tactic| wp_store $h:ident) => `(tactic| (
      iapply wp_store _ _ _ _ _ _ _ _ _ _ _ (by agar_eval) (by agar_eval)
      isplitl [$h]
      iexact $h))

/-- `wp_load_keep HP` is `wp_load HP` followed by `iintro !> HP`,
restoring the points-to into the spatial context under the post-step. -/
scoped syntax "wp_load_keep " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_load_keep $h:ident) => `(tactic| (
      iapply wp_load _ _ _ _ _ _ _ _ _ _ (by agar_eval)
      isplitl [$h]
      iexact $h
      iintro !> $h:ident))

/-- `wp_store_keep HP` is `wp_store HP` followed by `iintro !> HP`,
restoring the (updated) points-to into the spatial context under `▷`. -/
scoped syntax "wp_store_keep " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_store_keep $h:ident) => `(tactic| (
      iapply wp_store _ _ _ _ _ _ _ _ _ _ _ (by agar_eval) (by agar_eval)
      isplitl [$h]
      iexact $h
      iintro !> $h:ident))

/-- `wp_load_direct HP heval` is like `wp_load_keep HP`, but takes an
explicit term `heval : Expr.eval env e = some (.loc l)` rather than
trying `agar_eval`. Useful in non-atomic regions where the location
expression is bound by a hypothesis rather than a literal name. The
points-to `HP` is restored under `▷` after the step. -/
scoped syntax "wp_load_direct " ident ppSpace term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_load_direct $h:ident $heval:term) => `(tactic| (
      iapply wp_load _ _ _ _ _ _ _ _ _ _ $heval
      isplitl [$h]
      iexact $h
      iintro !> $h:ident))

/-- `wp_store_direct HP heL heV` is like `wp_store_keep HP`, but takes
explicit terms for the two `Expr.eval` side conditions rather than
trying `agar_eval`. Useful in non-atomic regions where the source
expressions are bound by hypotheses rather than literals. The points-to
`HP` is restored (with the new value) under `▷` after the step. -/
scoped syntax "wp_store_direct " ident ppSpace term:max ppSpace term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_store_direct $h:ident $heL:term $heV:term) => `(tactic| (
      iapply wp_store _ _ _ _ _ _ _ _ _ _ _ $heL $heV
      isplitl [$h]
      iexact $h
      iintro !> $h:ident))

/-- `wp_free HP` consumes `HP : l ↦ v`. -/
scoped syntax "wp_free " ident : tactic
macro_rules
  | `(tactic| wp_free $h:ident) => `(tactic| (
      iapply wp_free _ _ _ _ _ _ _ _ _ (by agar_eval)
      isplitl [$h]
      iexact $h))

/-- `wp_cas_succ HP heq` consumes `HP : l ↦ vO` and produces `HP : l ↦ vN`
under `▷`. The three `Expr.eval` side conditions are discharged via
`agar_eval`; the `(vO == vO) = true` reflexivity obligation is supplied
as the term `heq` (the derived `BEq Val` is opaque outside `Syntax.lean`,
so the caller must produce it). -/
scoped syntax "wp_cas_succ " ident (ppSpace colGt term:max)? : tactic
macro_rules
  | `(tactic| wp_cas_succ $h:ident) => `(tactic| (
      iapply wp_cas_succ _ _ _ _ _ _ _ _ _ _ _ _ _
        (by agar_eval) (by agar_eval) (by agar_eval)
        (by first | exact val_beq_refl _ | rfl | decide)
      isplitl [$h]
      iexact $h))
  | `(tactic| wp_cas_succ $h:ident $heq:term) => `(tactic| (
      iapply wp_cas_succ _ _ _ _ _ _ _ _ _ _ _ _ _
        (by agar_eval) (by agar_eval) (by agar_eval) $heq
      isplitl [$h]
      iexact $h))

/-- `wp_cas_fail HP hne` consumes `HP : l ↦ cur` and restores it under
`▷`. Three `Expr.eval` side conditions discharged via `agar_eval`; the
discriminating `(cur == vO) = false` obligation is supplied as the
term `hne`. The points-to is split out *first* so `cur` is pinned by
the time `hne` elaborates. -/
scoped syntax "wp_cas_fail " ident ppSpace term:max : tactic
macro_rules
  | `(tactic| wp_cas_fail $h:ident $hne:term) => `(tactic| (
      iapply wp_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (by agar_eval) (by agar_eval) (by agar_eval) $hne
      isplitl [$h]
      iexact $h))

/-- `wp_alloc` leaves a `▷ ∀ l, l ↦ v -∗ wp …` obligation. -/
scoped macro "wp_alloc" : tactic => `(tactic|
  iapply wp_alloc _ _ _ _ _ _ _ _ _ (by agar_eval))

/-- `wp_alloc_intro HP` is `wp_alloc` followed by `iintro !> %l HP`:
strips the `▷`, binds the fresh location as a pure `l` (callers can
also write `wp_alloc_intro l HP` to choose the location name), and
names the fresh points-to fragment `HP` in the IPM context. -/
scoped syntax "wp_alloc_intro " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_alloc_intro $h:ident) => `(tactic| (
      iapply wp_alloc _ _ _ _ _ _ _ _ _ (by agar_eval)
      iintro !> %l $h:ident))

/-! ## Procedure call / fork variants

These handle the procedure-table lookup (`procs f = some proc`), the
argument evaluation, and the arity check. The lookup is discharged via
`rfl` so the procedure table must be statically known at the call site. -/

/-- `wp_call` (no argument) discharges the call's three side conditions
and leaves the WP of the procedure body under `▷`. The argument form
`wp_call f` additionally strips the resulting `▷` and unfolds the
named procedure body `f`. -/
scoped syntax (name := wpCallTac) "wp_call" (colGt ident)? : tactic
macro_rules
  | `(tactic| wp_call) => `(tactic|
      iapply wp_call _ _ _ _ _ _ _ _ _ _ _ rfl (by agar_eval) rfl)
  | `(tactic| wp_call $f:ident) => `(tactic| (
      wp_call
      iintro !>
      unfold $f))

/-- `wp_unfold_proc f` is a back-compat alias for `wp_call f`. -/
scoped syntax "wp_unfold_proc " ident : tactic
macro_rules
  | `(tactic| wp_unfold_proc $f:ident) => `(tactic| wp_call $f:ident)

/-- `wp_fork` discharges the fork's three side conditions and leaves a
separating conjunction of the forked-thread WP and the parent's
continuation WP. -/
scoped macro "wp_fork" : tactic => `(tactic|
  iapply wp_fork _ _ _ _ _ _ _ _ _ _ rfl (by agar_eval) rfl)

/-- `wp_call_pure proc` fuses the recurring 8-step skeleton seen in
closed adequacy proofs whose main thread calls a pure procedure, binds
the result to a local, and returns it:

```
wp_step    -- wp_seq: head call ; return v
iintro !>
wp_step    -- wp_call: enter callee body
iintro !>
unfold proc
wp_step    -- wp_ite_* / wp_ret_pop_nil inside the body
iintro !>
wp_steps   -- drive to terminal value
itrivial
```

The middle `wp_step ; iintro !>` pair handles the first internal
statement of the callee (an `if` guard, a `return e`, etc.); `wp_steps`
takes over from there. Used to compress `progCallSeven_closed`,
`progCallAdd_closed`, `progCallMin_closed`, `max_5_3_closed`,
`abs_neg3_closed` into a single line of WP discharge each. -/
scoped syntax "wp_call_pure " ident : tactic
macro_rules
  | `(tactic| wp_call_pure $f:ident) => `(tactic| (
      wp_step
      iintro !>
      wp_step
      iintro !>
      unfold $f
      wp_step
      iintro !>
      wp_steps
      itrivial))

/-! ## Universal Hoare-spec application

Closed adequacy proofs that derive from a universal `*_spec` /
`*_spec_gen` lemma share a verbose pattern: instantiate the spec at
positional arguments (`procs`, `fork_post`, the substantive `a/b/n/x/eX`,
`cont`, `env`, `stack`), and discharge the trailing
`procs "f" = some f` / `Expr.eval env e = some _` side conditions with
`rfl` / `agar_eval`.

### `wp_apply` — bare-hypothesis entry point

`wp_apply h` (defined further down) accepts a hypothesis or term whose
conclusion entails (or *is*) `wp ⟨.call …⟩ Φ`, and `iapply`s it. This
handles:

* a Löb IH inside a recursive-proc proof (`wp_apply HIH $$ %a …`);
* a fully-instantiated spec term (`wp_apply (maxProc_spec _ _ 5 3 …)`);
* a `*_spec` lemma in *Hoare-triple* form (the triple notation
  `⦃ P ⦄ t ⦃ Q ⦄` unfolds to a plain entailment, so `iapply` accepts it).

For shape-specific call-site application with auto-discharge of the
`procs "f" = some f` and `Expr.eval … = some _` side conditions, the
legacy per-shape macros (`wp_apply_binop_spec`, `wp_apply_unary_spec`,
`wp_apply_gen_call_spec`, `wp_apply_gen_binop_spec`) remain available —
they bake the trailing arguments and discharge them via
`rfl` / `agar_eval`. A unified positional `wp_apply h args*` form was
*not* added because the four shapes are not all distinguishable by
arity (binop and gen-call both take 9 positional terms), so a single
keyword would either resolve ambiguously or require an explicit
shape-selector. The (E := ⊤) annotation is fixed in the `_gen`
variants; the non-gen variants leave `E` implicit. -/

scoped syntax "wp_apply_binop_spec " term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| wp_apply_binop_spec $spec $a $b $x $eA $eB $cont $env $stack) =>
      `(tactic|
        iapply ($spec _ _ $a $b $x $eA $eB $cont $env $stack _
                  rfl (by agar_eval) (by agar_eval)))

scoped syntax "wp_apply_unary_spec " term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| wp_apply_unary_spec $spec $x $r $eX $cont $env $stack) =>
      `(tactic|
        iapply ($spec _ _ $x $r $eX $cont $env $stack _
                  rfl (by agar_eval)))

scoped syntax "wp_apply_gen_call_spec " term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| wp_apply_gen_call_spec $spec $procs $Φ $n $x $eN $cont $env $stack) =>
      `(tactic|
        iapply ($spec (E := ⊤) $procs iprop(emp : IProp _) (by rfl) $Φ
                  $n $x $eN $cont $env $stack (by agar_eval)))

scoped syntax "wp_apply_gen_binop_spec " term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
    ppSpace term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| wp_apply_gen_binop_spec $spec $procs $Φ $a $b $ha $hb $eA $eB
                $x $cont $env $stack) =>
      `(tactic|
        iapply ($spec (E := ⊤) $procs iprop(emp : IProp _) (by rfl) $Φ
                  $a $b $ha $hb $x $eA $eB $cont $env $stack
                  (by agar_eval) (by agar_eval)))

/-- Bare-hypothesis form: `wp_apply h` is equivalent to `iapply h`.
This is the most general form — it accepts any term whose type entails
the current WP goal, including:

* a Löb induction hypothesis (`wp_apply HIH $$ %a %b ...` with
  pmTerm-style specialisation arguments);
* a fully-instantiated spec term (`wp_apply (maxProc_spec _ _ 5 3 …)`);
* a `*_spec` lemma in *Hoare-triple* form (the triple notation
  `⦃ P ⦄ t ⦃ Q ⦄` unfolds to a plain entailment, so `iapply` accepts it).

For shape-specific call-site application with auto-discharge of the
`procs "f" = some f` and `Expr.eval … = some _` side conditions, use
the per-shape macros below (`wp_apply_binop_spec`,
`wp_apply_unary_spec`, `wp_apply_gen_call_spec`,
`wp_apply_gen_binop_spec`). -/
scoped syntax (name := wpApplyBare) "wp_apply " colGt pmTerm : tactic
macro_rules
  | `(tactic| wp_apply $h:pmTerm) => `(tactic| iapply $h:pmTerm)

/-! ## Invariant-allocation combinator

`wp_inv_alloc_pt HP HI N` allocates a shared-cell invariant
`inv nroot (∃ v, l ↦ v)` from a heap fragment `HP : l ↦ Val.int N`,
binding the resulting (persistent) invariant as `HI`. Replaces the
6-line `iapply fupd_wp ; imod inv_alloc ... ; · inext ... ; imodintro`
motif repeated 5+ times in `ClosedProofInv.lean`. -/
scoped syntax "wp_inv_alloc_pt " ident ppSpace icasesPat ppSpace term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wp_inv_alloc_pt $h:ident $hi:icasesPat $n:term) => do
      let hf : Lean.TSyntax `frameIdent ← `(frameIdent| $h:ident)
      `(tactic| (
        iapply fupd_wp
        imod (inv_alloc nroot CoPset.full
                iprop(∃ v : Agar.Val, points_to _ v)) $$ [$hf] with $hi
        · inext; iexists (Agar.Val.int $n); iexact $h
        imodintro))

/-! ## Shared adequacy preamble macros

`heap_adequacy_intro` bundles the seven-line `wp_strong_adequacy_bupd`
opener used by every heap-touching `prog*_closed` theorem: allocate the
initial heap ghost, package the `AgarG` instance, supply the
`StateInterp` and a trivial frame `emp`, and frame the heap-auth
assumption `HA`. The caller is left staring at the WP for
`Thread.initial (main of prog)`.

`start_closed_proof_with_heap` additionally absorbs the leading
`intro _LC` that introduces the late-credit.
-/

@[expose] scoped syntax "heap_adequacy_intro" (ppSpace ident)? : tactic
set_option hygiene false in
scoped macro_rules
  | `(tactic| heap_adequacy_intro) => `(tactic| (
      imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
      imodintro
      letI : Agar.Logic.AgarG GF F := G
      letI SI : StateInterp GF := inferInstance
      iexists SI
      iexists iprop(emp : IProp GF)
      iframe HA))
  | `(tactic| heap_adequacy_intro $p:ident) => `(tactic|
      (heap_adequacy_intro; unfold Thread.initial $p))

@[expose] scoped syntax "start_closed_proof_with_heap" (ppSpace ident)? : tactic
set_option hygiene false in
scoped macro_rules
  | `(tactic| start_closed_proof_with_heap) => `(tactic|
      (intro _LC; heap_adequacy_intro))
  | `(tactic| start_closed_proof_with_heap $p:ident) => `(tactic|
      (intro _LC; heap_adequacy_intro $p))

/-! ## Extensions: ▷-commute helpers

`inext_or H` commutes `▷` past a disjunction in the IPM hypothesis
`H`, rewriting `H : ▷ (P ∨ Q)` to `H : ▷ P ∨ ▷ Q`. The caller
typically follows with `icases H with (>HL | >HR)` to strip the `▷`
from each arm (when the arms are timeless) and case-split. -/
scoped syntax "inext_or " ident : tactic
macro_rules
  | `(tactic| inext_or $h:ident) => `(tactic|
      ihave $h:ident := BI.later_or.mp $$ $h:ident)

end Agar.Logic

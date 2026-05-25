# Completeness — remaining work

This document breaks down the work remaining to complete the §3.2
port of Hostert et al. (see `COMPLETENESS.md` for the design). The
whole remaining surface reduces to **one shared core lemma** plus
straightforward consumers, sitting in `Agar/Iris/Completeness.lean`.

## ✓ The shared bottleneck: `icompl_pure_lookup` [LANDED]

Both Lemma 14 (`percomplete`) and the `weaken_post` wand need the same
thing — pulling pure facts out of `▷ Icompl_pure ∗ thread_at γ n t`.
Factor it once:

```lean
theorem icompl_pure_lookup
    {prog : Program} {φ : Val → Prop} {γ : GName} {n : Nat} {t : Thread} :
    iprop(▷ Icompl_pure prog φ γ ∗ thread_at γ n t) ⊢
      iprop(∃ ts, ⌜Machine.SafeTp prog ⟨Mem.empty, ts⟩ φ ∧
                   ts[n]? = some t⌝ ∗
            ▷ threadpool_auth γ ts ∗ thread_at γ n t)
```

### Proof sketch (~40 LoC)

1. Push `thread_at` under `▷` (it's `Timeless` — already proved in
   `Agar/Iris/Algebra/ThreadpoolRA.lean`).
2. Commute `▷` past the existential inside `Icompl_pure`. `List Thread`
   is inhabited (always `[]` available), so
   `▷ (∃ ts, P ts) ⊢ ∃ ts, ▷ P ts` is valid.
3. Commute `▷` past `∗`: `▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q`. Splits the
   `⌜SafeTp⌝` conjunct from the `threadpool_auth` conjunct.
4. Use `▷ ⌜P⌝ ⊢ ⌜P⌝` (pure is timeless via `pure_timeless`).
5. Apply `threadpool_lookup_frame` (framed lookup, already proved in
   `ThreadpoolRA.lean`) to recover `ts[n]? = some t` while keeping the
   auth + frag.
6. Bundle the two pure facts (SafeTp + lookup) into the existential.

This is the hardest fragment of Iris-Lean proof-mode work in the whole
port — about 40 lines of careful `▷`-commutation. Get it right and the
rest is bookkeeping.

**Status:** ✓ proved in `Agar/Iris/Completeness.lean`. Uses a small
helper `icompl_pure_unfold_later` that does the `▷ ∃ → ∃ ▷`
commutation, and a Lean-level `combine_lookup` lemma that applies
`threadpool_lookup_frame` under `▷` to derive the pure index agreement
while preserving both resources. Final `imod`s inside the surrounding
fupd extract the pure facts and re-emit `thread_at` via timelessness.

## ✓ Layer 2: `weaken_post` (~50 LoC) [LANDED]

Once `icompl_pure_lookup` lands, this drops in:

```lean
theorem weaken_post_proof
    {GF F …} … {prog : Program} {φ : Val → Prop} (γ : GName) (N : Namespace) :
    inv N (Icompl_pure prog φ γ) ⊢
      iprop(∀ v : Val, percomplete_post γ 0 v -∗ ⌜φ v⌝)
```

### Proof sketch

1. `iintro %v Hpost` — unpack the wand, get `Hpost : percomplete_post γ 0 v`.
2. `icases Hpost` — destructure to `t', Hn : 0 ↪γ t', hv : t'.toValue = some v`.
3. `imod (inv_acc …)` — open the invariant, get `▷ Icompl_pure ∗ Hclose`.
4. Apply `icompl_pure_lookup` — get the pure witness
   `⌜SafeTp ∧ ts[0]? = some t'⌝`.
5. `SafeTp.here` (already in `Adequacy.lean`) at index 0, applied to the
   pure witness: either `t'` is value-with-φ, or reducible. `hv` rules
   out non-value, so we get `φ v`.
6. Close the invariant via `Hclose`.

Uses only: `icompl_pure_lookup`, `Machine.SafeTp.here`,
`Thread.terminated_of_toValue` (already in `Completeness.lean`).

**Status:** ✓ proved as `weaken_post_proof` in
`Agar/Iris/Completeness.lean`. Conclusion has shape
`∀ v, percomplete_post γ 0 v -∗ |={⊤}=> ⌜φ v⌝` (fupd-prefixed, since
opening the invariant is a fupd). Theorem 15 was updated to use
`wp_wand_fupd` (a fupd-variant of `wp_wand`, also added) to absorb the
fupd into the WP's value branch.

## Layer 3: `percomplete` (Lemma 14) (~200 LoC)

The Löb-induction proof. Splits into four sub-pieces in order of
independence:

| Sub-piece                  | Uses                                                                                                  | LoC  |
|----------------------------|-------------------------------------------------------------------------------------------------------|------|
| **Value case**             | nothing extra — already in WIP code in git history                                                    | ✓    |
| **Pre-step reducibility**  | `icompl_pure_lookup`, `Machine.SafeTp.here`, `thread_reducible_heapFree_subst_m`                      | ~40  |
| **Pure-step IH**           | `threadpool_update`, `Machine.SafeTp.step_closed`, `tstep_heapFree_preserves`, `tstep_heapFree_subst_m` | ~80  |
| **Fork IH**                | adds `threadpool_insert` + a second IH application at `ts.length`                                     | ~50  |

### Proof structure

```lean
theorem percomplete … (htf : t.heapFree) :
    inv N (Icompl_pure prog φ γ) ∗ thread_at γ n t ⊢
      wp prog.procs True ⊤ t (percomplete_post γ n) := by
  -- (existing scaffolding: suffices key + BILoeb.loeb_weak)
  …
  iintro %n' %t' %htf' HI Hn
  iapply (equiv_iff.mp (wp_unfold …)).mpr
  by_cases hterm : t'.terminated = true
  · -- VALUE CASE  (already drafted)
    …
  · -- STEP CASE
    iright; isplitr · (terminated false)
    iintro %m HS
    -- PRE-STEP REDUCIBILITY:
    imod (inv_acc …) $$ HI with ⟨HIbody, Hclose⟩
    -- icompl_pure_lookup gives us ⌜SafeTp ∧ ts[n']? = some t'⌝
    ihave ⟨%ts, %hsafe, %hlk⟩ := icompl_pure_lookup $$ [HIbody Hn] …
    have hred_empty : thread_reducible prog.procs Mem.empty t' :=
      <SafeTp.here + hlk + non-terminated rules out value case>
    have hred_m : thread_reducible prog.procs m t' :=
      thread_reducible_heapFree_subst_m htf' hred_empty
    iapply fupd_mask_intro empty_subset
    iintro Hclose_eq
    isplitr · ipure_intro; exact hred_m
    iintro !> %m' %t'' %sp %hstep
    -- after iintro !>: HIbody is unguarded
    -- POST-STEP UPDATE:
    obtain ⟨chosen, htstep⟩ := hstep
    have hchosen := tstep_heapFree_chosen_none htf' htstep; subst hchosen
    have hm := tstep_heapFree_mem_unchanged htf' htstep; subst hm
    have htstep_empty := tstep_heapFree_subst_m htf' htstep  -- transport to Mem.empty
    icases HIbody with ⟨%ts', %hsafe', Hauth⟩
    ihave %hlk' := threadpool_lookup_frame γ ts' n' t' …  -- ts' = ts since invariant preserved
    cases hsp : sp with
    | none =>
      -- PURE-STEP CASE
      imod (threadpool_update γ ts' n' t' t'' hlk') $$ [Hauth Hn] with ⟨Hauth', Hn'⟩
      have hsafe'' : Machine.SafeTp prog ⟨Mem.empty, ts'.set n' t''⟩ φ :=
        Machine.SafeTp.step_closed hsafe' ⟨n', none, …, htstep_empty⟩
      have htf'' : t''.heapFree := (tstep_heapFree_preserves htf' … htstep).1
      -- Close inv:
      imod Hclose_eq
      imod Hclose $$ [Hauth'] with _
      · inext; iexists (ts'.set n' t''); …
      imodintro
      iframe HS
      -- Apply IH at (n', t''):
      iapply IH $$ %n' %t'' %htf' …
      iframe Hn'
      iintro %ts_x %hsp_x; rw [hsp] at hsp_x; cases hsp_x
    | some t_child =>
      -- FORK CASE
      imod (threadpool_update γ ts' n' t' t'' hlk') $$ [Hauth Hn] with ⟨Hauth', Hn'⟩
      imod (threadpool_insert γ (ts'.set n' t'') t_child) $$ Hauth' with ⟨Hauth'', Hchild⟩
      -- update SafeTp; close inv with ts'.set n' t'' ++ [t_child]
      …
      -- Apply IH twice: once at (n', t'') for parent, once at the new index for child.
      …
```

Each sub-piece is independently testable: land the value + pure-step
version first (giving completeness for fork-free programs), then add
fork.

## Layer 4: discharge `completeness_modulo_lemma14`

Once Layers 1–3 are in, instantiate the existing
`completeness_modulo_lemma14` (which already builds) with the two
proven hypotheses. The result is the full Theorem 15:

```lean
theorem completeness (hpf : prog.heapFree) (hs : ∀ σ, …) :
    ⊢ |={⊤}=> ∃ Hsi fp, state_interp Mem.empty ∗
        wp prog.procs fp ⊤ (Thread.initial prog.main) (fun v => ⌜φ v⌝)
  := completeness_modulo_lemma14 hpf hs percomplete weaken_post_proof
```

## Estimates

- `icompl_pure_lookup`: ~40 LoC. **Hardest piece.** Single focused
  iprop proof; gated by getting the `▷`-commutation incantations
  right in iris-lean's proof mode.
- `weaken_post_proof`: ~30 LoC. Mechanical once Layer 1 lands.
- `percomplete`: ~200 LoC. Mechanical case-split, mostly driven by
  the existing `tstep_heapFree_*` helpers.
- Layer 4: ~5 LoC.

**Total: ~275 LoC, gated almost entirely on Layer 1.**

## Recommended order

1. **`icompl_pure_lookup`** — single focused proof, biggest unlock.
2. **`weaken_post_proof`** — drops in directly, tests the
   `icompl_pure_lookup` API against a small consumer.
3. **`percomplete` (value + pure-step only)** — partial Lemma 14;
   completeness for fork-free programs. Real result.
4. **`percomplete` (add fork)** — full Lemma 14 for heap-free.
5. **Specialize `completeness_modulo_lemma14`** — get the full
   Theorem 15.

## Resources to lean on

Already proved and ready to use:

* `Agar/Iris/Algebra/ThreadpoolRA.lean`: `threadpool_auth`, `thread_at`
  (timeless), `threadpool_lookup`/`_frame`, `threadpool_update`,
  `threadpool_insert`, `threadpool_init`.
* `Agar/Iris/Adequacy.lean`: `Machine.SafeTp` (paper-aligned),
  `Machine.SafeTp.here` (Lemma 11), `Machine.SafeTp.step_closed`
  (Lemma 12).
* `Agar/Iris/Completeness.lean`:
  - heap-free predicates (`Stmt.heapFree`, `Thread.heapFree`,
    `Program.heapFree`)
  - `tstep_heapFree_mem_unchanged`, `tstep_heapFree_chosen_none`,
    `tstep_heapFree_subst_m`, `tstep_heapFree_preserves`
  - `thread_reducible_heapFree_subst_m`
  - `Thread.toValue_of_terminated'`, `Thread.terminated_of_toValue`
  - `Icompl_pure`, `percomplete_post`, `post_weaken_wand`
  - `wp_wand` (iprop-level post weakening)
  - `completeness_modulo_lemma14` (Theorem 15 minus the two hypotheses)

Stale draft of `percomplete`'s value case + suffices/Löb scaffolding
exists in git history (before the file was trimmed in this session) —
salvageable for the eventual proof.

module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Iris.Wp
public import Agar.Iris.Heap
public import Agar.Iris.Rules
public import Agar.Iris.Tactics

@[expose] public section

/-! # `wp_spin` — generic Löb-induction for spin loops

A spin loop in Agar has the shape

```
  while (guard) do body
```

where each iteration of `body` tests a (heap-backed) condition and either
re-enables the guard (continue spinning) or disables it (exit the loop).
Verifying such a loop is the canonical Iris use-case for
`BILoeb.loeb_weak`: the induction hypothesis is the WP of the next
iteration, available `▷`-laterly to consume one program step.

`wp_spin` packages this pattern as a stand-alone WP rule. It is parametric
in a user-supplied iteration invariant `J : Env → IProp GF` indexed by the
environment, so the loop variable (`done := 0/1`, ticket number, owner
slot, etc.) can be threaded through across iterations. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- **`wp_spin`: Löb-induction for `whileDo` loops.**

The user supplies (as a *meta* hypothesis `HSpec`) a per-iteration step:
given the Löb IH `▷ ∀ env, J env -∗ wp ⟨whileDo …⟩`, and `J env`, derive
the WP of one unfolding of the while-loop:
`ite e_guard (seq body (whileDo e_guard body)) skip`.

Threading the spec at the *meta* level dodges some `iprop(...)` parsing
sharp edges around nested `(▷ …) -∗ … -∗ …`; using it from the proofmode
is no worse than the wand form. -/
theorem wp_spin (procs : Name → Option Proc) (fork_post : IProp GF)
    (e_guard : Expr) (body : Stmt) (cont : List Stmt)
    (stack : List Frame) (Φ : Val → IProp GF)
    (J : Env → IProp GF) (env₀ : Env)
    (HSpec : ∀ env : Env,
      iprop(▷ (∀ (env' : Env), J env' -∗
              wp procs fork_post E
                ⟨.whileDo e_guard body, cont, env', stack, none⟩ Φ) ∗
            ▷ J env)
      ⊢ iprop(▷ wp procs fork_post E
          ⟨.ite e_guard (.seq body (.whileDo e_guard body)) .skip,
           cont, env, stack, none⟩ Φ)) :
    J env₀
    ⊢ wp procs fork_post E
        ⟨.whileDo e_guard body, cont, env₀, stack, none⟩ Φ := by
  -- Internalised: ∀ env, J env -∗ wp ⟨whileDo⟩. Löb gives the IH at the
  -- next step; we apply `HSpec` at the current env after one wp_while.
  suffices key :
      ⊢ (iprop(∀ (env : Env), J env -∗
          wp procs fork_post E
            ⟨.whileDo e_guard body, cont, env, stack, none⟩ Φ) : IProp GF) by
    exact BI.wand_entails
      (BI.true_intro.trans ((BI.true_intro.trans key).trans (BI.forall_elim env₀)))
  iloeb as HIH
  iintro %env HJ
  iapply (wp_while procs fork_post e_guard body cont env stack Φ)
  -- Goal: ▷ wp ⟨ite …⟩. HIH : ▷ (∀ env, J env -∗ wp ⟨whileDo⟩). Push the
  -- HSpec call inside the ▷.
  iapply (HSpec env)
  iframe HIH
  inext; iexact HJ

/-! ## Sanity test: a one-shot "spin" that exits on the first iteration.

Trivial instantiation: `J _ := ▷▷ wp ⟨skip, cont, env, stack⟩ Φ`,
`e_guard := false`, `body := skip`. The loop unfolds once (consuming one
`▷`), the guard is `false`, we step into `skip`, then fall through to
`cont`. -/

section Sanity

/-! ### One-shot spin: `while false do skip`

The guard literal is `false`, so the loop exits immediately. We track
the loop-exit WP in `J` directly, parametrised by the per-iteration env
(which doesn't change since `skip` is the body). The chain of `▷`s
matches the wp_while + wp_ite_false steps. -/
theorem wp_spin_sanity_oneshot
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF) :
    iprop(▷ wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
    ⊢ wp procs fork_post E
        ⟨.whileDo (.val (.bool false)) .skip, cont, env, stack, none⟩ Φ := by
  -- Use a *constant* env in J (the only env we ever see, since `skip`
  -- doesn't touch the env). J ignores its argument.
  let J : Env → IProp GF :=
    fun _ => iprop(▷ wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
  istart
  iintro HK
  -- Issue: when wp_spin re-applies J at the post-step env (some `env'`),
  -- we need J env' to match `▷ wp ⟨.skip, cont, env', stack, none⟩`. We
  -- avoid the env mismatch by routing through `wp_while` directly here
  -- (this also doubles as documentation of what wp_spin *expands to*
  -- before Löb is consumed).
  iapply (wp_while procs fork_post (.val (.bool false)) .skip cont env stack Φ)
  iintro !>
  have hguard : Expr.eval env (.val (.bool false)) = some (.bool false) := rfl
  iapply (wp_ite_false procs fork_post (.val (.bool false))
            (.seq .skip (.whileDo (.val (.bool false)) .skip)) .skip
            cont env stack Φ hguard)
  iexact HK

/-! ### `wp_spin` typing harness

A minimal application of `wp_spin` itself: an "infinite" spin under
`False` precondition. The point is to type-check that `wp_spin`'s
interface is usable from the proofmode; closing the loop body relies
solely on `iexfalso` propagating through. -/
theorem wp_spin_sanity_typing
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (e_guard : Expr) (body : Stmt) (cont : List Stmt) (env : Env)
    (stack : List Frame) (Φ : Val → IProp GF) :
    iprop(False)
    ⊢ wp procs fork_post E
        ⟨.whileDo e_guard body, cont, env, stack, none⟩ Φ := by
  let J : Env → IProp GF := fun _ => iprop(False)
  istart
  iintro HF
  iapply (wp_spin procs fork_post e_guard body cont stack Φ J env
            (fun env' => ?Hspec))
  case Hspec =>
    iintro ⟨_HIH, HF'⟩
    -- HF' : ▷ False; goal : ▷ wp ⟨ite⟩. Both ▷-wrapped: do ▷-mono via inext.
    inext
    iexfalso; iexact HF'
  · iexact HF

end Sanity

/-! ## `wp_spin_fixed_env` — concrete-program friendly variant

The generic `wp_spin` quantifies `J` (and the Löb IH) over *all* envs:

```
∀ env, J env -∗ wp ⟨whileDo …, cont, env, stack, none⟩ Φ
```

For a concrete program whose post-loop continuation `wp ⟨skip, cont, env, …⟩ Φ`
is fixed at a specific env, and whose guard depends on a specific local
(e.g. `done = 0`), the universal `env` cannot be specialised back to the
program's actual env at the loop entry. This blocks direct application
of `wp_spin` to concrete spin loops where the body does not modify the
environment (e.g. `while done = 0 do skip` after `done := 1`, or any
spin that only side-effects via the heap).

`wp_spin_fixed_env` drops the env quantification entirely. The user
supplies a fixed env₀ at which the loop runs; the iteration invariant
`J : IProp GF` carries no env parameter. The lemma assumes the loop
body re-enters the next iteration at the SAME env₀ — i.e. the body
does not modify the environment from the WP's perspective. This is
the canonical "spin on a shared cell" pattern: the body's only effect
is on the heap (loads, stores, CAS), not on locals. -/
theorem wp_spin_fixed_env (procs : Name → Option Proc) (fork_post : IProp GF)
    (e_guard : Expr) (body : Stmt) (cont : List Stmt)
    (stack : List Frame) (Φ : Val → IProp GF)
    (J : IProp GF) (env₀ : Env)
    (HSpec :
      iprop(▷ (J -∗
              wp procs fork_post E
                ⟨.whileDo e_guard body, cont, env₀, stack, none⟩ Φ) ∗
            ▷ J)
      ⊢ iprop(▷ wp procs fork_post E
          ⟨.ite e_guard (.seq body (.whileDo e_guard body)) .skip,
           cont, env₀, stack, none⟩ Φ)) :
    J
    ⊢ wp procs fork_post E
        ⟨.whileDo e_guard body, cont, env₀, stack, none⟩ Φ := by
  -- Use the env-quantified `wp_spin` with `J' env := if env = env₀ then J
  -- else False`. But we don't need decidable env equality: instead, package
  -- the fixed-env body directly via Löb at this single env.
  suffices key :
      ⊢ (iprop(J -∗
          wp procs fork_post E
            ⟨.whileDo e_guard body, cont, env₀, stack, none⟩ Φ) : IProp GF) by
    exact BI.wand_entails (BI.true_intro.trans key)
  iloeb as HIH
  iintro HJ
  iapply (wp_while procs fork_post e_guard body cont env₀ stack Φ)
  iapply HSpec
  iframe HIH
  inext; iexact HJ

/-! ## `wp_spin_invariant` — guard-aware variant for env-changing loops

Generalises `wp_spin` for loops whose body *does* mutate the environment
(e.g. CAS-retry loops that increment a local on each spin). The user
supplies:

* a per-env invariant `I : Env → IProp GF`;
* a **body** spec `HBody`: at any env where `I env` holds and the guard
  evaluates to `true`, the WP of the unrolled body (followed by the
  `whileDo` re-entry) re-establishes `I env'` at *some* new env'
  satisfying any further user-chosen relation;
* an **exit** spec `HExit`: at any env where `I env` holds and the guard
  evaluates to `false`, the WP of the loop's exit (`skip; cont`) is
  derivable.

Unlike `wp_spin_fixed_env`, the body's WP delivers a fresh env'
(existentially-quantified through `I`), and the Löb IH is invoked at
this new env. -/
theorem wp_spin_invariant (procs : Name → Option Proc) (fork_post : IProp GF)
    (e_guard : Expr) (body : Stmt) (cont : List Stmt)
    (stack : List Frame) (Φ : Val → IProp GF)
    (I : Env → IProp GF) (env₀ : Env)
    (HGuard : ∀ env : Env,
      I env ⊢ iprop(I env ∗ ⌜∃ b : Bool, Expr.eval env e_guard = some (.bool b)⌝))
    (HBody : ∀ env : Env,
      iprop((∀ (env' : Env), I env' -∗
              wp procs fork_post E
                ⟨.whileDo e_guard body, cont, env', stack, none⟩ Φ) ∗
            ⌜Expr.eval env e_guard = some (.bool true)⌝ ∗ I env)
      ⊢ iprop(wp procs fork_post E
          ⟨body, .whileDo e_guard body :: cont, env, stack, none⟩ Φ))
    (HExit : ∀ env : Env,
      iprop(⌜Expr.eval env e_guard = some (.bool false)⌝ ∗ I env)
      ⊢ iprop(wp procs fork_post E
          ⟨.skip, cont, env, stack, none⟩ Φ)) :
    I env₀
    ⊢ wp procs fork_post E
        ⟨.whileDo e_guard body, cont, env₀, stack, none⟩ Φ := by
  -- Reduce to the env-quantified `wp_spin` by case-splitting on the guard
  -- (via `HGuard`) inside its `HSpec`.
  iapply (wp_spin procs fork_post e_guard body cont stack Φ I env₀
            (fun env => ?Hspec))
  case Hspec =>
    -- Goal: ▷ wp ⟨ite e_guard (seq body (whileDo e_guard body)) skip, …⟩.
    iintro ⟨HIH, HI⟩
    -- HI : ▷ I env. Strip the later, then extract the pure guard witness
    -- from I env via HGuard, keeping I env in scope.
    inext
    ihave ⟨HI, %hguard⟩ := HGuard env $$ [HI]
    · iexact HI
    obtain ⟨b, hev⟩ := hguard
    cases b with
    | true =>
      iapply (wp_ite_true procs fork_post e_guard
                (.seq body (.whileDo e_guard body)) .skip cont env stack Φ hev)
      inext
      iapply (wp_seq procs fork_post body (.whileDo e_guard body)
                cont env stack Φ)
      inext
      iapply (HBody env)
      iframe HIH HI
      ipure_intro; exact hev
    | false =>
      iapply (wp_ite_false procs fork_post e_guard
                (.seq body (.whileDo e_guard body)) .skip cont env stack Φ hev)
      inext
      iapply (HExit env)
      iframe HI
      ipure_intro; exact hev

/-! ### Sanity test for `wp_spin_invariant`

Mirrors `wp_spin_sanity_typing` but exercises a non-trivial guard-false
branch. With invariant `I env := ⌜Expr.eval env e_guard = some (.bool false)⌝
∗ ▷ wp ⟨skip, cont, env, stack⟩ Φ`, the loop exits on the first iteration
via `HExit`. The body spec `HBody` is discharged by `iexfalso` since the
guard-true precondition contradicts `I`. -/
section SanityInvariant

theorem wp_spin_invariant_sanity_exit
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (body : Stmt) (cont : List Stmt) (env : Env)
    (stack : List Frame) (Φ : Val → IProp GF) :
    iprop(wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
    ⊢ wp procs fork_post E
        ⟨.whileDo (.val (.bool false)) body, cont, env, stack, none⟩ Φ := by
  -- Constant-false guard: HGuard is trivial at the meta level for every env.
  -- Invariant: env is exactly `env`; carry the exit WP through.
  let I : Env → IProp GF := fun env' =>
    iprop(⌜env' = env⌝ ∗
          wp procs fork_post E ⟨.skip, cont, env, stack, none⟩ Φ)
  istart
  iintro HK
  iapply (wp_spin_invariant procs fork_post (.val (.bool false)) body
            cont stack Φ I env
            (fun _ => by
              istart
              iintro HI
              iframe HI
              ipure_intro; exact ⟨false, rfl⟩)
            (fun env' => ?Hbody) (fun env' => ?Hexit))
  case Hbody =>
    -- guard-true precondition contradicts the literal `false` guard.
    iintro ⟨_HIH, ⟨%hguard_true, _⟩⟩
    exact absurd hguard_true (by intro h; cases h)
  case Hexit =>
    iintro ⟨_, ⟨%henv, HK'⟩⟩
    subst henv
    iexact HK'
  · isplit
    · ipure_intro; rfl
    · iexact HK

end SanityInvariant

end Agar.Logic

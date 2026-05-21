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
public import Agar.Iris.Algebra.LockRA
public import Agar.Iris.Algebra.CounterRA

@[expose] public section

/-! # `progSpinFlag` — spin-on-flag and `wp_load_atomic`

A two-thread program with a setter and a parent that loads a shared
flag through `wp_load_atomic` and then runs a structurally-present
`whileDo` loop arranged to exit on the first iteration. The example
validates the atomic-triple form of `wp_load` under invariant sharing
and motivates why a general `wp_spin` lemma cannot close concrete
fixed-env loops — see the in-file discussion of the env-mismatch
obstacle and the `wp_while` route we take instead.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-! ## Spin-on-flag program: `wp_spin` composability demo

`progSpinFlag` is the smallest two-thread program that exercises a
*structurally present* `whileDo`-loop alongside `wp_load_atomic`:

```
setterProc(flag) := store flag 1
progSpinFlag.main := ags(
  flag := alloc 0 ;
  fork setterProc(flag) ;
  v    := load flag ;          -- one invariant-mediated load
  done := 1 ;                  -- statically arrange loop exit
  while done = 0 do skip       -- loop is structurally present but degenerate
)
```

Both threads share `inv N (∃ v, flag ↦ v)`. The parent reads the flag
through `wp_load_atomic` (validating the new atomic-triple form against
the spin context), then runs `while done = 0 do skip`. Since `done = 1`
in the env, the loop's `whileDo → ite → ite_false → skip` chain falls
through to the post-loop continuation.

### Why we don't use `wp_spin` here (the documented obstacle)

`wp_spin` quantifies `J` (and the IH derived by Löb) over *all* envs:

```
∀ env, J env -∗ wp ⟨whileDo e_guard body, cont, env, stack, none⟩ Φ
```

For a concrete program whose guard depends on a particular local (e.g.
`done = 0`) and whose post-loop continuation `wp ⟨skip, cont, env, …⟩ Φ`
fixes a specific env, the universal `env` in `J` cannot be specialised
back to the program's actual env at the loop entry. Equivalently: the
HSpec hypothesis `iintro %env HJ` introduces a *fresh* env over which we
must produce `▷ wp ⟨ite e_guard (seq body whileDo) skip, cont, env, …⟩`,
but `eval env e_guard` is not computable without knowing env, and the
post-loop WP we hold is at a fixed env₀ — exactly the env-mismatch
called out in `wp_spin_sanity_oneshot`.

The same obstacle blocks instantiations like `J env := True` or
`J env := emp`: HSpec can still apply `wp_while`, but cannot evaluate
the guard at the arbitrary `env`, and cannot match a fixed-env post-loop
WP. Closing `wp_spin` for a concrete loop requires either (a) a `J` that
encodes the guard's evaluation as a hypothesis (a more flexible spec
than today's `wp_spin`), or (b) routing through `wp_while` directly when
the loop is statically known to exit on the first iteration — which is
what we do below.

Adequacy conclusion: safety + the head thread terminates at `Val.unit`.
The closed claim cannot say "the loop exits after the setter writes 1"
because we made `done := 1` static; the body of the demo is a witness
that `wp_load_atomic` composes with `wp_while` / `wp_ite_false` in the
presence of `fork` and shared-cell invariants. -/

def setterProc : Proc where
  params := ["flag"]
  body   := ags( store flag 1 )

def progSpinFlag : Program where
  procs := fun n => if n = "setterProc" then some setterProc else none
  main  := ags(
    flag := alloc 0 ;
    fork setterProc(flag) ;
    v    := load flag ;
    done := 1 ;
    while done = 0 do skip
  )

theorem progSpinFlag_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSpinFlag n
            (Machine.initial progSpinFlag) μ') :
    Machine.Adequate progSpinFlag μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progSpinFlag ?_ n μ' htr
  start_closed_proof_with_heap progSpinFlag
  -- main := alloc "flag" 0 ; fork setterProc(flag) ; load "v" flag ;
  --        assign "done" 1 ; whileDo (done=0) skip
  wp_pures                                      -- wp_seq
  wp_alloc_intro HP                             -- HP : l ↦ 0
  wp_pures                                      -- skip_cons; seq exposing `fork`
  -- Allocate the shared invariant before the fork.
  wp_inv_alloc_pt HP HI 0
  ihave #HI := HI
  -- fork setterProc(flag); cont = [load v flag ; done := 1 ; whileDo ...]
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "setterProc" [Expr.var "flag"] setterProc [Val.loc _]
    [Stmt.seq (Stmt.load "v" (Expr.var "flag"))
      (Stmt.seq (Stmt.assign "done" (Expr.val (Val.int 1)))
        (Stmt.whileDo
          (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
          Stmt.skip))] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked setter thread: body = store flag 1.
    iintro !>
    unfold setterProc
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    iintro !>
    wp_done
  · -- Parent continuation: load flag via wp_load_atomic, then trivial spin.
    wp_pures                                    -- skip_cons; seq exposing `load v flag`
    -- Goal: wp ⟨load "v" flag, [done:=1; whileDo ...], env, [], none⟩ ⌜·=unit⌝
    iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
      (P := iprop(∃ v : Val, points_to (GF := GF) (F := F) _ v))
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval)
    iframe HI
    -- Accessor obligation: (▷ ∃ v, l↦v) ={E∖↑N}=∗ ∃ vcur, l↦vcur ∗ (close-wand)
    iintro >⟨%vcur, HP⟩
    -- HP : l ↦ vcur (▷-stripped via the timeless body).
    imodintro
    iexists vcur
    isplitl [HP]
    · iexact HP
    -- Closing wand: l ↦ vcur ={E∖↑N}=∗ (▷ ∃v, l↦v) ∗ wp ⟨...⟩
    iintro HP
    imodintro
    isplitl [HP]
    · inext; iexists vcur; iexact HP
    -- Post-load: env has "v" bound to vcur. Continue with the rest.
    wp_step                                     -- wp_skip_cons
    iintro !>
    wp_step                                     -- wp_seq exposing `done := 1`
    iintro !>
    wp_step                                     -- wp_assign
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    -- Goal: wp ⟨whileDo (done=0) skip, [], env(done=1, v=vcur), [], none⟩
    -- Discharge via the env-friendly `wp_spin_fixed_env`. The body is
    -- `skip` so env never changes; we instantiate `J := emp` and rely
    -- on the guard evaluating to false statically at this fixed env.
    iapply (wp_spin_fixed_env _ _ _ _ _ _ _ iprop(emp : IProp GF) _
      (HSpec := ?Hspec))
    case Hspec =>
      iintro ⟨_HIH, _Hemp⟩
      -- Goal: ▷ wp ⟨ite (done=0) (seq skip whileDo) skip, [], env, [], none⟩
      inext
      iapply wp_ite_false (heval := by agar_eval)
      iintro !>
      wp_done
    · -- J = emp at the loop entry: trivially available.
      iemp_intro

/-! ## Genuinely-spinning recv side: `progChanSpin`

`progChanSpin` is a simplified inlined variant of the bounded-buffer
message-passing program `Examples.progChan` whose recv side now
*genuinely* spins on a shared flag through `wp_spin` (not the degenerate
`wp_spin_fixed_env` of `progSpinFlag`).

```
setterProc(flag) := store flag 1
progChanSpin.main := ags(
  flag := alloc 0 ;
  fork setterProc(flag) ;
  done := 0 ;
  while done = 0 do (
    f := load flag ;
    if f = 1 then done := 1 else skip
  )
)
```

This is intentionally a *one-cell* simplification of the original
`Examples.progChan`. The full `progChan` has *two* shared cells (a
`data` slot and a `flag`) plus a procedure call (`call chanRecv`); both
threads spin on the flag. To verify the literal `progChan` we would
additionally need:

* a way to drive the proof through `call` / `return` Löb-interleaved
  with the inner while-Löb (the call-frame stack changes shape under
  the IH, so the env-quantified `J` would have to encode the stack
  too — not currently expressible with the spin lemmas we have); and
* a J that disjunctively gates on *both* loop locals (`done` and
  `result` for recv, `done` for send) — doable but very verbose.

For the present milestone, the spinning recv against a trivial setter
already exercises everything new: `wp_load_atomic` inside a while body
verified by `wp_spin`, with a J that gates the guard on both branches
of the post-body env. Adequacy conclusion: safety + the head thread
terminates at `Val.unit`. We do not — and adequacy does not let us —
claim the loop terminates dynamically; we only claim every reachable
configuration is reducible or terminated.

### J construction

```
J env := ∃ b : Bool, ⌜eval env (done = 0) = some (.bool b)⌝
```

That is, J just witnesses that the guard evaluates somewhere on `env`.
In HSpec, this lets us case-split on `b`:

* `b = true`: open the invariant via `wp_load_atomic`, branch on the
  loaded value `vcur`, and re-establish `J env_new` for the
  post-body env by re-evaluating the guard (which depends only on
  `env "done"`, unchanged by setting `f`, or changed to `Val.int 1`
  by the `done := 1` assignment — both cases yield a pure-decidable
  guard value).
* `b = false`: the loop exits, the body's WP is unreachable, but the
  ite-false branch through `wp_ite_false` lands at `wp ⟨skip, [], env,
  [], none⟩ Φ`, which is `Φ Val.unit ≡ ⌜Val.unit = Val.unit⌝ ≡ emp`.
-/

def chanSpinSetterProc : Proc where
  params := ["flag"]
  body   := ags( store flag 1 )

def progChanSpin : Program where
  procs := fun n => if n = "chanSpinSetterProc" then some chanSpinSetterProc else none
  main  := ags(
    flag := alloc 0 ;
    fork chanSpinSetterProc(flag) ;
    done := 0 ;
    while done = 0 do (
      f := load flag ;
      if f = 1 then done := 1 else skip
    )
  )

theorem progChanSpin_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progChanSpin n
            (Machine.initial progChanSpin) μ') :
    Machine.Adequate progChanSpin μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progChanSpin ?_ n μ' htr
  start_closed_proof_with_heap progChanSpin
  -- main := alloc "flag" 0 ; fork setter(flag) ; done := 0 ; whileDo (done=0) body
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc_intro HP                             -- HP : l ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing `fork`
  iintro !>
  -- Allocate the shared invariant before the fork.
  wp_inv_alloc_pt HP HI 0
  ihave #HI := HI
  -- Apply wp_fork.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "chanSpinSetterProc" [Expr.var "flag"] chanSpinSetterProc [Val.loc _]
    [Stmt.seq (Stmt.assign "done" (Expr.val (Val.int 0)))
      (Stmt.whileDo
        (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
        (Stmt.seq (Stmt.load "f" (Expr.var "flag"))
          (Stmt.ite
            (Expr.bin BinOp.eq (Expr.var "f") (Expr.val (Val.int 1)))
            (Stmt.assign "done" (Expr.val (Val.int 1)))
            Stmt.skip)))] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked setter thread: body = store flag 1.
    iintro !>
    unfold chanSpinSetterProc
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    iintro !>
    wp_done
  · -- Parent continuation: done := 0 ; while done = 0 do (load+branch).
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    wp_step                                     -- wp_seq exposing `done := 0`
    iintro !>
    wp_step                                     -- wp_assign
    iintro !>
    wp_step                                     -- wp_skip_cons
    iintro !>
    -- Goal: wp ⟨whileDo (done=0) body, [], env_loop, [], none⟩ ⌜·=unit⌝
    -- where env_loop = (env.set "flag" l).set "done" (Val.int 0).
    -- Apply wp_spin with J env := ∃ b, eval env (done=0) = some (.bool b).
    iapply (wp_spin (GF := GF) _ _ _ _ _ _ _
      (J := fun env =>
        iprop(inv nroot (∃ v : Val, points_to (GF := GF) (F := F) l v) ∗
          ∃ b : Bool,
          ⌜Expr.eval env
            (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
            = some (.bool b) ∧
            Expr.eval env (Expr.var "flag") = some (.loc l)⌝)) _
      (HSpec := fun env => ?Hspec))
    case Hspec =>
      iintro ⟨HIH, ⟨#HI, HJ⟩⟩
      inext
      icases HJ with ⟨%b, %hpure⟩
      obtain ⟨hev, hflag⟩ := hpure
      cases b with
      | false =>
        -- Guard false: exit via wp_ite_false → skip → trivial Φ.
        iapply wp_ite_false (heval := hev)
        iintro !>
        wp_done
      | true =>
        -- Guard true: unroll body, do the atomic load, branch on result.
        iapply wp_ite_true (heval := hev)
        -- Drive through nested seq: body = seq (load "f" flag) (ite (f=1) ...)
        wp_pures
        -- Goal: wp ⟨load f flag, [.ite (f=1) ...; whileDo], env, [], none⟩
        iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
          (P := iprop(∃ v : Val, points_to (GF := GF) (F := F) _ v))
          (Hsub := by rw [nclose_root])
          (heL := hflag)
        iframe HI
        iintro >⟨%vcur, HP⟩
        imodintro
        iexists vcur
        isplitl [HP]
        · iexact HP
        iintro HP
        imodintro
        isplitl [HP]
        · inext; iexists vcur; iexact HP
        -- Goal: wp ⟨skip, [.ite ...] :: [whileDo], env.set "f" vcur, [], none⟩
        wp_step                                  -- wp_skip_cons
        iintro !>
        -- Goal: wp ⟨.ite (f=1) (done:=1) skip, [whileDo], env_f, [], none⟩
        -- Branch on whether vcur = Val.int 1.
        by_cases hvcur : vcur = Val.int 1
        · -- Then-branch.
          iapply wp_ite_true
            (heval := by
              subst hvcur
              show Expr.eval _ _ = _
              simp [agar_eval]
              show (Val.int 1 == Val.int 1) = true
              show Val.beq (.int 1) (.int 1) = true
              exact val_beq_refl _)
          iintro !>
          -- Goal: wp ⟨done := 1, [whileDo], env_f, [], none⟩
          iapply wp_assign (heval := by agar_eval)
          iintro !>
          wp_step                                -- wp_skip_cons
          iintro !>
          -- Goal: wp ⟨whileDo, [], env_done1, [], none⟩
          -- Apply HIH at env_done1 with J env_done1 (guard now false).
          ihave HIH := HIH $$ %((env.set "f" vcur).set "done" (Val.int 1))
          iapply HIH
          isplitl []
          · iexact HI
          iexists false
          ipure_intro
          refine ⟨?_, ?_⟩
          · -- eval (env_done1) (done=0) = some (.bool false)
            show Expr.eval _ _ = _
            simp [agar_eval]
            show Val.beq (.int 1) (.int 0) = false
            rfl
          · -- eval env_done1 (.var "flag") = some (.loc _)
            show Expr.eval _ _ = _
            show Env.set _ _ _ "flag" = _
            simp [agar_eval]
            show Expr.eval env (Expr.var "flag") = _
            exact hflag
        · -- Else-branch.
          iapply wp_ite_false
            (heval := by
              show Expr.eval _ _ = _
              simp [Expr.eval, Env.set]
              cases vcur with
              | int i =>
                  have hne : i ≠ 1 := fun h => hvcur (by cases h; rfl)
                  show BinOp.eval BinOp.eq (Val.int i) (Val.int 1) = some (Val.bool false)
                  show some (Val.bool (Val.beq (.int i) (.int 1))) = _
                  show some (Val.bool (i == 1)) = _
                  have : (i == 1) = false := by
                    simp [hne]
                  rw [this]
              | bool _ => rfl
              | loc _ => rfl
              | unit => rfl
              | struct _ => rfl)
          iintro !>
          wp_step                                -- wp_skip_cons
          iintro !>
          -- Goal: wp ⟨whileDo, [], env.set "f" vcur, [], none⟩
          ihave HIH := HIH $$ %(env.set "f" vcur)
          iapply HIH
          isplitl []
          · iexact HI
          iexists true
          ipure_intro
          refine ⟨?_, ?_⟩
          · -- eval (env.set "f" vcur) (done=0): "done" lookup unchanged.
            show Expr.eval _ _ = _
            have h1 : (Env.set env "f" vcur) "done" = env "done" := by
              simp [agar_eval]
            have h2 : Expr.eval (Env.set env "f" vcur)
                (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
                = Expr.eval env
                    (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0))) := by
              show (((Env.set env "f" vcur) "done").bind _) = _
              rw [h1]
              rfl
            rw [h2]; exact hev
          · -- eval (env.set "f" vcur) (.var "flag")
            show Expr.eval _ _ = _
            show Env.set _ _ _ "flag" = _
            simp [agar_eval]
            exact hflag
    · -- Initial J at env_loop = (env.set "flag" l).set "done" (Val.int 0):
      -- guard evaluates to true (done = 0); flag evaluates to l.
      isplitl []
      · iexact HI
      iexists true
      ipure_intro
      refine ⟨?_, ?_⟩
      · agar_eval
      · agar_eval

/-! ## Statically-bounded "CAS-retry" loop: `wp_spin_invariant` on
an env-changing body

`progCasRetry` is the smallest single-thread program exercising the new
`wp_spin_invariant` lemma (Variant C from `WpSpin.lean`) on a loop
body that **changes the environment** between iterations:

```
progCasRetry.main := ags(
  c := alloc 0 ;
  done := 0 ;
  while done = 0 do (
    prev := load c ;
    done := 1
  )
)
```

This is the "CAS-retry" pattern collapsed to its essence: per-iteration
read a shared cell, decide whether to retry, then either exit or loop.
Here the decision is statically `done := 1` (one-shot, never retries),
which keeps the proof self-contained while still exercising the
env-changing body case — the post-iteration env binds `prev` AND `done`
to fresh values.

### Why this exercises `wp_spin_invariant`, not `wp_spin`

`wp_spin` (used by `progChanSpin_closed`) quantifies `J` over all envs
in the Löb IH; HSpec must produce a `▷ wp ⟨ite …⟩` at an arbitrary env
that the IH instantiates to the loop's post-body env. The invariant
variant instead factors the per-iteration step into:
* a body spec `HBody`: at any env with `I env` and the guard true, the
  WP of the unrolled body (followed by re-entry through the IH at
  *some* fresh env') is derivable;
* an exit spec `HExit`: at any env with `I env` and the guard false,
  the WP of `skip; cont` is derivable.

This matches the shape of every interesting spin loop: each iteration
yields a *new* env via the body's effects, and the IH is invoked at
that fresh env. `progChanSpin_closed` had to encode this manually inside
its `wp_spin` HSpec; here `wp_spin_invariant` packages the dance.

### Invariant

```
I env := c ↦ Val.int 0 ∗
        ⌜eval env (var c) = some (.loc l) ∧
          ∃ b : Bool, eval env (done = 0) = some (.bool b)⌝
```

We hold the heap points-to directly inside `I` (rather than behind an
Iris `inv`), since the program is single-threaded. The pure conjunct
serves two purposes: (1) reproducing `eval env_new (var c) = some
(.loc l)` after the body adds the `prev` and `done` bindings, and
(2) discharging `wp_spin_invariant`'s `HGuard` premise, which requires
the guard to evaluate to *some* Boolean at every env where `I env`
holds. -/

def progCasRetry : Program where
  procs := fun _ => none
  main  := ags(
    c := alloc 0 ;
    done := 0 ;
    while done = 0 do (
      prev := load c ;
      done := 1
    )
  )

theorem progCasRetry_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progCasRetry n
            (Machine.initial progCasRetry) μ') :
    Machine.Adequate progCasRetry μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) progCasRetry ?_ n μ' htr
  start_closed_proof_with_heap progCasRetry
  -- main := alloc "c" 0 ; done := 0 ; whileDo (done=0) (prev:=load c ; done:=1)
  wp_step                                       -- wp_seq
  iintro !>
  wp_alloc_intro HP                             -- HP : l ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing `done := 0`
  iintro !>
  wp_step                                       -- wp_assign
  iintro !>
  wp_step                                       -- wp_skip_cons
  iintro !>
  -- Goal: wp ⟨whileDo (done=0) body, [], env_loop, [], none⟩ ⌜·=unit⌝
  -- Apply wp_spin_invariant with I env := points_to l 0 ∗
  --   ⌜eval env (var c) = some (.loc l) ∧ ∃ b, eval env (done=0) = some (.bool b)⌝.
  -- Holding the points-to *inside* I (rather than via an Iris invariant)
  -- avoids the wp_cas_inv split-into-success/fail obligation, which would
  -- otherwise duplicate the (linear) HIH wand across two sub-proofs.
  iapply (wp_spin_invariant (GF := GF) _ _ _ _ _ _ _
    (I := fun env =>
      iprop(points_to (GF := GF) (F := F) l (Val.int 0) ∗
        ⌜Expr.eval env (Expr.var "c") = some (.loc l) ∧
          ∃ b : Bool, Expr.eval env
            (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
            = some (.bool b)⌝))
    _
    (HGuard := fun env => ?HGuard)
    (HBody := fun env => ?HBody)
    (HExit := fun env => ?HExit))
  case HGuard =>
    -- Return I env (consume + reproduce) and extract the pure witness.
    istart
    iintro ⟨HP', %hpure⟩
    isplitl [HP']
    · isplitl [HP']
      · iexact HP'
      · ipure_intro; exact hpure
    · ipure_intro; exact hpure.2
  case HBody =>
    -- Premise: IH at any env' ∗ ⌜guard env = true⌝ ∗ I env.
    -- Goal: wp ⟨body, whileDo :: [], env, [], none⟩ Φ.
    iintro ⟨HIH, ⟨%_hgtrue, ⟨HP', %hpure⟩⟩⟩
    have hflag := hpure.1
    -- body = (prev := load c) ; (done := 1)
    wp_pures
    -- Goal: wp ⟨prev := load c, [done:=1] :: [whileDo], env, [], none⟩
    wp_load_direct HP' hflag
    -- env now binds "prev" to (Val.int 0). Drive on through done := 1.
    wp_step                              -- wp_skip_cons (post-load skip)
    iintro !>
    wp_step                              -- wp_assign (done := 1)
    iintro !>
    wp_step                              -- wp_skip_cons (post-assign)
    iintro !>
    -- Goal: wp ⟨whileDo, [], env_new, [], none⟩.
    -- Apply IH at env_new = ((env.set "prev" 0).set "done" 1).
    ihave HIH := HIH $$ %((env.set "prev" (Val.int 0)).set "done" (Val.int 1))
    iapply HIH
    isplitl [HP']
    · iexact HP'
    ipure_intro
    refine ⟨?_, false, ?_⟩
    · -- eval env_new (var "c") : "c" lookup unchanged by "prev"/"done" sets.
      show Expr.eval _ _ = _
      show Env.set _ _ _ "c" = _
      simp [agar_eval]
      show Env.set env "prev" (Val.int 0) "c" = _
      simp [agar_eval]
      exact hflag
    · -- eval env_new (done = 0): "done" lookup now Val.int 1, beq fails.
      show Expr.eval _ _ = _
      simp [agar_eval]
      show Val.beq (.int 1) (.int 0) = false
      rfl
  case HExit =>
    -- Premise: ⌜guard env = false⌝ ∗ I env. Goal: wp ⟨skip, [], env, [], none⟩ Φ.
    iintro ⟨%_hgfalse, ⟨_HP', %_hpure⟩⟩
    wp_done
  · -- Initial I at env_loop = (env.set "c" l).set "done" 0:
    -- `c` evaluates to l; the guard `done = 0` evaluates to `some (.bool true)`.
    isplitl [HP]
    · iexact HP
    ipure_intro
    refine ⟨?_, true, ?_⟩
    · agar_eval
    · agar_eval

end Agar.Logic

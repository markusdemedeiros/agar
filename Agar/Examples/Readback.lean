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

/-! # `progReadback` — concurrent register with functional-correctness return

A two-thread program whose main thread returns a *nontrivial* value
witnessing that the consumer correctly observed the producer's write
across a synchronisation:

```
producerProc(flag) := store flag 42

progReadback.main := ags(
  flag := alloc 0 ;
  fork producerProc(flag) ;
  done := 0 ;
  result := 0 ;
  while done = 0 do (
    v := load flag ;
    if v = 0 then skip else (result := v ; done := 1)
  ) ;
  return result
)
```

The shared cell is the simplest concurrent data structure: a *single-cell
shared register* whose abstract value transitions monotonically from `0`
(unwritten) to `42` (written). The consumer spin-loads it; on observing
the nonzero value it commits `result := 42` and exits. The post-loop
`return result` yields the program's value.

### What this proves

`progReadback_closed` discharges
`Machine.Adequate progReadback μ' (Val.int 42)`: every thread is
terminated or reducible, AND every terminated main thread returns
`Val.int 42` — never `0`, never anything else. This is genuine
*functional* correctness, not just safety: the register's read-side
faithfully observes its write-side.

Every other forking/spinning example in this directory closes adequacy
at `Val.unit` (safety alone — main falls through after the fork(s)).
This example is the one with a nontrivial post-condition.

### Invariant shape

The shared cell is protected by a *bounded* existential invariant:

```
flagInv := ∃ v, flag ↦ v ∗ ⌜v = 0 ∨ v = 42⌝
```

Two design choices follow:

1. The producer uses `wp_store_atomic` (not `wp_store_inv`) so it can
   supply this *bounded* body in place of the unrestricted
   `∃ v, flag ↦ v`. Re-establishing the body after writing `42`
   discharges the pure disjunct on the right.
2. The consumer's `wp_load_atomic` is instantiated with the same body,
   so the loaded `vcur` comes paired with `⌜vcur = 0 ∨ vcur = 42⌝`.
   The `if v = 0` branch is then a *complete* case-split: the then-
   branch is taken iff `vcur = 0`; the else-branch's `result := v`
   provably writes `Val.int 42`.

### Loop invariant

The spin loop runs under `wp_spin` with:

```
J env := inv N flagInv ∗
        ⌜eval env (var flag) = some (.loc l) ∧
          ((env "done" = some (.int 0) ∧ env "result" = some (.int 0))
         ∨ (env "done" = some (.int 1) ∧ env "result" = some (.int 42)))⌝
```

The disjunction on `(done, result)` is the heart of the
functional-correctness proof: it carries the conditional `done = 1 →
result = 42` through the loop. On guard-false exit we land in the
right disjunct, `env "result" = Val.int 42`, and `return result`
evaluates to `Val.int 42`. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-! ## The program -/

def readbackProducerProc : Proc where
  params := ["flag"]
  body   := ags( store flag 42 )

def progReadback : Program where
  procs := fun n =>
    if n = "readbackProducerProc" then some readbackProducerProc else none
  main  := ags(
    flag   := alloc 0 ;
    fork readbackProducerProc(flag) ;
    done   := 0 ;
    result := 0 ;
    (while done = 0 do (
      v := load flag ;
      if v = 0 then skip else (result := v ; done := 1)
    )) ;
    return result
  )

/-- The bounded existential invariant body shared across producer and
consumer: the register's value is always either `0` or `42`. -/
private abbrev flagInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    (l : Loc) : IProp GF :=
  iprop(∃ v : Val,
    points_to (GF := GF) (F := F) l v ∗
    ⌜v = Val.int 0 ∨ v = Val.int 42⌝)

/-! ## Closed adequacy theorem

The proof mirrors `progChanSpin_closed`'s `wp_spin` skeleton but with a
richer J encoding the (done, result) disjunction, and a producer that
goes through `wp_store_atomic` (not `wp_store_inv`) so it can pin the
heap value to the {0, 42} set across the write. -/

theorem progReadback_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progReadback n
            (Machine.initial progReadback) μ') :
    Machine.Adequate progReadback μ' (Val.int 42) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 42) progReadback ?_ n μ' htr
  start_closed_proof_with_heap progReadback
  -- main : flag := alloc 0 ; fork producer(flag) ;
  --        done := 0 ; result := 0 ;
  --        while done=0 do (v := load flag ; if v=0 then skip else (...)) ;
  --        return result
  wp_step                                       -- wp_seq exposing alloc
  iintro !>
  wp_alloc
  iintro !> %l HP                               -- HP : l ↦ 0
  wp_step                                       -- wp_skip_cons
  iintro !>
  wp_step                                       -- wp_seq exposing fork
  iintro !>
  -- Allocate the shared bounded invariant in the LEFT disjunct.
  iapply fupd_wp
  imod (inv_alloc nroot CoPset.full (flagInv GF F l)) $$ [HP] with HI
  · inext; iexists (Val.int 0); isplitl [HP]
    · iexact HP
    · ipure_intro; left; rfl
  imodintro
  ihave #HI := HI
  -- fork readbackProducerProc(flag); cont = the rest of main.
  iapply wp_fork (GF := GF) (F := F) (fork_post := iprop(emp : IProp GF))
    _ "readbackProducerProc" [Expr.var "flag"] readbackProducerProc
    [Val.loc _]
    [ags(
      done   := 0 ;
      result := 0 ;
      (while done = 0 do (
        v := load flag ;
        if v = 0 then skip else (result := v ; done := 1)
      )) ;
      return result
    )] _ [] _
    rfl (by agar_eval) rfl
  isplitr
  · -- Forked producer: body = store flag 42, opens the bounded invariant.
    iintro !>
    unfold readbackProducerProc
    iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
      (P := flagInv GF F l)
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HI
    iintro >⟨%vold, HP, %_hpold⟩
    imodintro
    iexists vold
    isplitl [HP]
    · iexact HP
    iintro HP                                   -- HP : l ↦ Val.int 42
    imodintro
    isplitl [HP]
    · inext; iexists (Val.int 42); isplitl [HP]
      · iexact HP
      · ipure_intro; right; rfl
    wp_done
  · -- Parent continuation: done := 0 ; result := 0 ; whileDo … ; return result.
    iintro !>
    -- 8 pure steps to reach the whileDo at env_loop binding done=0, result=0
    -- (skip_cons; seq; assign done; skip_cons; seq; assign result; skip_cons; seq).
    wp_step; iintro !>            -- wp_skip_cons (post-fork)
    wp_step; iintro !>            -- wp_seq exposing `done := 0`
    wp_step; iintro !>            -- wp_assign done
    wp_step; iintro !>            -- wp_skip_cons
    wp_step; iintro !>            -- wp_seq exposing `result := 0`
    wp_step; iintro !>            -- wp_assign result
    wp_step; iintro !>            -- wp_skip_cons
    wp_step; iintro !>            -- wp_seq exposing the whileDo
    -- env_loop now binds: flag↦l, done↦0, result↦0.
    -- Goal: wp ⟨whileDo (done=0) body, [return result], env_loop, [], none⟩.
    iapply (wp_spin (GF := GF) _ _ _ _ _ _ _
      (J := fun env =>
        iprop(inv nroot (flagInv GF F l) ∗
          ⌜Expr.eval env (Expr.var "flag") = some (.loc l) ∧
            ((env "done" = some (.int 0) ∧ env "result" = some (.int 0)) ∨
             (env "done" = some (.int 1) ∧ env "result" = some (.int 42)))⌝)) _
      (HSpec := fun env => ?Hspec))
    case Hspec =>
      iintro ⟨HIH, ⟨#HI, HJ⟩⟩
      inext
      icases HJ with %hpure
      obtain ⟨hflag, hdr⟩ := hpure
      -- Case-split on the (done, result) disjunct.
      rcases hdr with ⟨hdone, hresult⟩ | ⟨hdone, hresult⟩
      · -- LEFT disjunct: done = 0, result = 0. Guard true. Run body.
        have hguard : Expr.eval env
            (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
            = some (.bool true) := by
          show Expr.eval _ _ = _
          show (env "done").bind _ = _
          rw [hdone]; rfl
        iapply wp_ite_true (heval := hguard)
        iintro !>
        -- We're at `seq BODY whileDo` where BODY = seq (load) (ite v=0 ...).
        -- Peel the outer seq, then the inner seq, to expose `load v flag`.
        wp_step; iintro !>                       -- wp_seq exposing BODY
        wp_step; iintro !>                       -- wp_seq exposing load
        iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
          (P := flagInv GF F l)
          (Hsub := by rw [nclose_root])
          (heL := hflag)
        iframe HI
        iintro >⟨%vcur, HP, %hpcur⟩
        imodintro
        iexists vcur
        isplitl [HP]
        · iexact HP
        iintro HP
        imodintro
        isplitl [HP]
        · inext; iexists vcur; isplitl [HP]
          · iexact HP
          · ipure_intro; exact hpcur
        -- env after load: env_v = env.set "v" vcur. Continue.
        wp_step                                  -- wp_skip_cons (post-load)
        iintro !>
        -- Branch on whether vcur = 0 or vcur = 42 (extracted from hpcur).
        rcases hpcur with h0 | h42
        · -- vcur = 0: take then-branch (skip). State unchanged on (done, result).
          subst h0
          iapply wp_ite_true
            (heval := by
              show Expr.eval _ _ = _
              simp [agar_eval]
              show Val.beq (.int 0) (.int 0) = true
              rfl)
          iintro !>
          wp_step                                -- wp_skip_cons
          iintro !>
          -- Goal: wp ⟨whileDo, [return result], env.set "v" 0, [], none⟩.
          ihave HIH := HIH $$ %(env.set "v" (Val.int 0))
          iapply HIH
          isplitl []
          · iexact HI
          ipure_intro
          refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
          · -- flag lookup unchanged.
            show Expr.eval _ _ = _
            show Env.set _ _ _ "flag" = _
            simp [agar_eval]
            show Expr.eval env (Expr.var "flag") = _
            exact hflag
          · -- done lookup unchanged.
            show Env.set env "v" (Val.int 0) "done" = _
            simp [agar_eval]
            exact hdone
          · -- result lookup unchanged.
            show Env.set env "v" (Val.int 0) "result" = _
            simp [agar_eval]
            exact hresult
        · -- vcur = 42: take else-branch (result := v ; done := 1).
          subst h42
          iapply wp_ite_false
            (heval := by
              show Expr.eval _ _ = _
              simp [agar_eval]
              show Val.beq (.int 42) (.int 0) = false
              rfl)
          iintro !>
          -- body of else: result := v ; done := 1.
          wp_step                                -- wp_seq exposing `result := v`
          iintro !>
          iapply wp_assign (heval := by agar_eval)
          iintro !>
          wp_step                                -- wp_skip_cons
          iintro !>
          iapply wp_assign (heval := by agar_eval)
          iintro !>
          wp_step                                -- wp_skip_cons
          iintro !>
          -- env_new = ((env.set "v" 42).set "result" 42).set "done" 1.
          ihave HIH := HIH $$ %(((env.set "v" (Val.int 42)).set "result"
              (Val.int 42)).set "done" (Val.int 1))
          iapply HIH
          isplitl []
          · iexact HI
          ipure_intro
          refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
          · -- flag lookup: all three sets touch other keys.
            show Expr.eval _ (Expr.var "flag") = _
            exact hflag
          · -- done lookup: last set was "done" → Val.int 1.
            rfl
          · -- result lookup: "done" set above doesn't touch "result";
            -- the prior "result" set gave Val.int 42.
            rfl
      · -- RIGHT disjunct: done = 1, result = 42. Guard false. Exit loop.
        have hguard : Expr.eval env
            (Expr.bin BinOp.eq (Expr.var "done") (Expr.val (Val.int 0)))
            = some (.bool false) := by
          show (env "done").bind _ = _
          rw [hdone]; rfl
        iapply wp_ite_false (heval := hguard)
        iintro !>
        wp_step; iintro !>                       -- wp_skip_cons (after loop)
        -- Goal: wp ⟨ret result, [], env, [], none⟩ ⌜·= Val.int 42⌝.
        iapply (wp_ret_top _ _ (Expr.var "result") (Val.int 42) [] env _
          (heval := by
            show Expr.eval _ _ = _
            rw [show Expr.eval env (Expr.var "result") = env "result" from rfl]
            rw [hresult]))
        ipure_intro; rfl
    · -- Initial J at env_loop = (env.set "flag" l).set "done" 0).set "result" 0.
      isplitl []
      · iexact HI
      ipure_intro
      refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
      · agar_eval
      · -- env_loop "done" = some (Val.int 0).
        show Env.set _ _ _ "done" = _
        simp [agar_eval]
      · -- env_loop "result" = some (Val.int 0).
        show Env.set _ _ _ "result" = _
        simp [agar_eval]

end Agar.Logic

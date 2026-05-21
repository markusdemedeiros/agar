module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.Hoare

@[expose] public section

/-! # A small verified Agar library

Two reusable procedures with closed adequacy theorems:

* `maxProc(a, b) := if a < b then return b else return a`
* `absProc(x)    := if x < 0 then return 0 - x else return x`

Each proof follows the `progCallMin_closed` skeleton:
`wp_step → wp_call → unfold proc → wp_ite_* → wp_ret_pop_nil
  → wp_skip_cons → wp_ret_top`.

### Naming convention

Procedure specs come in two shapes. The bare `<proc>_spec` form is the
**general, lifted-Φ** WP triple: usable as a building block under any
postcondition. The `<proc>_spec_gen` suffix is used historically when
the file also exposes a more specialised variant; new specs should
prefer the bare name. The two coexist for backward-compatibility with
existing callers (`gcdProc_spec_gen`, `factProc_spec_gen`). -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Agar.Logic

/-- Local helper: `Val.beq` on `Val.int` reduces to decidable equality.
Shared between `gcdProc_spec_gen` and `sumProc_spec_gen`. -/
private theorem val_int_beq (x y : Int) :
    (Val.int x == Val.int y) = decide (x = y) := by
  show Val.beq _ _ = _
  show (x == y) = _
  by_cases h : x = y
  · subst h; simp
  · simp [h]

/-- `max(a, b)` as a Agar procedure. -/
def maxProc : Proc where
  params := ["a", "b"]
  body   := ags( if a < b then return b else return a )

/-! ## Universally-quantified Hoare-style spec for `maxProc`

`maxProc_spec` captures, once and for all, the WP triple for a call
site `x := call maxProc(eA, eB)` whose argument expressions evaluate
to `Val.int a` and `Val.int b`. From the spec the caller derives the
post-call continuation with `x` bound to `Val.int (if a < b then b
else a)` under three `▷` modalities (one each for `wp_call`,
`wp_ite_*`, `wp_ret_pop_nil`). -/

section MaxProcSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Post-call thread state for `maxProc`: result `Val.int (if a < b then
b else a)` bound to `x` in the caller's env, with the caller's stack
restored. We dispatch on the shape of the caller's continuation so the
spec applies uniformly whether the call is the last statement (cont =
`[]`) or has a follow-up (cont = `s :: cs`). -/
def maxProc_post (a b : Int) (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x (.int (if a < b then b else a))
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Hoare-style spec for `maxProc`: given a call site whose argument
expressions evaluate to `Val.int a` and `Val.int b`, the WP reduces
to the continuation with `x` bound to `Val.int (if a < b then b else a)`
under three later modalities. The procedure table must map `"maxProc"`
to `maxProc`. -/
theorem maxProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (a b : Int) (x : Name) (eA eB : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (hproc : procs "maxProc" = some maxProc)
    (hA : Expr.eval env eA = some (.int a))
    (hB : Expr.eval env eB = some (.int b)) :
    ⦃ ▷ ▷ ▷ wp procs fork_post E (maxProc_post a b x cont env stack) Φ ⦄
    (⟨.call x "maxProc" [eA, eB], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ := by
  -- Discharge the procedure call.
  have hargs : evalArgs env [eA, eB] = some [.int a, .int b] := by
    simp [agar_eval, hA, hB]
  have harity : ([Val.int a, Val.int b]).length = maxProc.params.length := rfl
  iintro HK
  iapply (wp_call procs fork_post x "maxProc" [eA, eB]
            maxProc [.int a, .int b] cont env stack Φ hproc hargs harity)
  iintro !>
  -- Body is `if a < b then return b else return a`.
  unfold maxProc
  -- The bound env: `a ↦ Val.int a, b ↦ Val.int b`.
  have hEvalA : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                  (age(a)) = some (.int a) := by
    simp [agar_eval]
  have hEvalB : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                  (age(b)) = some (.int b) := by
    simp [agar_eval]
  by_cases hab : a < b
  · -- True branch.
    have hGuard : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                    (age(a < b)) = some (.bool true) := by
      simp [agar_eval, hab]
    iapply wp_ite_true (heval := hGuard)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalB)
      iintro !>
      -- env.set x (.int b) = env.set x (.int (if a<b then b else a)) under hab.
      unfold maxProc_post
      simp [hab]
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalB)
      iintro !>
      unfold maxProc_post
      simp [hab]
  · -- False branch.
    have hGuard : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                    (age(a < b)) = some (.bool false) := by
      simp [agar_eval, hab]
    iapply wp_ite_false (heval := hGuard)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalA)
      iintro !>
      unfold maxProc_post
      simp [hab]
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalA)
      iintro !>
      unfold maxProc_post
      simp [hab]

end MaxProcSpec

/-- `min(a, b)` as a Agar procedure. -/
def minProc : Proc where
  params := ["a", "b"]
  body   := ags( if a < b then return a else return b )

/-! ## Universally-quantified Hoare-style spec for `minProc`

Mirrors `maxProc_spec`; the only difference is the comparison
direction picks `a` on the true branch and `b` on the false branch. -/

section MinProcSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Post-call thread state for `minProc`: result `Val.int (if a < b then
a else b)` bound to `x` in the caller's env. -/
def minProc_post (a b : Int) (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x (.int (if a < b then a else b))
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Hoare-style spec for `minProc`: given a call site whose argument
expressions evaluate to `Val.int a` and `Val.int b`, the WP reduces
to the continuation with `x` bound to `Val.int (if a < b then a else b)`
under three later modalities. -/
theorem minProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (a b : Int) (x : Name) (eA eB : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (hproc : procs "minProc" = some minProc)
    (hA : Expr.eval env eA = some (.int a))
    (hB : Expr.eval env eB = some (.int b)) :
    ⦃ ▷ ▷ ▷ wp procs fork_post E (minProc_post a b x cont env stack) Φ ⦄
    (⟨.call x "minProc" [eA, eB], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ := by
  have hargs : evalArgs env [eA, eB] = some [.int a, .int b] := by
    simp [agar_eval, hA, hB]
  have harity : ([Val.int a, Val.int b]).length = minProc.params.length := rfl
  iintro HK
  iapply (wp_call procs fork_post x "minProc" [eA, eB]
            minProc [.int a, .int b] cont env stack Φ hproc hargs harity)
  iintro !>
  unfold minProc
  have hEvalA : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                  (age(a)) = some (.int a) := by
    simp [agar_eval]
  have hEvalB : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                  (age(b)) = some (.int b) := by
    simp [agar_eval]
  by_cases hab : a < b
  · -- True branch: return a.
    have hGuard : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                    (age(a < b)) = some (.bool true) := by
      simp [agar_eval, hab]
    iapply wp_ite_true (heval := hGuard)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalA)
      iintro !>
      unfold minProc_post
      simp [hab]
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalA)
      iintro !>
      unfold minProc_post
      simp [hab]
  · -- False branch: return b.
    have hGuard : Expr.eval (bindParams ["a", "b"] [Val.int a, Val.int b])
                    (age(a < b)) = some (.bool false) := by
      simp [agar_eval, hab]
    iapply wp_ite_false (heval := hGuard)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalB)
      iintro !>
      unfold minProc_post
      simp [hab]
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalB)
      iintro !>
      unfold minProc_post
      simp [hab]

end MinProcSpec

/-- `abs(x)` as a Agar procedure. -/
def absProc : Proc where
  params := ["x"]
  body   := ags( if x < 0 then return 0 - x else return x )

/-! ## Universally-quantified Hoare-style spec for `absProc`

Mirrors `maxProc_spec`. Result is `if x < 0 then -x else x` (i.e.
`Int.natAbs x` as an `Int`, but stated in the form that lines up
with the embedded `0 - x` computation). -/

section AbsProcSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Post-call thread state for `absProc`: result `Val.int (if x < 0
then 0 - x else x)` bound to `r` in the caller's env, with the
caller's stack restored. -/
def absProc_post (x : Int) (r : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set r (.int (if x < 0 then 0 - x else x))
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Hoare-style spec for `absProc`: given a call site whose argument
expression evaluates to `Val.int x`, the WP reduces to the continuation
with `r` bound to `Val.int (if x < 0 then 0 - x else x)` under three
later modalities. The procedure table must map `"absProc"` to `absProc`. -/
theorem absProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Int) (r : Name) (eX : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (Φ : Val → IProp GF)
    (hproc : procs "absProc" = some absProc)
    (hX : Expr.eval env eX = some (.int x)) :
    ⦃ ▷ ▷ ▷ wp procs fork_post E (absProc_post x r cont env stack) Φ ⦄
    (⟨.call r "absProc" [eX], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ := by
  -- Discharge the procedure call.
  have hargs : evalArgs env [eX] = some [.int x] := by
    simp [agar_eval, hX]
  have harity : ([Val.int x]).length = absProc.params.length := rfl
  iintro HK
  iapply (wp_call procs fork_post r "absProc" [eX]
            absProc [.int x] cont env stack Φ hproc hargs harity)
  iintro !>
  -- Body is `if x < 0 then return 0 - x else return x`.
  unfold absProc
  -- The bound env: `x ↦ Val.int x`.
  have hEvalX : Expr.eval (bindParams ["x"] [Val.int x])
                  (age(x)) = some (.int x) := by
    simp [agar_eval]
  have hEvalNeg : Expr.eval (bindParams ["x"] [Val.int x])
                    (age(0 - x)) = some (.int (0 - x)) := by
    simp [agar_eval]
  by_cases hx : x < 0
  · -- True branch.
    have hGuard : Expr.eval (bindParams ["x"] [Val.int x])
                    (age(x < 0)) = some (.bool true) := by
      simp [agar_eval, hx]
    iapply wp_ite_true (heval := hGuard)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalNeg)
      iintro !>
      unfold absProc_post
      simp [hx]
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalNeg)
      iintro !>
      unfold absProc_post
      simp [hx]
  · -- False branch.
    have hGuard : Expr.eval (bindParams ["x"] [Val.int x])
                    (age(x < 0)) = some (.bool false) := by
      simp [agar_eval, hx]
    iapply wp_ite_false (heval := hGuard)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalX)
      iintro !>
      unfold absProc_post
      simp [hx]
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalX)
      iintro !>
      unfold absProc_post
      simp [hx]

end AbsProcSpec

/-- Sample program: `v := max(5, 3) ; return v` evaluates to `5`. -/
def progMax53 : Program where
  procs := fun n => if n = "maxProc" then some maxProc else none
  main  := ags(
    v := call maxProc(5, 3) ;
    return v
  )

/-- Nested-call sample: `t := max(2, 5); r := max(t, 4); return r` evaluates to `5`. -/
def progMaxOfThree : Program where
  procs := fun n => if n = "maxProc" then some maxProc else none
  main  := ags(
    t := call maxProc(2, 5) ;
    r := call maxProc(t, 4) ;
    return r
  )

/-- Sample program: `v := min(5, 3) ; return v` evaluates to `3`. -/
def progMin53 : Program where
  procs := fun n => if n = "minProc" then some minProc else none
  main  := ags(
    v := call minProc(5, 3) ;
    return v
  )

/-! ## Recursive subtraction-based `gcdProc`

`gcdProc(a, b) := if a = b then return a
                   else (if a < b then (r := call gcdProc(a, b - a) ; return r)
                                  else (r := call gcdProc(a - b, b) ; return r))`

Since Agar's `BinOp` lacks `mod`, we use the subtraction-based Euclidean
algorithm. We do not prove a universal Löb spec here; instead we follow
the concrete-unroll template from the original `fact_3_closed` and prove
`gcd_6_4_closed` directly by repeated `wp_step`. The recursion depth for
`gcd(6, 4)` is three calls: `gcd(6,4) → gcd(2,4) → gcd(2,2)`, with the
base case `a = b = 2` returning `2`. -/

/-- Subtraction-based GCD as a Agar procedure. -/
def gcdProc : Proc where
  params := ["a", "b"]
  body   := ags(
    if a = b then return a
    else (
      if a < b then (r := call gcdProc(a, b - a) ; return r)
      else          (r := call gcdProc(a - b, b) ; return r)
    )
  )

/-! ## Universal Löb-induction spec for `gcdProc`

Math model: subtraction-based GCD on `Nat`. Totalised at zero arguments
(unused — the spec carries a positivity precondition). Recursion on
`a + b` is structurally decreasing because each recursive call shrinks
the sum: `a + (b - a) < a + b` when `0 < a ≤ b`, and symmetrically. -/

/-- Subtraction-based GCD on `Nat`, totalised at zero. -/
def gcdSub : Nat → Nat → Nat
  | 0, b => b
  | a, 0 => a
  | a+1, b+1 =>
    if a+1 = b+1 then a+1
    else if a+1 < b+1 then gcdSub (a+1) (b+1 - (a+1))
    else gcdSub (a+1 - (b+1)) (b+1)
  termination_by a b => a + b

/-- Unfolding lemma for `gcdSub` when both arguments are positive. -/
theorem gcdSub_pos_eq (a b : Nat) (ha : a > 0) (hb : b > 0) :
    gcdSub a b =
      if a = b then a else if a < b then gcdSub a (b - a) else gcdSub (a - b) b := by
  match a, b, ha, hb with
  | _+1, _+1, _, _ => simp [gcdSub]

section GcdProcSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Post-call thread state for `gcdProc`: result `Val.int (gcdSub a b)`
bound to `x` in the caller's env, with the caller's stack restored. -/
def gcdProc_post (a b : Nat) (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x (.int (gcdSub a b))
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Generalised universal spec for `gcdProc`, by Löb induction. The
arguments are arbitrary expressions `eA, eB` evaluating to the positive
integers `a, b`. The recursive call sites inside `gcdProc` use the
non-literal expressions `age(b - a)` and `age(a - b)`, so generality
is essential. -/
theorem gcdProc_spec_gen
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "gcdProc" = some gcdProc)
    (Φ : Val → IProp GF) (a b : Nat) (ha : a > 0) (hb : b > 0)
    (x : Name) (eA eB : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (hA : Expr.eval env eA = some (.int (a : Int)))
    (hB : Expr.eval env eB = some (.int (b : Int))) :
    ⦃ ▷ wp procs fork_post E (gcdProc_post a b x cont env stack) Φ ⦄
    (⟨.call x "gcdProc" [eA, eB], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ := by
  -- Bundle into iProp with all per-recursion data quantified.
  suffices key :
      ⊢ (iprop(∀ (a b : Nat) (x : Name) (eA eB : Expr) (cont : List Stmt)
                (env : Env) (stack : List Frame),
          ⌜a > 0⌝ -∗ ⌜b > 0⌝ -∗
          ⌜Expr.eval env eA = some (.int (a : Int))⌝ -∗
          ⌜Expr.eval env eB = some (.int (b : Int))⌝ -∗
          (▷ wp procs fork_post E (gcdProc_post a b x cont env stack) Φ) -∗
          wp procs fork_post E
            ⟨.call x "gcdProc" [eA, eB], cont, env, stack, none⟩ Φ) : IProp GF) by
    have step : (True : IProp GF) ⊢
        iprop((▷ wp procs fork_post E (gcdProc_post a b x cont env stack) Φ) -∗
              wp procs fork_post E
                ⟨.call x "gcdProc" [eA, eB], cont, env, stack, none⟩ Φ) := by
      iintro _ HK
      iapply key
      · ipure_intro; exact ha
      · ipure_intro; exact hb
      · ipure_intro; exact hA
      · ipure_intro; exact hB
      · iexact HK
    exact BI.wand_entails (BI.true_intro.trans step)
  iloeb as HIH
  iintro %a %b %x %eA %eB %cont %env %stack %ha %hb %hA %hB HK
  -- Outer call: discharge with `wp_call`.
  have hargs : evalArgs env [eA, eB] = some [.int (a : Int), .int (b : Int)] := by
    simp [agar_eval, hA, hB]
  have harity : ([Val.int (a : Int), Val.int (b : Int)]).length
                  = gcdProc.params.length := rfl
  iapply (wp_call procs fork_post x "gcdProc" [eA, eB]
            gcdProc [.int (a : Int), .int (b : Int)] cont env stack Φ
            hproc hargs harity)
  iintro !>
  simp only [gcdProc]
  -- Eval facts under the body's bound env `bindParams ["a","b"] [Val.int a, Val.int b]`.
  have hEvalA : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                  (age(a)) = some (.int (a : Int)) := by
    simp [agar_eval]
  have hEvalB : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                  (age(b)) = some (.int (b : Int)) := by
    simp [agar_eval]
  have hGuardEq : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    (age(a = b)) = some (.bool (decide ((a : Int) = (b : Int)))) := by
    simp [agar_eval, val_int_beq]
  have hGuardLt : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    (age(a < b)) = some (.bool (decide ((a : Int) < (b : Int)))) := by
    simp [agar_eval]
  -- Int eq/lt on Nats reduces to Nat eq/lt (by `exact_mod_cast`).
  have hIntEqNat : ((a : Int) = (b : Int)) ↔ a = b := by omega
  have hIntLtNat : ((a : Int) < (b : Int)) ↔ a < b := by omega
  by_cases hab : a = b
  · -- Equal-case branch: return a.
    subst hab
    have hGuardT : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (a : Int)])
                    (age(a = b)) = some (.bool true) := by
      rw [hGuardEq]; simp
    iapply wp_ite_true (heval := hGuardT)
    iintro !>
    -- gcdSub a a = a (a > 0).
    have hgcd : gcdSub a a = a := by
      rw [gcdSub_pos_eq a a ha ha]; simp
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hEvalA)
      iintro !>
      unfold gcdProc_post
      simp [hgcd]
      iexact HK
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hEvalA)
      iintro !>
      unfold gcdProc_post
      simp [hgcd]
      iexact HK
  · -- a ≠ b. False branch of outer if, then case on inner `a < b`.
    have habI : ¬ ((a : Int) = (b : Int)) := fun h => hab (hIntEqNat.mp h)
    have hGuardF : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    (age(a = b)) = some (.bool false) := by
      rw [hGuardEq]; simp [habI]
    iapply wp_ite_false (heval := hGuardF)
    iintro !>
    by_cases hlt : a < b
    · -- a < b: recurse on (a, b - a).
      have hltI : (a : Int) < (b : Int) := by exact_mod_cast hlt
      have hGuardLtT : Expr.eval (bindParams ["a", "b"]
                          [Val.int (a : Int), Val.int (b : Int)])
                          (age(a < b)) = some (.bool true) := by
        rw [hGuardLt]; simp [hltI]
      iapply wp_ite_true (heval := hGuardLtT)
      iintro !>
      iapply wp_seq
      iintro !>
      -- Eval of `age(b - a)` under the body env.
      have hSub : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    (age(b - a)) = some (.int (((b - a : Nat)) : Int)) := by
        have h1 : Expr.eval (bindParams ["a", "b"]
                    [Val.int (a : Int), Val.int (b : Int)]) (age(b - a))
                  = some (.int ((b : Int) - (a : Int))) := by
          simp [agar_eval]
        rw [h1]; congr 2; omega
      have hba_pos : b - a > 0 := Nat.sub_pos_of_lt hlt
      -- Apply HIH at (a, b-a, "r", age(a), age(b - a), [return r], body-env,
      --   ⟨x,cont,env⟩::stack).
      iapply HIH $$ %a %(b - a) %"r" %(age(a)) %(age(b - a))
                    %([ags(return r)])
                    %(bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    %(⟨x, cont, env⟩ :: stack)
                    %ha %hba_pos %hEvalA %hSub
      iintro !>
      unfold gcdProc_post
      simp
      -- gcdSub a b = gcdSub a (b - a) since a < b.
      have hgcd : gcdSub a b = gcdSub a (b - a) := by
        rw [gcdSub_pos_eq a b ha hb]; simp [hab, hlt]
      have hEvalR : Expr.eval
          ((bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)]).set "r"
              (.int ((gcdSub a (b - a) : Nat) : Int)))
          (age(r)) = some (.int ((gcdSub a (b - a) : Nat) : Int)) := by
        simp [agar_eval]
      rcases hcont : cont with _ | ⟨s, cs⟩
      · iapply wp_ret_pop_nil (heval := hEvalR)
        iintro !>
        simp [hgcd]
        iexact HK
      · iapply wp_ret_pop_cons (heval := hEvalR)
        iintro !>
        simp [hgcd]
        iexact HK
    · -- a > b (since a ≠ b and ¬ a < b). Recurse on (a - b, b).
      have hgt : b < a := by omega
      have hltI : ¬ ((a : Int) < (b : Int)) := by exact_mod_cast hlt
      have hGuardLtF : Expr.eval (bindParams ["a", "b"]
                          [Val.int (a : Int), Val.int (b : Int)])
                          (age(a < b)) = some (.bool false) := by
        rw [hGuardLt]; simp [hltI]
      iapply wp_ite_false (heval := hGuardLtF)
      iintro !>
      iapply wp_seq
      iintro !>
      have hSub : Expr.eval (bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    (age(a - b)) = some (.int (((a - b : Nat)) : Int)) := by
        have h1 : Expr.eval (bindParams ["a", "b"]
                    [Val.int (a : Int), Val.int (b : Int)]) (age(a - b))
                  = some (.int ((a : Int) - (b : Int))) := by
          simp [agar_eval]
        rw [h1]; congr 2; omega
      have hab_pos : a - b > 0 := Nat.sub_pos_of_lt hgt
      iapply HIH $$ %(a - b) %b %"r" %(age(a - b)) %(age(b))
                    %([ags(return r)])
                    %(bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)])
                    %(⟨x, cont, env⟩ :: stack)
                    %hab_pos %hb %hSub %hEvalB
      iintro !>
      unfold gcdProc_post
      simp
      have hgcd : gcdSub a b = gcdSub (a - b) b := by
        rw [gcdSub_pos_eq a b ha hb]; simp [hab, hlt]
      have hEvalR : Expr.eval
          ((bindParams ["a", "b"] [Val.int (a : Int), Val.int (b : Int)]).set "r"
              (.int ((gcdSub (a - b) b : Nat) : Int)))
          (age(r)) = some (.int ((gcdSub (a - b) b : Nat) : Int)) := by
        simp [agar_eval]
      rcases hcont : cont with _ | ⟨s, cs⟩
      · iapply wp_ret_pop_nil (heval := hEvalR)
        iintro !>
        simp [hgcd]
        iexact HK
      · iapply wp_ret_pop_cons (heval := hEvalR)
        iintro !>
        simp [hgcd]
        iexact HK

/-- User-facing universal spec for `gcdProc` with value-literal arguments. -/
theorem gcdProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "gcdProc" = some gcdProc)
    (Φ : Val → IProp GF) (a b : Nat) (ha : a > 0) (hb : b > 0)
    (x : Name) (cont : List Stmt) (env : Env) (stack : List Frame) :
    ⦃ ▷ wp procs fork_post E (gcdProc_post a b x cont env stack) Φ ⦄
    (⟨.call x "gcdProc" [Expr.val (.int a), Expr.val (.int b)],
      cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ :=
  gcdProc_spec_gen procs fork_post hproc Φ a b ha hb x
    (Expr.val (.int a)) (Expr.val (.int b)) cont env stack rfl rfl

end GcdProcSpec

/-- Sample program: `v := gcd(6, 4) ; return v` evaluates to `2`. -/
def progGcd64 : Program where
  procs := fun n => if n = "gcdProc" then some gcdProc else none
  main  := ags(
    v := call gcdProc(6, 4) ;
    return v
  )

theorem gcd_6_4_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progGcd64 n (Machine.initial progGcd64) μ') :
    Machine.Adequate progGcd64 μ' (Val.int 2) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 2) progGcd64 ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · unfold Thread.initial progGcd64
    -- main = (v := call gcdProc(6, 4)) ; return v
    wp_step              -- wp_seq
    iintro !>
    -- Outer call: gcdProc(6, 4). Pushes frame ⟨v, [return v], Env.empty⟩.
    wp_call gcdProc
    -- Body with env {a ↦ 6, b ↦ 4}. Guard a = b is false.
    wp_step              -- wp_ite_false (outer if)
    iintro !>
    -- Inner if. Guard a < b: 6 < 4 is false.
    wp_step              -- wp_ite_false (inner if)
    iintro !>
    -- Body = r := call gcdProc(a - b, b) ; return r. seq, then call.
    wp_step              -- wp_seq
    iintro !>
    wp_step              -- wp_call gcdProc(2, 4)
    iintro !>
    -- Env {a ↦ 2, b ↦ 4}. Guard a = b is false.
    wp_step              -- wp_ite_false (outer if)
    iintro !>
    -- Guard a < b: 2 < 4 is true.
    wp_step              -- wp_ite_true (inner if)
    iintro !>
    wp_step              -- wp_seq
    iintro !>
    wp_step              -- wp_call gcdProc(2, 2)
    iintro !>
    -- Env {a ↦ 2, b ↦ 2}. Guard a = b is true.
    wp_step              -- wp_ite_true (outer if)
    iintro !>
    -- return a from gcdProc(2,2). Pops frame, binds r := 2 in caller.
    wp_step              -- wp_ret_pop_cons
    iintro !>
    -- ⟨return r, [], {a=2, b=4, r=2}, ...⟩
    wp_step              -- wp_ret_pop_cons (return r in middle frame)
    iintro !>
    -- ⟨return r, [], {a=6, b=4, r=2}, ⟨v,[return v],∅⟩⟩
    wp_step              -- wp_ret_pop_cons (return r in outer frame)
    iintro !>
    -- ⟨return v, [], {v=2}, []⟩
    wp_steps
    itrivial

/-- Closed adequacy for `progGcd64` derived from the universal Löb spec
`gcdProc_spec_gen`. Parallels how `fact_3_closed` is derived from
`factProc_spec_gen`. -/
theorem gcd_6_4_via_spec_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progGcd64 n (Machine.initial progGcd64) μ') :
    Machine.Adequate progGcd64 μ' (Val.int 2) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 2) progGcd64 ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · unfold Thread.initial progGcd64
    wp_step                     -- wp_seq
    iintro !>
    -- Apply the universal Löb spec at a=6, b=4, x="v", cont=[return v].
    wp_apply (gcdProc_spec_gen (E := ⊤)
              (fun n => if n = "gcdProc" then some gcdProc else none)
              iprop(emp : IProp GF) (by rfl)
              (fun v => iprop(⌜(fun w : Val => w = Val.int 2) v⌝))
              6 4 (by decide) (by decide) "v" (age(6)) (age(4))
              [ags(return v)] Env.empty [] rfl rfl)
    iintro !>
    unfold gcdProc_post
    simp only [show gcdSub 6 4 = 2 from by simp [gcdSub]]
    wp_steps
    itrivial

/-! ## Recursive `sumProc`: `sum(n) = 0 + 1 + ... + n`

A third recursive procedure validating that the Löb-induction
Hoare-spec pattern (`factProc_spec_gen`, `gcdProc_spec_gen`) composes
uniformly. Same skeleton, different arithmetic.

`sumProc(n) := if n = 0 then return 0
               else (r := call sumProc(n - 1) ; return n + r)` -/

/-- Recursive sum on `Nat`. -/
def sumNat : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumNat n

@[simp] theorem sumNat_zero : sumNat 0 = 0 := rfl
@[simp] theorem sumNat_succ (n : Nat) : sumNat (n + 1) = (n + 1) + sumNat n := rfl

/-- `sum` as a Agar procedure. -/
def sumProc : Proc where
  params := ["n"]
  body   := ags(
    if n = 0 then return 0
    else (r := call sumProc(n - 1) ; return n + r)
  )

section SumProcSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Post-call thread state for `sumProc`: result `Val.int (sumNat n)`
bound to `x` in the caller's env, with the caller's stack restored. -/
def sumProc_post (n : Nat) (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x (.int (sumNat n))
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Generalised universal spec for `sumProc`, by Löb induction.
Mirrors `factProc_spec_gen` / `gcdProc_spec_gen`. -/
theorem sumProc_spec_gen
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "sumProc" = some sumProc)
    (Φ : Val → IProp GF) (n : Nat) (x : Name) (eN : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (hN : Expr.eval env eN = some (.int (n : Int))) :
    ⦃ ▷ wp procs fork_post E (sumProc_post n x cont env stack) Φ ⦄
    (⟨.call x "sumProc" [eN], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ := by
  suffices key :
      ⊢ (iprop(∀ (n : Nat) (x : Name) (eN : Expr) (cont : List Stmt)
                (env : Env) (stack : List Frame),
          ⌜Expr.eval env eN = some (.int (n : Int))⌝ -∗
          (▷ wp procs fork_post E (sumProc_post n x cont env stack) Φ) -∗
          wp procs fork_post E
            ⟨.call x "sumProc" [eN], cont, env, stack, none⟩ Φ) : IProp GF) by
    have step : (True : IProp GF) ⊢
        iprop((▷ wp procs fork_post E (sumProc_post n x cont env stack) Φ) -∗
              wp procs fork_post E
                ⟨.call x "sumProc" [eN], cont, env, stack, none⟩ Φ) := by
      iintro _ HK
      iapply key
      · ipure_intro; exact hN
      · iexact HK
    exact BI.wand_entails (BI.true_intro.trans step)
  iloeb as HIH
  iintro %n %x %eN %cont %env %stack %hN HK
  have hargs : evalArgs env [eN] = some [.int (n : Int)] := by
    simp [agar_eval, hN]
  have harity : ([Val.int (n : Int)]).length = sumProc.params.length := rfl
  iapply (wp_call procs fork_post x "sumProc" [eN]
            sumProc [.int (n : Int)] cont env stack Φ hproc hargs harity)
  iintro !>
  simp only [sumProc]
  have hZero : ∀ ρ : Env, Expr.eval ρ (age(0)) = some (.int 0) := fun _ => rfl
  have hGuard : Expr.eval (bindParams ["n"] [Val.int (n : Int)])
                  (age(n = 0)) = some (.bool (decide ((n : Int) = 0))) := by
    simp [agar_eval, val_int_beq]
  by_cases hn0 : n = 0
  · -- Base case.
    subst hn0
    have hGuardT : Expr.eval (bindParams ["n"] [Val.int ((0:Nat) : Int)])
                     (age(n = 0)) = some (.bool true) := by
      rw [hGuard]; simp
    iapply wp_ite_true (heval := hGuardT)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hZero _)
      iintro !>
      unfold sumProc_post
      simp [sumNat]
      iexact HK
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hZero _)
      iintro !>
      unfold sumProc_post
      simp [sumNat]
      iexact HK
  · -- Recursive case: n > 0.
    have hn_pos : n ≥ 1 := Nat.pos_of_ne_zero hn0
    have hnIntNe : ¬ ((n : Int) = 0) := by exact_mod_cast hn0
    have hGuardF : Expr.eval (bindParams ["n"] [Val.int (n : Int)])
                     (age(n = 0)) = some (.bool false) := by
      rw [hGuard]; simp [hn0]
    iapply wp_ite_false (heval := hGuardF)
    iintro !>
    iapply wp_seq
    iintro !>
    have hSubNat : Expr.eval (bindParams ["n"] [Val.int (n : Int)])
                     (age(n - 1)) = some (.int (((n - 1 : Nat)) : Int)) := by
      have hcast : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
      simp [agar_eval, hcast]
    iapply HIH $$ %(n - 1) %"r" %(age(n - 1)) %([ags(return n + r)])
                  %(bindParams ["n"] [Val.int (n : Int)])
                  %(⟨x, cont, env⟩ :: stack)
                  %hSubNat
    iintro !>
    unfold sumProc_post
    simp
    have hAdd : Expr.eval
        ((bindParams ["n"] [Val.int (n : Int)]).set "r"
            (.int ((sumNat (n - 1 : Nat) : Int))))
        (age(n + r))
      = some (.int ((sumNat n : Int))) := by
      have hstep : Expr.eval
          ((bindParams ["n"] [Val.int (n : Int)]).set "r"
              (.int ((sumNat (n - 1 : Nat) : Int))))
          (age(n + r))
        = some (.int ((n : Int) + (sumNat (n - 1 : Nat) : Int))) := by
        simp [agar_eval]
      rw [hstep]
      congr 1
      have hsum : sumNat n = n + sumNat (n - 1) := by
        have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
        rw [hn_eq, sumNat]
        simp
      rw [hsum]; push_cast; rfl
    rcases hcont : cont with _ | ⟨s, cs⟩
    · iapply wp_ret_pop_nil (heval := hAdd)
      iintro !>
      iexact HK
    · iapply wp_ret_pop_cons (heval := hAdd)
      iintro !>
      iexact HK

/-- User-facing universal spec for `sumProc` with a value-literal argument. -/
theorem sumProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "sumProc" = some sumProc)
    (Φ : Val → IProp GF) (n : Nat) (x : Name) (cont : List Stmt)
    (env : Env) (stack : List Frame) :
    ⦃ ▷ wp procs fork_post E (sumProc_post n x cont env stack) Φ ⦄
    (⟨.call x "sumProc" [Expr.val (.int n)], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ :=
  sumProc_spec_gen procs fork_post hproc Φ n x (Expr.val (.int n))
    cont env stack rfl

end SumProcSpec

/-- Sample program: `v := sum(3) ; return v` evaluates to `6`. -/
def progSum3 : Program where
  procs := fun n => if n = "sumProc" then some sumProc else none
  main  := ags(
    v := call sumProc(3) ;
    return v
  )

/-- Closed adequacy for `progSum3` derived from `sumProc_spec_gen`. -/
theorem sum_3_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progSum3 n (Machine.initial progSum3) μ') :
    Machine.Adequate progSum3 μ' (Val.int 6) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 6) progSum3 ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · unfold Thread.initial progSum3
    wp_step                     -- wp_seq
    iintro !>
    wp_apply_gen_call_spec sumProc_spec_gen
      (fun n => if n = "sumProc" then some sumProc else none)
      (fun v => iprop(⌜(fun w : Val => w = Val.int 6) v⌝))
      3 "v" (age(3)) [ags(return v)] Env.empty []
    iintro !>
    unfold sumProc_post
    simp only [show sumNat 3 = 6 from rfl]
    wp_steps
    itrivial

/-- Sample program: `v := abs(-3) ; return v` evaluates to `3`. -/
def progAbsNeg3 : Program where
  procs := fun n => if n = "absProc" then some absProc else none
  main  := ags(
    v := call absProc(0 - 3) ;
    return v
  )

theorem max_5_3_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progMax53 n (Machine.initial progMax53) μ') :
    Machine.Adequate progMax53 μ' (Val.int 5) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 5) progMax53 ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · -- Derive from `maxProc_spec`. Main is `v := call maxProc(5,3) ; return v`.
    unfold Thread.initial progMax53
    -- Step the `seq` to get cont = [return v].
    wp_step  -- wp_seq
    iintro !>
    -- Apply the universal spec; cont = [return v], a = 5, b = 3.
    wp_apply_binop_spec maxProc_spec 5 3 "v" (.val (.int 5)) (.val (.int 3))
      [ags(return v)] Env.empty []
    iintro !> !> !>
    -- Post: `wp ⟨return v, [], Env.empty.set "v" (.int 5), [], none⟩ Φ`.
    unfold maxProc_post
    simp
    wp_done

theorem min_5_3_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progMin53 n (Machine.initial progMin53) μ') :
    Machine.Adequate progMin53 μ' (Val.int 3) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 3) progMin53 ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · -- Derive from `minProc_spec`. Main is `v := call minProc(5,3) ; return v`.
    unfold Thread.initial progMin53
    wp_step  -- wp_seq
    iintro !>
    -- Apply the universal spec; cont = [return v], a = 5, b = 3.
    -- 5 < 3 is false so result is b = 3.
    wp_apply_binop_spec minProc_spec 5 3 "v" (.val (.int 5)) (.val (.int 3))
      [ags(return v)] Env.empty []
    iintro !> !> !>
    unfold minProc_post
    simp
    wp_done

theorem abs_neg3_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progAbsNeg3 n (Machine.initial progAbsNeg3) μ') :
    Machine.Adequate progAbsNeg3 μ' (Val.int 3) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 3) progAbsNeg3 ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · -- Derive from `absProc_spec`. Main is `v := call absProc(0 - 3) ; return v`.
    unfold Thread.initial progAbsNeg3
    wp_step  -- wp_seq
    iintro !>
    -- Apply the universal spec; cont = [return v], x = -3.
    wp_apply_unary_spec absProc_spec (-3) "v" (age(0 - 3))
      [ags(return v)] Env.empty []
    iintro !> !> !>
    unfold absProc_post
    simp
    wp_done

theorem max_of_three_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progMaxOfThree n (Machine.initial progMaxOfThree) μ') :
    Machine.Adequate progMaxOfThree μ' (Val.int 5) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 5) progMaxOfThree ?_ n μ' htr
  intro _LC
  imod (heap_init (GF := GF) (F := F)) with ⟨%G, HA⟩
  imodintro
  letI : Agar.Logic.AgarG GF F := G
  letI SI : StateInterp GF := inferInstance
  iexists SI
  iexists iprop(emp : IProp GF)
  iframe HA
  · -- Derive from two applications of `maxProc_spec`.
    unfold Thread.initial progMaxOfThree
    wp_step  -- wp_seq
    iintro !>
    -- First call: maxProc(2, 5) → 5.
    wp_apply (maxProc_spec _ _ 2 5 "t" (.val (.int 2)) (.val (.int 5))
              [ags(r := call maxProc(t, 4); return r)] Env.empty []
              _ rfl rfl rfl)
    iintro !> !> !>
    unfold maxProc_post
    simp
    wp_step  -- wp_seq
    iintro !>
    -- Second call: maxProc(t, 4) where t = 5 → 5.
    wp_apply (maxProc_spec _ _ 5 4 "r" (age(t)) (.val (.int 4))
              [ags(return r)] (Env.empty.set "t" (.int 5)) []
              _ rfl (by simp [agar_eval]) rfl)
    iintro !> !> !>
    unfold maxProc_post
    simp
    wp_done

end Agar.Logic

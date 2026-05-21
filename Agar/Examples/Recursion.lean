module

public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Iris.Instances.Lib.FUpd
public import Agar.Iris.Wp
public import Agar.Iris.Rules
public import Agar.Iris.Heap
public import Agar.Iris.Adequacy
public import Agar.Iris.Tactics
public import Agar.Iris.Hoare

@[expose] public section

/-! # Recursion example programs

* `progFact` — recursive factorial; exercises `call` / `return` and the
                procedure table.

The `Examples.procTable` helper lives here because the recursive
factorial example is one of the first programs to reference it.
-/

namespace Agar
namespace Examples

/-- Build a procedure table from a literal list. -/
def procTable (ps : List (Name × Proc)) : Name → Option Proc :=
  fun n => (ps.find? (·.fst = n)).map (·.snd)

/-! ## Recursive factorial -/

def fact : Proc where
  params := ["n"]
  body := ags(
    if n < 1 then
      return 1
    else (
      r := call fact(n - 1) ;
      return n * r
    )
  )

def progFact : Program where
  procs := procTable [("fact", fact)]
  main  := ags(r := call fact(5))

example : progFact.procs "fact" = some fact := rfl

end Examples
end Agar


namespace Agar.Logic

open Iris Iris.BI Iris.OFE Agar.Logic

/-! ## Universal Löb-induction spec for `factProc`

The previous theorem `fact_3_closed` was the concrete `n = 3` unroll.
Here we give the universally quantified spec for `Examples.fact` using
Löb induction. The spec mirrors `maxProc_spec`'s shape: a call site
`x := call fact(n)` reduces to its post-thread under a single `▷`. -/

section FactProcSpec
open Iris Iris.BI

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- Local factorial on `Nat` (no Mathlib dependency). -/
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl
@[simp] theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

/-- Post-call thread state for `factProc`: result `Val.int (factorial n)`
bound to `x` in the caller's env, with the caller's stack restored.
Dispatches on the caller's continuation shape so the spec applies
uniformly whether the call is last (`cont = []`) or has a follow-up
(`cont = s :: cs`). -/
def factProc_post (n : Nat) (x : Name) (cont : List Stmt) (env : Env)
    (stack : List Frame) : Thread :=
  let env' : Env := env.set x (.int (factorial n))
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

/-- Generalised universal spec for `Examples.fact`, by Löb induction.
The argument is an arbitrary expression `eN` that evaluates to
`Val.int n` under the caller's `env`. This generality is essential
because the recursive call site inside `fact` itself uses the
expression `n - 1`, not a value literal. -/
theorem factProc_spec_gen
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "fact" = some Examples.fact)
    (Φ : Val → IProp GF) (n : Nat) (x : Name) (eN : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (hN : Expr.eval env eN = some (.int (n : Int))) :
    ⦃ ▷ wp procs fork_post E (factProc_post n x cont env stack) Φ ⦄
    (⟨.call x "fact" [eN], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ := by
  -- Bundle into iProp with eN, hN, n, x, cont, env, stack quantified.
  -- Keep `procs`, `fork_post`, `E`, `hproc`, `Φ` fixed across the recursion.
  suffices key :
      ⊢ (iprop(∀ (n : Nat) (x : Name) (eN : Expr) (cont : List Stmt)
                (env : Env) (stack : List Frame),
          ⌜Expr.eval env eN = some (.int (n : Int))⌝ -∗
          (▷ wp procs fork_post E (factProc_post n x cont env stack) Φ) -∗
          wp procs fork_post E
            ⟨.call x "fact" [eN], cont, env, stack, none⟩ Φ) : IProp GF) by
    -- Specialize inside the proofmode: derive the wand `▷ wp(post) -∗ wp(call)`
    -- as a `True`-entailment, then use `wand_entails`.
    have step : (True : IProp GF) ⊢
        iprop((▷ wp procs fork_post E (factProc_post n x cont env stack) Φ) -∗
              wp procs fork_post E
                ⟨.call x "fact" [eN], cont, env, stack, none⟩ Φ) := by
      iintro _ HK
      iapply key
      · ipure_intro; exact hN
      · iexact HK
    exact BI.wand_entails (BI.true_intro.trans step)
  iloeb as HIH
  iintro %n %x %eN %cont %env %stack %hN HK
  -- Outer call: discharge with `wp_call`.
  have hargs : evalArgs env [eN] = some [.int (n : Int)] := by
    simp [agar_eval, hN]
  have harity : ([Val.int (n : Int)]).length = Examples.fact.params.length := rfl
  iapply (wp_call procs fork_post x "fact" [eN]
            Examples.fact [.int (n : Int)] cont env stack Φ hproc hargs harity)
  -- Strip later — also strips ▷ from HIH and HK.
  iintro !>
  simp only [Examples.fact]
  -- Useful eval facts under the body's bound env `bindParams ["n"] [Val.int n]`.
  have hOne : ∀ ρ : Env, Expr.eval ρ (age(1)) = some (.int 1) := fun _ => rfl
  have hGuard : Expr.eval (bindParams ["n"] [Val.int (n : Int)])
                (age(n < 1)) = some (.bool (decide ((n : Int) < 1))) := by
    simp [agar_eval]
  -- Case split on `n < 1`.
  by_cases hlt : (n : Int) < 1
  · -- Base case: `n = 0`.
    have hn0 : n = 0 := by omega
    subst hn0
    have hGuardT : Expr.eval (bindParams ["n"] [Val.int ((0:Nat) : Int)])
                     (age(n < 1)) = some (.bool true) := by
      rw [hGuard]; simp
    iapply wp_ite_true (heval := hGuardT)
    iintro !>
    cases hcont : cont with
    | nil =>
      iapply wp_ret_pop_nil (heval := hOne _)
      iintro !>
      unfold factProc_post
      simp [factorial]
      iexact HK
    | cons s cs =>
      iapply wp_ret_pop_cons (heval := hOne _)
      iintro !>
      unfold factProc_post
      simp [factorial]
      iexact HK
  · -- Recursive case: `n ≥ 1`.
    have hn_pos : n ≥ 1 := by omega
    have hGuardF : Expr.eval (bindParams ["n"] [Val.int (n : Int)])
                     (age(n < 1)) = some (.bool false) := by
      rw [hGuard]; simp [hlt]
    iapply wp_ite_false (heval := hGuardF)
    wp_pures
    -- Inner call argument: `age(n - 1)`, evaluates to `Val.int ((n-1 : Nat) : Int)`.
    have hSubNat : Expr.eval (bindParams ["n"] [Val.int (n : Int)])
                     (age(n - 1)) = some (.int (((n - 1 : Nat)) : Int)) := by
      have : Expr.eval (bindParams ["n"] [Val.int (n : Int)]) (age(n - 1))
           = some (.int ((n : Int) - 1)) := by
        simp [agar_eval]
      rw [this]
      have hcast : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by
        have := Nat.sub_add_cancel hn_pos  -- (n-1) + 1 = n
        omega
      rw [hcast]
    -- Apply the IH at (n-1, "r", age(n-1), [return n*r], envB, ⟨x,cont,env⟩::stack).
    wp_apply HIH $$ %(n - 1) %"r" %(age(n - 1)) %([ags(return n * r)])
                  %(bindParams ["n"] [Val.int (n : Int)])
                  %(⟨x, cont, env⟩ :: stack)
                  %hSubNat
    iintro !>
    -- factProc_post (n-1) "r" [return n*r] envB (⟨x,cont,env⟩::stack)
    --  = ⟨return n*r, [], envB.set "r" (.int ((n-1)!)), ⟨x,cont,env⟩::stack, none⟩
    unfold factProc_post
    simp
    -- Step `return n*r`: pops the frame ⟨x, cont, env⟩, evaluating n*r
    -- in envB.set "r" (.int ((n-1)!)). The product is n * (n-1)! = n!.
    have hMul : Expr.eval
        ((bindParams ["n"] [Val.int (n : Int)]).set "r"
            (.int ((factorial (n - 1 : Nat) : Int))))
        (age(n * r))
      = some (.int ((factorial n : Int))) := by
      have hstep : Expr.eval
          ((bindParams ["n"] [Val.int (n : Int)]).set "r"
              (.int ((factorial (n - 1 : Nat) : Int))))
          (age(n * r))
        = some (.int ((n : Int) * (factorial (n - 1 : Nat) : Int))) := by
        simp [agar_eval]
      rw [hstep]
      congr 1
      -- n * (n-1)! = n!
      have hfact : factorial n = n * factorial (n - 1) := by
        have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
        rw [hn_eq, factorial]
        simp
      rw [hfact]; push_cast; rfl
    -- Split on the outer caller's continuation; HK matches by iota-reduction.
    rcases hcont : cont with _ | ⟨s, cs⟩
    · iapply wp_ret_pop_nil (heval := hMul)
      iintro !>
      -- HK : wp (match [] with | [] => skip-thread | _ => ...) reduces by iota
      iexact HK
    · iapply wp_ret_pop_cons (heval := hMul)
      iintro !>
      iexact HK

/-- The user-facing universal spec for `factProc`, with a value-literal
argument. Special case of `factProc_spec_gen`. -/
theorem factProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "fact" = some Examples.fact)
    (Φ : Val → IProp GF) (n : Nat) (x : Name) (cont : List Stmt)
    (env : Env) (stack : List Frame) :
    ⦃ ▷ wp procs fork_post E (factProc_post n x cont env stack) Φ ⦄
    (⟨.call x "fact" [Expr.val (.int n)], cont, env, stack, none⟩ : Thread)
    ⦃ Φ ⦄ :=
  factProc_spec_gen procs fork_post hproc Φ n x (Expr.val (.int n))
    cont env stack rfl

end FactProcSpec

/-- Self-contained `fact(3)` driver. Uses the recursive `Examples.fact`
procedure verbatim; the procedure table is the simple branchy form so
`procs "fact" = some fact` reduces by `rfl`. -/
def progFact3 : Program where
  procs := fun n => if n = "fact" then some Examples.fact else none
  main  := ags(
    v := call fact(3) ;
    return v
  )

/-- Closed adequacy: `progFact3` returns `Val.int 6` on every
terminated main thread of every `StepStarN`-trace. Derived as an
instantiation of the universal Löb spec `factProc_spec`. -/
theorem fact_3_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN progFact3 n (Machine.initial progFact3) μ') :
    Machine.Adequate progFact3 μ' (Val.int 6) := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.int 6) progFact3 ?_ n μ' htr
  start_closed_proof_with_heap progFact3
  -- main = (v := call fact(3)) ; return v
  wp_step                     -- wp_seq
  iintro !>
  -- Apply the universal Löb spec at n=3, x="v", cont=[return v].
  -- Note: we pass the literal `procs` lambda (matching the unfolded goal)
  -- and η-expanded Φ so `iapply`'s unifier accepts both.
  wp_apply_gen_call_spec factProc_spec_gen
    (fun n => if n = "fact" then some Examples.fact else none)
    (fun v => iprop(⌜(fun w : Val => w = Val.int 6) v⌝))
    3 "v" (age(3)) [ags(return v)] Env.empty []
  iintro !>
  -- Post-thread: ⟨return v, [], Env.empty.set "v" (.int 6), [], none⟩.
  unfold factProc_post
  simp only [show factorial 3 = 6 from rfl]
  wp_steps
  itrivial

/-! ## Closed adequacy for the existing `Examples.progFact`

`Examples.progFact.main = ags(r := call fact(5))` — a single
`call` with no follow-up `return`, so after the call the thread
falls through to `skip` and terminates with `toValue = some Val.unit`.
The numeric result `Val.int 120` is bound to `r` in the local env
but never observed by `toValue`. -/
theorem progFact_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    (n : Nat) (μ' : Machine)
    (htr : Machine.StepStarN Examples.progFact n
            (Machine.initial Examples.progFact) μ') :
    Machine.Adequate Examples.progFact μ' Val.unit := by
  unfold Machine.Adequate Machine.Safe Machine.MainReturns
  refine wp_strong_adequacy_bupd (GF := GF)
    (φ := fun v => v = Val.unit) Examples.progFact ?_ n μ' htr
  start_closed_proof_with_heap Examples.progFact
  -- main = (r := call fact(5)) with empty continuation.
  wp_apply_gen_call_spec factProc_spec_gen
    (Examples.procTable [("fact", Examples.fact)])
    (fun v => iprop(⌜(fun w : Val => w = Val.unit) v⌝))
    5 "r" (age(5)) [] Env.empty []
  iintro !>
  -- Post-thread: ⟨skip, [], Env.empty.set "r" (.int 120), [], none⟩.
  unfold factProc_post
  wp_done

end Agar.Logic

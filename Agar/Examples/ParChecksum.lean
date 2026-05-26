module

public import Std.Do.Triple
public import Std.Do.WP
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Lang.Denotational
public import Agar.Iris.PureHelperBridge
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
public import Agar.Iris.TacticsAtomic
public import Agar.Iris.WpSpin
public import Agar.Iris.Algebra.CounterRA
public import Agar.Operational.Composition
public import Agar.Iris.Completeness
public import Agar.Operational.StrictHelper
public import Agar.Iris.StackPush
public import Agar.Iris.RouteABridge

@[expose] public section

/-! # `parChecksumComposite` — Iris-load-bearing showcase for Std.Do dispatch

**What this example shows off.** Two forked workers each call a pure
arithmetic helper `sumSquares n a := a² + (a+1)² + … + (a+n-1)²` and
CAS-write the result into a shared cell. Main spin-loads the cell until
it observes the full sum and returns it. Closed adequacy at the
concrete value `Val.int 91` (= `14 + 77`).

**Why it's a better showcase than `ExternalSolver`.** The Iris half is
genuine concurrent reasoning: a three-state shared-cell invariant, two
`wp_fork`s, atomic CAS inside the invariant, and a spin-load join.
None of that would make sense in a sequential logic. The pure
arithmetic — the kind of thing that's painful to `wp_pures` through —
gets dispatched to one short `Std.Do.Triple` and reused at *both* call
sites. **One pure spec, two concurrent dispatch sites.**

**The bridge is example-independent.** `wp_callee_routeA_generic` is
imported from `Agar/Iris/RouteABridge.lean`; the local
`wp_sumSquares_callee_routeA` is just a one-line specialization, the
same shape as `ExternalSolver`'s. The composite's heap-using main and
its CAS-using worker procs **do not need to be heap-free** — the
generic bridge handles that via `wp_procs_irrel_strict` (Iris-level
procs-irrelevance for strict helpers).

**Status.** The bridge instantiation, helper-init operational facts,
and adequacy-corollary statement are all closed. Remaining sorrys:
- `helper_safeTp_sumSquares` — the Std.Do triple → operational safety
  chain (mechanical copy of `ExternalSolver`'s `helper_safeTp`).
- `workerA_spec` / `workerB_spec` — the per-worker WP, using
  `wp_sumSquares_callee_routeA` for the helper call + a CAS rule.
- `parChecksum_closed` — adequacy entry-point that ties it together. -/

namespace Agar
open Agar.Logic
namespace ParChecksum

/-! ## The pure helper -/

/-- Loop body: `acc := acc + i*i ; i := i + 1`. -/
def sumSqBody : PureStmt :=
  .seq (.assign "acc"
          (.bin .add (.var "acc") (.bin .mul (.var "i") (.var "i"))))
       (.assign "i" (.bin .add (.var "i") (.val (.int 1))))

/-- Full body PureStmt: `acc := 0 ; i := a ; forN n sumSqBody`. -/
def sumSqProg (n : Nat) : PureStmt :=
  .seq (.assign "acc" (.val (.int 0)))
   (.seq (.assign "i" (.var "a"))
    (.forN n sumSqBody))

/-- `sumSquares n`: pure helper proc. Param `a` is the start; `n` is
baked at the proc level. -/
def sumSquares (n : Nat) : Proc where
  params := ["a"]
  body   := .seq (embed (sumSqProg n)) (.ret (.var "acc"))

/-- Closed-form: `a² + (a+1)² + … + (a+k-1)²`. -/
def sumSquaresValue (a : Int) : Nat → Int
  | 0     => 0
  | k + 1 => a*a + sumSquaresValue (a + 1) k

/-- Right-extension identity: extending the closed form by one
right-end term `(a+k)²`. Used by the inner-loop invariant step. -/
theorem sumSquaresValue_succ (a : Int) (k : Nat) :
    sumSquaresValue a (k+1) = sumSquaresValue a k + (a + k) * (a + k) := by
  induction k generalizing a with
  | zero => simp [sumSquaresValue]
  | succ k ih =>
      show a*a + sumSquaresValue (a+1) (k+1) = (a*a + sumSquaresValue (a+1) k) + _
      rw [ih (a+1)]
      have heq : (a + 1 + (k : Int)) = (a + ((k+1 : Nat) : Int)) := by push_cast; omega
      rw [heq, Int.add_assoc]

/-- Helper-post: at `vs = [int a]`, the return value is the closed
form `sumSquaresValue a n`. -/
def sumSquares_post (n : Nat) (vs : List Val) (v : Val) : Prop :=
  ∃ a : Int, vs = [Val.int a] ∧ v = Val.int (sumSquaresValue a n)

/-! ### Std.Do triple for the pure helper (Layer 2)

The headline `Std.Do.Triple` on `denoteM (sumSqProg n)` —
the `do`-block monadic denotation, which can be reasoned about
directly with the `Std.Do` machinery (no `denote`-shaped match form
in the way). Proved with `mvcgen` + the `@[spec]`-registered
`iterM_spec` loop-invariant rule + a body-step lemma `sumSqBody_step`
(itself also closed by `mvcgen`).
Everything below (layers 3–5 plus the operational connection in
`helper_safeTp_sumSquares`) consumes this triple. -/

section StdDo
open Std.Do

/-- **`mvcgen` spec for `iterM`.** Given a per-iteration invariant `Inv`
indexed by *iterations completed so far*, where the body advances
`Inv k` to `Inv (k+1)` with a `some ()` result, `iterM body n` advances
`Inv 0` to a final state where the result is `some ()` and `Inv n` holds.

Auto-registered as `@[spec]` so `mvcgen` discovers it when traversing
`iterM`. The user supplies the invariant when invoking `mvcgen`. -/
@[spec]
theorem iterM_spec
    (body : StateM Env (Option Unit))
    (Inv : Nat → Env → Prop)
    (step : ∀ k,
      ⦃fun ρ => ⌜Inv k ρ⌝⦄
      body
      ⦃⇓ r => fun ρ' => ⌜r = some () ∧ Inv (k+1) ρ'⌝⦄)
    (n : Nat) :
    ⦃fun ρ => ⌜Inv 0 ρ⌝⦄
    Agar.iterM body n
    ⦃⇓ r => fun ρ' => ⌜r = some () ∧ Inv n ρ'⌝⦄ := by
  -- Reformulate as a pair-level pointwise fact, prove by induction,
  -- then re-wrap.
  suffices aux : ∀ (j n : Nat) (ρ : Env),
      Inv j ρ →
      (Agar.iterM body n ρ).fst = some () ∧ Inv (j + n) (Agar.iterM body n ρ).snd by
    intro ρ hpre
    have := aux 0 n ρ hpre
    simpa using this
  intro j n
  induction n generalizing j with
  | zero =>
      intro ρ hpre
      refine ⟨rfl, ?_⟩
      simpa using hpre
  | succ k ih =>
      intro ρ hpre
      rw [iterM_succ]
      simp only [bind, StateT.bind]
      -- Extract the pair-form fact from `step j`.
      have hstep : (body ρ).fst = some () ∧ Inv (j+1) (body ρ).snd := by
        have h := step j ρ hpre
        exact h
      rcases hb : body ρ with ⟨ob, ρb⟩
      rw [hb] at hstep
      obtain ⟨hres, hInv⟩ := hstep
      subst hres
      simp only
      have hih := ih (j+1) ρb hInv
      have heq : j + (k+1) = (j+1) + k := by omega
      rw [heq]
      exact hih

/-- Per-iteration invariant for the inner `iterM` loop of `sumSqProg`,
parameterised on the initial value `a` of variable `"i"` at loop entry:
after `k` iterations, `acc` holds the partial sum and `i` is `a + k`. -/
def sumSqInv (a : Int) (k : Nat) (ρ : Env) : Prop :=
  ρ "acc" = some (Val.int (sumSquaresValue a k)) ∧
  ρ "i"   = some (Val.int (a + k))

/-- **mvcgen-driven body-step lemma**: one iteration of `sumSqBody`
(viewed through `denoteM`) preserves `sumSqInv`. Closed by `mvcgen`,
which generates exactly three VCs (acc-eval failure, i-eval failure,
and the successful invariant step); each is discharged by basic
environment-update arithmetic. -/
theorem sumSqBody_step (a : Int) (k : Nat) :
    ⦃fun ρ => ⌜sumSqInv a k ρ⌝⦄
    denoteM sumSqBody
    ⦃⇓ r => fun ρ' => ⌜r = some () ∧ sumSqInv a (k+1) ρ'⌝⦄ := by
  intro ρ ⟨hacc, hi⟩
  simp only [sumSqBody, denoteM_norm]
  mvcgen
  · -- vc1: Expr.eval acc+i*i = none, contradicts hacc + hi.
    rename_i hev
    simp [Expr.eval, hacc, hi, BinOp.eval] at hev
  · -- vc2: Expr.eval i+1 = none after acc was set, contradicts hi.
    rename_i v_acc _ hev_i
    have hρ_i : (ρ.set "acc" v_acc) "i" = some (Val.int (a + k)) := by
      show (if "i" = "acc" then _ else ρ "i") = _
      simp [hi]
    simp [Expr.eval, hρ_i, BinOp.eval] at hev_i
  · -- vc3: success — invariant holds after both updates.
    rename_i v_acc hev_acc v_i hev_i
    have hv_acc : v_acc = Val.int (sumSquaresValue a k + (a + k) * (a + k)) := by
      simp [Expr.eval, hacc, hi, BinOp.eval] at hev_acc
      exact hev_acc.symm
    subst hv_acc
    have hρ_i : (ρ.set "acc" (Val.int (sumSquaresValue a k + (a+k)*(a+k)))) "i"
                  = some (Val.int (a + k)) := by
      show (if "i" = "acc" then _ else ρ "i") = _
      simp [hi]
    have hv_i : v_i = Val.int (a + k + 1) := by
      simp [Expr.eval, hρ_i, BinOp.eval] at hev_i
      exact hev_i.symm
    subst hv_i
    refine ⟨trivial, ?_, ?_⟩
    · -- acc-component.
      show ((ρ.set "acc" _).set "i" _) "acc" = _
      show (if "acc" = "i" then _ else _) = _; simp
      show (if "acc" = "acc" then _ else _) = _; simp
      rw [sumSquaresValue_succ]
    · -- i-component.
      show ((ρ.set "acc" _).set "i" _) "i" = _
      show (if "i" = "i" then _ else _) = _; simp
      push_cast
      omega

/-- **mvcgen-driven proof of the headline triple.** The full triple
on `denoteM (sumSqProg n)` closes via three pieces:
1. `mvcgen` walks the top-level `acc := 0 ; i := a ; forN n sumSqBody`
   sequence, applying spec lemmas mechanically.
2. `iterM_spec` (auto-discovered as `@[spec]`) lets `mvcgen` reduce the
   `forN`/`iterM` loop to: a body-step obligation and an exit
   obligation, parameterised on the loop invariant `sumSqInv`.
3. The body step is `sumSqBody_step` — itself proved by `mvcgen` plus
   three trivial discharges. The exit and entry obligations are
   environment-update bookkeeping. -/
theorem sumSquares_spec (n : Nat) (a : Int) :
    ⦃fun ρ : Env => ⌜ρ "a" = some (Val.int a)⌝⦄
    denoteM (sumSqProg n)
    ⦃⇓ r => fun ρ' : Env =>
      ⌜r = some () ∧ ρ' "acc" = some (Val.int (sumSquaresValue a n))⌝⦄ := by
  intro ρ hpre
  have ha : ρ "a" = some (Val.int a) := hpre
  let ρ₂ : Env := (ρ.set "acc" (.int 0)).set "i" (.int a)
  have hρ₂_inv : sumSqInv a 0 ρ₂ := by
    refine ⟨?_, ?_⟩
    · show (if "acc" = "i" then some (Val.int a) else _) = _
      simp
      show (if "acc" = "acc" then _ else _) = _
      simp [sumSquaresValue]
    · show (if "i" = "i" then _ else _) = _; simp
  -- Loop result via `iterM_spec` + `sumSqBody_step`.
  have hloop := iterM_spec (denoteM sumSqBody) (sumSqInv a)
                  (fun k => sumSqBody_step a k) n ρ₂ hρ₂_inv
  obtain ⟨hr, hacc, _hi⟩ := hloop
  -- Connect denoteM (sumSqProg n) ρ to iterM (denoteM sumSqBody) n ρ₂.
  have hva : Expr.eval (ρ.set "acc" (Val.int 0)) (.var "a") = some (Val.int a) := by
    show (ρ.set "acc" (Val.int 0)) "a" = _
    show (if "a" = "acc" then _ else ρ "a") = _; simp [ha]
  have h0 : Expr.eval ρ (.val (.int 0)) = some (Val.int 0) := rfl
  have hprog : denoteM (sumSqProg n) ρ =
                iterM (denoteM sumSqBody) n ρ₂ := by
    show denoteM (.seq (.assign "acc" _) (.seq (.assign "i" _) (.forN n sumSqBody))) ρ = _
    simp only [denoteM_norm, bind, StateT.bind, get, getThe, MonadStateOf.get,
               StateT.get, StateT.set, set, MonadStateOf.set,
               pure, StateT.pure, h0, hva]
    rfl
  refine ⟨?_, ?_⟩
  · show (denoteM (sumSqProg n) ρ).fst = some ()
    rw [hprog]; exact hr
  · show (denoteM (sumSqProg n) ρ).snd "acc" = some (Val.int (sumSquaresValue a n))
    rw [hprog]; exact hacc

end StdDo

/-! ## The composite

Workers each call `sumSquares 3` with a different start value:
- `workerA` calls with `a = 1` → `1 + 4 + 9 = 14`.
- `workerB` calls with `a = 4` → `16 + 25 + 36 = 77`.

Each worker CAS-bumps the shared cell from its observed value `k` to
`k + result` (a simple inline CAS loop is left implicit in the surface
syntax for now — the proof shape pins the cell to two transitions
LEFT → MIDDLE → RIGHT in the invariant). Main spin-loads until it
observes `91`. -/

/-- The "middle" value the shared cell observes once workerA wins its
CAS: `sumSquaresValue Nb Na`. -/
abbrev midVal (Na : Nat) (Nb : Int) : Int := sumSquaresValue Nb Na

/-- The "top" value the shared cell observes once workerB wins its
CAS: `sumSquaresValue Nb Na + sumSquaresValue Nc Na`. This is the
adequacy-claim value. -/
abbrev topVal (Na : Nat) (Nb Nc : Int) : Int :=
  sumSquaresValue Nb Na + sumSquaresValue Nc Na

/-- Worker A: compute `sumSquares Na Nb`, then CAS-write the result
into shared cell `s` (expected: `0`, new: `midVal Na Nb`).

The helper's loop count `Na` is implicit via the procs table (which
binds `"sumSquares"` to `sumSquares Na`); the worker proc itself only
mentions `Nb`. -/
def workerA (Nb : Int) : Proc where
  params := ["s"]
  body   :=
    .seq (.call "v" "sumSquares" [.val (.int Nb)])
     (.seq (.cas "p" (.var "s") (.val (.int 0)) (.var "v"))
           (.ret (.val .unit)))

/-- Worker B: compute `sumSquares Na Nc`, then CAS-write the
accumulated total into shared cell `s` (expected: `midVal Na Nb`,
new: `topVal Na Nb Nc`). The CAS expected value is pinned to
workerA's outcome, reflecting the staged "A then B" design. -/
def workerB (Na : Nat) (Nb Nc : Int) : Proc where
  params := ["s"]
  body   :=
    .seq (.call "v" "sumSquares" [.val (.int Nc)])
     (.seq (.cas "p" (.var "s") (.val (.int (midVal Na Nb)))
                                (.val (.int (topVal Na Nb Nc))))
           (.ret (.val .unit)))

/-- The composite program, parameterized over the helper loop count
`Na` and the two worker arguments `Nb`, `Nc`. The original showcase
instance is `(Na, Nb, Nc) = (3, 1, 4)`, yielding `topVal = 91`. -/
def parChecksumComposite (Na : Nat) (Nb Nc : Int) : Program where
  procs := fun name =>
    if name = "sumSquares" then some (sumSquares Na)
    else if name = "workerA" then some (workerA Nb)
    else if name = "workerB" then some (workerB Na Nb Nc)
    else none
  main  := ags(
    s      := alloc 0 ;
    fork workerA(s) ;
    fork workerB(s) ;
    done   := 0 ;
    result := 0 ;
    (while done = 0 do (
      v := load s ;
      if v = #(Expr.val (Val.int (topVal Na Nb Nc))) then (result := v ; done := 1) else skip
    )) ;
    return result
  )

/-! ## Iris-side proof skeleton -/

end ParChecksum
end Agar

namespace Agar.Logic
open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet
open Agar.ParChecksum

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-- Three-state invariant for the shared sum cell: tracks the
`0 → midVal → topVal` write progression. Phrased as a direct ternary
disjunction (rather than `∃ v, points_to l v ∗ ⌜v ∈ …⌝`) so the
later-commutation in each CAS branch fires. -/
abbrev sumInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    (Na : Nat) (Nb Nc : Int) (l : Loc) : IProp GF :=
  iprop(
    points_to (GF := GF) (F := F) l (Val.int 0)
      ∨ (points_to (GF := GF) (F := F) l (Val.int (midVal Na Nb))
          ∨ points_to (GF := GF) (F := F) l (Val.int (topVal Na Nb Nc))))

/-! ### Operational obligations for the composite

These are the inputs the generic bridge needs. The first two are
mechanical case-splits on the composite's structure; the third —
`helper_safeTp_sumSquares` — is what the Std.Do triple will eventually
deliver via the operational pipeline (left as `sorry` for now). -/

/-- Helper-init thread for `sumSquares n` at argument `a`. -/
def sumSquares_init (n : Nat) (a : Int) : Thread :=
  ⟨(sumSquares n).body, [], bindParams ["a"] [Val.int a], [], none⟩

/-- Heap-freeness of the standalone helper-init thread. The helper
itself is a pure arithmetic loop — no heap ops. -/
theorem sumSquares_init_heapFree (n : Nat) (a : Int) :
    (sumSquares_init n a).heapFree := by
  refine ⟨?_, ?_, ?_⟩
  · show Stmt.heapFree _
    exact ⟨embed_heapFree _, trivial⟩
  · intro s hs; cases hs
  · intro f hf; cases hf

/-- `sumSqProg` is while-free (it's a `forN`, not a `while`). -/
theorem sumSqProg_whileFree (n : Nat) : (sumSqProg n).whileFree := by
  unfold sumSqProg sumSqBody PureStmt.whileFree
  exact ⟨trivial, trivial, ⟨trivial, trivial⟩⟩

/-- Strict-helper-thread structure of `sumSquares_init`. This is the
key fact that lets the new bridge skip heap-freeness on the composite's
procs: strict helpers don't consult the procs table during execution. -/
theorem sumSquares_init_strictHelperThread (n : Nat) (a : Int) :
    StrictHelperThread (sumSquares_init n a) := by
  refine ⟨?_, ?_, rfl⟩
  · change StrictHelperShape (.seq (embed (sumSqProg n)) (.ret (.var "acc")))
    exact .seq _ _ (embed_strictHelperShape _ (sumSqProg_whileFree n)) (.ret _)
  · intro s hmem; cases hmem

/-! ### Layers 3–5: operational chain consuming `sumSquares_spec`

Mechanical port from ExternalSolver. The whole pipeline is parametric
in the Std.Do triple, which is now closed (see `sumSquares_spec`). -/

/-- Standalone env containing only `a = Val.int a`. -/
def env_with_a (a : Int) : Env := Env.empty.set "a" (.int a)

theorem env_with_a_eq_bindParams (a : Int) :
    env_with_a a = bindParams ["a"] [Val.int a] := by
  simp [env_with_a, bindParams]

/-- **Layer 3 (a).** Cosmetic repackaging of the triple: the helper
monadic denotation actually evaluates to some `(some (), ρ_f)` with
the right `acc`. -/
theorem sumSquares_denoteM_converges (n : Nat) (a : Int) :
    ∃ ρ_f, denoteM (sumSqProg n) (env_with_a a) = (some (), ρ_f) ∧
      Expr.eval ρ_f (.var "acc") = some (Val.int (sumSquaresValue a n)) := by
  have hpre : (env_with_a a) "a" = some (Val.int a) := by
    simp [env_with_a, Env.set]
  have hpost := sumSquares_spec n a (env_with_a a) hpre
  obtain ⟨hr, hacc⟩ := hpost
  refine ⟨(denoteM (sumSqProg n) (env_with_a a)).2, ?_, ?_⟩
  · show denoteM (sumSqProg n) (env_with_a a)
      = (some (), (denoteM (sumSqProg n) (env_with_a a)).2)
    rw [← hr]
    rfl
  · simp [Expr.eval]
    exact hacc

/-- Sum-squares packaged as a `PureHelper` for the standalone-helper
program. -/
def sumSquaresHelper (n : Nat) : PureHelper where
  body := sumSqProg n
  ret  := .var "acc"

/-- **Layer 3 (b).** `denoteHelperM` evaluates to the closed form. -/
theorem sumSquares_denoteHelperM (n : Nat) (a : Int) :
    denoteHelperM (sumSquaresHelper n) (env_with_a a)
      = some (Val.int (sumSquaresValue a n)) := by
  obtain ⟨ρ_f, hd, hv⟩ := sumSquares_denoteM_converges n a
  simp [denoteHelperM, sumSquaresHelper, hd]
  exact hv

/-- Standalone helper program (no worker procs). -/
abbrev sumSquaresHelperProg (n : Nat) : Program :=
  programOfHelper (sumSquaresHelper n)

theorem sumSquares_init_helperThread (n : Nat) (a : Int) :
    HelperThread (sumSquares_init n a) := by
  refine ⟨?_, ?_, rfl⟩
  · change HelperShape (.seq (embed (sumSqProg n)) (.ret (.var "acc")))
    exact .seq _ _ (embedShape_helperShape (embed_embedShape _)) (.ret _)
  · intro s hmem; cases hmem

/-- **Layer 4.** The standalone helper-init thread reaches the
helper-terminal: `pstep` once into the embedded body, run
`denoteM_sound` for the body, `pstep` through `skip → ret`, arrive at
`helperTerminal`. -/
theorem sumSquares_init_reaches_terminal (n : Nat) (a : Int) :
    PureSteps (sumSquares_init n a)
      (helperTerminal
        ((denoteM (sumSqProg n) (env_with_a a)).2)
        (Val.int (sumSquaresValue a n))) := by
  obtain ⟨ρ_f, hd, hv⟩ := sumSquares_denoteM_converges n a
  have hρ_f : (denoteM (sumSqProg n) (env_with_a a)).2 = ρ_f := by rw [hd]
  rw [hρ_f]
  have hstep1 : pstep (sumSquares_init n a) =
      some ⟨embed (sumSqProg n), [.ret (.var "acc")],
            bindParams ["a"] [Val.int a], [], none⟩ := by
    show pstep ⟨.seq (embed (sumSqProg n)) (.ret (.var "acc")), [],
                bindParams ["a"] [Val.int a], [], none⟩ = _
    rfl
  have hbody : PureSteps
      ⟨embed (sumSqProg n), [.ret (.var "acc")],
       bindParams ["a"] [Val.int a], [], none⟩
      ⟨.skip, [.ret (.var "acc")], ρ_f, [], none⟩ := by
    have := denoteM_sound (sumSqProg n) [.ret (.var "acc")]
      (bindParams ["a"] [Val.int a]) ρ_f
      (env_with_a_eq_bindParams a ▸ hd)
    exact this
  have hstep3 : pstep ⟨.skip, [.ret (.var "acc")], ρ_f, [], none⟩ =
      some ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ := rfl
  have hstep4 : pstep ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ =
      some (helperTerminal ρ_f (Val.int (sumSquaresValue a n))) := by
    show pstep ⟨.ret (.var "acc"), [], ρ_f, [], none⟩ = _
    simp [pstep, tstep, hv, doReturn, helperTerminal]
  exact .step hstep1 (hbody.trans (.step hstep3 (.single hstep4)))

private theorem sumSquaresHelperProg_stepStarN_chain (n : Nat) (σ : Mem) :
    ∀ steps t₀ μ', HelperThread t₀ →
      Machine.StepStarN (sumSquaresHelperProg n) steps ⟨σ, [t₀]⟩ μ' →
      ∃ t', μ' = ⟨σ, [t']⟩ ∧ PureSteps t₀ t' ∧ HelperThread t' := by
  intro steps
  induction steps with
  | zero =>
      intro t₀ μ' he htraj
      cases htraj
      exact ⟨t₀, rfl, .refl, he⟩
  | succ k ih =>
      intro t₀ μ' he htraj
      cases htraj with
      | step h1 h2 =>
          have ⟨t', hμ_mid, hp, hHt'⟩ := machineStep_helper _ σ _ _ he h1
          rw [hμ_mid] at h2
          have ⟨t'', hμ_end, hps, hHt''⟩ := ih _ _ hHt' h2
          exact ⟨t'', hμ_end, .step hp hps, hHt''⟩

/-- **Layer 5.** Operational safety of the standalone helper under
`noProcs`. -/
theorem sumSquaresHelperProg_safe (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp (sumSquaresHelperProg n) ⟨σ, [sumSquares_init n a]⟩
        (fun v => v = Val.int (sumSquaresValue a n)) := by
  intro σ steps μ' htraj k t htk
  obtain ⟨ρ_f, hd, hv⟩ := sumSquares_denoteM_converges n a
  have h_reach := sumSquares_init_reaches_terminal n a
  have hρ_f_eq : (denoteM (sumSqProg n) (env_with_a a)).2 = ρ_f := by rw [hd]
  rw [hρ_f_eq] at h_reach
  have ⟨t', hμ', hps, hHt'⟩ :=
    sumSquaresHelperProg_stepStarN_chain n σ steps _ μ'
      (sumSquares_init_helperThread n a) htraj
  rcases k with _ | k
  · rw [hμ'] at htk
    simp at htk
    subst htk
    rcases hp : pstep t' with _ | tn
    · have hstuck_term :
          pstuck (helperTerminal ρ_f (Val.int (sumSquaresValue a n))) :=
        helperTerminal_pstuck _ _
      have hstuck_t' : pstuck t' := hp
      have ht_eq : t' = helperTerminal ρ_f (Val.int (sumSquaresValue a n)) :=
        PureSteps.stuck_unique hps hstuck_t' h_reach hstuck_term
      subst ht_eq
      left
      refine ⟨Val.int (sumSquaresValue a n),
              helperTerminal_toValue _ _, fun _ => rfl⟩
    · right
      rw [hμ']
      refine ⟨σ, tn, none, none, ?_⟩
      show tstep (sumSquaresHelperProg n).procs none _ _ = _
      show tstep noProcs none σ t' = _
      exact tstep_helperShape_chosen_none hp σ
  · rw [hμ'] at htk
    simp at htk

/-- **Operational obligation (Route A).** The standalone helper under
the composite's procs is safe with the closed-form post. Eventually
discharged by the Std.Do triple via the operational pipeline
(`denote_sound` + `helperProg_safe` + `SafeTp_procs_irrel_of_strict`),
mirroring `helper_safeTp` in `ExternalSolver`. -/
theorem helper_safeTp_sumSquares (Na : Nat) (Nb Nc : Int)
    (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp (parChecksumComposite Na Nb Nc)
        ⟨σ, [sumSquares_init n a]⟩ (sumSquares_post n [Val.int a]) := by
  intro σ
  have h_safe_strong :
      Machine.SafeTp (parChecksumComposite Na Nb Nc)
        ⟨σ, [sumSquares_init n a]⟩
        (fun v => v = Val.int (sumSquaresValue a n)) :=
    SafeTp_procs_irrel_of_strict
      (prog1 := sumSquaresHelperProg n) (prog2 := parChecksumComposite Na Nb Nc)
      (sumSquares_init_strictHelperThread n a)
      (sumSquaresHelperProg_safe n a σ)
  -- Weaken post: `v = Val.int (sumSquaresValue a n)` ⇒ `sumSquares_post n [Val.int a] v`.
  intro steps μ' htraj k t htk
  rcases h_safe_strong steps μ' htraj k t htk with ⟨v, htv, hφ⟩ | hred
  · left
    refine ⟨v, htv, ?_⟩
    intro hk
    exact ⟨a, rfl, hφ hk⟩
  · right; exact hred

/-- **Route A bridge specialized to `parChecksumComposite Na Nb Nc` /
`sumSquares`.** A one-line specialization of
`wp_callee_routeA_generic`. -/
theorem wp_sumSquares_callee_routeA
    [TpGpreS GF F] [InvGS_gen false GF]
    (Na : Nat) (Nb Nc : Int)
    (n : Nat) (a : Int) (x : Name) (cont : List Stmt) (env : Env)
    (Φ : Val → IProp GF) :
    (∀ v, iprop(⌜sumSquares_post n [Val.int a] v⌝ -∗
        wp (parChecksumComposite Na Nb Nc).procs (iprop(True : IProp GF)) ⊤
          (BodyTraj.postDoReturnThread ⟨x, cont, env⟩ [] v) Φ))
    ⊢ |={⊤}=> wp (parChecksumComposite Na Nb Nc).procs (iprop(True : IProp GF)) ⊤
        ⟨(sumSquares n).body, [], bindParams ["a"] [Val.int a],
         [⟨x, cont, env⟩], none⟩ Φ :=
  wp_callee_routeA_generic (GF := GF) (F := F)
    (parChecksumComposite Na Nb Nc)
    (sumSquares_init n a)
    (sumSquares_init_heapFree n a)
    (sumSquares_init_strictHelperThread n a)
    rfl
    (sumSquares_post n [Val.int a])
    (helper_safeTp_sumSquares Na Nb Nc n a)
    ⟨x, cont, env⟩
    Φ

/-! ### Worker spec

Each worker: load its helper via the bridge, then CAS-write into `s`.
Threaded against `sumInv`. -/

/-- Worker A: starting from `inv sumInv`, run `call sumSquares(Nb);
cas s 0 v; ret unit`. The helper returns `Val.int (midVal Na Nb)`, the
CAS either succeeds (LEFT disjunct, cell `↦ 0` → `↦ midVal`) or fails
(the cell was already advanced).

**Side conditions.** The CAS expected value `0` must be distinct from
the other two invariant disjuncts (`midVal Na Nb` and `topVal Na Nb Nc`),
otherwise the failure-branch case-splits collapse. -/
theorem workerA_spec
    [TpGpreS GF F] [InvGS_gen false GF]
    (Na : Nat) (Nb Nc : Int)
    (h_mid_ne_0 : midVal Na Nb ≠ 0)
    (h_top_ne_0 : topVal Na Nb Nc ≠ 0)
    (l : Loc) :
    inv (GF := GF) nroot (sumInv GF F Na Nb Nc l) ⊢
      wp (parChecksumComposite Na Nb Nc).procs (iprop(True : IProp GF)) ⊤
        ⟨(workerA Nb).body, [], bindParams ["s"] [Val.loc l], [], none⟩
        (fun _ => iprop(True : IProp GF)) := by
  iintro #HI
  unfold workerA
  iapply wp_seq
  iintro !>
  iapply wp_call (GF := GF) (F := F) (fork_post := iprop(True : IProp GF))
    _ "v" "sumSquares" [.val (.int Nb)] (sumSquares Na) [Val.int Nb]
    [Stmt.seq (.cas "p" (.var "s") (.val (.int 0)) (.var "v"))
              (.ret (.val .unit))]
    _ _ _
    (by show (parChecksumComposite Na Nb Nc).procs _ = _; rfl)
    (by agar_eval)
    rfl
  iintro !>
  iapply fupd_wp
  change _ ⊢ |={⊤}=> wp (parChecksumComposite Na Nb Nc).procs
      (iprop(True : IProp GF)) ⊤
    ⟨(sumSquares Na).body, [], bindParams ["a"] [Val.int Nb],
     [⟨"v", [Stmt.seq (.cas "p" (.var "s") (.val (.int 0)) (.var "v"))
                       (.ret (.val .unit))],
       bindParams ["s"] [Val.loc l]⟩],
     none⟩ _
  iintro #HI2
  iapply (wp_sumSquares_callee_routeA (GF := GF) (F := F) Na Nb Nc Na Nb "v"
    [Stmt.seq (.cas "p" (.var "s") (.val (.int 0)) (.var "v"))
              (.ret (.val .unit))]
    (bindParams ["s"] [Val.loc l]) _)
  iintro %v Hpv
  icases Hpv with %hpv
  obtain ⟨a, heq_args, hv⟩ := hpv
  have ha : a = Nb := by
    injection heq_args with h _
    injection h with h'
    exact h'.symm
  rw [ha] at hv
  clear ha heq_args
  subst hv
  show _ ⊢ wp _ _ _
    ⟨Stmt.seq (.cas "p" (.var "s") (.val (.int 0)) (.var "v"))
              (.ret (.val .unit)),
     [],
     (bindParams ["s"] [Val.loc l]).set "v" (Val.int (sumSquaresValue Nb Na)),
     [], none⟩ _
  iintro #HI3
  iapply wp_seq
  iintro !>
  iapply wp_cas_atomic (GF := GF) (F := F) (N := nroot)
    (P := sumInv GF F Na Nb Nc l)
    (vO := Val.int 0) (vN := Val.int (sumSquaresValue Nb Na))
    (Hsub := by
      rw [nclose_root]; exact (fun _ _ => CoPset.mem_full))
    (heL := by agar_eval) (heO := by agar_eval) (heN := by agar_eval)
    (heq := by decide)
    (hne_of_ne := val_beq_int_false 0)
  iframe HI3
  iintro HP
  ihave HP := BI.later_or.mp $$ HP
  icases HP with (>HC0 | HP1)
  · -- LEFT: cell ↦ 0. CAS succeeds (transition to MIDDLE).
    imodintro
    iexists (Val.int 0)
    isplitl [HC0]
    · iexact HC0
    isplitl []
    · iintro %_hv0 HC'
      imodintro
      isplitl [HC']
      · inext; iright; ileft; iexact HC'
      wp_pures
      iapply wp_ret_top _ _ _ (.unit) _ _ _ rfl
      ipure_intro; trivial
    · cas_dead
  · ihave HP1 := BI.later_or.mp $$ HP1
    icases HP1 with (>HCmid | >HCtop)
    · -- MIDDLE: cell ↦ midVal. CAS fails (midVal ≠ 0).
      imodintro
      iexists (Val.int (sumSquaresValue Nb Na))
      isplitl [HCmid]
      · iexact HCmid
      isplitr
      · iintro %heq_abs _
        exfalso
        have : (sumSquaresValue Nb Na : Int) = 0 := by
          have := Val.int.inj heq_abs
          exact this
        exact h_mid_ne_0 this
      · iintro %_hne HC'
        imodintro
        isplitl [HC']
        · inext; iright; ileft; iexact HC'
        wp_pures
        iapply wp_ret_top _ _ _ (.unit) _ _ _ rfl
        ipure_intro; trivial
    · -- RIGHT: cell ↦ topVal. CAS fails (topVal ≠ 0).
      imodintro
      iexists (Val.int (topVal Na Nb Nc))
      isplitl [HCtop]
      · iexact HCtop
      isplitr
      · iintro %heq_abs _
        exfalso
        have : (topVal Na Nb Nc : Int) = 0 := Val.int.inj heq_abs
        exact h_top_ne_0 this
      · iintro %_hne HC'
        imodintro
        isplitl [HC']
        · inext; iright; iright; iexact HC'
        wp_pures
        iapply wp_ret_top _ _ _ (.unit) _ _ _ rfl
        ipure_intro; trivial

/-- Worker B: starting from `inv sumInv`, run `call sumSquares(Nc);
cas s midVal topVal; ret unit`. The helper returns
`Val.int (sumSquaresValue Nc Na)`, the CAS either succeeds (MIDDLE
disjunct, cell `↦ midVal` → `↦ topVal`) or fails. Post: `True`.

**Side conditions.** The CAS expected value `midVal` must be distinct
from the other two invariant disjuncts (`0` and `topVal`). -/
theorem workerB_spec
    [TpGpreS GF F] [InvGS_gen false GF]
    (Na : Nat) (Nb Nc : Int)
    (h_mid_ne_0 : midVal Na Nb ≠ 0)
    (h_mid_ne_top : midVal Na Nb ≠ topVal Na Nb Nc)
    (l : Loc) :
    inv (GF := GF) nroot (sumInv GF F Na Nb Nc l) ⊢
      wp (parChecksumComposite Na Nb Nc).procs (iprop(True : IProp GF)) ⊤
        ⟨(workerB Na Nb Nc).body, [], bindParams ["s"] [Val.loc l], [], none⟩
        (fun _ => iprop(True : IProp GF)) := by
  iintro #HI
  unfold workerB
  iapply wp_seq
  iintro !>
  iapply wp_call (GF := GF) (F := F) (fork_post := iprop(True : IProp GF))
    _ "v" "sumSquares" [.val (.int Nc)] (sumSquares Na) [Val.int Nc]
    [Stmt.seq (.cas "p" (.var "s") (.val (.int (midVal Na Nb)))
                                   (.val (.int (topVal Na Nb Nc))))
              (.ret (.val .unit))]
    _ _ _
    (by show (parChecksumComposite Na Nb Nc).procs _ = _; rfl)
    (by agar_eval)
    rfl
  iintro !>
  iapply fupd_wp
  change _ ⊢ |={⊤}=> wp (parChecksumComposite Na Nb Nc).procs
      (iprop(True : IProp GF)) ⊤
    ⟨(sumSquares Na).body, [], bindParams ["a"] [Val.int Nc],
     [⟨"v", [Stmt.seq (.cas "p" (.var "s") (.val (.int (midVal Na Nb)))
                                            (.val (.int (topVal Na Nb Nc))))
                       (.ret (.val .unit))],
       bindParams ["s"] [Val.loc l]⟩],
     none⟩ _
  iintro #HI2
  iapply (wp_sumSquares_callee_routeA (GF := GF) (F := F) Na Nb Nc Na Nc "v"
    [Stmt.seq (.cas "p" (.var "s") (.val (.int (midVal Na Nb)))
                                   (.val (.int (topVal Na Nb Nc))))
              (.ret (.val .unit))]
    (bindParams ["s"] [Val.loc l]) _)
  iintro %v Hpv
  icases Hpv with %hpv
  obtain ⟨a, heq_args, hv⟩ := hpv
  have ha : a = Nc := by
    injection heq_args with h _
    injection h with h'
    exact h'.symm
  -- Substitute `a := Nc` (not the other way). Lean's `subst` is sensitive
  -- to which variable is eliminable; force the direction.
  rw [ha] at hv
  clear ha heq_args
  subst hv
  -- Unfold the post-bridge thread to its explicit form. Inline a local
  -- `have` for the target shape so `change` doesn't have to re-derive
  -- structural equality through the abbreviations.
  show _ ⊢ wp _ _ _
    ⟨Stmt.seq (.cas "p" (.var "s") (.val (.int (midVal Na Nb)))
                                   (.val (.int (topVal Na Nb Nc))))
              (.ret (.val .unit)),
     [],
     (bindParams ["s"] [Val.loc l]).set "v" (Val.int (sumSquaresValue Nc Na)),
     [], none⟩ _
  iintro #HI3
  iapply wp_seq
  iintro !>
  iapply wp_cas_atomic (GF := GF) (F := F) (N := nroot)
    (P := sumInv GF F Na Nb Nc l)
    (vO := Val.int (midVal Na Nb)) (vN := Val.int (topVal Na Nb Nc))
    (Hsub := by
      rw [nclose_root]; exact (fun _ _ => CoPset.mem_full))
    (heL := by agar_eval) (heO := by agar_eval) (heN := by agar_eval)
    (heq := val_beq_refl _)
    (hne_of_ne := val_beq_int_false (midVal Na Nb))
  iframe HI3
  iintro HP
  ihave HP := BI.later_or.mp $$ HP
  icases HP with (>HC0 | HP1)
  · -- LEFT: cell ↦ 0. CAS fails (0 ≠ midVal).
    imodintro
    iexists (Val.int 0)
    isplitl [HC0]
    · iexact HC0
    isplitr
    · iintro %heq_abs _
      exfalso
      have : (0 : Int) = midVal Na Nb := Val.int.inj heq_abs
      exact h_mid_ne_0 this.symm
    · iintro %_hne HC'
      imodintro
      isplitl [HC']
      · inext; ileft; iexact HC'
      wp_pures
      iapply wp_ret_top _ _ _ (.unit) _ _ _ rfl
      ipure_intro; trivial
  · ihave HP1 := BI.later_or.mp $$ HP1
    icases HP1 with (>HCmid | >HCtop)
    · -- MIDDLE: cell ↦ midVal. CAS succeeds (transition to RIGHT).
      imodintro
      iexists (Val.int (midVal Na Nb))
      isplitl [HCmid]
      · iexact HCmid
      isplitl []
      · iintro %_hvmid HC'
        imodintro
        isplitl [HC']
        · inext; iright; iright; iexact HC'
        wp_pures
        iapply wp_ret_top _ _ _ (.unit) _ _ _ rfl
        ipure_intro; trivial
      · cas_dead
    · -- RIGHT: cell ↦ topVal. CAS fails (topVal ≠ midVal).
      imodintro
      iexists (Val.int (topVal Na Nb Nc))
      isplitl [HCtop]
      · iexact HCtop
      isplitr
      · iintro %heq_abs _
        exfalso
        have : (topVal Na Nb Nc : Int) = midVal Na Nb := Val.int.inj heq_abs
        exact h_mid_ne_top this.symm
      · iintro %_hne HC'
        imodintro
        isplitl [HC']
        · inext; iright; iright; iexact HC'
        wp_pures
        iapply wp_ret_top _ _ _ (.unit) _ _ _ rfl
        ipure_intro; trivial

/-! ### Closed adequacy

The main theorem: `parChecksumComposite` returns exactly `Val.int 91`.
The proof shape mirrors `progReadback_closed` (alloc + invariant +
fork ×2 + spin-readback) but with two workers instead of one and the
spin-loop's `J` carrying the three-state observed-value tag. -/

theorem parChecksum_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    [TpGpreS GF F]
    (Na : Nat) (Nb Nc : Int)
    (h_mid_ne_0 : midVal Na Nb ≠ 0)
    (h_top_ne_0 : topVal Na Nb Nc ≠ 0)
    (h_mid_ne_top : midVal Na Nb ≠ topVal Na Nb Nc)
    :
    Machine.safe (parChecksumComposite Na Nb Nc)
      (· = Val.int (topVal Na Nb Nc)) := by
  refine wp_safe_bupd (GF := GF) (φ := fun v => v = Val.int (topVal Na Nb Nc))
    (parChecksumComposite Na Nb Nc) ?_
  intro _LC
  (heap_adequacy_intro; unfold Thread.initial parChecksumComposite)
  wp_pures
  wp_alloc_intro l HP
  wp_pures
  inv_alloc_with (sumInv GF F Na Nb Nc l) [HP] HI by
    inext; ileft; iexact HP
  -- Fork worker A.
  wp_fork_emp "workerA" [Expr.var "s"] (workerA Nb) [Val.loc _]
    [ags(
      fork workerB(s) ;
      done   := 0 ;
      result := 0 ;
      (while done = 0 do (
        v := load s ;
        if v = #(Expr.val (Val.int (topVal Na Nb Nc))) then
          (result := v ; done := 1) else skip
      )) ;
      return result
    )]
  isplitr
  · iintro !>
    change _ ⊢ wp (parChecksumComposite Na Nb Nc).procs
        (iprop(True : IProp GF)) ⊤
      ⟨(workerA Nb).body, [], bindParams ["s"] [Val.loc l], [], none⟩
      (fun _ => iprop(True : IProp GF))
    iintro #HIA
    iapply (workerA_spec (GF := GF) (F := F) Na Nb Nc h_mid_ne_0 h_top_ne_0 l)
    iexact HIA
  · iintro !>
    wp_pures
    wp_fork_emp "workerB" [Expr.var "s"] (workerB Na Nb Nc) [Val.loc _]
      [ags(
        done   := 0 ;
        result := 0 ;
        (while done = 0 do (
          v := load s ;
          if v = #(Expr.val (Val.int (topVal Na Nb Nc))) then
            (result := v ; done := 1) else skip
        )) ;
        return result
      )]
    isplitr
    · iintro !>
      change _ ⊢ wp (parChecksumComposite Na Nb Nc).procs
          (iprop(True : IProp GF)) ⊤
        ⟨(workerB Na Nb Nc).body, [], bindParams ["s"] [Val.loc l], [], none⟩
        (fun _ => iprop(True : IProp GF))
      iintro #HIB
      iapply (workerB_spec (GF := GF) (F := F) Na Nb Nc h_mid_ne_0
                h_mid_ne_top l)
      iexact HIB
    · iintro !>
      wp_pures_no_loop
      -- Spin loop J: (done, result) ∈ {(0,0), (1, topVal)}.
      iapply (wp_spin (GF := GF) _ _ _ _ _ _ _
        (J := fun env =>
          iprop(inv nroot (sumInv GF F Na Nb Nc l) ∗
            ⌜Expr.eval env (Expr.var "s") = some (.loc l) ∧
              ((env "done" = some (.int 0) ∧ env "result" = some (.int 0)) ∨
               (env "done" = some (.int 1) ∧
                env "result" = some (.int (topVal Na Nb Nc))))⌝)) _
        (HSpec := fun env => ?Hspec))
      case Hspec =>
        iintro ⟨HIH, ⟨#HI, HJ⟩⟩
        inext
        icases HJ with %hpure
        obtain ⟨hs, hdr⟩ := hpure
        rcases hdr with ⟨hdone, hresult⟩ | ⟨hdone, hresult⟩
        · iapply wp_ite_true (heval := by simp [agar_eval, hdone]; rfl)
          iintro !>
          wp_lstep
          wp_lstep
          iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
            (P := sumInv GF F Na Nb Nc l)
            (Hsub := by rw [nclose_root])
            (heL := hs)
          iframe HI
          iintro HP
          ihave HP := BI.later_or.mp $$ HP
          icases HP with (>HC0 | HP1)
          · -- cell ↦ 0: load returns 0, take else-branch (skip), keep J LEFT.
            imodintro
            iexists (Val.int 0)
            isplitl [HC0]
            · iexact HC0
            iintro HC0
            imodintro
            isplitl [HC0]
            · inext; ileft; iexact HC0
            wp_lstep
            have h0_ne_top : (Val.int 0 : Val) ≠ Val.int (topVal Na Nb Nc) :=
              fun heq => h_top_ne_0 (Val.int.inj heq).symm
            iapply wp_ite_false (heval := by
              simp [agar_eval, val_beq_int_false _ _ h0_ne_top])
            iintro !>
            wp_lstep
            ihave HIH := HIH $$ %(env.set "v" (Val.int 0))
            iapply HIH
            isplitl []
            · iexact HI
            ipure_intro
            refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
            · simpa [agar_eval] using hs
            · simpa [agar_eval] using hdone
            · simpa [agar_eval] using hresult
          · ihave HP1 := BI.later_or.mp $$ HP1
            icases HP1 with (>HCmid | >HCtop)
            · -- cell ↦ midVal: load returns midVal, else-branch, keep J LEFT.
              imodintro
              iexists (Val.int (midVal Na Nb))
              isplitl [HCmid]
              · iexact HCmid
              iintro HCmid
              imodintro
              isplitl [HCmid]
              · inext; iright; ileft; iexact HCmid
              wp_lstep
              have hmid_ne_top : (Val.int (midVal Na Nb) : Val) ≠
                  Val.int (topVal Na Nb Nc) :=
                fun heq => h_mid_ne_top (Val.int.inj heq)
              iapply wp_ite_false (heval := by
                simp [agar_eval, val_beq_int_false _ _ hmid_ne_top])
              iintro !>
              wp_lstep
              ihave HIH := HIH $$ %(env.set "v" (Val.int (midVal Na Nb)))
              iapply HIH
              isplitl []
              · iexact HI
              ipure_intro
              refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
              · simpa [agar_eval] using hs
              · simpa [agar_eval] using hdone
              · simpa [agar_eval] using hresult
            · -- cell ↦ topVal: load returns topVal, then-branch, J → RIGHT.
              imodintro
              iexists (Val.int (topVal Na Nb Nc))
              isplitl [HCtop]
              · iexact HCtop
              iintro HCtop
              imodintro
              isplitl [HCtop]
              · inext; iright; iright; iexact HCtop
              wp_lstep
              iapply wp_ite_true (heval := by
                simp [agar_eval, val_beq_refl])
              iintro !>
              wp_lstep
              iapply wp_assign (heval := by agar_eval)
              iintro !>
              wp_lstep
              iapply wp_assign (heval := by agar_eval)
              iintro !>
              wp_lstep
              ihave HIH := HIH $$ %(((env.set "v" (Val.int (topVal Na Nb Nc))).set
                  "result" (Val.int (topVal Na Nb Nc))).set "done" (Val.int 1))
              iapply HIH
              isplitl []
              · iexact HI
              ipure_intro
              refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
              · show Expr.eval _ (Expr.var "s") = _
                exact hs
              · rfl
              · rfl
        · -- RIGHT: guard false, exit, return result = topVal.
          iapply wp_ite_false (heval := by simp [agar_eval, hdone]; rfl)
          iintro !>
          wp_lstep
          iapply (wp_ret_top _ _ (Expr.var "result") (Val.int (topVal Na Nb Nc))
            [] env _ (heval := by simp [agar_eval, hresult]))
          ipure_intro; rfl
      · isplitl []
        · iexact HI
        ipure_intro
        refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩ <;> agar_eval

/-! ## Adequacy corollary

The headline statement an external consumer reads: *the composite
program, dispatching its pure helper through `Std.Do.Triple` and
running it under genuine Iris-style concurrent reasoning, is safe and
returns the specified value.* -/

/-- **End-to-end adequacy: parallel checksum returns 91.** The
original showcase instance at `(Na, Nb, Nc) = (3, 1, 4)`:
`sumSquaresValue 1 3 + sumSquaresValue 4 3 = 14 + 77 = 91`. Every
terminal configuration reachable from the initial machine state of
`parChecksumComposite 3 1 4` has main thread returning `Val.int 91`. -/
theorem parChecksum_returns_91
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    [TpGpreS GF F]
    :
    Machine.safe (parChecksumComposite 3 1 4) (· = (Val.int 91)) := by
  have h : topVal 3 1 4 = 91 := by decide
  have h_mid_ne_0 : midVal 3 1 ≠ 0 := by decide
  have h_top_ne_0 : topVal 3 1 4 ≠ 0 := by decide
  have h_mid_ne_top : midVal 3 1 ≠ topVal 3 1 4 := by decide
  have := parChecksum_closed (GF := GF) (F := F) 3 1 4
    h_mid_ne_0 h_top_ne_0 h_mid_ne_top
  rw [h] at this
  exact this

end Agar.Logic

/-! ## Fully closed adequacy: allocate the GFunctors concretely

The variants above (`parChecksum_closed`, `parChecksum_returns_91`) take
the `GFunctors` bundle as a typeclass parameter, leaving the actual
choice of resource algebras to the caller. This section discharges
those parameters by allocating a concrete six-slot bundle:

  - slot 0: `InvMapF`              (invariants — self-referential)
  - slot 1: `DisjointLeibnizSet CoPset`  (invariant mask "enabled")
  - slot 2: `DisjointLeibnizSet PosSet`  (invariant mask "disabled")
  - slot 3: `AuthURF (F := PNat) (constOF Credit)`  (later credits)
  - slot 4: `HeapF PNat`           (heap resource)
  - slot 5: `TpF PNat`             (thread-pool resource)

Slots 0–3 mirror `Iris/Examples/ClosedProofs.lean`; slots 4–5 add the
Agar-specific heap and thread-pool resources. -/

namespace Agar.ParChecksum.Closed
open Iris Iris.BI COFE HeapView Auth Std.LawfulSet Agar Agar.Logic

/-- Concrete `BundledGFunctors` for the parallel-checksum showcase. -/
noncomputable def GF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (F := PNat) (constOF Credit), by infer_instance⟩
  | 4 => ⟨HeapF PNat, by infer_instance⟩
  | 5 => ⟨TpF PNat, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS GF where
  inv := { τ := 0, transp := by unfold GF; rfl }
  enabled := { τ := 1, transp := by unfold GF; rfl }
  disabled := { τ := 2, transp := by unfold GF; rfl }

instance : LcGpreS GF where
  lc_elem := { τ := 3, transp := by unfold GF; rfl }

instance : InvGpreS GF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : Agar.Logic.AgarGpreS GF PNat where
  τ := 4
  transp := by unfold GF; rfl

instance : Agar.Logic.TpGpreS GF PNat where
  τ := 5
  transp := by unfold GF; rfl

/-- **Fully closed adequacy, quantified.** Parallel-checksum returns
the closed-form `Val.int (topVal Na Nb Nc)` for any well-formed
parameter triple `(Na, Nb, Nc)`, with the GFunctors bundle and fraction
algebra resolved internally — no typeclass parameters left for the
caller. -/
theorem parChecksum_closed_concrete
    (Na : Nat) (Nb Nc : Int)
    (h_mid_ne_0 : midVal Na Nb ≠ 0)
    (h_top_ne_0 : topVal Na Nb Nc ≠ 0)
    (h_mid_ne_top : midVal Na Nb ≠ topVal Na Nb Nc) :
    Machine.safe (parChecksumComposite Na Nb Nc)
      (· = Val.int (topVal Na Nb Nc)) :=
  Agar.Logic.parChecksum_closed (GF := GF) (F := PNat) Na Nb Nc
    h_mid_ne_0 h_top_ne_0 h_mid_ne_top

/-- **Fully closed adequacy.** Parallel-checksum returns `Val.int 91`,
with the GFunctors bundle and fraction algebra resolved internally — no
typeclass parameters left for the caller. -/
theorem parChecksum_returns_91_closed :
    Machine.safe (parChecksumComposite 3 1 4) (· = (Val.int 91)) :=
  Agar.Logic.parChecksum_returns_91 (GF := GF) (F := PNat)

end Agar.ParChecksum.Closed

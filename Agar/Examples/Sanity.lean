module

public import Iris.Std.CoPset
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Agar.Lang.Notation
public import Agar.Iris.Wp
public import Agar.Iris.Heap
public import Agar.Iris.Rules
public import Agar.Iris.Tactics

@[expose] public section

/-! # Sanity-check examples for the WP rules

These small examples drive composition of the rules end-to-end to
verify the design works as a unit. They are stated as `example`s so
they have no name-pollution effect on the library API.

The post-conditions are now over `Val`: a fall-through thread shows up
to `Φ` as `Val.unit`, and a thread that hit a top-level `return e` shows
up as `Φ v`.
-/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- A skip with a pending `cont = [.skip]` reduces to the post-condition
in two steps. The thread falls through, so its value is `Val.unit`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env)
    (Φ : Val → IProp GF) :
    ▷ Φ .unit ⊢ wp procs fork_post E ⟨.skip, [.skip], env, [], none⟩ Φ := by
  istart
  iintro Hpre
  iapply wp_skip_cons
  iintro !>
  iapply wp_value _ _ _ .unit _ rfl
  iexact Hpre

/-- `assign x e; skip` falls through with `Val.unit`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (e : Expr) (v : Val) (env : Env)
    (Φ : Val → IProp GF) (heval : Expr.eval env e = some v) :
    ▷ ▷ Φ .unit ⊢ wp procs fork_post E ⟨.assign x e, [.skip], env, [], none⟩ Φ := by
  istart
  iintro Hpre
  iapply wp_assign (heval := heval)
  iintro !>
  iapply wp_skip_cons
  iintro !>
  iapply wp_value _ _ _ .unit _ rfl
  iexact Hpre

/-- `return e` at the top: the thread observes the returned value. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (e : Expr) (v : Val) (cont : List Stmt) (env : Env)
    (Φ : Val → IProp GF) (heval : Expr.eval env e = some v) :
    Φ v ⊢ wp procs fork_post E ⟨.ret e, cont, env, [], none⟩ Φ :=
  wp_ret_top procs fork_post e v cont env Φ heval

/-- Load returns the cell's value, then the thread terminates with
`Val.unit` (it fell through after the load). -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (e : Expr) (l : Loc) (v : Val) (env : Env)
    (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some (.loc l)) :
    (points_to (GF := GF) (F := F) l v ∗ ▷ (points_to l v -∗ Φ .unit))
    ⊢ wp procs fork_post E ⟨.load x e, [], env, [], none⟩ Φ := by
  istart
  iintro ⟨HP, HK⟩
  wp_load_direct HP heval
  iapply wp_value _ _ _ .unit _ rfl
  iapply HK $$ HP

/-- Post-condition strengthening: `wp_mono` weakens the post, here from
"the points-to is still owned" to `True`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (e : Expr) (l : Loc) (v : Val) (env : Env)
    (Φ : Val → IProp GF)
    (heval : Expr.eval env e = some (.loc l))
    (hweak : ∀ w, Φ w ⊢ (iprop(True) : IProp GF)) :
    (points_to (GF := GF) (F := F) l v ∗ ▷ (points_to l v -∗ Φ .unit))
    ⊢ wp procs fork_post E ⟨.load x e, [], env, [], none⟩
        (fun (_ : Val) => (iprop(True) : IProp GF)) := by
  refine .trans ?_ (wp_mono procs fork_post
    (Φ := Φ) (Ψ := fun (_ : Val) => iprop(True))
    hweak _)
  istart
  iintro ⟨HP, HK⟩
  wp_load_direct HP heval
  iapply wp_value _ _ _ .unit _ rfl
  iapply HK $$ HP

/-! ## Examples with return values

These exercise the refactor: the post-condition observes the value
flowing out of a top-level `return e`. -/

/-- `return 7` returns `Val.int 7`; the post-condition is satisfied with
that exact value. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.ret (.val (.int 7)), [], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) :=
  (BI.pure_intro (φ := (.int 7 : Val) = .int 7) rfl).trans
    (wp_ret_top procs fork_post (.val (.int 7)) (.int 7) [] env
      (fun v => iprop(⌜v = .int 7⌝)) rfl)

/-- `x := 7; return x` returns `Val.int 7` — composes `wp_assign`,
`wp_skip_cons`, and `wp_ret_top`, with the value plumbed through the
local environment and observed by the post. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.assign "x" (.val (.int 7)), [.ret (.var "x")], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  iapply wp_assign (heval := rfl)
  iintro !>
  iapply wp_skip_cons
  iintro !>
  -- The `ret` evaluates `.var "x"` in `env.set "x" (.int 7)`, yielding 7.
  iapply wp_ret_top _ _ _ (.int 7) [] _ _
    (show Expr.eval (env.set "x" (.int 7)) (.var "x") = some (.int 7)
      from by simp [agar_eval])
  ipure_intro
  rfl

/-! ## Allocation

`wp_alloc` consumes the post-condition's `∀ l, l ↦ v -∗ wp …` and
produces a heap cell. The example below allocates, then ignores the
fresh location, terminating with `Val.unit`. -/

example (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (env : Env)
    (Φ : Val → IProp GF) :
    (▷ ∀ (l : Loc), points_to (GF := GF) (F := F) l (.int 7) -∗ Φ .unit)
    ⊢ wp procs fork_post E
        ⟨.alloc x (.val (.int 7)), [], env, [], none⟩ Φ := by
  istart
  iintro HK
  iapply wp_alloc _ _ _ _ _ _ _ _ _ (rfl :
    Expr.eval env (.val (.int 7)) = some (.int 7))
  iintro !> %l HP
  iapply wp_value _ _ _ .unit _ rfl
  iapply HK $$ %l HP

/-- Allocate-then-free returning unit. Threads the points-to through
`wp_alloc` and back into `wp_free`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.alloc x (.val (.int 0)), [.free (.var x)], env, [], none⟩
        (fun (_ : Val) => (iprop(True) : IProp GF)) := by
  istart
  iapply wp_alloc _ _ _ _ _ _ _ _ _ (rfl :
    Expr.eval env (.val (.int 0)) = some (.int 0))
  iintro !> %l HP
  iapply wp_skip_cons
  iintro !>
  iapply wp_free _ _ _ _ _ _ _ _ _ (show
    Expr.eval (env.set x (.loc l)) (.var x) = some (.loc l)
    from by simp [agar_eval])
  iframe HP
  iintro !>
  iapply wp_value _ _ _ .unit _ rfl
  ipure_intro; trivial

/-! ## Invariants

These examples exercise the fancy-update / invariant machinery now that
the WP is mask-parameterised. -/

/-- A `points_to` can be turned into a (persistent) `inv` at the value
point. We finish on `skip` with `Val.unit`, and the post is the
freshly-allocated invariant `inv N (l ↦ v)`. The allocation lives
inside the value-branch fupd via `wp_value_fupd`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env)
    (l : Loc) (v : Val) (N : Namespace) :
    points_to (GF := GF) (F := F) l v ⊢
      wp procs fork_post E ⟨.skip, [], env, [], none⟩
        (fun _ => inv N (points_to l v)) := by
  istart
  iintro HP
  iapply wp_value_fupd _ _ _ .unit _ rfl
  iapply inv_alloc N E (points_to l v)
  iintro !>
  iexact HP

/-- An already-owned `inv N P` is preserved through any pure step (here
`skip`). `inv` is persistent (it lives under `□`), so we can introduce
it intuitionistically with `#` and reuse it at the value point. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env)
    (N : Namespace) (P : IProp GF) :
    inv N P ⊢
      wp procs fork_post E ⟨.skip, [.skip], env, [], none⟩
        (fun _ => inv N P) := by
  istart
  iintro #HI
  iapply wp_skip_cons
  iintro !>
  iapply wp_value _ _ _ .unit _ rfl
  iexact HI

/-! ### Atomic rules opening an invariant

`wp_load_inv`, `wp_store_inv`, `wp_cas_inv` open `inv N (∃ v, l ↦ v)`
across one atomic heap operation. These examples drive them
end-to-end. -/

/-- Read a value through an inv: open inv, read, restore inv. The thread
falls through to `Val.unit`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (x : Name) (l : Loc) (env : Env)
    (Hsub : ↑N ⊆ E) :
    inv N (iprop(∃ v : Val, points_to (GF := GF) (F := F) l v))
    ⊢ wp procs fork_post E
        ⟨.load x (.val (.loc l)), [], env, [], none⟩
        (fun _ : Val => (iprop(True) : IProp GF)) := by
  istart
  iintro #HI
  iapply wp_load_inv _ _ _ _ _ _ _ _ _ _ Hsub (rfl :
    Expr.eval env (.val (.loc l)) = some (.loc l))
  iframe HI
  iintro !> %v HP
  iframe HP
  iapply wp_value _ _ _ .unit _ rfl
  ipure_intro; trivial

/-- Store a constant through an inv. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (N : Namespace) (l : Loc) (env : Env)
    (Hsub : ↑N ⊆ E) :
    inv N (iprop(∃ v : Val, points_to (GF := GF) (F := F) l v))
    ⊢ wp procs fork_post E
        ⟨.store (.val (.loc l)) (.val (.int 42)), [], env, [], none⟩
        (fun _ : Val => (iprop(True) : IProp GF)) := by
  istart
  iintro #HI
  iapply wp_store_inv _ _ _ _ _ _ _ _ _ _ _ Hsub
    (rfl : Expr.eval env (.val (.loc l)) = some (.loc l))
    (rfl : Expr.eval env (.val (.int 42)) = some (.int 42))
  iframe HI
  iintro !>
  iapply wp_value _ _ _ .unit _ rfl
  ipure_intro; trivial

/-! ## `wp_step` tactic suite

These reprove earlier sanity examples in a fraction of the lines. -/

/-- Compare to the `skip; skip` example above: `wp_step` picks
`wp_skip_cons` automatically. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env)
    (Φ : Val → IProp GF) :
    ▷ Φ .unit ⊢ wp procs fork_post E ⟨.skip, [.skip], env, [], none⟩ Φ := by
  istart
  iintro Hpre
  wp_step
  iintro !>
  wp_done
  iexact Hpre

/-- `assign x e; skip` falls through; `wp_step` discharges both the
assign (with its eval side condition via `agar_eval`) and the skip. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.assign "x" (.val (.int 7)), [.ret (.var "x")], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  wp_step
  iintro !>
  wp_step
  iintro !>
  wp_step
  ipure_intro; rfl

/-- `ite true` with a constant guard: `wp_step` solves the guard by
`rfl` and picks `wp_ite_true`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env)
    (Φ : Val → IProp GF) :
    ▷ Φ .unit ⊢ wp procs fork_post E
      ⟨.ite (.val (.bool true)) .skip .skip, [], env, [], none⟩ Φ := by
  istart
  iintro Hpre
  wp_step
  iintro !>
  wp_done
  iexact Hpre

/-- Heap step via `wp_load HP`: matches `points_to` from context. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (x : Name) (l : Loc) (v : Val) (env : Env)
    (Φ : Val → IProp GF) :
    (points_to (GF := GF) (F := F) l v ∗ ▷ (points_to l v -∗ Φ .unit))
    ⊢ wp procs fork_post E ⟨.load x (.val (.loc l)), [], env, [], none⟩ Φ := by
  istart
  iintro ⟨HP, HK⟩
  wp_load HP
  iintro !>
  iintro HP
  wp_done
  iapply HK $$ HP

/-- `wp_cas_succ HP heq`: CAS on `l ↦ vO` with expected `vO` and new `vN`
succeeds; the cell becomes `l ↦ vN` and the local `x` is bound to `vO`.
The BEq reflexivity `(vO == vO) = true` is supplied as `heq` (the
derived `BEq Val` is opaque outside `Syntax.lean`). -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (l : Loc) (vO vN : Val) (env : Env) (Φ : Val → IProp GF)
    (heq : (vO == vO) = true) :
    (points_to (GF := GF) (F := F) l vO ∗
      ▷ (points_to l vN -∗ Φ .unit))
    ⊢ wp procs fork_post E
        ⟨.cas "x" (.val (.loc l)) (.val vO) (.val vN),
          [], env, [], none⟩ Φ := by
  istart
  iintro ⟨HP, HK⟩
  wp_cas_succ HP heq
  iintro !> HP
  wp_done
  iapply HK $$ HP

/-- `wp_cas_fail HP hne`: CAS on `l ↦ cur` with expected `vO ≠ cur`
fails; the cell stays `l ↦ cur` and the local `x` is bound to `cur`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF)
    (l : Loc) (cur vO vN : Val) (env : Env) (Φ : Val → IProp GF)
    (hne : (cur == vO) = false) :
    (points_to (GF := GF) (F := F) l cur ∗
      ▷ (points_to l cur -∗ Φ .unit))
    ⊢ wp procs fork_post E
        ⟨.cas "x" (.val (.loc l)) (.val vO) (.val vN),
          [], env, [], none⟩ Φ := by
  istart
  iintro ⟨HP, HK⟩
  wp_cas_fail HP hne
  iintro !> HP
  wp_done
  iapply HK $$ HP

/-! ## Procedure call / fork via `wp_call` / `wp_fork`

A tiny inline program: `procRet7` returns `7`; `procSkip` falls through. -/

private abbrev procRet7 : Proc where
  params := []
  body := .ret (.val (.int 7))

private abbrev procSkip : Proc where
  params := []
  body := .skip

private abbrev procsCF : Name → Option Proc
  | "ret7" => some procRet7
  | "sk"   => some procSkip
  | _      => none

/-- `r := call ret7()` followed by `return r`: `wp_call` jumps into the
body, `wp_ret_pop_cons` returns into the caller binding `r := 7`, and
the final `return r` is observed by the post. -/
example (fork_post : IProp GF) (env : Env) :
    ⊢ wp procsCF fork_post E
        ⟨.call "r" "ret7" [], [.ret (.var "r")], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  wp_call
  iintro !>
  iapply wp_ret_pop_cons _ _ _ (.int 7) _ _ _ _ _ _ _ _ rfl
  iintro !>
  iapply wp_ret_top _ _ _ (.int 7) _ _ _
    (show Expr.eval (env.set "r" (.int 7)) (.var "r") = some (.int 7)
      from by simp [agar_eval])
  ipure_intro; rfl

/-- `fork sk()` leaves two WPs: the parent's `skip` continuation and the
forked thread running `procSkip`. Both finish at `Val.unit` / `fork_post`. -/
example (env : Env) (Φ : Val → IProp GF) :
    (▷ Φ .unit) ∗ (▷ (iprop(True) : IProp GF))
    ⊢ wp procsCF iprop(True) E
        ⟨.fork "sk" [], [], env, [], none⟩ Φ := by
  istart
  iintro ⟨HK, HF⟩
  wp_fork
  isplitl [HF]
  · iintro !>
    iapply wp_value _ _ _ .unit _ rfl
    iexact HF
  · iintro !>
    iapply wp_value _ _ _ .unit _ rfl
    iexact HK

/-- Same call as the first call-test, but driven entirely through
`wp_step` — which dispatches `wp_call` automatically. -/
example (fork_post : IProp GF) (env : Env) :
    ⊢ wp procsCF fork_post E
        ⟨.call "r" "ret7" [], [.ret (.var "r")], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  wp_step
  iintro !>
  wp_step
  iintro !>
  wp_step
  ipure_intro; rfl

/-! ## `wp_call <ident>`: step into the named callee body -/

private def addProc : Proc where
  params := ["a", "b"]
  body   := ags( return a + b )

private abbrev procsAdd : Name → Option Proc
  | "addProc" => some addProc
  | _         => none

/-- `wp_call addProc` discharges the call and lands us at the
start of `addProc`'s body (here: `return a + b`), ready for further
reasoning. From there `wp_steps; itrivial` drives the body to the
final value. -/
example (fork_post : IProp GF) (env : Env) :
    ⊢ wp procsAdd fork_post E
        ⟨.call "r" "addProc" [.val (.int 3), .val (.int 4)],
          [.ret (.var "r")], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  wp_call addProc
  -- Goal: head is `addProc`'s body `return (a + b)` under the bound env
  -- `a ↦ 3, b ↦ 4`. Drive home.
  wp_steps
  itrivial

/-! ## New tactics: `wp_steps` later-strip, `wp_done` for return,
`wp_alloc_intro`. -/

/-- `wp_steps` chains pure steps stripping intermediate `▷`s. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.assign "x" (.val (.int 7)), [.ret (.var "x")], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  wp_steps
  ipure_intro; rfl

/-- `wp_done` closes a `return e` goal via `wp_ret_top`. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.ret (.val (.int 7)), [], env, [], none⟩
        (fun v => (iprop(⌜v = .int 7⌝) : IProp GF)) := by
  istart
  wp_done

/-- `wp_done` also closes an `emp`-post terminal thread (the case that
arises with `fork_post := emp` on a forked value-thread). -/
example (procs : Name → Option Proc) (env : Env) :
    ⊢ wp procs (iprop(emp : IProp GF)) E
        ⟨.skip, [], env, [], none⟩
        (fun (_ : Val) => (iprop(emp : IProp GF))) := by
  istart
  wp_done

/-- `wp_alloc_intro HP` introduces the fresh location `l` and points-to
`HP` in one step. -/
example (procs : Name → Option Proc) (fork_post : IProp GF) (env : Env) :
    ⊢ wp procs fork_post E
        ⟨.alloc "x" (.val (.int 0)), [.free (.var "x")], env, [], none⟩
        (fun (_ : Val) => (iprop(True) : IProp GF)) := by
  istart
  wp_alloc_intro HP
  iapply wp_skip_cons
  iintro !>
  iapply wp_free _ _ _ _ _ _ _ _ _ (show
    Expr.eval (env.set "x" (.loc l)) (.var "x") = some (.loc l)
    from by simp [agar_eval])
  iframe HP
  iintro !>
  wp_done

/-! ## Sanity tests for `iframe` / `itrivial`

These pin the basic API of the local proof-mode helpers added in
`Tactics.lean`. They are intentionally trivial — they fire the macros
on a goal small enough that the entire proof is one line. -/

example (P Q : IProp GF) : P ∗ Q ⊢ P ∗ Q := by
  istart; iintro ⟨HP, HQ⟩
  iframe HP; iassumption

example (P Q R : IProp GF) : P ∗ Q ∗ R ⊢ P ∗ Q ∗ R := by
  istart; iintro ⟨HP, HQ, HR⟩
  iframe HP HQ; iassumption

example (P : IProp GF) : P ⊢ P := by
  istart; iintro HP; itrivial

example : ⊢ (emp : IProp GF) := by
  istart; itrivial

example : ⊢ (⌜(1 : Nat) = 1⌝ : IProp GF) := by
  istart; itrivial

end Agar.Logic

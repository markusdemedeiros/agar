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

Producer stores `42` into a shared cell; main spin-reads until it
observes the write, then `return result`. Adequacy at `Val.int 42`.

The bounded invariant `∃ v, flag ↦ v ∗ ⌜v = 0 ∨ v = 42⌝` pins the cell's
abstract state to two values; the spin loop's `J` carries the matching
`(done, result) ∈ {(0,0), (1,42)}` correlation so guard-false exit
lands in `result = 42`. (Cf. `progCounterCas`: same spin-readback shape
applied to a disjunctive CAS-counter invariant.) -/

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
    :
    Machine.safe progReadback (· = (Val.int 42)) := by
  adequacy_with_heap_intro progReadback (Val.int 42)
  wp_pures
  wp_alloc_intro l HP
  wp_pures
  inv_alloc_with (flagInv GF F l) [HP] HI by
    inext; iexists (Val.int 0); isplitl [HP]
    · iexact HP
    · ipure_intro; left; rfl
  wp_fork_emp "readbackProducerProc" [Expr.var "flag"] readbackProducerProc
    [Val.loc _]
    [ags(
      done   := 0 ;
      result := 0 ;
      (while done = 0 do (
        v := load flag ;
        if v = 0 then skip else (result := v ; done := 1)
      )) ;
      return result
    )]
  isplitr
  · -- Producer: store flag 42, transitioning the cell from 0 to 42.
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
    iintro HP
    imodintro
    isplitl [HP]
    · inext; iexists (Val.int 42); isplitl [HP]
      · iexact HP
      · ipure_intro; right; rfl
    wp_done
  · iintro !>
    wp_pures_no_loop
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
      rcases hdr with ⟨hdone, hresult⟩ | ⟨hdone, hresult⟩
      · -- LEFT (unwritten): run the body, atomic-load, branch on vcur ∈ {0, 42}.
        iapply wp_ite_true (heval := by simp [agar_eval, hdone]; rfl)
        iintro !>
        wp_lstep
        wp_lstep
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
        wp_lstep
        rcases hpcur with h0 | h42
        · -- vcur = 0: register still unwritten, keep `J` in LEFT.
          subst h0
          iapply wp_ite_true (heval := by agar_eval)
          iintro !>
          wp_lstep
          ihave HIH := HIH $$ %(env.set "v" (Val.int 0))
          iapply HIH
          isplitl []
          · iexact HI
          ipure_intro
          refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
          · simpa [agar_eval] using hflag
          · simpa [agar_eval] using hdone
          · simpa [agar_eval] using hresult
        · -- vcur = 42: producer observed → run `result := v ; done := 1`,
          -- transition `J` LEFT → RIGHT.
          subst h42
          iapply wp_ite_false (heval := by agar_eval)
          iintro !>
          wp_lstep
          iapply wp_assign (heval := by agar_eval)
          iintro !>
          wp_lstep
          iapply wp_assign (heval := by agar_eval)
          iintro !>
          wp_lstep
          ihave HIH := HIH $$ %(((env.set "v" (Val.int 42)).set "result"
              (Val.int 42)).set "done" (Val.int 1))
          iapply HIH
          isplitl []
          · iexact HI
          ipure_intro
          refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
          · show Expr.eval _ (Expr.var "flag") = _
            exact hflag
          · rfl
          · rfl
      · -- RIGHT (observed): guard is false, exit loop, return `result = 42`.
        iapply wp_ite_false (heval := by simp [agar_eval, hdone]; rfl)
        iintro !>
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "result") (Val.int 42) [] env _
          (heval := by simp [agar_eval, hresult]))
        ipure_intro; rfl
    · -- Initial `J` at loop entry: LEFT disjunct (unwritten).
      isplitl []
      · iexact HI
      ipure_intro
      refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩ <;> agar_eval

/-! ## `progReadbackRace` — predicate-form adequacy: `result ∈ {0, 42}`

Sibling program that drops the spin-readback. Main forks the producer
and reads the flag exactly once. The observed value depends on whether
the producer's `store flag 42` has fired yet, so the result is a *set*
`{0, 42}`. This is what `Machine.safe`-with-predicate captures that
`Machine.safe`-with-equality cannot — a postcondition that ranges over a property
rather than pinning to a single value. -/

def progReadbackRace : Program where
  procs := fun n =>
    if n = "readbackProducerProc" then some readbackProducerProc else none
  main  := ags(
    flag := alloc 0 ;
    fork readbackProducerProc(flag) ;
    v := load flag ;
    return v
  )

theorem progReadbackRace_closedP
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progReadbackRace
      (fun v => v = Val.int 0 ∨ v = Val.int 42) := by
  adequacy_with_heap_intro_P progReadbackRace
    (fun v => v = Val.int 0 ∨ v = Val.int 42)
  wp_pures
  wp_alloc_intro l HP
  wp_pures
  inv_alloc_with (flagInv GF F l) [HP] HI by
    inext; iexists (Val.int 0); isplitl [HP]
    · iexact HP
    · ipure_intro; left; rfl
  wp_fork_emp "readbackProducerProc" [Expr.var "flag"] readbackProducerProc
    [Val.loc _]
    [ags(v := load flag ; return v)]
  isplitr
  · iintro !>
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
    iintro HP
    imodintro
    isplitl [HP]
    · inext; iexists (Val.int 42); isplitl [HP]
      · iexact HP
      · ipure_intro; right; rfl
    wp_done
  · iintro !>
    wp_pures
    iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
      (P := flagInv GF F l)
      (Hsub := by rw [nclose_root])
      (heL := by agar_eval)
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
    wp_lstep
    iapply (wp_ret_top _ _ (Expr.var "v") vcur [] _ _
      (heval := by agar_eval))
    ipure_intro; exact hpcur

end Agar.Logic

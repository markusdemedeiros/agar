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
public import Agar.Iris.TacticsAtomic
public import Agar.Iris.WpSpin
public import Agar.Iris.Algebra.CounterRA

@[expose] public section

/-! # `progCounterCas` — CAS-based shared counter, observed by main

Two threads bump a shared counter via a single inline `cas c 0 1`; main
then spin-reads the counter and returns the observed value. The
disjunctive invariant `counterInv` bundles the heap cell with both
halves of an `Auth Nat` ghost (LEFT `= 0`, RIGHT `= 1`); the CAS-winner
runs `counter_increment` through the success wand while the loser
re-establishes RIGHT unchanged. Adequacy at `Val.int 1` — functional
correctness: every terminating main thread observes the bumped value. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet
open CMRA UCMRA Auth CommMonoidLike

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## The program -/

/-- The CAS-bump worker procedure: a single inline CAS attempt to bump
the shared counter from `0` to `1`. -/
def casBumpProc : Proc where
  params := ["c"]
  body   := ags( prev := cas c 0 1 )

/-- The full program: allocate the shared counter, fork two contending
workers, spin-read until the counter is non-zero, return the value. -/
def progCounterCas : Program where
  procs := fun n => if n = "casBumpProc" then some casBumpProc else none
  main  := ags(
    c      := alloc 0 ;
    fork casBumpProc(c) ;
    fork casBumpProc(c) ;
    done   := 0 ;
    result := 0 ;
    (while done = 0 do (
      v := load c ;
      if v = 0 then skip else (result := v ; done := 1)
    )) ;
    return result
  )

/-- The invariant body: a two-state disjunction tying the heap value
to a matching `(counter_auth γ, counter_frag γ)` pair. -/
private abbrev counterInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    [CounterGpreS GF] (cLoc : Loc) (γ : GName) : IProp GF :=
  iprop(
    (points_to (GF := GF) (F := F) cLoc (Val.int 0) ∗
        counter_auth (GF := GF) γ 0 ∗
        counter_frag (GF := GF) γ 0)
      ∨ (points_to (GF := GF) (F := F) cLoc (Val.int 1) ∗
          counter_auth (GF := GF) γ 1 ∗
          counter_frag (GF := GF) γ 1))

/-! ## Worker thread spec (single CAS under `counterInv`) -/

private theorem casBumpProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    [CounterGpreS GF] {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (cLoc : Loc) (γ : GName) :
    iprop(inv (GF := GF) nroot (counterInv GF F cLoc γ)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨casBumpProc.body, [],
          bindParams casBumpProc.params [Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold casBumpProc
  wp_cas_atomic_split HI
    (counterInv GF F cLoc γ) (Val.int 0) (Val.int 1)
    (val_beq_int_false 0)
    with (⟨>HC, >Hauth, >Hfrag⟩ | ⟨>HC, >Hauth, >Hfrag⟩)
  · -- Open LEFT (c↦0, auth=frag=0); CAS succeeds, ghost step (0,0) ⤳ (1,1).
    imodintro
    iexists (Val.int 0)
    iframe HC
    isplitl [Hauth Hfrag]
    · iintro %_hv0 HC'
      imod (counter_increment (GF := GF) γ 0 0) $$ [Hauth Hfrag]
            with ⟨Hauth, Hfrag⟩
      · isplitl [Hauth] <;> iassumption
      imodintro
      isplitl [HC' Hauth Hfrag]
      · inext; iright; iframe HC'; iframe Hauth; iexact Hfrag
      wp_done
    · cas_dead
  · -- Open RIGHT (c↦1); CAS fails, re-close RIGHT with same witnesses.
    imodintro
    iexists (Val.int 1)
    iframe HC
    isplitr
    · cas_dead
    · iintro %_hne HC'
      imodintro
      isplitl [HC' Hauth Hfrag]
      · inext; iright; iframe HC'; iframe Hauth; iexact Hfrag
      wp_done

theorem progCounterCas_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [CounterGpreS GF]
    :
    Machine.safe progCounterCas (· = (Val.int 1)) := by
  adequacy_with_heap_intro progCounterCas (Val.int 1)
  wp_pures
  wp_alloc_intro cLoc' HPC
  wp_pures
  iapply fupd_wp
  imod (counter_alloc (GF := GF)) with ⟨%γ, Hauth, Hfrag⟩
  imodintro
  inv_alloc_with (counterInv GF F cLoc' γ) [HPC Hauth Hfrag] HI by
    inext; ileft; iframe HPC; iframe Hauth; iexact Hfrag
  wp_fork_emp "casBumpProc" [Expr.var "c"] casBumpProc [Val.loc _]
    [ags(
      fork casBumpProc(c) ;
      done   := 0 ;
      result := 0 ;
      (while done = 0 do (
        v := load c ;
        if v = 0 then skip else (result := v ; done := 1)
      )) ;
      return result
    )]
  isplitr
  · iintro !>
    iapply casBumpProc_wp_body
    iexact HI
  · iintro !>
    wp_pures
    wp_fork_emp "casBumpProc" [Expr.var "c"] casBumpProc [Val.loc _]
      [ags(
        done   := 0 ;
        result := 0 ;
        (while done = 0 do (
          v := load c ;
          if v = 0 then skip else (result := v ; done := 1)
        )) ;
        return result
      )]
    isplitr
    · iintro !>
      iapply casBumpProc_wp_body
      iexact HI
    · iintro !>
      wp_pures_no_loop
      iapply (wp_spin (GF := GF) _ _ _ _ _ _ _
        (J := fun env =>
          iprop(inv nroot (counterInv GF F cLoc' γ) ∗
            ⌜Expr.eval env (Expr.var "c") = some (.loc cLoc') ∧
              ((env "done" = some (.int 0) ∧ env "result" = some (.int 0)) ∨
               (env "done" = some (.int 1) ∧ env "result" = some (.int 1)))⌝)) _
        (HSpec := fun env => ?Hspec))
      case Hspec =>
        iintro ⟨HIH, ⟨#HI, HJ⟩⟩
        inext
        icases HJ with %hpure
        obtain ⟨hcLoc, hdr⟩ := hpure
        rcases hdr with ⟨hdone, hresult⟩ | ⟨hdone, hresult⟩
        · -- LEFT (unobserved): guard true, run body, load c, branch on c ∈ {0, 1}.
          iapply wp_ite_true (heval := by simp [agar_eval, hdone]; rfl)
          iintro !>
          wp_lstep
          wp_lstep
          iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
            (P := counterInv GF F cLoc' γ)
            (Hsub := by rw [nclose_root])
            (heL := hcLoc)
          iframe HI
          iintro HP
          ihave HP := BI.later_or.mp $$ HP
          icases HP with (⟨>HC, >Hauth, >Hfrag⟩ | ⟨>HC, >Hauth, >Hfrag⟩)
          · -- c ↦ 0: load returns 0, take then-branch (skip), keep J in LEFT.
            imodintro
            iexists (Val.int 0)
            isplitl [HC]
            · iexact HC
            iintro HC
            imodintro
            isplitl [HC Hauth Hfrag]
            · inext; ileft; iframe HC; iframe Hauth; iexact Hfrag
            wp_lstep
            iapply wp_ite_true (heval := by agar_eval)
            iintro !>
            wp_lstep
            ihave HIH := HIH $$ %(env.set "v" (Val.int 0))
            iapply HIH
            isplitl []
            · iexact HI
            ipure_intro
            refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
            · simpa [agar_eval] using hcLoc
            · simpa [agar_eval] using hdone
            · simpa [agar_eval] using hresult
          · -- c ↦ 1: load returns 1, take else-branch, transition J LEFT → RIGHT.
            imodintro
            iexists (Val.int 1)
            isplitl [HC]
            · iexact HC
            iintro HC
            imodintro
            isplitl [HC Hauth Hfrag]
            · inext; iright; iframe HC; iframe Hauth; iexact Hfrag
            wp_lstep
            iapply wp_ite_false (heval := by agar_eval)
            iintro !>
            wp_lstep
            iapply wp_assign (heval := by agar_eval)
            iintro !>
            wp_lstep
            iapply wp_assign (heval := by agar_eval)
            iintro !>
            wp_lstep
            ihave HIH := HIH $$ %(((env.set "v" (Val.int 1)).set "result"
                (Val.int 1)).set "done" (Val.int 1))
            iapply HIH
            isplitl []
            · iexact HI
            ipure_intro
            refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
            · show Expr.eval _ (Expr.var "c") = _
              exact hcLoc
            · rfl
            · rfl
        · -- RIGHT (observed): guard false, exit loop, return `result = 1`.
          iapply wp_ite_false (heval := by simp [agar_eval, hdone]; rfl)
          iintro !>
          wp_lstep
          iapply (wp_ret_top _ _ (Expr.var "result") (Val.int 1) [] env _
            (heval := by simp [agar_eval, hresult]))
          ipure_intro; rfl
      · -- Initial J at loop entry: LEFT disjunct.
        isplitl []
        · iexact HI
        ipure_intro
        refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩ <;> agar_eval

/-! ## `progCounterRace` — predicate-form adequacy: `result ∈ {0, 1}`

Same CAS-bump workers as `progCounterCas`, but main reads the counter
exactly once instead of spin-waiting. The observed value depends on
whether any forked CAS has fired yet. `Machine.safe`-with-predicate captures the
race precisely. -/

def progCounterRace : Program where
  procs := fun n => if n = "casBumpProc" then some casBumpProc else none
  main  := ags(
    c := alloc 0 ;
    fork casBumpProc(c) ;
    fork casBumpProc(c) ;
    v := load c ;
    return v
  )

theorem progCounterRace_closedP
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [CounterGpreS GF]
    :
    Machine.safe progCounterRace
      (fun v => v = Val.int 0 ∨ v = Val.int 1) := by
  adequacy_with_heap_intro_P progCounterRace
    (fun v => v = Val.int 0 ∨ v = Val.int 1)
  wp_pures
  wp_alloc_intro cLoc' HPC
  wp_pures
  iapply fupd_wp
  imod (counter_alloc (GF := GF)) with ⟨%γ, Hauth, Hfrag⟩
  imodintro
  inv_alloc_with (counterInv GF F cLoc' γ) [HPC Hauth Hfrag] HI by
    inext; ileft; iframe HPC; iframe Hauth; iexact Hfrag
  wp_fork_emp "casBumpProc" [Expr.var "c"] casBumpProc [Val.loc _]
    [ags(
      fork casBumpProc(c) ;
      v := load c ;
      return v
    )]
  isplitr
  · iintro !>
    iapply casBumpProc_wp_body
    iexact HI
  · iintro !>
    wp_pures
    wp_fork_emp "casBumpProc" [Expr.var "c"] casBumpProc [Val.loc _]
      [ags(v := load c ; return v)]
    isplitr
    · iintro !>
      iapply casBumpProc_wp_body
      iexact HI
    · iintro !>
      wp_pures
      iapply wp_load_atomic (GF := GF) (F := F) (N := nroot)
        (P := counterInv GF F cLoc' γ)
        (Hsub := by rw [nclose_root])
        (heL := by agar_eval)
      iframe HI
      iintro HP
      ihave HP := BI.later_or.mp $$ HP
      icases HP with (⟨>HC, >Hauth, >Hfrag⟩ | ⟨>HC, >Hauth, >Hfrag⟩)
      · imodintro
        iexists (Val.int 0)
        isplitl [HC]
        · iexact HC
        iintro HC
        imodintro
        isplitl [HC Hauth Hfrag]
        · inext; ileft; iframe HC; iframe Hauth; iexact Hfrag
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "v") (Val.int 0) [] _ _
          (heval := by agar_eval))
        ipure_intro; left; rfl
      · imodintro
        iexists (Val.int 1)
        isplitl [HC]
        · iexact HC
        iintro HC
        imodintro
        isplitl [HC Hauth Hfrag]
        · inext; iright; iframe HC; iframe Hauth; iexact Hfrag
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "v") (Val.int 1) [] _ _
          (heval := by agar_eval))
        ipure_intro; right; rfl

end Agar.Logic

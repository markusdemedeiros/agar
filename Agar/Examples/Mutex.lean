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
public import Agar.Iris.Algebra.LockRA
public import Agar.Iris.Algebra.CounterRA

@[expose] public section

/-! # Mutex examples — three programs of increasing strength

* `progMiniMutex` — safety baseline. CAS-acquire / CS / release, but no
  ghost token: both threads execute the entire body unconditionally and
  both `wp_cas_inv` branches discharge identically. Two existential
  heap invariants `∃ v, lk ↦ v` and `∃ v, c ↦ v`. Adequacy at `Val.unit`.
* `progMiniMutexExcl` — real mutual exclusion. Body is conditional on
  the CAS-acquire result; `lockExclInv` carries an exclusive
  `lockOwner γ` token in its UNLOCKED disjunct, and `lockOwner_exclusive`
  rules out the impossible "two threads see UNLOCKED" case.
* `progMutexCounter` — adds an `Auth Nat` ghost-counter bundled with the
  protected cell `c` in `lockCntInv`; the winner runs `counter_increment`
  in lockstep with the heap store. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE Iris.COFE Iris.Std.LawfulSet

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]
variable {E : CoPset}

/-- The critical-section procedure body: acquire (CAS), write counter, release. -/
def critProc : Proc where
  params := ["lk", "c"]
  body := ags(
    prev := cas lk 0 1 ;
    store c 1 ;
    store lk 0
  )

/-- The mini-mutex program: allocate lock + counter, fork two contenders,
fall through. -/
def progMiniMutex : Program where
  procs := fun n => if n = "critProc" then some critProc else none
  main  := ags(
    lk := alloc 0 ;
    c  := alloc 0 ;
    fork critProc(lk, c) ;
    fork critProc(lk, c)
  )

private theorem critProc_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (lkLoc cLoc : Loc) :
    iprop(inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) lkLoc v) ∗
          inv (GF := GF) nroot
            iprop(∃ v : Val, points_to (GF := GF) (F := F) cLoc v)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨critProc.body, [],
          bindParams critProc.params [Val.loc lkLoc, Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro ⟨#HIL, #HIC⟩
  unfold critProc
  -- Safety baseline: no ghost, so both CAS branches do the same work.
  wp_pures
  iapply wp_cas_inv (GF := GF) (F := F) (N := nroot)
    (vO := Val.int 0) (vN := Val.int 1)
    (Hsub := fun _ _ => CoPset.mem_full)
    (heL := by agar_eval) (heO := by agar_eval) (heN := by agar_eval)
    (heq := by decide)
    (hne_of_ne := (val_beq_int_false 0))
  iframe HIL
  isplitr
  · wp_pures
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIC
    wp_pures
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIL
    iintro !>
    wp_done
  · iintro !> %v _hvne
    wp_pures
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIC
    wp_pures
    iapply wp_store_inv (GF := GF) (F := F) (N := nroot)
      (Hsub := fun _ _ => CoPset.mem_full)
      (heL := by agar_eval) (heV := by agar_eval)
    iframe HIL
    iintro !>
    wp_done

theorem progMiniMutex_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progMiniMutex (· = Val.unit) := by
  adequacy_with_heap_intro progMiniMutex Val.unit
  wp_pures
  wp_alloc_intro HPL
  wp_pures
  wp_alloc_intro HPC
  wp_pures
  wp_inv_alloc_pt HPL HIL 0
  wp_inv_alloc_pt HPC HIC 0
  wp_fork_emp "critProc" [Expr.var "lk", Expr.var "c"] critProc
    [Val.loc _, Val.loc _]
    [Stmt.fork "critProc" [Expr.var "lk", Expr.var "c"]]
  isplitr
  · iintro !>
    iapply critProc_wp_body
    iframe HIL HIC
  · iintro !>
    wp_pures
    wp_fork_emp "critProc" [Expr.var "lk", Expr.var "c"] critProc
      [Val.loc _, Val.loc _] []
    isplitr
    · iintro !>
      iapply critProc_wp_body
      iframe HIL HIC
    · iintro !>
      wp_done

/-! ## `progMiniMutexExcl` — real mutual exclusion via `lockOwner γ` -/

/-- The strengthened critical-section procedure: conditional release. -/
def critProcExcl : Proc where
  params := ["lk", "c"]
  body := ags(
    prev := cas lk 0 1 ;
    if prev = 0 then
      (store c 1 ; store lk 0)
    else skip
  )

/-- The lock invariant for the exclusive mini-mutex. UNLOCKED disjunct
bundles the lock cell, the exclusive token `lockOwner γ`, and the
existentially-quantified critical-section resource `c ↦ vc`. The LOCKED
disjunct holds only the heap cell — whoever holds the token is the
current critical-section holder. -/
private abbrev lockExclInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    [LockGpreS GF] (γ : GName) (lkLoc cLoc : Loc) : IProp GF :=
  iprop(
    (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
        lockOwner (GF := GF) γ ∗
        ∃ vc : Val, points_to (GF := GF) (F := F) cLoc vc)
      ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1))

/-- The strengthened mini-mutex program. -/
def progMiniMutexExcl : Program where
  procs := fun n => if n = "critProcExcl" then some critProcExcl else none
  main  := ags(
    lk := alloc 0 ;
    c  := alloc 0 ;
    fork critProcExcl(lk, c) ;
    fork critProcExcl(lk, c)
  )

/-- The forked-thread proof obligation under the lock invariant. -/
private theorem critProcExcl_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    [LockGpreS GF] {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (lkLoc cLoc : Loc) (γ : GName) :
    iprop(inv (GF := GF) nroot (lockExclInv GF F γ lkLoc cLoc)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨critProcExcl.body, [],
          bindParams critProcExcl.params [Val.loc lkLoc, Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold critProcExcl
  wp_pures
  wp_cas_atomic_split HI (lockExclInv GF F γ lkLoc cLoc)
    (Val.int 0) (Val.int 1)
    (val_beq_int_false 0)
    with (⟨>HLk, >Hown, %vc, >HC⟩ | >HLk)
  · imodintro
    iexists (Val.int 0)
    iframe HLk
    isplitl [Hown HC]
    · inv_close_right HLk'
      wp_pures
      wp_store_keep HC
      wp_pures
      iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
        (P := lockExclInv GF F γ lkLoc cLoc)
        (l := lkLoc) (v := Val.int 0)
        (Hsub := fun _ _ => CoPset.mem_full)
        (heL := by agar_eval) (heV := by agar_eval)
      iframe HI
      iintro HP
      inext_or HP
      icases HP with (>⟨_HLk, Hown', %_vc', _HC'⟩ | >HLkR)
      · iexfalso
        iapply lockOwner_exclusive γ
        iframe Hown
        iexact Hown'
      · imodintro
        iexists (Val.int 1)
        iframe HLkR
        iintro HLk2
        imodintro
        isplitl [HLk2 Hown HC]
        · inext; ileft
          iframe HLk2
          iframe Hown
          iexists (Val.int 1); iexact HC
        wp_done
    · cas_dead
  · imodintro
    iexists (Val.int 1)
    iframe HLk
    isplitr
    · cas_dead
    · inv_close_right HLk'
      wp_pures
      wp_done

theorem progMiniMutexExcl_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F] [LockGpreS GF]
    :
    Machine.safe progMiniMutexExcl (· = Val.unit) := by
  adequacy_with_heap_intro progMiniMutexExcl Val.unit
  wp_pures
  wp_alloc_intro lkLoc' HPL
  wp_pures
  wp_alloc_intro cLoc' HPC
  wp_pures
  wp_lock_alloc γ Hown HI : (lockExclInv GF F γ lkLoc' cLoc')
        := [HPL Hown HPC] by
    inext; ileft
    iframe HPL
    iframe Hown
    iexists (Val.int 0); iexact HPC
  wp_fork_emp "critProcExcl" [Expr.var "lk", Expr.var "c"] critProcExcl
    [Val.loc _, Val.loc _]
    [Stmt.fork "critProcExcl" [Expr.var "lk", Expr.var "c"]]
  isplitr
  · iintro !>
    iapply critProcExcl_wp_body
    iexact HI
  · iintro !>
    wp_pures
    wp_fork_emp "critProcExcl" [Expr.var "lk", Expr.var "c"] critProcExcl
      [Val.loc _, Val.loc _] []
    isplitr
    · iintro !>
      iapply critProcExcl_wp_body
      iexact HI
    · iintro !>
      wp_done

/-! ## `progMutexCounter` — `lockExclInv` extended with `Auth Nat` ghost -/

/-- The counter-tracking critical-section procedure: acquire (CAS),
read + increment counter, release. -/
def critProcCnt : Proc where
  params := ["lk", "c"]
  body := ags(
    prev := cas lk 0 1 ;
    if prev = 0 then {
      tmp := load c ;
      store c (tmp + 1) ;
      store lk 0
    }
  )

/-- The mutex + counter program. -/
def progMutexCounter : Program where
  procs := fun n => if n = "critProcCnt" then some critProcCnt else none
  main  := ags(
    lk := alloc 0 ;
    c  := alloc 0 ;
    fork critProcCnt(lk, c) ;
    fork critProcCnt(lk, c)
  )

/-- The combined lock + counter invariant. The UNLOCKED disjunct bundles
the lock cell, the exclusive lock token `lockOwner γL`, the protected
cell `c ↦ n`, AND both halves of the counter ghost `auth γC n ∗ frag γC n`
in sync with `c`'s value. Bundling auth+frag inside the lock is what
lets the per-iteration `(n,n) ⤳ (n+1,n+1)` increment discharge in one
fell swoop, while the lock keeps other threads from observing an
inconsistent (heap, ghost) pair. -/
private abbrev lockCntInv
    (GF : BundledGFunctors.{0,0,0}) (F : Type _) [UFraction F] [AgarG GF F]
    [LockGpreS GF] [CounterGpreS GF] (γL γC : GName) (lkLoc cLoc : Loc) :
    IProp GF :=
  iprop(
    (points_to (GF := GF) (F := F) lkLoc (Val.int 0) ∗
        lockOwner (GF := GF) γL ∗
        ∃ n : Nat,
          points_to (GF := GF) (F := F) cLoc (Val.int n) ∗
          counter_auth (GF := GF) γC n ∗
          counter_frag (GF := GF) γC n)
      ∨ points_to (GF := GF) (F := F) lkLoc (Val.int 1))

/-- The forked-thread proof obligation under the combined lock + counter
invariant. Both threads execute the same body; with `fork_post := emp`
both branches close at `emp`. -/
private theorem critProcCnt_wp_body
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F] [AgarG GF F]
    [LockGpreS GF] [CounterGpreS GF] {hlc : Bool} [InvGS_gen hlc GF]
    (procs : Name → Option Proc) (lkLoc cLoc : Loc) (γL γC : GName) :
    iprop(inv (GF := GF) nroot (lockCntInv GF F γL γC lkLoc cLoc)) ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨critProcCnt.body, [],
          bindParams critProcCnt.params [Val.loc lkLoc, Val.loc cLoc],
          [], none⟩
        (fun _ => iprop(emp : IProp GF)) := by
  istart
  iintro #HI
  unfold critProcCnt
  wp_step                                    -- wp_seq exposing `cas`
  iintro !>
  wp_cas_atomic_split HI (lockCntInv GF F γL γC lkLoc cLoc)
    (Val.int 0) (Val.int 1)
    (val_beq_int_false 0)
    with (⟨>HLk, >Hown, %n, >HC, >Hauth, >Hfrag⟩ | >HLk)
  ·
    imodintro
    iexists (Val.int 0)
    iframe HLk
    isplitl [Hown HC Hauth Hfrag]
    · inv_close_right HLk'
      wp_pures
      wp_load_keep HC
      wp_pures
      wp_store_keep HC
      -- Ghost step `(n, n) ⤳ (n+1, n+1)` in lockstep with the heap store.
      iapply fupd_wp
      imod (counter_increment (GF := GF) γC n n) $$ [Hauth Hfrag]
            with ⟨Hauth, Hfrag⟩
      · isplitl [Hauth] <;> iassumption
      imodintro
      wp_lstep
      iapply wp_store_atomic (GF := GF) (F := F) (N := nroot)
        (P := lockCntInv GF F γL γC lkLoc cLoc)
        (l := lkLoc) (v := Val.int 0)
        (Hsub := fun _ _ => CoPset.mem_full)
        (heL := by agar_eval) (heV := by agar_eval)
      iframe HI
      iintro HP2
      inext_or HP2
      icases HP2 with (>⟨_HLk2, Hown', %_n', _HC', _Hauth', _Hfrag'⟩ | >HLkR)
      ·
        iexfalso
        iapply lockOwner_exclusive γL
        iframe Hown
        iexact Hown'
      · imodintro
        iexists (Val.int 1)
        iframe HLkR
        iintro HLk2
        imodintro
        have hcast : Val.int ((n : Int) + 1) = Val.int (((n + 1 : Nat) : Int)) := by
          congr 1
        isplitl [HLk2 Hown HC Hauth Hfrag]
        · inext; ileft
          iframe HLk2
          iframe Hown
          iexists (n + 1)
          isplitl [HC]
          · rw [← hcast]; iexact HC
          iframe Hauth
          iexact Hfrag
        wp_done
    · cas_dead
  · imodintro
    iexists (Val.int 1)
    iframe HLk
    isplitr
    · cas_dead
    · inv_close_right HLk'
      wp_pures
      wp_done

theorem progMutexCounter_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    [LockGpreS GF] [CounterGpreS GF]
    :
    Machine.safe progMutexCounter (· = Val.unit) := by
  adequacy_with_heap_intro progMutexCounter Val.unit
  wp_pures
  wp_alloc_intro lkLoc' HPL
  wp_pures
  wp_alloc_intro cLoc' HPC
  wp_pures
  iapply fupd_wp
  imod counter_alloc with ⟨%γC, Hauth, Hfrag⟩
  imodintro
  wp_lock_alloc γL Hown HI : (lockCntInv GF F γL γC lkLoc' cLoc')
        := [HPL Hown HPC Hauth Hfrag] by
    inext; ileft
    iframe HPL
    iframe Hown
    iexists 0
    iframe HPC
    iframe Hauth
    iexact Hfrag
  wp_fork_emp "critProcCnt" [Expr.var "lk", Expr.var "c"] critProcCnt
    [Val.loc _, Val.loc _]
    [Stmt.fork "critProcCnt" [Expr.var "lk", Expr.var "c"]]
  isplitr
  · iintro !>
    iapply critProcCnt_wp_body
    iexact HI
  · iintro !>
    wp_pures
    wp_fork_emp "critProcCnt" [Expr.var "lk", Expr.var "c"] critProcCnt
      [Val.loc _, Val.loc _] []
    isplitr
    · iintro !>
      iapply critProcCnt_wp_body
      iexact HI
    · iintro !>
      wp_done

end Agar.Logic

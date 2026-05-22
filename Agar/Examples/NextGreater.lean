module

public import Agar.Examples.StackReverse
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
public import Agar.Iris.WpSpin

@[expose] public section

/-! # Next-greater-sum: monotonic-stack client over the Treiber interface

A classic single-result algorithm built atop the imported Treiber-stack
interface. Drain an `input` stack while maintaining a monotone-
decreasing `helper` stack. For each popped `x`, drain `helper` of all
entries `≤ x`; if any remain, the top is `x`'s next-greater and
contributes to the result sum.

The architecture decomposes the inner loop into its own procedure
`drainHelperProc` with its own body-level and call-level specs. The
outer `sumNGEProc` then composes via three call-level specs
(`popProc_spec`, `drainHelperProc_spec`, `pushProc_spec`) — only one
`wp_spin_invariant` is used at each level, no nesting.

**Roadmap**

1. Pure spec: `dropLE`, `addendOf`, `helperAfter`, `stepNGE`,
   `processNGE`, `sumNGE`.
2. `drainHelperProc` + invariant `drainInv` + body spec
   `drainHelperProc_wp_body` + call spec `drainHelperProc_spec`.
3. `sumNGEProc` + invariant `outerInv` + body spec
   `sumNGEProc_wp_body` + call spec `sumNGEProc_spec`.
4. Closed programs `progSumNextGreater` (`[3,1] → 3`) and
   `progSumNextGreater5` (`[1,5,2,4,3] → 14`) with adequacy theorems.

**Outer-continuation threading.** Both `drainInv` and `outerInv` take
an `HK_iprop : IProp GF` parameter. The body-level proofs pass
`iprop(emp)`; the call-level specs pass the actual outer-continuation
wand `tstack ... -∗ wp ... post Φ`. The spin loop's HE branch
(`hgfalse`) then applies that wand against the final tstack resources
to discharge the post — letting the caller pick up where the call
left off without an additional sorry boundary. -/

namespace Agar.Logic

open Iris Iris.BI Iris.OFE

variable {GF : BundledGFunctors.{0,0,0}} {hlc : Bool} [InvGS_gen hlc GF]
variable {F : Type _} [UFraction F] [AgarG GF F]

/-! ## Pure specification

`dropLE x h` drops the prefix of `≤ x` elements from `h`.
`addendOf x h` is the contribution of `x` (head of `dropLE x h`, or 0).
`sumNGE` folds these contributions over the input list. -/

/-- Drop the prefix of `h` consisting of entries `≤ x`. -/
def dropLE (x : Int) : List Int → List Int
  | []      => []
  | t :: ts => if decide (t ≤ x) then dropLE x ts else t :: ts

/-- Contribution of `x` to the running sum: the head of `dropLE x h`
(the smallest entry in `h` strictly greater than `x`), or `0` if none
exists. -/
def addendOf (x : Int) (h : List Int) : Int :=
  match dropLE x h with
  | []     => 0
  | t :: _ => t

/-- New helper stack after processing `x`: drop `≤ x` entries and push `x`
on top, preserving the monotone-decreasing invariant. -/
def helperAfter (x : Int) (h : List Int) : List Int :=
  x :: dropLE x h

/-- One fold step: `result += addendOf x helper; helper := helperAfter x helper`. -/
def stepNGE (state : Int × List Int) (x : Int) : Int × List Int :=
  let (r, hl) := state
  (r + addendOf x hl, helperAfter x hl)

/-- Fold `stepNGE` over the pop sequence, returning `(sum, final helper)`. -/
def processNGE (xs : List Int) : Int × List Int := xs.foldl stepNGE (0, [])

/-- Functional spec: the sum of next-greater contributions over `xs`. -/
def sumNGE (xs : List Int) : Int := (processNGE xs).1

/-- Unfold one step from the right — used by the body proof when the
spin loop's IH advances `ys` to `ys ++ [x]`. -/
theorem processNGE_append (ys : List Int) (x : Int) :
    processNGE (ys ++ [x]) =
      let st := processNGE ys
      (st.1 + addendOf x st.2, helperAfter x st.2) := by
  simp [processNGE, List.foldl_append, stepNGE]

/-! ## `drainHelperProc` — the inner loop, as its own procedure

Drains `helper` of all entries `≤ x`. If any entry `> x` remains, the
top is `addendOf x xs`; otherwise 0. The procedure RETURNS this
addend so the caller can `result := result + addend`. -/

/-- Inner-loop procedure: take `helper` and `x`, pop entries `≤ x` until
either `helper` is empty (return `0`) or the top `t > x` (push `t`
back, return `t`). Modifies `helper` to leave it as `dropLE x helper`,
matching `helperAfter` minus the final push of `x` (which `sumNGEProc`
does separately). -/
def drainHelperProc : Proc where
  params := ["helper", "x"]
  body := ags(
    done   := 0 ;
    result := 0 ;
    (while done = 0 do (
      hh := load helper ;
      if hh = 0 then done := 1
      else (
        t := call popProc(helper) ;
        if x < t then (
          result := t ;
          tmp    := call pushProc(helper, t) ;
          done   := 1
        ) else skip
      )
    )) ;
    return result
  )

/-! ### Loop invariant for the drain

Two cases, joined by `∨`:
- **In-progress** (`done = 0`, `result = 0`): we own `tstack curr_h helper`
  for some `curr_h` whose `dropLE x` matches the spec's `dropLE x xs`.
  Resources may have been popped but not yet pushed back.
- **Finished** (`done = 1`, `result = addendOf x xs`): we own
  `tstack (dropLE x xs) helper` — the post-state matching
  `helperAfter` minus the final outer push.

`HK_iprop` is the outer continuation, threaded through unchanged so
the call-level spec can apply it after the loop. -/

private abbrev drainInv (HK_iprop : IProp GF) (x : Int) (xs : List Int)
    (helper : Loc) (env : Env) : IProp GF :=
  iprop(⌜env "helper" = some (Val.loc helper) ∧
        env "x" = some (Val.int x)⌝ ∗
    term(HK_iprop) ∗
    ((⌜env "done" = some (Val.int 0) ∧
        env "result" = some (Val.int 0)⌝ ∗
      ∃ curr_h : List Int, ⌜dropLE x curr_h = dropLE x xs⌝ ∗
        term(tstack (GF := GF) (F := F) curr_h helper)) ∨
     (⌜env "done" = some (Val.int 1) ∧
        env "result" = some (Val.int (addendOf x xs))⌝ ∗
      term(tstack (GF := GF) (F := F) (dropLE x xs) helper))))

/-! ### Body-level spec for `drainHelperProc` -/

theorem drainHelperProc_wp_body
    (procs : Name → Option Proc)
    (hpush : procs "pushProc" = some pushProc)
    (hpop  : procs "popProc"  = some popProc)
    (x : Int) (xs : List Int) (helper : Loc) :
    tstack (GF := GF) (F := F) xs helper ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨drainHelperProc.body, [],
          bindParams drainHelperProc.params [Val.loc helper, Val.int x],
          [], none⟩
        (fun r => iprop(⌜r = Val.int (addendOf x xs)⌝ ∗
          term(tstack (GF := GF) (F := F) (dropLE x xs) helper))) := by
  istart
  iintro HS
  unfold drainHelperProc
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := drainInv (GF := GF) (F := F) iprop(emp : IProp GF) x xs helper) _
    (HGuard := fun env => ?HG)
    (HBody  := fun env => ?HB)
    (HExit  := fun env => ?HE))
  case HG =>
    iintro HI
    icases HI with ⟨%hpure, _HoutHK, HDone⟩
    obtain ⟨hhelp, hxv⟩ := hpure
    icases HDone with (⟨%hpureL, %currH, %hdrop, HSh⟩ | ⟨%hpureR, HSh⟩)
    · obtain ⟨hdone, hres⟩ := hpureL
      isplitl [HSh]
      · isplitr
        · ipure_intro; exact ⟨hhelp, hxv⟩
        isplitl []
        · iemp_intro
        ileft
        isplitr
        · ipure_intro; exact ⟨hdone, hres⟩
        iexists currH
        isplitr
        · ipure_intro; exact hdrop
        iexact HSh
      ipure_intro
      refine ⟨true, ?_⟩
      simp [agar_eval, hdone]; rfl
    · obtain ⟨hdone, hres⟩ := hpureR
      isplitl [HSh]
      · isplitr
        · ipure_intro; exact ⟨hhelp, hxv⟩
        isplitl []
        · iemp_intro
        iright
        isplitr
        · ipure_intro; exact ⟨hdone, hres⟩
        iexact HSh
      ipure_intro
      refine ⟨false, ?_⟩
      simp [agar_eval, hdone]; rfl
  case HB =>
    iintro ⟨HIH, %hgtrue, HI⟩
    icases HI with ⟨%hpure, _HoutHK, HDone⟩
    obtain ⟨hhelp, hxv⟩ := hpure
    icases HDone with (⟨%hpureL, %currH, %hdrop, HSh⟩ | ⟨%hpureR, _HSh⟩)
    · obtain ⟨hdone, hres⟩ := hpureL
      -- Unpack tstack currH helper to load its head.
      icases HSh with ⟨%hv_curr, HPh, HLcurr⟩
      wp_lstep
      wp_load_direct HPh (by simpa using hhelp)
      wp_lstep
      cases currH with
      | nil =>
          icases HLcurr with %hhv0
          subst hhv0
          iapply wp_ite_true (heval := by simp [agar_eval]; rfl)
          iintro !>
          wp_lstep
          wp_lstep
          ihave HIH := HIH $$
            %((env.set "hh" (Val.int 0)).set "done" (Val.int 1))
          iapply HIH
          have hdrop_init : dropLE x xs = [] := by
            have h := hdrop.symm
            simp [dropLE] at h
            exact h
          have haddend : addendOf x xs = 0 := by
            unfold addendOf; rw [hdrop_init]
          isplitr
          · ipure_intro
            refine ⟨?_, ?_⟩
            · simp [agar_eval, hhelp]
            · simp [agar_eval, hxv]
          isplitl []
          · iemp_intro
          iright
          isplitr
          · ipure_intro
            refine ⟨?_, ?_⟩
            · simp [agar_eval]
            · simp [agar_eval, hres, haddend]
          rw [hdrop_init]
          iapply tstack_nil_intro; iexact HPh
      | cons t rest =>
          icases HLcurr with ⟨%l_t, %hhv, %nx_t, HCt, HTrest⟩
          subst hhv
          iapply wp_ite_false
            (heval := by
              have hbeq : Val.beq (Val.loc l_t) (Val.int 0) = false := by
                simp [Val.beq]
              simp [agar_eval, BEq.beq, hbeq])
          iintro !>
          wp_lstep
          iapply (popProc_spec (procs := procs) (hproc := hpop)
            (x := "t") (eStk := Expr.var "helper") (popped := t) (xs := rest)
            (stk := helper) (hStk := by simpa using hhelp))
          isplitl [HPh HCt HTrest]
          · iexists (Val.loc l_t); isplitl [HPh]
            · iexact HPh
            iexists l_t; isplitr
            · ipure_intro; rfl
            iexists nx_t; isplitl [HCt]
            · iexact HCt
            iexact HTrest
          iintro HSpost
          unfold popProc_post
          by_cases hcmp : (x : Int) < t
          · -- t > x: record t, push back, set done := 1.
            iapply wp_ite_true (heval := by
              have h : decide ((x : Int) < t) = true := decide_eq_true hcmp
              simp [agar_eval, hxv, h])
            iintro !>
            wp_lstep
            iapply wp_assign (heval := by simp [agar_eval]; rfl)
            iintro !>
            wp_lstep
            wp_lstep
            iapply (pushProc_spec (procs := procs) (hproc := hpush)
              (xs := rest) (stk := helper) (v := t) (x := "tmp")
              (eStk := Expr.var "helper") (eV := Expr.var "t")
              (hStk := by simp [agar_eval, hhelp])
              (hV := by simp [agar_eval]))
            isplitl [HSpost]
            · iexact HSpost
            iintro HSpost'
            unfold pushProc_post
            wp_lstep
            wp_lstep
            ihave HIH := HIH $$
              %((((((env.set "hh" (Val.loc l_t)).set "t" (Val.int t)).set
                  "result" (Val.int t)).set "tmp" Val.unit).set
                  "done" (Val.int 1)))
            iapply HIH
            have hdrop_init : dropLE x xs = t :: rest := by
              have h : dropLE x (t :: rest) = t :: rest := by
                simp [dropLE]; omega
              rw [h] at hdrop
              exact hdrop.symm
            have haddend : addendOf x xs = t := by
              unfold addendOf; rw [hdrop_init]
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval, hhelp]
              · simp [agar_eval, hxv]
            isplitl []
            · iemp_intro
            iright
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval]
              · simp [agar_eval, haddend]
            rw [hdrop_init]
            iexact HSpost'
          · -- t ≤ x: discard t, continue with currH = rest.
            iapply wp_ite_false (heval := by
              have h : decide ((x : Int) < t) = false := decide_eq_false hcmp
              simp [agar_eval, hxv, h])
            iintro !>
            wp_lstep
            ihave HIH := HIH $$
              %((env.set "hh" (Val.loc l_t)).set "t" (Val.int t))
            iapply HIH
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval, hhelp]
              · simp [agar_eval, hxv]
            isplitl []
            · iemp_intro
            ileft
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval, hdone]
              · simp [agar_eval, hres]
            iexists rest
            isplitr
            · ipure_intro
              have hle : t ≤ x := by omega
              have hstep : dropLE x (t :: rest) = dropLE x rest := by
                simp [dropLE, hle]
              rw [← hstep]; exact hdrop
            iexact HSpost
    · -- RIGHT case: done = 1 contradicts guard-true precondition.
      obtain ⟨hdone, _⟩ := hpureR
      exfalso
      exact absurd hgtrue (by simp [agar_eval, hdone]; decide)
  case HE =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with ⟨%hpure, _HoutHK, HDone⟩
    obtain ⟨hhelp, hxv⟩ := hpure
    icases HDone with (⟨%hpureL, %_currH, %_hdrop, _HSh⟩ | ⟨%hpureR, HSh⟩)
    · obtain ⟨hdone, _⟩ := hpureL
      exfalso
      exact absurd hgfalse (by simp [agar_eval, hdone]; decide)
    · obtain ⟨hdone, hres⟩ := hpureR
      wp_lstep
      iapply (wp_ret_top _ _ (Expr.var "result") (Val.int (addendOf x xs)) [] _ _
        (heval := by simpa using hres))
      isplitr
      · ipure_intro; rfl
      iexact HSh
  -- Initial drainInv (LEFT case, done = 0, result = 0, currH = xs).
  isplitr
  · ipure_intro
    refine ⟨?_, ?_⟩
    · simp [agar_eval]
    · simp [agar_eval]
  isplitl []
  · iemp_intro
  ileft
  isplitr
  · ipure_intro
    refine ⟨?_, ?_⟩
    · simp [agar_eval]
    · simp [agar_eval]
  iexists xs
  isplitr
  · ipure_intro; rfl
  iexact HS

/-! ### Call-level spec for `drainHelperProc` -/

/-- Thread state the caller resumes in after `drainHelperProc` returns:
the return-binder `x` is set to `Val.int addend` and execution
continues at the caller's next statement (`cont`'s head, or `skip` if
`cont` is empty). The call-level spec's outer continuation `HK` is a
wand from `tstack ...` to `wp ... (drainHelperProc_post ...)`. -/
def drainHelperProc_post (x : Name) (addend : Int) (cont : List Stmt)
    (env : Env) (stack : List Frame) : Thread :=
  let env' : Env := env.set x (Val.int addend)
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

theorem drainHelperProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc : procs "drainHelperProc" = some drainHelperProc)
    (hpush : procs "pushProc" = some pushProc)
    (hpop  : procs "popProc"  = some popProc)
    (Φ : Val → IProp GF) (x : Name) (eHelper eX : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (helper : Loc) (xv : Int) (xs : List Int)
    (hHelper : Expr.eval env eHelper = some (Val.loc helper))
    (hX : Expr.eval env eX = some (Val.int xv)) :
    tstack (GF := GF) (F := F) xs helper ∗
      (tstack (GF := GF) (F := F) (dropLE xv xs) helper -∗
        wp (GF := GF) procs fork_post CoPset.full
          (drainHelperProc_post x (addendOf xv xs) cont env stack) Φ)
    ⊢ wp (GF := GF) procs fork_post CoPset.full
        ⟨.call x "drainHelperProc" [eHelper, eX], cont, env, stack, none⟩ Φ := by
  istart
  iintro ⟨HS, HK⟩
  have hargs : evalArgs env [eHelper, eX] = some [Val.loc helper, Val.int xv] := by
    simp [agar_eval, hHelper, hX]
  have harity : ([Val.loc helper, Val.int xv]).length =
                  drainHelperProc.params.length := rfl
  iapply (wp_call procs fork_post x "drainHelperProc" [eHelper, eX]
    drainHelperProc [Val.loc helper, Val.int xv] cont env stack Φ
    hproc hargs harity)
  iintro !>
  unfold drainHelperProc
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := drainInv (GF := GF) (F := F)
            iprop(term(tstack (GF := GF) (F := F) (dropLE xv xs) helper) -∗
              wp (GF := GF) procs fork_post CoPset.full
                (drainHelperProc_post x (addendOf xv xs) cont env stack) Φ)
            xv xs helper) _
    (HGuard := fun e => ?HG)
    (HBody  := fun e => ?HB)
    (HExit  := fun e => ?HE))
  case HG =>
    iintro HI
    icases HI with ⟨%hpure, HoutHK, HDone⟩
    obtain ⟨hhelp, hxv'⟩ := hpure
    icases HDone with (⟨%hpureL, %currH, %hdrop, HSh⟩ | ⟨%hpureR, HSh⟩)
    · obtain ⟨hdone, hres⟩ := hpureL
      isplitl [HSh HoutHK]
      · isplitr
        · ipure_intro; exact ⟨hhelp, hxv'⟩
        isplitl [HoutHK]
        · iexact HoutHK
        ileft
        isplitr
        · ipure_intro; exact ⟨hdone, hres⟩
        iexists currH
        isplitr
        · ipure_intro; exact hdrop
        iexact HSh
      ipure_intro
      refine ⟨true, ?_⟩
      simp [agar_eval, hdone]; rfl
    · obtain ⟨hdone, hres⟩ := hpureR
      isplitl [HSh HoutHK]
      · isplitr
        · ipure_intro; exact ⟨hhelp, hxv'⟩
        isplitl [HoutHK]
        · iexact HoutHK
        iright
        isplitr
        · ipure_intro; exact ⟨hdone, hres⟩
        iexact HSh
      ipure_intro
      refine ⟨false, ?_⟩
      simp [agar_eval, hdone]; rfl
  case HB =>
    iintro ⟨HIH, %hgtrue, HI⟩
    icases HI with ⟨%hpure, HoutHK, HDone⟩
    obtain ⟨hhelp, hxv'⟩ := hpure
    icases HDone with (⟨%hpureL, %currH, %hdrop, HSh⟩ | ⟨%hpureR, _HSh⟩)
    · obtain ⟨hdone, hres⟩ := hpureL
      icases HSh with ⟨%hv_curr, HPh, HLcurr⟩
      wp_lstep
      wp_load_direct HPh (by simpa using hhelp)
      wp_lstep
      cases currH with
      | nil =>
          icases HLcurr with %hhv0
          subst hhv0
          iapply wp_ite_true (heval := by simp [agar_eval]; rfl)
          iintro !>
          wp_lstep
          wp_lstep
          ihave HIH := HIH $$
            %((e.set "hh" (Val.int 0)).set "done" (Val.int 1))
          iapply HIH
          have hdrop_init : dropLE xv xs = [] := by
            have h := hdrop.symm
            simp [dropLE] at h
            exact h
          have haddend : addendOf xv xs = 0 := by
            unfold addendOf; rw [hdrop_init]
          isplitr
          · ipure_intro
            refine ⟨?_, ?_⟩
            · simp [agar_eval, hhelp]
            · simp [agar_eval, hxv']
          isplitl [HoutHK]
          · iexact HoutHK
          iright
          isplitr
          · ipure_intro
            refine ⟨?_, ?_⟩
            · simp [agar_eval]
            · simp [agar_eval, hres, haddend]
          rw [hdrop_init]
          iapply tstack_nil_intro; iexact HPh
      | cons t rest =>
          icases HLcurr with ⟨%l_t, %hhv, %nx_t, HCt, HTrest⟩
          subst hhv
          iapply wp_ite_false
            (heval := by
              have hbeq : Val.beq (Val.loc l_t) (Val.int 0) = false := by
                simp [Val.beq]
              simp [agar_eval, BEq.beq, hbeq])
          iintro !>
          wp_lstep
          iapply (popProc_spec (procs := procs) (hproc := hpop)
            (x := "t") (eStk := Expr.var "helper") (popped := t) (xs := rest)
            (stk := helper) (hStk := by simpa using hhelp))
          isplitl [HPh HCt HTrest]
          · iexists (Val.loc l_t); isplitl [HPh]
            · iexact HPh
            iexists l_t; isplitr
            · ipure_intro; rfl
            iexists nx_t; isplitl [HCt]
            · iexact HCt
            iexact HTrest
          iintro HSpost
          unfold popProc_post
          by_cases hcmp : (xv : Int) < t
          · iapply wp_ite_true (heval := by
              have h : decide ((xv : Int) < t) = true := decide_eq_true hcmp
              simp [agar_eval, hxv', h])
            iintro !>
            wp_lstep
            iapply wp_assign (heval := by simp [agar_eval]; rfl)
            iintro !>
            wp_lstep
            wp_lstep
            iapply (pushProc_spec (procs := procs) (hproc := hpush)
              (xs := rest) (stk := helper) (v := t) (x := "tmp")
              (eStk := Expr.var "helper") (eV := Expr.var "t")
              (hStk := by simp [agar_eval, hhelp])
              (hV := by simp [agar_eval]))
            isplitl [HSpost]
            · iexact HSpost
            iintro HSpost'
            unfold pushProc_post
            wp_lstep
            wp_lstep
            ihave HIH := HIH $$
              %((((((e.set "hh" (Val.loc l_t)).set "t" (Val.int t)).set
                  "result" (Val.int t)).set "tmp" Val.unit).set
                  "done" (Val.int 1)))
            iapply HIH
            have hdrop_init : dropLE xv xs = t :: rest := by
              have h : dropLE xv (t :: rest) = t :: rest := by
                simp [dropLE]; omega
              rw [h] at hdrop
              exact hdrop.symm
            have haddend : addendOf xv xs = t := by
              unfold addendOf; rw [hdrop_init]
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval, hhelp]
              · simp [agar_eval, hxv']
            isplitl [HoutHK]
            · iexact HoutHK
            iright
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval]
              · simp [agar_eval, haddend]
            rw [hdrop_init]
            iexact HSpost'
          · iapply wp_ite_false (heval := by
              have h : decide ((xv : Int) < t) = false := decide_eq_false hcmp
              simp [agar_eval, hxv', h])
            iintro !>
            wp_lstep
            ihave HIH := HIH $$
              %((e.set "hh" (Val.loc l_t)).set "t" (Val.int t))
            iapply HIH
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval, hhelp]
              · simp [agar_eval, hxv']
            isplitl [HoutHK]
            · iexact HoutHK
            ileft
            isplitr
            · ipure_intro
              refine ⟨?_, ?_⟩
              · simp [agar_eval, hdone]
              · simp [agar_eval, hres]
            iexists rest
            isplitr
            · ipure_intro
              have hle : t ≤ xv := by omega
              have hstep : dropLE xv (t :: rest) = dropLE xv rest := by
                simp [dropLE, hle]
              rw [← hstep]; exact hdrop
            iexact HSpost
    · obtain ⟨hdone, _⟩ := hpureR
      exfalso
      exact absurd hgtrue (by simp [agar_eval, hdone]; decide)
  case HE =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with ⟨%hpure, HoutHK, HDone⟩
    obtain ⟨hhelp, hxv'⟩ := hpure
    icases HDone with (⟨%hpureL, %_currH, %_hdrop, _HSh⟩ | ⟨%hpureR, HSh⟩)
    · obtain ⟨hdone, _⟩ := hpureL
      exfalso
      exact absurd hgfalse (by simp [agar_eval, hdone]; decide)
    · obtain ⟨hdone, hres⟩ := hpureR
      wp_lstep
      -- HoutHK is in persistent context — the threaded HK wand.
      cases hcont : cont with
      | nil =>
          iapply (wp_ret_pop_nil _ _ (Expr.var "result")
            (Val.int (addendOf xv xs)) [] _ _ _ _ _
            (heval := by simpa using hres))
          iintro !>
          unfold drainHelperProc_post
          iapply HoutHK
          iexact HSh
      | cons s cs =>
          iapply (wp_ret_pop_cons _ _ (Expr.var "result")
            (Val.int (addendOf xv xs)) [] _ _ _ _ _ _ _
            (heval := by simpa using hres))
          iintro !>
          unfold drainHelperProc_post
          iapply HoutHK
          iexact HSh
  -- Initial drainInv (LEFT case, done = 0, result = 0, currH = xs).
  isplitr
  · ipure_intro
    refine ⟨?_, ?_⟩
    · simp [agar_eval]
    · simp [agar_eval]
  isplitl [HK]
  · iexact HK
  ileft
  isplitr
  · ipure_intro
    refine ⟨?_, ?_⟩
    · simp [agar_eval]
    · simp [agar_eval]
  iexists xs
  isplitr
  · ipure_intro; rfl
  iexact HS

/-! ## `sumNGEProc` — the outer driver

Pop each element from `input`, drain `helper` of `≤ x` entries via
`drainHelperProc` (which returns the next-greater value or 0), add to
`result`, push `x` onto `helper`, reload `h`. Single spin loop. -/

/-- Outer driver procedure. Drains `input` one element at a time, using
`helper` as a monotone-decreasing stack of candidate next-greater
values. Returns `sumNGE xs` where `xs` is the input pop sequence.
Requires `helper` to start empty. -/
def sumNGEProc : Proc where
  params := ["input", "helper"]
  body := ags(
    result := 0 ;
    h := load input ;
    (while h != 0 do (
      x      := call popProc(input) ;
      addend := call drainHelperProc(helper, x) ;
      result := result + addend ;
      tmp    := call pushProc(helper, x) ;
      h      := load input
    )) ;
    return result
  )

/-- Outer-loop invariant for `sumNGEProc`. The first parameter
`HK_iprop` carries the caller's outer continuation (the post-call
wand); `sumNGEProc_wp_body` passes `emp` for it, and `sumNGEProc_spec`
passes the actual wand so the HE branch can apply it at the
frame-pop. Same shape as `drainInv`. -/
private abbrev outerInv (HK_iprop : IProp GF) (xs : List Int)
    (input helper : Loc) (env : Env) : IProp GF :=
  iprop(term(HK_iprop) ∗
    ∃ (ys zs : List Int) (hv : Val),
      ⌜ys ++ zs = xs ∧
        env "input"  = some (Val.loc input) ∧
        env "helper" = some (Val.loc helper) ∧
        env "h"      = some hv ∧
        env "result" = some (Val.int (processNGE ys).1)⌝ ∗
      points_to (GF := GF) (F := F) input hv ∗
      term(llist (GF := GF) (F := F) zs hv) ∗
      term(tstack (GF := GF) (F := F) (processNGE ys).2 helper))

theorem sumNGEProc_wp_body
    (procs : Name → Option Proc)
    (hpush  : procs "pushProc" = some pushProc)
    (hpop   : procs "popProc"  = some popProc)
    (hdrain : procs "drainHelperProc" = some drainHelperProc)
    (xs : List Int) (input helper : Loc) :
    tstack (GF := GF) (F := F) xs input ∗ tstack (GF := GF) (F := F) [] helper ⊢
      wp (GF := GF) procs iprop(emp : IProp GF) CoPset.full
        ⟨sumNGEProc.body, [],
          bindParams sumNGEProc.params [Val.loc input, Val.loc helper],
          [], none⟩
        (fun r => iprop(⌜r = Val.int (sumNGE xs)⌝ ∗
          term(tstack (GF := GF) (F := F) [] input) ∗
          ∃ final_h : List Int, term(tstack (GF := GF) (F := F) final_h helper))) := by
  istart
  iintro ⟨HSinput, HShelper⟩
  icases HSinput with ⟨%hv0, HPi, HLi⟩
  unfold sumNGEProc
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_load_keep HPi
  wp_lstep
  wp_lstep
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := outerInv (GF := GF) (F := F)
            iprop(emp : IProp GF) xs input helper) _
    (HGuard := fun env => ?HG)
    (HBody  := fun env => ?HB)
    (HExit  := fun env => ?HE))
  case HG =>
    iintro HI
    icases HI with ⟨_HoutHK, %ys, %zs, %hv, %hpure, HPi, HLi, HSh⟩
    obtain ⟨hsplit, hinput, hhelper, hh, hresult⟩ := hpure
    cases zs with
    | nil =>
        icases HLi with %hhv
        subst hhv
        isplitl [HPi HSh]
        · isplitl []
          · iemp_intro
          iexists ys; iexists []; iexists (Val.int 0)
          isplitr
          · ipure_intro; exact ⟨hsplit, hinput, hhelper, hh, hresult⟩
          isplitl [HPi]
          · iexact HPi
          isplitr
          · unfold llist; ipure_intro; rfl
          iexact HSh
        ipure_intro
        refine ⟨false, ?_⟩
        simp [agar_eval, hh]; rfl
    | cons x xs' =>
        icases HLi with ⟨%l, %hhv, %nx, HC, HT⟩
        subst hhv
        isplitl [HPi HC HT HSh]
        · isplitl []
          · iemp_intro
          iexists ys; iexists (x :: xs'); iexists (Val.loc l)
          isplitr
          · ipure_intro; exact ⟨hsplit, hinput, hhelper, hh, hresult⟩
          isplitl [HPi]
          · iexact HPi
          isplitl [HC HT]
          · iexists l
            isplitr
            · ipure_intro; rfl
            iexists nx
            isplitl [HC]
            · iexact HC
            iexact HT
          iexact HSh
        ipure_intro
        refine ⟨true, ?_⟩
        simp [agar_eval, hh]; rfl
  case HB =>
    iintro ⟨HIH, %hgtrue, HI⟩
    icases HI with ⟨_HoutHK, %ys, %zs, %hv, %hpure, HPi, HLi, HSh⟩
    obtain ⟨hsplit, hinput, hhelper, hh, hresult⟩ := hpure
    cases zs with
    | nil =>
        icases HLi with %hhv
        exfalso
        subst hhv
        exact absurd hgtrue (by simp [agar_eval, hh]; decide)
    | cons x xs' =>
        icases HLi with ⟨%l, %hhv, %nx, HC, HT⟩
        subst hhv
        wp_lstep
        -- Pop x from input.
        iapply (popProc_spec (procs := procs) (hproc := hpop)
          (x := "x") (eStk := Expr.var "input") (popped := x) (xs := xs')
          (stk := input) (hStk := by simpa using hinput))
        isplitl [HPi HC HT]
        · iexists (Val.loc l); isplitl [HPi]
          · iexact HPi
          iexists l; isplitr
          · ipure_intro; rfl
          iexists nx; isplitl [HC]
          · iexact HC
          iexact HT
        iintro HSinput
        unfold popProc_post
        wp_lstep
        -- Drain helper of ≤ x and get the addend.
        iapply (drainHelperProc_spec (procs := procs) (hproc := hdrain)
          (hpush := hpush) (hpop := hpop)
          (x := "addend") (eHelper := Expr.var "helper") (eX := Expr.var "x")
          (helper := helper) (xv := x) (xs := (processNGE ys).2)
          (hHelper := by simp [agar_eval, hhelper])
          (hX := by simp [agar_eval]))
        isplitl [HSh]
        · iexact HSh
        iintro HShPost
        unfold drainHelperProc_post
        wp_lstep
        iapply wp_assign (heval := by simp [agar_eval, hresult]; rfl)
        iintro !>
        wp_lstep
        wp_lstep
        -- Push x onto helper.
        iapply (pushProc_spec (procs := procs) (hproc := hpush)
          (xs := dropLE x (processNGE ys).2) (stk := helper) (v := x)
          (x := "tmp") (eStk := Expr.var "helper") (eV := Expr.var "x")
          (hStk := by simp [agar_eval, hhelper])
          (hV := by simp [agar_eval]))
        isplitl [HShPost]
        · iexact HShPost
        iintro HShFinal
        unfold pushProc_post
        -- Reload h from input. Unpack HSinput.
        icases HSinput with ⟨%hv_new, HPi_new, HLi_new⟩
        wp_load_direct HPi_new (by simpa using hinput)
        wp_lstep
        -- Recurse via outer HIH.
        ihave HIH := HIH $$
          %(((((env.set "x" (Val.int x)).set "addend"
            (Val.int (addendOf x (processNGE ys).2))).set "result"
            (Val.int ((processNGE ys).1 + addendOf x (processNGE ys).2))).set
            "tmp" Val.unit).set "h" hv_new)
        iapply HIH
        isplitl []
        · iemp_intro
        iexists (ys ++ [x]); iexists xs'; iexists hv_new
        isplitr
        · ipure_intro
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc] using hsplit
          · simp [agar_eval, hinput]
          · simp [agar_eval, hhelper]
          · simp [agar_eval]
          · rw [processNGE_append]
            simp [agar_eval]
        isplitl [HPi_new]
        · iexact HPi_new
        isplitl [HLi_new]
        · iexact HLi_new
        rw [processNGE_append]
        unfold helperAfter
        iexact HShFinal
  case HE =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with ⟨_HoutHK, %ys, %zs, %hv, %hpure, HPi, HLi, HSh⟩
    obtain ⟨hsplit, hinput, hhelper, hh, hresult⟩ := hpure
    cases zs with
    | nil =>
        icases HLi with %hhv
        subst hhv
        rw [List.append_nil] at hsplit
        subst hsplit
        wp_lstep
        iapply (wp_ret_top _ _ (Expr.var "result") (Val.int (sumNGE ys)) [] _ _
          (heval := by simp [agar_eval]; simpa [sumNGE] using hresult))
        isplitr
        · ipure_intro; rfl
        isplitl [HPi]
        · iapply tstack_nil_intro; iexact HPi
        iexists (processNGE ys).2
        iexact HSh
    | cons x xs' =>
        icases HLi with ⟨%l, %hhv, %nx, HC, HT⟩
        exfalso
        subst hhv
        have hbeq : Val.beq (Val.loc l) (Val.int 0) = false := by simp [Val.beq]
        simp [agar_eval, hh, BEq.beq, hbeq] at hgfalse
  -- Initial outer invariant (HK = emp at the body level).
  isplitl []
  · iemp_intro
  iexists []; iexists xs; iexists hv0
  isplitr
  · ipure_intro
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [agar_eval]
    · simp [agar_eval]
    · simp [agar_eval]
    · simp [agar_eval, processNGE]
  isplitl [HPi]
  · iexact HPi
  isplitl [HLi]
  · iexact HLi
  simp only [processNGE, List.foldl_nil]
  iexact HShelper

/-! ## Call-level spec for `sumNGEProc`

Same shape as `drainHelperProc_spec`: `wp_call` to push the caller
frame, run the body via `wp_spin_invariant`, pop the frame at return.
The outer continuation `HK` is threaded through the `HK_iprop`
parameter of `outerInv` so the HE branch can apply it
against the final tstack-shape resources. -/

/-- Thread state the caller resumes in after `sumNGEProc` returns:
return-binder `x` is set to `Val.int result` (where `result = sumNGE xs`
in the spec) and execution continues at `cont`'s head (or `skip`). -/
def sumNGEProc_post (x : Name) (result : Int) (cont : List Stmt)
    (env : Env) (stack : List Frame) : Thread :=
  let env' : Env := env.set x (Val.int result)
  match cont with
  | []      => ⟨.skip, [], env', stack, none⟩
  | s :: cs => ⟨s,     cs, env', stack, none⟩

theorem sumNGEProc_spec
    (procs : Name → Option Proc) (fork_post : IProp GF)
    (hproc  : procs "sumNGEProc" = some sumNGEProc)
    (hdrain : procs "drainHelperProc" = some drainHelperProc)
    (hpush  : procs "pushProc" = some pushProc)
    (hpop   : procs "popProc"  = some popProc)
    (Φ : Val → IProp GF) (x : Name) (eInput eHelper : Expr)
    (cont : List Stmt) (env : Env) (stack : List Frame)
    (input helper : Loc) (xs : List Int)
    (hInput  : Expr.eval env eInput  = some (Val.loc input))
    (hHelper : Expr.eval env eHelper = some (Val.loc helper)) :
    tstack (GF := GF) (F := F) xs input ∗
      tstack (GF := GF) (F := F) [] helper ∗
      (tstack (GF := GF) (F := F) [] input ∗
        (∃ final_h : List Int,
          term(tstack (GF := GF) (F := F) final_h helper)) -∗
        wp (GF := GF) procs fork_post CoPset.full
          (sumNGEProc_post x (sumNGE xs) cont env stack) Φ)
    ⊢ wp (GF := GF) procs fork_post CoPset.full
        ⟨.call x "sumNGEProc" [eInput, eHelper], cont, env, stack, none⟩ Φ := by
  istart
  iintro ⟨HSinput, HShelper, HK⟩
  have hargs : evalArgs env [eInput, eHelper] =
                  some [Val.loc input, Val.loc helper] := by
    simp [agar_eval, hInput, hHelper]
  have harity : ([Val.loc input, Val.loc helper]).length =
                  sumNGEProc.params.length := rfl
  iapply (wp_call procs fork_post x "sumNGEProc" [eInput, eHelper]
    sumNGEProc [Val.loc input, Val.loc helper] cont env stack Φ
    hproc hargs harity)
  iintro !>
  icases HSinput with ⟨%hv0, HPi, HLi⟩
  unfold sumNGEProc
  wp_lstep
  wp_lstep
  wp_lstep
  wp_lstep
  wp_load_keep HPi
  wp_lstep
  wp_lstep
  iapply (wp_spin_invariant _ _ _ _ _ _ _
    (I := outerInv (GF := GF) (F := F)
            iprop(term(tstack (GF := GF) (F := F) [] input) ∗
              (∃ final_h : List Int,
                term(tstack (GF := GF) (F := F) final_h helper)) -∗
              wp (GF := GF) procs fork_post CoPset.full
                (sumNGEProc_post x (sumNGE xs) cont env stack) Φ)
            xs input helper) _
    (HGuard := fun e => ?HG)
    (HBody  := fun e => ?HB)
    (HExit  := fun e => ?HE))
  case HG =>
    iintro HI
    icases HI with ⟨HoutHK, %ys, %zs, %hv, %hpure, HPi, HLi, HSh⟩
    obtain ⟨hsplit, hinput, hhelper, hh, hresult⟩ := hpure
    cases zs with
    | nil =>
        icases HLi with %hhv
        subst hhv
        isplitl [HPi HSh HoutHK]
        · isplitl [HoutHK]
          · iexact HoutHK
          iexists ys; iexists []; iexists (Val.int 0)
          isplitr
          · ipure_intro; exact ⟨hsplit, hinput, hhelper, hh, hresult⟩
          isplitl [HPi]
          · iexact HPi
          isplitr
          · unfold llist; ipure_intro; rfl
          iexact HSh
        ipure_intro
        refine ⟨false, ?_⟩
        simp [agar_eval, hh]; rfl
    | cons xh xs' =>
        icases HLi with ⟨%l, %hhv, %nx, HC, HT⟩
        subst hhv
        isplitl [HPi HC HT HSh HoutHK]
        · isplitl [HoutHK]
          · iexact HoutHK
          iexists ys; iexists (xh :: xs'); iexists (Val.loc l)
          isplitr
          · ipure_intro; exact ⟨hsplit, hinput, hhelper, hh, hresult⟩
          isplitl [HPi]
          · iexact HPi
          isplitl [HC HT]
          · iexists l
            isplitr
            · ipure_intro; rfl
            iexists nx
            isplitl [HC]
            · iexact HC
            iexact HT
          iexact HSh
        ipure_intro
        refine ⟨true, ?_⟩
        simp [agar_eval, hh]; rfl
  case HB =>
    iintro ⟨HIH, %hgtrue, HI⟩
    icases HI with ⟨HoutHK, %ys, %zs, %hv, %hpure, HPi, HLi, HSh⟩
    obtain ⟨hsplit, hinput, hhelper, hh, hresult⟩ := hpure
    cases zs with
    | nil =>
        icases HLi with %hhv
        exfalso
        subst hhv
        exact absurd hgtrue (by simp [agar_eval, hh]; decide)
    | cons xh xs' =>
        icases HLi with ⟨%l, %hhv, %nx, HC, HT⟩
        subst hhv
        wp_lstep
        iapply (popProc_spec (procs := procs) (hproc := hpop)
          (x := "x") (eStk := Expr.var "input") (popped := xh) (xs := xs')
          (stk := input) (hStk := by simpa using hinput))
        isplitl [HPi HC HT]
        · iexists (Val.loc l); isplitl [HPi]
          · iexact HPi
          iexists l; isplitr
          · ipure_intro; rfl
          iexists nx; isplitl [HC]
          · iexact HC
          iexact HT
        iintro HSinput
        unfold popProc_post
        wp_lstep
        iapply (drainHelperProc_spec (procs := procs) (hproc := hdrain)
          (hpush := hpush) (hpop := hpop)
          (x := "addend") (eHelper := Expr.var "helper") (eX := Expr.var "x")
          (helper := helper) (xv := xh) (xs := (processNGE ys).2)
          (hHelper := by simp [agar_eval, hhelper])
          (hX := by simp [agar_eval]))
        isplitl [HSh]
        · iexact HSh
        iintro HShPost
        unfold drainHelperProc_post
        wp_lstep
        iapply wp_assign (heval := by simp [agar_eval, hresult]; rfl)
        iintro !>
        wp_lstep
        wp_lstep
        iapply (pushProc_spec (procs := procs) (hproc := hpush)
          (xs := dropLE xh (processNGE ys).2) (stk := helper) (v := xh)
          (x := "tmp") (eStk := Expr.var "helper") (eV := Expr.var "x")
          (hStk := by simp [agar_eval, hhelper])
          (hV := by simp [agar_eval]))
        isplitl [HShPost]
        · iexact HShPost
        iintro HShFinal
        unfold pushProc_post
        icases HSinput with ⟨%hv_new, HPi_new, HLi_new⟩
        wp_load_direct HPi_new (by simpa using hinput)
        wp_lstep
        ihave HIH := HIH $$
          %(((((e.set "x" (Val.int xh)).set "addend"
            (Val.int (addendOf xh (processNGE ys).2))).set "result"
            (Val.int ((processNGE ys).1 + addendOf xh (processNGE ys).2))).set
            "tmp" Val.unit).set "h" hv_new)
        iapply HIH
        isplitl [HoutHK]
        · iexact HoutHK
        iexists (ys ++ [xh]); iexists xs'; iexists hv_new
        isplitr
        · ipure_intro
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc] using hsplit
          · simp [agar_eval, hinput]
          · simp [agar_eval, hhelper]
          · simp [agar_eval]
          · rw [processNGE_append]
            simp [agar_eval]
        isplitl [HPi_new]
        · iexact HPi_new
        isplitl [HLi_new]
        · iexact HLi_new
        rw [processNGE_append]
        unfold helperAfter
        iexact HShFinal
  case HE =>
    iintro ⟨%hgfalse, HI⟩
    icases HI with ⟨HoutHK, %ys, %zs, %hv, %hpure, HPi, HLi, HSh⟩
    obtain ⟨hsplit, hinput, hhelper, hh, hresult⟩ := hpure
    cases zs with
    | nil =>
        icases HLi with %hhv
        subst hhv
        rw [List.append_nil] at hsplit
        subst hsplit
        wp_lstep
        cases hcont : cont with
        | nil =>
            iapply (wp_ret_pop_nil _ _ (Expr.var "result")
              (Val.int (sumNGE ys)) [] _ _ _ _ _
              (heval := by simp [agar_eval]; simpa [sumNGE] using hresult))
            iintro !>
            unfold sumNGEProc_post
            iapply HoutHK
            isplitl [HPi]
            · iapply tstack_nil_intro; iexact HPi
            iexists (processNGE ys).2
            iexact HSh
        | cons s cs =>
            iapply (wp_ret_pop_cons _ _ (Expr.var "result")
              (Val.int (sumNGE ys)) [] _ _ _ _ _ _ _
              (heval := by simp [agar_eval]; simpa [sumNGE] using hresult))
            iintro !>
            unfold sumNGEProc_post
            iapply HoutHK
            isplitl [HPi]
            · iapply tstack_nil_intro; iexact HPi
            iexists (processNGE ys).2
            iexact HSh
    | cons xh xs' =>
        icases HLi with ⟨%l, %hhv, %nx, HC, HT⟩
        exfalso
        subst hhv
        have hbeq : Val.beq (Val.loc l) (Val.int 0) = false := by simp [Val.beq]
        simp [agar_eval, hh, BEq.beq, hbeq] at hgfalse
  isplitl [HK]
  · iexact HK
  iexists []; iexists xs; iexists hv0
  isplitr
  · ipure_intro
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [agar_eval]
    · simp [agar_eval]
    · simp [agar_eval]
    · simp [agar_eval, processNGE]
  isplitl [HPi]
  · iexact HPi
  isplitl [HLi]
  · iexact HLi
  simp only [processNGE, List.foldl_nil]
  iexact HShelper

/-! ## Closed programs with adequacy

Each `progSumNextGreaterK` allocates two heap cells, populates one as
an `input` Treiber stack with a literal push sequence, and runs
`sumNGEProc(input, helper)` against it. The `helper` cell starts at
sentinel `0`, which `sumNGEProc_spec` consumes as `tstack [] helper`.

Pushes happen in *reverse* of the desired top-to-bottom order:
`push a; push b; push c` yields the stack `[c, b, a]` (top → bottom).
`sumNGEProc` then pops in that order — so the *pop sequence* equals
the top-to-bottom stack contents, and the `xs` argument supplied to
`sumNGEProc_spec` is that same list.

### `progSumNextGreater` — 2 elements

Push order `1, 3` → stack `[3, 1]` (top → bottom) → pop sequence `3, 1`.

| pop | helper before | drop ≤ x | helper after | addend |
|----:|---------------|----------|--------------|-------:|
| 3   | []            | []       | [3]          | 0      |
| 1   | [3]           | []       | [1,3]        | 3      |

`sumNGE [3, 1] = 0 + 3 = 3`. -/

/-- Procedure table shared by every `progSumNextGreaterK`: the two
Treiber primitives, the inner drain, and the outer driver. -/
def nextGreaterProcs : Name → Option Proc
  | "pushProc"        => some pushProc
  | "popProc"         => some popProc
  | "drainHelperProc" => some drainHelperProc
  | "sumNGEProc"      => some sumNGEProc
  | _                 => none

def progSumNextGreater : Program where
  procs := nextGreaterProcs
  main := ags(
    input  := alloc 0 ;
    helper := alloc 0 ;
    t1     := call pushProc(input, 1) ;
    t2     := call pushProc(input, 3) ;
    r      := call sumNGEProc(input, helper) ;
    return r
  )

theorem progSumNextGreater_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progSumNextGreater (· = (Val.int 3)) := by
  adequacy_with_heap_intro progSumNextGreater (Val.int 3)
  wp_lstep
  wp_alloc_intro lInput HPi
  wp_lstep
  wp_lstep
  wp_alloc_intro lHelper HPh
  wp_lstep
  wp_lstep
  -- Push 1 → input stack: [1]
  iapply (pushProc_spec (hproc := by rfl)
    (xs := []) (stk := lInput) (v := 1) (x := "t1")
    (eStk := Expr.var "input") (eV := age(1))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HPi]
  · iapply tstack_nil_intro; iexact HPi
  iintro HSinput1
  unfold pushProc_post
  wp_lstep
  -- Push 3 → input stack: [3, 1]  (final pop sequence)
  iapply (pushProc_spec (hproc := by rfl)
    (xs := [1]) (stk := lInput) (v := 3) (x := "t2")
    (eStk := Expr.var "input") (eV := age(3))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HSinput1]
  · iexact HSinput1
  iintro HSinput3
  unfold pushProc_post
  wp_lstep
  -- Call sumNGEProc. Pack tstack [] helper inline.
  iapply (sumNGEProc_spec (hproc := by rfl)
    (hdrain := by rfl) (hpush := by rfl) (hpop := by rfl)
    (x := "r") (eInput := Expr.var "input") (eHelper := Expr.var "helper")
    (input := lInput) (helper := lHelper) (xs := [3, 1])
    (hInput := by simp [agar_eval])
    (hHelper := by simp [agar_eval]))
  isplitl [HSinput3]
  · iexact HSinput3
  isplitl [HPh]
  · iapply tstack_nil_intro; iexact HPh
  iintro _Hpost
  unfold sumNGEProc_post
  wp_step
  ipure_intro
  simp [sumNGE, processNGE, stepNGE, addendOf, dropLE, helperAfter]

/-! ### `progSumNextGreater5` — 5 elements

Push order `3, 4, 2, 5, 1` → stack `[1, 5, 2, 4, 3]` (top → bottom)
→ pop sequence `1, 5, 2, 4, 3`. Trace of `sumNGE` (helper shown
top → bottom, addend = top of `helper` after dropping ≤-prefix):

| pop | helper before | drop ≤ x | helper after | addend |
|----:|---------------|----------|--------------|-------:|
| 1   | []            | []       | [1]          | 0      |
| 5   | [1]           | []       | [5]          | 0      |
| 2   | [5]           | [5]      | [2,5]        | 5      |
| 4   | [2,5]         | [5]      | [4,5]        | 5      |
| 3   | [4,5]         | [4,5]    | [3,4,5]      | 4      |

`sumNGE [1, 5, 2, 4, 3] = 0 + 0 + 5 + 5 + 4 = 14`. -/

def progSumNextGreater5 : Program where
  procs := nextGreaterProcs
  main := ags(
    input  := alloc 0 ;
    helper := alloc 0 ;
    t1     := call pushProc(input, 3) ;
    t2     := call pushProc(input, 4) ;
    t3     := call pushProc(input, 2) ;
    t4     := call pushProc(input, 5) ;
    t5     := call pushProc(input, 1) ;
    r      := call sumNGEProc(input, helper) ;
    return r
  )

theorem progSumNextGreater5_closed
    {GF : BundledGFunctors.{0,0,0}} {F : Type _} [UFraction F]
    [InvGpreS GF] [Agar.Logic.AgarGpreS GF F]
    :
    Machine.safe progSumNextGreater5 (· = (Val.int 14)) := by
  adequacy_with_heap_intro progSumNextGreater5 (Val.int 14)
  wp_lstep
  wp_alloc_intro lInput HPi
  wp_lstep
  wp_lstep
  wp_alloc_intro lHelper HPh
  wp_lstep
  wp_lstep
  -- Push 3 → input stack: [3]
  iapply (pushProc_spec (hproc := by rfl)
    (xs := []) (stk := lInput) (v := 3) (x := "t1")
    (eStk := Expr.var "input") (eV := age(3))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HPi]
  · iapply tstack_nil_intro; iexact HPi
  iintro HS1
  unfold pushProc_post
  wp_lstep
  -- Push 4 → input stack: [4, 3]
  iapply (pushProc_spec (hproc := by rfl)
    (xs := [3]) (stk := lInput) (v := 4) (x := "t2")
    (eStk := Expr.var "input") (eV := age(4))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HS1]
  · iexact HS1
  iintro HS2
  unfold pushProc_post
  wp_lstep
  -- Push 2 → input stack: [2, 4, 3]
  iapply (pushProc_spec (hproc := by rfl)
    (xs := [4, 3]) (stk := lInput) (v := 2) (x := "t3")
    (eStk := Expr.var "input") (eV := age(2))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HS2]
  · iexact HS2
  iintro HS3
  unfold pushProc_post
  wp_lstep
  -- Push 5 → input stack: [5, 2, 4, 3]
  iapply (pushProc_spec (hproc := by rfl)
    (xs := [2, 4, 3]) (stk := lInput) (v := 5) (x := "t4")
    (eStk := Expr.var "input") (eV := age(5))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HS3]
  · iexact HS3
  iintro HS4
  unfold pushProc_post
  wp_lstep
  -- Push 1 → input stack: [1, 5, 2, 4, 3]  (final pop sequence)
  iapply (pushProc_spec (hproc := by rfl)
    (xs := [5, 2, 4, 3]) (stk := lInput) (v := 1) (x := "t5")
    (eStk := Expr.var "input") (eV := age(1))
    (hStk := by simp [agar_eval])
    (hV := by simp [agar_eval]))
  isplitl [HS4]
  · iexact HS4
  iintro HS5
  unfold pushProc_post
  wp_lstep
  -- Run sumNGEProc on input stack [1, 5, 2, 4, 3].
  iapply (sumNGEProc_spec (hproc := by rfl)
    (hdrain := by rfl) (hpush := by rfl) (hpop := by rfl)
    (x := "r") (eInput := Expr.var "input") (eHelper := Expr.var "helper")
    (input := lInput) (helper := lHelper) (xs := [1, 5, 2, 4, 3])
    (hInput := by simp [agar_eval])
    (hHelper := by simp [agar_eval]))
  isplitl [HS5]
  · iexact HS5
  isplitl [HPh]
  · iapply tstack_nil_intro; iexact HPh
  iintro _Hpost
  unfold sumNGEProc_post
  wp_step
  ipure_intro
  simp [sumNGE, processNGE, stepNGE, addendOf, dropLE, helperAfter]

end Agar.Logic

module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Std.CoPset
public import Agar.Lang.Syntax
public import Agar.Lang.Semantics
public import Agar.Lang.Notation
public import Agar.Iris.Wp

@[expose] public section

/-! # Variant-B delaboration for `wp` goals

Pretty-prints `Agar.Logic.wp procs fork_post mask thread Φ` as a
multi-line block: `wp <procs>` on one line, indented labeled fields
below. Trivial fields are suppressed:

* `fork_post = iprop(emp)` hides the `fork:` row.
* `mask = CoPset.full` (or `⊤`) hides the `mask:` row.
* `Φ = (fun _ => iprop(emp))` hides the `post:` row.
* `cont = []` hides the `cont:` row.
* `stack = []` hides the `stack:` row.
* `env = Env.empty` or `bindParams _ []` hides the `env:` row.
* `procs` of the form `Foo.procs` (a `Program` projection) renders just
  as `Foo`.

`Env.set` chains are rendered compactly as `⟨"x" ↦ v, "y" ↦ w⟩` via a
dedicated recursive delaborator on `Agar.Env.set`.

The Thread argument is recognised by struct-instance pattern matching;
anything that doesn't fit the shape falls back to the default print.

Implemented as a `delab` (not an `app_unexpander`) so we can emit a
dedicated syntax kind whose declaration doesn't register a new
term-level parser — that would clash with input occurrences of `wp ...`
in proof files. The pattern mirrors iris-lean's `Iris.ProofMode.Display`. -/

namespace Agar.Logic.WpDisplay

open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator
  Lean.PrettyPrinter.Delaborator.SubExpr

/-- One labeled field row under a `wp` display. Declared without `: cat`
so no new term parser is introduced; only the formatter is generated. -/
syntax wpFieldStx := ppDedent(ppLine ident ":" ppHardSpace term)

/-- The multi-line `wp` display. -/
syntax wpDisplayStx := "wp " term:max wpFieldStx*

/-- One `"x" ↦ v` pair inside an env enclosure. -/
syntax envBindStx := term:max " ↦ " term:max

/-- Compact env display: `⟨"x" ↦ v, "y" ↦ w⟩`. No `: cat` annotation,
so no new term parser is introduced. -/
syntax envDisplay := "⟨" envBindStx,* "⟩"

/-! ### Helpers on already-delaborated syntax -/

meta def envIsEmpty? (envS : TSyntax `term) : Bool :=
  match envS with
  | `(Env.empty)               => true
  | `(Agar.Env.empty)         => true
  | `(bindParams [] [])        => true
  | `(bindParams $_ [])        => true
  | `(Agar.bindParams [] [])  => true
  | `(Agar.bindParams $_ [])  => true
  | _                           => false

meta def listIsEmpty? (xs : TSyntax `term) : Bool :=
  match xs with
  | `([]) => true
  | _     => false

meta def maskIsFull? (m : TSyntax `term) : Bool :=
  match m with
  | `(CoPset.full)          => true
  | `(Iris.Std.CoPset.full) => true
  | `(⊤)                    => true
  | _                        => false

meta def postIsTrivial? (p : TSyntax `term) : Bool :=
  match p with
  | `(fun $_ => iprop(emp)) => true
  | _                        => false

meta def forkIsEmp? (f : TSyntax `term) : Bool :=
  match f with
  | `(iprop(emp)) => true
  | _              => false

/-! ### Postcondition syntactic simplification

`wp_strong_adequacy[_bupd]` instantiates `Φ` as `fun v => ⌜φ v⌝` where the
user-supplied `φ` is itself a lambda — yielding the doubly-lambda'd shape
`fun v => iprop(⌜(fun v => …) v⌝)`. Detect that pattern and beta-reduce
the inner application at the syntax level when the outer-bound identifier
is passed as-is to the inner lambda whose binder shares the same name. -/

/-- Substitute occurrences of identifier `from` with identifier `to` in
`stx`. Conservative: walks only `Syntax`, matching identifiers by the
short name (sufficient because our beta-step always renames the same
short name, and binder shadows are also identifier-based at the syntax
level — we don't recurse into inner binders that rebind `from`). -/
meta partial def renameIdent (from_ to_ : Lean.Name) : Lean.Syntax → Lean.Syntax
  | s@(Lean.Syntax.ident _ _ n _) =>
    if n == from_ then Lean.mkIdent to_ else s
  | Lean.Syntax.node info kind args =>
    Lean.Syntax.node info kind (args.map (renameIdent from_ to_))
  | s => s

/-- Strip leading `Term.paren` wrappers. -/
meta partial def stripParens : Lean.Syntax → Lean.Syntax
  | s@(Lean.Syntax.node _ kind args) =>
    if kind == `Lean.Parser.Term.paren then
      -- paren: '(' term ')' or empty; the term sits at index 1.
      if args.size ≥ 2 then stripParens args[1]! else s
    else s
  | s => s

/-- Find the first identifier name appearing in a syntax subtree. -/
meta partial def findFirstIdent : Lean.Syntax → Option Lean.Name
  | Lean.Syntax.ident _ _ n _ => some n
  | Lean.Syntax.node _ _ children => Id.run do
      for c in children do
        if let some n := findFirstIdent c then return some n
      pure none
  | _ => none

/-- Recognise a `fun x => body` lambda, returning `(x, body)`.
The Lean 4 surface tree is `Term.fun #["fun", Term.basicFun #[binders, _,
"=>", body]]`; we reach into the inner `basicFun` for the body. -/
meta def asLambda? (s : Lean.Syntax) : Option (Lean.Name × Lean.Syntax) :=
  match s with
  | Lean.Syntax.node _ kind children =>
    if kind == `Lean.Parser.Term.fun && children.size ≥ 2 then
      let inner := children[1]!
      match inner with
      | Lean.Syntax.node _ _ ichildren =>
        if ichildren.size ≥ 2 then
          let binderBlock := ichildren[0]!
          let body := ichildren[ichildren.size - 1]!
          match findFirstIdent binderBlock with
          | some n => some (n, body)
          | none   => none
        else none
      | _ => none
    else none
  | _ => none

/-- Try to simplify `(fun $x => $body) $arg` to `$body[arg/x]` at the
syntax level. Returns the simplified term, or `none` if the pattern
doesn't match. -/
meta def betaApp? (t : TSyntax `term) : Option (TSyntax `term) :=
  match t.raw with
  | Lean.Syntax.node _ kind args =>
    if kind == `Lean.Parser.Term.app && args.size == 2 then
      let f := stripParens args[0]!
      let argNode := args[1]!
      -- `argNode` may be a `null` wrapper containing the actual args.
      let argSyn :=
        match argNode with
        | Lean.Syntax.node _ k children =>
          if k == `null && children.size == 1 then children[0]! else argNode
        | _ => argNode
      match asLambda? f, argSyn with
      | some (x, body), Lean.Syntax.ident _ _ argName _ =>
          some ⟨renameIdent x argName body⟩
      | _, _ => none
    else none
  | _ => none

/-- Recursively walk `Syntax`, beta-reducing every `(fun x => body) y`
application where `y` is an identifier. -/
meta partial def betaReduceAll : Lean.Syntax → Lean.Syntax
  | s =>
    -- First, recurse into children.
    let s := match s with
      | Lean.Syntax.node info kind args =>
        Lean.Syntax.node info kind (args.map betaReduceAll)
      | other => other
    -- Then attempt a top-level beta step.
    match (⟨s⟩ : TSyntax `term) |> betaApp? with
    | some r => r.raw
    | none   => s

/-- Simplify the post syntax by eagerly beta-reducing redexes of the form
`(fun x => body) y` (with `y` an identifier) anywhere inside. -/
meta def simplifyPost (p : TSyntax `term) :
    Lean.PrettyPrinter.Delaborator.DelabM (TSyntax `term) := do
  return ⟨betaReduceAll p.raw⟩

/-! ### Procedure-table chain recognition

`procTable [("x", X), ("y", Y), …]` reduces to
`fun n => if n = "x" then some X else if n = "y" then some Y else … else none`.
Recognise that exact pattern at the syntax level and re-render it as
`procTable [...]` to match how programs are typically written. -/

/-- Walk an if-then-else chain `if $v = $name then some $proc else $rest`
ending in `none`, collecting `($name, $proc)` pairs. Returns `none` if
the chain doesn't match the expected shape. -/
meta partial def collectProcChain (v : Lean.Name) :
    TSyntax `term → Option (Array (TSyntax `term × TSyntax `term))
  | body =>
    match body with
    | `(none) => some #[]
    | `(if $lhs:ident = $name:str then some $proc else $rest) =>
        if lhs.getId == v then do
          let rest' ← collectProcChain v rest
          some (#[(⟨name.raw⟩, proc)] ++ rest')
        else none
    | _ => none

/-- Try to render `fun $v => if $v = "n1" then some p1 else …` as
`procTable [("n1", p1), …]`. Returns the original syntax if no match. -/
meta def simplifyProcsLambda (p : TSyntax `term) :
    Lean.PrettyPrinter.Delaborator.DelabM (TSyntax `term) := do
  match p with
  | `(fun $v:ident => $body) =>
    match collectProcChain v.getId body with
    | some pairs =>
      if pairs.isEmpty then return p
      let entries : Array (TSyntax `term) ← pairs.mapM fun (n, proc) =>
        `(($n:term, $proc:term))
      let pt := mkIdent (`Agar.Examples.procTable)
      `($pt [$entries,*])
    | none => return p
  | _ => return p

/-- Build an unhygienic Program-literal syntax with the given fields. -/
meta def mkProgramLit (procs main : TSyntax `term) :
    Lean.PrettyPrinter.Delaborator.DelabM (TSyntax `term) := do
  let procsId := mkIdent `procs
  let mainId  := mkIdent `main
  `({ $procsId:ident := $procs, $mainId:ident := $main })

/-- Apply `simplifyProcsLambda`, also descending into a Program literal
`{ procs := …, main := … }` (possibly followed by a `.main` projection)
and rewriting the `procs` field. -/
meta def simplifyProcs (p : TSyntax `term) :
    Lean.PrettyPrinter.Delaborator.DelabM (TSyntax `term) := do
  match p with
  | `({ procs := $procs, main := $main }) => do
    let procs' ← simplifyProcsLambda procs
    mkProgramLit procs' main
  | `({ procs := $procs, main := $main }.main) => do
    let procs' ← simplifyProcsLambda procs
    let lit ← mkProgramLit procs' main
    let mainId := mkIdent `main
    `($lit.$mainId:ident)
  | _ => simplifyProcsLambda p

/-! ### Recursive delaborator for `Env.set` chains

Walks an `Env.set ... (Env.set ... Env.empty x v) y w ...` expression at
the `Expr` level, collecting `(name, value)` pairs, and emits an
`envDisplay` enclosure. Falls back to the default printer (via
`failure`) whenever the chain doesn't terminate in `Env.empty`. -/

meta partial def collectEnvSet
    (acc : Array (TSyntax ``envBindStx)) :
    DelabM (Array (TSyntax ``envBindStx)) := do
  let e ← getExpr
  if e.isAppOfArity ``Agar.Env.set 3 then
    -- Expr layout: ((Env.set ρ) x) v.
    -- withAppArg               → v
    -- withAppFn withAppArg     → x
    -- withAppFn (withAppFn (withAppArg ...)) → recurse on ρ
    let valStx  : TSyntax `term ← withAppArg delab
    let nameStx : TSyntax `term ← withAppFn (withAppArg delab)
    let bind ← `(envBindStx| $nameStx:term ↦ $valStx:term)
    withAppFn (withAppFn (withAppArg (collectEnvSet (acc.push bind))))
  else if e.isConstOf ``Agar.Env.empty then
    return acc
  else
    failure

@[delab app.Agar.Env.set]
meta def delabEnvSet : Delab := do
  let e ← getExpr
  if !e.isAppOfArity ``Agar.Env.set 3 then failure
  let binds ← collectEnvSet #[]
  -- `collectEnvSet` collects outermost-first; reverse for left-to-right.
  let binds := binds.reverse
  let stx ← `(envDisplay| ⟨$binds,*⟩)
  return ⟨stx⟩

/-! ### Frame delaborator

`Frame.mk retVar cont env` renders as
`<"r" : [return r * v] | env: ⟨"n" ↦ 3⟩>`, suppressing the `cont` slot
when it's `[]` and the `env:` slot when the env is empty. -/

/-- A single frame display. -/
syntax frameDisplay :=
  "⟨frame " term:max (ppSpace ":" ppSpace term)? (ppSpace "|env:" ppSpace term)? "⟩"

@[delab app.Agar.Frame.mk]
meta def delabFrame : Delab := do
  let e ← getExpr
  if !e.isAppOfArity ``Agar.Frame.mk 3 then failure
  -- args: retVar, cont, env
  let envS  : TSyntax `term ← withAppArg delab
  let contS : TSyntax `term ← withAppFn (withAppArg delab)
  let rvS   : TSyntax `term ← withAppFn (withAppFn (withAppArg delab))
  let contEmpty := listIsEmpty? contS
  let envEmpty  := envIsEmpty? envS
  let stx ←
    match contEmpty, envEmpty with
    | true,  true  => `(frameDisplay| ⟨frame $rvS:term⟩)
    | false, true  => `(frameDisplay| ⟨frame $rvS:term : $contS:term⟩)
    | true,  false => `(frameDisplay| ⟨frame $rvS:term |env: $envS:term⟩)
    | false, false => `(frameDisplay| ⟨frame $rvS:term : $contS:term |env: $envS:term⟩)
  return ⟨stx⟩

/-! ### Struct-instance projection for `Thread`

Extracts the `stmt`/`cont`/`env`/`stack` field syntaxes from a
`{ stmt := _, cont := _, env := _, stack := _ }` literal. -/

meta def extractThread? (thread : TSyntax `term) :
    Option (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) :=
  match thread with
  | `({ stmt := $s, cont := $c, env := $e, stack := $st })       => some (s, c, e, st)
  | `({ stmt := $s, cont := $c, env := $e, stack := $st, })      => some (s, c, e, st)
  | _                                                              => none

/-! ### The main delaborator -/

/-- Push a field row with a clean (unhygienic) label. -/
meta def pushField [Monad m] [Lean.MonadQuotation m]
    (fields : Array (TSyntax ``wpFieldStx)) (label : String)
    (val : TSyntax `term) : m (Array (TSyntax ``wpFieldStx)) := do
  let id := mkIdent (Name.mkSimple label)
  let row ← `(wpFieldStx| $id:ident : $val:term)
  return fields.push row

/-- Recognise `Agar.Program.procs <progExpr>` at the Expr level so we can
substitute the program name in place of the inlined `procs` lambda. -/
meta def procsExprAsProgram? (e : Lean.Expr) : Option Lean.Expr :=
  if Lean.Expr.isAppOfArity e ``Agar.Program.procs 1 then
    some (Lean.Expr.appArg! e)
  else
    none

@[delab app.Agar.Logic.wp]
meta def delabWp : Delab := do
  let e ← getExpr
  let n := Lean.Expr.getAppNumArgs e
  -- Fully applied form has 5 explicit args: procs, fork_post, mask, thread, Φ.
  if n < 5 then failure
  -- Detect whether procs is `Program.procs <P>` at the Expr level.
  let procsRawExpr :=
    Lean.Expr.appArg! (Lean.Expr.appFn! (Lean.Expr.appFn! (Lean.Expr.appFn! (Lean.Expr.appFn! e))))
  let useInnerProcs := (procsExprAsProgram? procsRawExpr).isSome
  let procsStx : TSyntax `term ←
    if useInnerProcs then
      -- descend into the inner Program expression beneath `.procs`
      withAppFn (withAppFn (withAppFn (withAppFn (withAppArg (withAppArg delab)))))
    else
      withAppFn (withAppFn (withAppFn (withAppFn (withAppArg delab))))
  let procsStx ← simplifyProcs procsStx
  let forkExpr  : TSyntax `term ← withAppFn (withAppFn (withAppFn (withAppArg delab)))
  let maskExpr  : TSyntax `term ← withAppFn (withAppFn (withAppArg delab))
  let threadExpr: TSyntax `term ← withAppFn (withAppArg delab)
  let postExpr  : TSyntax `term ← withAppArg delab
  -- Bail to default print if the thread isn't a recognised struct literal.
  let some (stmtS, contS, envS, stackS) := extractThread? threadExpr | failure
  let stmtS ← simplifyProcs stmtS
  let mut fields : Array (TSyntax ``wpFieldStx) := #[]
  fields ← pushField fields "stmt" stmtS
  if !envIsEmpty? envS then
    fields ← pushField fields "env" envS
  if !listIsEmpty? contS then
    fields ← pushField fields "cont" contS
  if !listIsEmpty? stackS then
    fields ← pushField fields "stack" stackS
  if !maskIsFull? maskExpr then
    fields ← pushField fields "mask" maskExpr
  if !postIsTrivial? postExpr then
    let postExpr ← simplifyPost postExpr
    fields ← pushField fields "post" postExpr
  if !forkIsEmp? forkExpr then
    fields ← pushField fields "fork_post" forkExpr
  let stx ← `(wpDisplayStx| wp $procsStx:term $fields*)
  return ⟨stx⟩

end Agar.Logic.WpDisplay

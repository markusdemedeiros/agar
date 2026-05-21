module

public import Agar.Lang.Syntax

@[expose] public section

/-! # Surface syntax for Agar

Quotations `age(...)` (expression) and `ags(...)` (statement). Identifiers
denote program variables; `# t` escapes to a Lean term (typed `Expr` or `Stmt`).
Struct literals/projection/update are not in the surface syntax for now —
build them via `#` escape with `Expr.mk`, `Expr.proj`, `Expr.upd`.
-/

namespace Agar

open Lean

declare_syntax_cat agar_exp
declare_syntax_cat agar_stmt

syntax:max "age(" agar_exp ")" : term
syntax:max "ags(" agar_stmt ")" : term

/-! ## Expression grammar -/

syntax:max "(" agar_exp ")" : agar_exp
syntax:max "#" term:max      : agar_exp
syntax:max num               : agar_exp
syntax:max ident             : agar_exp

syntax:75 "!" agar_exp:75   : agar_exp
syntax:75 "-" agar_exp:75   : agar_exp

syntax:70 agar_exp:70 " * "  agar_exp:71 : agar_exp
syntax:65 agar_exp:65 " + "  agar_exp:66 : agar_exp
syntax:65 agar_exp:65 " - "  agar_exp:66 : agar_exp
syntax:50 agar_exp:51 " = "  agar_exp:51 : agar_exp
syntax:50 agar_exp:51 " != " agar_exp:51 : agar_exp
syntax:50 agar_exp:51 " < "  agar_exp:51 : agar_exp
syntax:35 agar_exp:35 " && " agar_exp:36 : agar_exp
syntax:30 agar_exp:30 " || " agar_exp:31 : agar_exp

/-! ## Statement grammar -/

syntax:max "(" agar_stmt ")" : agar_stmt
syntax:max "{" agar_stmt "}" : agar_stmt
syntax:max "#" term:max       : agar_stmt
syntax:max "skip"             : agar_stmt

-- Each atomic action is a single statement; tokens are split so no atom
-- carries more than one keyword/operator at a time.
syntax:50 ident " := " agar_exp                                  : agar_stmt
syntax:50 ident " := " "load "  agar_exp                         : agar_stmt
syntax:50 "store "  agar_exp:max agar_exp:max                   : agar_stmt
syntax:50 ident " := " "alloc " agar_exp                         : agar_stmt
syntax:50 "free "   agar_exp                                     : agar_stmt
syntax:50 ident " := " "cas "   agar_exp:max agar_exp:max agar_exp:max : agar_stmt
syntax:50 ident " := " "call "  ident "(" agar_exp,* ")"         : agar_stmt
syntax:50 "return "  agar_exp                                    : agar_stmt
syntax:50 "fork "    ident "(" agar_exp,* ")"                    : agar_stmt

syntax:20 "if "    agar_exp " then " agar_stmt:10 " else " agar_stmt:10 : agar_stmt
syntax:20 "if "    agar_exp " then " agar_stmt:10                        : agar_stmt
syntax:20 "while " agar_exp " do "   agar_stmt:10                        : agar_stmt

-- Sequencing: right-associative, lowest precedence.
syntax:10 agar_stmt:11 " ; " agar_stmt:10 : agar_stmt

/-! ## Elaboration: expressions -/

macro_rules
  | `(age(($e)))             => `(age($e))
  | `(age(# $t:term))        => `(($t : Expr))
  | `(age($n:num))           => `(Expr.val (Val.int $n))
  | `(age($x:ident))         => `(Expr.var $(Syntax.mkStrLit x.getId.toString))
  | `(age(! $e))             => `(Expr.un  UnOp.not age($e))
  | `(age(- $e))             => `(Expr.un  UnOp.neg age($e))
  | `(age($a * $b))          => `(Expr.bin BinOp.mul age($a) age($b))
  | `(age($a + $b))          => `(Expr.bin BinOp.add age($a) age($b))
  | `(age($a - $b))          => `(Expr.bin BinOp.sub age($a) age($b))
  | `(age($a = $b))          => `(Expr.bin BinOp.eq  age($a) age($b))
  | `(age($a != $b))         => `(Expr.un  UnOp.not (Expr.bin BinOp.eq age($a) age($b)))
  | `(age($a < $b))          => `(Expr.bin BinOp.lt  age($a) age($b))
  | `(age($a && $b))         => `(Expr.bin BinOp.and age($a) age($b))
  | `(age($a || $b))         => `(Expr.bin BinOp.or  age($a) age($b))

/-! ## Elaboration: statements -/

macro_rules
  | `(ags(($s)))                              => `(ags($s))
  | `(ags({ $s }))                            => `(ags($s))
  | `(ags(# $t:term))                         => `(($t : Stmt))
  | `(ags(skip))                              => `(Stmt.skip)
  | `(ags($x:ident := $e))                    =>
      `(Stmt.assign $(Syntax.mkStrLit x.getId.toString) age($e))
  | `(ags($x:ident := load $e))               =>
      `(Stmt.load $(Syntax.mkStrLit x.getId.toString) age($e))
  | `(ags(store $eL $eV))                     =>
      `(Stmt.store age($eL) age($eV))
  | `(ags($x:ident := alloc $e))              =>
      `(Stmt.alloc $(Syntax.mkStrLit x.getId.toString) age($e))
  | `(ags(free $e))                           =>
      `(Stmt.free age($e))
  | `(ags($x:ident := cas $eL $eO $eN))       =>
      `(Stmt.cas $(Syntax.mkStrLit x.getId.toString) age($eL) age($eO) age($eN))
  | `(ags(return $e))                         =>
      `(Stmt.ret age($e))
  | `(ags($s₁ ; $s₂))                         =>
      `(Stmt.seq ags($s₁) ags($s₂))
  | `(ags(if $e then $s₁ else $s₂))           =>
      `(Stmt.ite age($e) ags($s₁) ags($s₂))
  | `(ags(if $e then $s))                     =>
      `(Stmt.ite age($e) ags($s) Stmt.skip)
  | `(ags(while $e do $s))                    =>
      `(Stmt.whileDo age($e) ags($s))

macro_rules
  | `(ags($x:ident := call $f:ident($args,*))) => do
      let argTerms : Array (TSyntax `term) ←
        args.getElems.mapM fun e => `(age($e))
      `(Stmt.call
          $(Syntax.mkStrLit x.getId.toString)
          $(Syntax.mkStrLit f.getId.toString)
          [$[$argTerms],*])
  | `(ags(fork $f:ident($args,*))) => do
      let argTerms : Array (TSyntax `term) ←
        args.getElems.mapM fun e => `(age($e))
      `(Stmt.fork
          $(Syntax.mkStrLit f.getId.toString)
          [$[$argTerms],*])

/-! ## Unexpanders (delaboration)

Make intermediate WP goals readable by pretty-printing `Expr`/`Stmt`
constructors back to the `age(...)`/`ags(...)` surface syntax.

Pattern (cf. iris-lean's HeapLang notation): each constructor gets an
`@[app_unexpander C]` rule that, on a fully-applied head, rebuilds a
`age`/`ags` quotation. Nested sub-expressions are unpacked via
`unpackExp` / `unpackStmt`: if the child already comes back as
`age(e)`/`ags(s)` we splice in `e`/`s` directly; otherwise we wrap
in `# t` escape syntax. -/

open Lean.PrettyPrinter

meta partial def unpackExp [Monad m] [MonadRef m] [MonadQuotation m] :
    Term → m (TSyntax `agar_exp)
  | `(age($e)) => `(agar_exp| $e)
  | `($t)      => `(agar_exp| # $t)

meta partial def unpackStmt [Monad m] [MonadRef m] [MonadQuotation m] :
    Term → m (TSyntax `agar_stmt)
  | `(ags($s)) => `(agar_stmt| $s)
  | `($t)       => `(agar_stmt| # $t)

@[app_unexpander Expr.var]
meta def unexpExprVar : Unexpander
  | `($_ $s:str) =>
      `(age($(Lean.mkIdent (Name.mkSimple s.getString)):ident))
  | _ => throw ()

@[app_unexpander Expr.val]
meta def unexpExprVal : Unexpander
  | `($_ (Val.int $n:num)) => `(age($n:num))
  | `($_ $v)               => `(age(# $v))
  | _ => throw ()

@[app_unexpander Expr.bin]
meta def unexpExprBin : Unexpander
  | `($_ BinOp.add $a $b) => do `(age($(← unpackExp a) + $(← unpackExp b)))
  | `($_ BinOp.sub $a $b) => do `(age($(← unpackExp a) - $(← unpackExp b)))
  | `($_ BinOp.mul $a $b) => do `(age($(← unpackExp a) * $(← unpackExp b)))
  | `($_ BinOp.eq  $a $b) => do `(age($(← unpackExp a) = $(← unpackExp b)))
  | `($_ BinOp.lt  $a $b) => do `(age($(← unpackExp a) < $(← unpackExp b)))
  | `($_ BinOp.and $a $b) => do `(age($(← unpackExp a) && $(← unpackExp b)))
  | `($_ BinOp.or  $a $b) => do `(age($(← unpackExp a) || $(← unpackExp b)))
  | _ => throw ()

@[app_unexpander Expr.un]
meta def unexpExprUn : Unexpander
  | `($_ UnOp.not $a) => do `(age(! $(← unpackExp a)))
  | `($_ UnOp.neg $a) => do `(age(- $(← unpackExp a)))
  | _ => throw ()

@[app_unexpander Stmt.skip]
meta def unexpStmtSkip : Unexpander
  | `($_) => `(ags(skip))

@[app_unexpander Stmt.assign]
meta def unexpStmtAssign : Unexpander
  | `($_ $x:str $e) => do
      `(ags($(Lean.mkIdent (Name.mkSimple x.getString)):ident := $(← unpackExp e)))
  | _ => throw ()

@[app_unexpander Stmt.load]
meta def unexpStmtLoad : Unexpander
  | `($_ $x:str $e) => do
      `(ags($(Lean.mkIdent (Name.mkSimple x.getString)):ident := load $(← unpackExp e)))
  | _ => throw ()

@[app_unexpander Stmt.store]
meta def unexpStmtStore : Unexpander
  | `($_ $eL $eV) => do `(ags(store $(← unpackExp eL) $(← unpackExp eV)))
  | _ => throw ()

@[app_unexpander Stmt.alloc]
meta def unexpStmtAlloc : Unexpander
  | `($_ $x:str $e) => do
      `(ags($(Lean.mkIdent (Name.mkSimple x.getString)):ident := alloc $(← unpackExp e)))
  | _ => throw ()

@[app_unexpander Stmt.free]
meta def unexpStmtFree : Unexpander
  | `($_ $e) => do `(ags(free $(← unpackExp e)))
  | _ => throw ()

@[app_unexpander Stmt.cas]
meta def unexpStmtCas : Unexpander
  | `($_ $x:str $eL $eO $eN) => do
      `(ags($(Lean.mkIdent (Name.mkSimple x.getString)):ident :=
              cas $(← unpackExp eL) $(← unpackExp eO) $(← unpackExp eN)))
  | _ => throw ()

@[app_unexpander Stmt.ret]
meta def unexpStmtRet : Unexpander
  | `($_ $e) => do `(ags(return $(← unpackExp e)))
  | _ => throw ()

@[app_unexpander Stmt.seq]
meta def unexpStmtSeq : Unexpander
  | `($_ $s₁ $s₂) => do `(ags($(← unpackStmt s₁) ; $(← unpackStmt s₂)))
  | _ => throw ()

@[app_unexpander Stmt.ite]
meta def unexpStmtIte : Unexpander
  | `($_ $e $s₁ Stmt.skip) => do
      `(ags(if $(← unpackExp e) then $(← unpackStmt s₁)))
  | `($_ $e $s₁ $s₂) => do
      `(ags(if $(← unpackExp e) then $(← unpackStmt s₁) else $(← unpackStmt s₂)))
  | _ => throw ()

@[app_unexpander Stmt.whileDo]
meta def unexpStmtWhile : Unexpander
  | `($_ $e $s) => do
      let e' ← unpackExp e
      let s' ← unpackStmt s
      `(ags(while $e' do $s'))
  | _ => throw ()

end Agar

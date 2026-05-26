module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-- `simp` lemma set for unfolding Agar evaluator definitions
(`Expr.eval`, `bindParams`, `Env.set`, `Env.empty`, `BinOp.eval`,
`UnOp.eval`, `evalArgs`). Use as `simp [agar_eval]` in place of the
long ad-hoc list. -/
register_simp_attr agar_eval

/-- `simp` lemma set for rewriting `denote (constructor …) ρ` into its
plain `match`-on-result form. Walks an entire `PureStmt` tree without
leaving stray `denote` calls. Designed for bridging `denote prog` to a
hand-written `StateM Env (Option Unit)` monadic mirror. -/
register_simp_attr denote_norm

/-- `simp` lemma set for rewriting `denoteM (constructor …)` into its
`do`-block / bind form. Monadic analogue of `denote_norm`, intended for
use with `mvcgen` and the `Std.Do.Triple` machinery. -/
register_simp_attr denoteM_norm

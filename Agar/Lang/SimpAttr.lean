module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-- `simp` lemma set for unfolding Agar evaluator definitions
(`Expr.eval`, `bindParams`, `Env.set`, `Env.empty`, `BinOp.eval`,
`UnOp.eval`, `evalArgs`). Use as `simp [agar_eval]` in place of the
long ad-hoc list. -/
register_simp_attr agar_eval

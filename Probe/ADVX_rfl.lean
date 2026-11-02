import ROBINSON_PlusPlus

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

-- ¿El puente `eqc = eqCodeFn` de §0 de EvalLiftcPrf seria `rfl`?
example (a b : Term) : eqc a b = eqCodeFn a b := rfl

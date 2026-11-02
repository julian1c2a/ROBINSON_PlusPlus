import ROBINSON_PlusPlus
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

-- ¿El sexto "puente" de §0 de EvalLiftcPrf es demostrable por `rfl` puro,
-- o realmente necesita el `.symm`?
theorem V4_es_rfl (a b : Term) : eqc a b = eqCodeFn a b := rfl

-- control negativo del arnes dentro de ESTE fichero
-- example (a b : Term) : eqc a b = eqc b a := rfl

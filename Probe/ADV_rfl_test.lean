import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability

-- ¿`formCodeM` y `formCode` son la MISMA constante (defeq)?
example (φ : Formula) : formCodeM φ = formCode φ := rfl

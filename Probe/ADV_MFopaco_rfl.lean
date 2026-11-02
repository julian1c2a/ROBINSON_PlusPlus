/- ADV: verificacion adversarial del puente formCode / formCodeM.
   Si el `rfl` de abajo COMPILA, la afirmacion del agente («no son la misma constante,
   el puente es una induccion») seria una exageracion inofensiva.
   Si FALLA, queda confirmado que el puente `formCodeM_eq` es NECESARIO. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability

namespace ADV_MFopaco_rfl

-- (1) ¿Son la MISMA constante? -- deberia fallar.
example (φ : Formula) : formCodeM φ = formCode φ := rfl

end ADV_MFopaco_rfl

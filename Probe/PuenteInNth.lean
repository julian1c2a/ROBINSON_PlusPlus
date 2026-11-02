/-
  SONDEO EXPRESS: ¿existe ya el puente ÍNDICE ⇄ PERTENENCIA?
  sondeos/SubCodesCritica.lean:1023 lo declara «No existe en el árbol (0 ocurrencias)».
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace PuenteProbe

/-- Copia VERBATIM de `sondeos/SubCodesCritica.lean:1023-1026`, bajo los MISMOS `open`. -/
def ObligacionPuenteInNth : Prop :=
  ∀ w x : Term, Prf (In x w) →
    Prf (Formula.ex (land (lt (.var 0) (liftTerm 0 (lenc w)))
      (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))))

/-- IDENTIDAD DE TÉRMINOS (no diff textual): el cuerpo de la obligación ES `boundedIn`. -/
example (w x : Term) :
    (Formula.ex (land (lt (.var 0) (liftTerm 0 (lenc w)))
      (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))))
      = boundedIn x w := rfl

/-- LA OBLIGACIÓN, DESCARGADA en una línea con producción existente
    (`Meta/BoundedInPrf.lean:321`). -/
theorem puente_DESCARGADA : ObligacionPuenteInNth :=
  fun w x h => prf_mp (prf_boundedIn_of_In x w) h

/-- Y la recíproca también está (bicondicional completo, `w` ABSTRACTO). -/
theorem puente_ida_y_vuelta (w x : Term) :
    Prf (In x w) ↔ Prf (boundedIn x w) :=
  ⟨fun h => prf_mp (prf_boundedIn_of_In x w) h,
   fun h => prf_mp (prf_In_of_boundedIn x w) h⟩

#print axioms puente_DESCARGADA
#print axioms puente_ida_y_vuelta

end PuenteProbe

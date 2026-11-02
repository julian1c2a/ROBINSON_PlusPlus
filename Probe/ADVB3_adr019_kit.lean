/- ADR-019 REAL TEST · destino `Meta/CodeCtorKit.lean` para `binK`/`prf_congr_binK`.
   Importa EXACTAMENTE los dos `import` de CodeCtorKit.lean (lineas 6-7).
   NO importa el barrel `ROBINSON_PlusPlus.Meta`, NO importa CodeCtorKit,
   NO importa nada aguas abajo (LiftcCodePrf, CodeTreeReflect, LineWFEfqPrf...). -/
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf

namespace ADVB3.KitPos

/-- CONTROL 1: CodeCtorKit NO esta importado aqui (si lo estuviera, esto compilaria). -/
example : True := by
  fail_if_success exact (ROBINSON_PlusPlus.Meta.CodeCtorKit.binT 5 zero zero = zero) ▸ trivial
  trivial

/-- §A · `binK` se DEFINE en la posicion de CodeCtorKit. -/
def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- §B · `prf_congr_binK` se PRUEBA en la posicion de CodeCtorKit, prueba byte-a-byte
    la del sondeo: solo `prf_congr_consT` + `prf_refl`. -/
theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- §C · El `binT` de CodeCtorKit, RE-DECLARADO aqui igual que en su modulo, y el
    corolario que ADR-019 pide: el particular sale del general SIN tactica. -/
def binT (m : Nat) (a b : Term) : Term :=
  consT (termCode (numeralM m)) (consT a (consT b (termCode nil)))

theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

theorem prf_congr_binT {m : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (binT m a b =eq binT m a' b') :=
  prf_congr_binK (H := termCode (numeralM m)) ha hb

end ADVB3.KitPos

#print axioms ADVB3.KitPos.prf_congr_binK
#print axioms ADVB3.KitPos.prf_congr_binT

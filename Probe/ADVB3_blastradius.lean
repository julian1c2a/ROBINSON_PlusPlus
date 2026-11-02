/- HALLAZGO DEL VERIFICADOR: el radio de `prf_congr_binT` NO es
   «CodeCtorKit + CodeTreeReflect» (lo que declara el sondeo), sino CUATRO modulos.
   Aqui se COMPILAN los dos call-sites que la medicion omitio. -/
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.LineWFEfqPrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.LiftcCodePrf

namespace ADVB3.Blast

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- CALL-SITE OMITIDO 1 · `LiftcCodePrf.lean:150` — `prf_congr_funccT` ES
    `prf_congr_binT hx hy`, porque `funccT X Y = binT 1 X Y` (`LiftcCodePrf:120`).
    Tambien lo cubre `binK`, luego LiftcCodePrf entra en el radio. -/
example {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') :=
  prf_congr_binK (H := termCode (numeralM 1)) hx hy

/-- CALL-SITE OMITIDO 2 · `LineWFEfqPrf.lean:86` y `:145` — la forma `binT 5 _ _`. -/
example {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binT 5 a b =eq binT 5 a' b') :=
  prf_congr_binK (H := termCode (numeralM 5)) ha hb

/-- Y el general del sondeo reproduce el particular de produccion (su §8). -/
example {m : Nat} {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binT m a b =eq binT m a' b') :=
  prf_congr_binK (H := termCode (numeralM m)) ha hb

end ADVB3.Blast

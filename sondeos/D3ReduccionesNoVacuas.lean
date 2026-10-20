/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO DE CONTROL · las ONCE reducciones de D3 (`d3_prf_of*`) NO son vacuas (T05, ADR‑171)

**Fecha:** 2026‑10‑20 · **Por qué:** T05 de `doc/AUDITORIA-SUELO-2026-10-12.md`, con la decisión del propietario
(ADR‑164): «censa y examina con la lente de vacuidad, si es vacua se retira, si no lo es, se queda con su
clasificación, y se anota si está en el cono». Las dos vacuas, `d3_prf_of_sigma1` y `d3_prf_of_reflect_bounded`, ya
salieron (ADR‑161; su refutación, `sondeos/D3Sigma1Vacuo.lean`, en registro). Quedan ONCE en el build (la auditoría
contaba diez: no veía `d3_prf_of`, la del parámetro `Phic`).

**La lente** (ADR‑067, F1): un teorema con hipótesis es vacuo si la CONJUNCIÓN de sus hipótesis es imposible; no basta
con mirarlas por separado. Lo que la descarta es exhibir un modelo de la conjunción. Aquí se exhibe algo más fuerte:
una PRUEBA de cada hipótesis, todas a la vez, con teoremas del build, y con ellas cada reducción se aplica sin
hipótesis. Si este fichero compila, ninguna de las once es vacua.

**Lo que se usa** (todo del build, sin hipótesis): las dos mitades del cuerpo, `hA_lineWFDotAt` (`Meta/D3BodyPrf.lean`)
y `hB_premsDotAt` (`Meta/PremsBdAllPrf.lean`), que son las que `d3_prf_real` pasa a `d3_prf_of_halves`; y de
`Meta/D3ChainDotPrf.lean`, `hbody_of_halves`, `hbdAllDot_of_hbody`, `hbdAll_of_dotted`, `hPinv_chainOkBPsi`,
`hwP_chainOkBPsi`, `hmatch_chainOkB`, `hPsiId_chainOkBPsiDot`, `DEUDA_chainOkBDot_of_body_only` y
`hC_dot_of_chainOkBDot`; de `Meta/D3InDotPrf.lean`, `hI_dot`; de `Meta/D3DottedPrf.lean`, `hbody_of_atoms`.

**Lo que NO dice:** que las once hagan falta. Las once concluyen lo mismo que `d3_prf_real` (D3), y sus hipótesis son
hoy teoremas: son pasos de la reducción, de REGISTRO (así las clasificó ADR‑134). Seis están en el cono de los
titulares, porque `d3_prf_real` pasa por ellas; cinco no (ADR‑171 tiene la tabla).

Es de CONTROL (`sondeos/CONTROLES.txt`): la CI lo compila en cada push, y un cambio que vuelva imposible alguna de las
hipótesis lo rompe.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.D3DottedPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.D3ChainDotPrf ROBINSON_PlusPlus.Meta.D3BodyPrf ROBINSON_PlusPlus.Meta.PremsBdAllPrf

namespace D3ReduccionesNoVacuas

/-! ## Las hipótesis, probadas -/

/-- `hbody`: el cuerpo del `∀` acotado, de las dos mitades. -/
theorem hbody₀ : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
    provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q)))) :=
  hbody_of_halves hA_lineWFDotAt hB_premsDotAt

/-- `hbdAll` sobre `chainOkBPsi`, del cuerpo dotado. -/
theorem hbdAll₀ : Prf (chainOk nil (.var 0) ⇒
    provFromCode (bdAllCode (tcFn (lenc (.var 0))) (chainOkBPsi (tcFn (.var 0)) (.var 0)))) :=
  hbdAll_of_dotted (hbdAllDot_of_hbody hbody₀)

/-- La obligación `DEUDA_chainOkBDot`. -/
theorem deuda₀ : DEUDA_chainOkBDot := DEUDA_chainOkBDot_of_body_only hbody₀

/-- `hC_dot`: la reflexión punteada del átomo `chainOk`. -/
theorem hC₀ : Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkDot) := hC_dot_of_chainOkBDot deuda₀

/-! ## Las once, aplicadas sin hipótesis -/

theorem testigo_d3_prf_of (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of φ (chainOkBPsi (tcFn (.var 0)) (.var 0)) hPinv_chainOkBPsi hwP_chainOkBPsi hmatch_chainOkB hbdAll₀

theorem testigo_d3_prf_of_chainOkBDot (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkBDot φ deuda₀

theorem testigo_d3_prf_of_hbdAll (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_hbdAll φ hPinv_chainOkBPsi hwP_chainOkBPsi hbdAll₀

theorem testigo_d3_prf_of_two (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_two φ hwP_chainOkBPsi hbdAll₀

theorem testigo_d3_prf_of_body (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_body φ hwP_chainOkBPsi hPsiId_chainOkBPsiDot hbody₀

theorem testigo_d3_prf_of_hbody (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_hbody φ hwP_chainOkBPsi hbody₀

theorem testigo_d3_prf_of_body_only (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_body_only φ hbody₀

theorem testigo_d3_prf_of_halves (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_halves φ hA_lineWFDotAt hB_premsDotAt

theorem testigo_d3_prf_of_dotted (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_dotted φ (hbody_of_atoms φ hC₀ (hI_dot φ))

theorem testigo_d3_prf_of_dotted_atoms (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_dotted_atoms φ hC₀ (hI_dot φ)

theorem testigo_d3_prf_of_chainOkDot (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkDot φ hC₀

end D3ReduccionesNoVacuas

-- (los footprints, para el registro: la base sancionada, como `d3_prf_real`)
#print axioms D3ReduccionesNoVacuas.testigo_d3_prf_of
#print axioms D3ReduccionesNoVacuas.testigo_d3_prf_of_body_only
#print axioms D3ReduccionesNoVacuas.testigo_d3_prf_of_chainOkDot

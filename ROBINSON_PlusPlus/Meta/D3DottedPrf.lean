/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.D3DottedPrf

/-!
## META — NIVEL D real (§33): D3 vía reflexión PUNTEADA (keystone de la ruta B)

`provCodeC' = provFromCode ∘ formCode` codifica el **esquema abierto** (variables como `varc n`),
que para fórmulas abiertas (`p` abstracto en `hbI`/`hbC`) es en general **falso**. La completitud‑Σ₁
provable canónica (Hájek‑Pudlák, Paulson) usa la **notación‑punto** de Feferman: cada variable libre
se sustituye por el **numeral de su valor** (`num = tcFn`). La capa tracked ya construida ES esa
formulación.

**Keystone.** `formCode (provCodeC' φ) = exc (formCode (bodyF φ))` (por `rfl` salvo `numeral 9 = σ⁹0`),
con `bodyF φ := chainOk nil #0 ∧ In ⌜φ⌝ (runFn nil #0)` (`#0 = p`, el testigo del `∃`). Entonces el
`∃`‑intro tracked (`pcc_exIntro_code_open`, testigo `tcFn #0`) lleva la **reflexión PUNTEADA del
cuerpo** —`provFromCode (substfc 0 (tcFn #0) (formCode (bodyF φ)))`— exactamente al target de D3
`provCodeC' (provCodeC' φ)`.

Esto **reduce D3** a `hbody`: la reflexión punteada del cuerpo Δ₀. Vía `prf_substfc_and` +
`pcc_and_intro_code`, `hbody` se descompone en las reflexiones punteadas de los dos átomos
`chainOk nil #0` e `In ⌜φ⌝ (runFn nil #0)` (los `hC_dot`/`hI_dot` — siguiente ladrillo, cuyo 2º
argumento compuesto `runFn nil p` pide la evaluación provable de `runFn`).
-/

/-- El cuerpo Δ₀ de `provCodeC' φ` con `p = #0`: `chainOk nil p ∧ In ⌜φ⌝ (runFn nil p)`. -/
noncomputable def bodyF (φ : Formula) : Formula :=
  land (chainOk nil (.var 0)) (In (formCode φ) (runFn nil (.var 0)))

/-- **Keystone estructural**: `formCode (provCodeC' φ) = exc (formCode (bodyF φ))`.
    (`provCodeC' φ = ∃p. bodyF`, y `formCode` de un `∃` es `exc` del código del cuerpo.) -/
theorem formCode_provCodeC'_eq (φ : Formula) :
    formCode (provCodeC' φ) = exc (formCode (bodyF φ)) := by
  simp only [provCodeC', provFormulaC', bodyF, substFormula, substTerm, substTerms, land,
    chainOk, In, runFn, nil, zero, formCode, exc, numeral, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm, liftTerm_formCode]

/-- **D3 reducida a la reflexión PUNTEADA del cuerpo** (keystone de la ruta B): dada
    `hbody : bodyF φ ⇒ provFromCode (substfc 0 (tcFn #0) (formCode (bodyF φ)))` —la reflexión del
    cuerpo Δ₀ con `p` **dotado** (`num p = tcFn p`)— se obtiene `d3_prf`
    `provCodeC' φ ⇒ provCodeC' (provCodeC' φ)`.

    `∃`‑elim de la hipótesis (testigo `p = #0`) + `pcc_exIntro_code_open` (testigo‑código `tcFn #0`)
    sobre `formCode (bodyF φ)`, cuyo `exc` es `formCode (provCodeC' φ)` por el keystone. -/
theorem d3_prf_of_dotted (φ : Formula)
    (hbody : Prf (bodyF φ ⇒ provFromCode (substfc zero (tcFn (.var 0)) (formCode (bodyF φ))))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_provCodeC']
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceEqDiff, reduceIte, FOL.substTerm_liftTerm, liftTerm_formCode]
  rw [provCodeC'_eq_provFromCode, formCode_provCodeC'_eq]
  have hb : PrfH [bodyF φ] (provFromCode (substfc zero (tcFn (.var 0)) (formCode (bodyF φ)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hbody _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _
    (prf_to_prfH (pcc_exIntro_code_open (formCode (bodyF φ)) (tcFn (.var 0))) _) hb

end ROBINSON_PlusPlus.Meta.D3DottedPrf

export ROBINSON_PlusPlus.Meta.D3DottedPrf (
  bodyF formCode_provCodeC'_eq d3_prf_of_dotted
)

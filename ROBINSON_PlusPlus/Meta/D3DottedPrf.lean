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

/-! ### Descomposición de `hbody` en los dos átomos punteados

`formCode (bodyF φ) = andc (formCode (chainOk nil #0)) (formCode (In ⌜φ⌝ (runFn nil #0)))` (rfl), y
`substfc` distribuye sobre `andc` (`prf_substfc_and`). Así que la reflexión punteada del cuerpo es
`pcc_and_intro_code` de las reflexiones punteadas de los dos átomos. -/

/-- Reflexión punteada de `chainOk nil #0` (código dotado del átomo, `p = #0 ↦ tcFn #0`). -/
abbrev chainOkDot : Term := substfc zero (tcFn (.var 0)) (formCode (chainOk nil (.var 0)))

/-- Reflexión punteada de `In ⌜φ⌝ (runFn nil #0)`. -/
abbrev inDot (φ : Formula) : Term :=
  substfc zero (tcFn (.var 0)) (formCode (In (formCode φ) (runFn nil (.var 0))))

/-- **`hbody` a partir de los dos átomos punteados**: dadas las reflexiones punteadas de
    `chainOk nil #0` (`hC`) e `In ⌜φ⌝ (runFn nil #0)` (`hI`), se obtiene `hbody`.

    Nota (§38): `hI` recibe **también** `chainOk nil #0`. No es gratuito: la reflexión punteada de
    `In` evalúa `carc (nthc p i)` (`pcc_eval_carc_nthc`), y esa evaluación exige que la línea `i` sea
    un `cons`, hecho que sólo provee `chainOk` (`prf_line_is_cons`). En el contexto `[bodyF φ]` ambas
    conjunciones están disponibles, así que pasarlas es inmediato. -/
theorem hbody_of_atoms (φ : Formula)
    (hC : Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkDot))
    (hI : Prf (chainOk nil (.var 0) ⇒
      (In (formCode φ) (runFn nil (.var 0)) ⇒ provFromCode (inDot φ)))) :
    Prf (bodyF φ ⇒ provFromCode (substfc zero (tcFn (.var 0)) (formCode (bodyF φ)))) := by
  refine prf_deduction ?_
  have hc : PrfH [bodyF φ] (chainOk nil (.var 0)) := PrfH_and_elim_left (prfH_hyp_self _)
  have hi : PrfH [bodyF φ] (In (formCode φ) (runFn nil (.var 0))) :=
    PrfH_and_elim_right (prfH_hyp_self _)
  have hCp : PrfH [bodyF φ] (provFromCode chainOkDot) := PrfH.mp _ _ _ (prf_to_prfH hC _) hc
  have hIp : PrfH [bodyF φ] (provFromCode (inDot φ)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hI _) hc) hi
  -- `∧`-intro a nivel de código (pcc_c1_code + dos pcc_mp_code_open, patrón de pcc_reflect_and)
  have step1 : Prf (provFromCode chainOkDot
      ⇒ provFromCode (implc (inDot φ) (andc chainOkDot (inDot φ)))) :=
    prf_mp (pcc_mp_code_open chainOkDot (implc (inDot φ) (andc chainOkDot (inDot φ))))
      (pcc_c1_code chainOkDot (inDot φ))
  have hImplY : PrfH [bodyF φ] (provFromCode (implc (inDot φ) (andc chainOkDot (inDot φ)))) :=
    PrfH.mp _ _ _ (prf_to_prfH step1 _) hCp
  have hYtoAnd : PrfH [bodyF φ]
      (provFromCode (inDot φ) ⇒ provFromCode (andc chainOkDot (inDot φ))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_mp_code_open (inDot φ) (andc chainOkDot (inDot φ))) _) hImplY
  have hand : PrfH [bodyF φ] (provFromCode (andc chainOkDot (inDot φ))) :=
    PrfH.mp _ _ _ hYtoAnd hIp
  -- transporte: `substfc 0 (tcFn #0) (formCode (bodyF φ)) =eq andc chainOkDot (inDot φ)`
  have hbridge : Prf (substfc zero (tcFn (.var 0)) (formCode (bodyF φ))
      =eq andc chainOkDot (inDot φ)) :=
    prf_substfc_and zero (tcFn (.var 0)) (formCode (chainOk nil (.var 0)))
      (formCode (In (formCode φ) (runFn nil (.var 0))))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hbridge)) _) hand

/-- **D3 reducida a las reflexiones punteadas de los DOS átomos** (`chainOk`, `In`): composición de
    `hbody_of_atoms` con `d3_prf_of_dotted`. Es el interfaz que `hC_dot`/`hI_dot` deben cumplir. -/
theorem d3_prf_of_dotted_atoms (φ : Formula)
    (hC : Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkDot))
    (hI : Prf (chainOk nil (.var 0) ⇒
      (In (formCode φ) (runFn nil (.var 0)) ⇒ provFromCode (inDot φ)))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_dotted φ (hbody_of_atoms φ hC hI)

end ROBINSON_PlusPlus.Meta.D3DottedPrf

export ROBINSON_PlusPlus.Meta.D3DottedPrf (
  bodyF formCode_provCodeC'_eq d3_prf_of_dotted
  chainOkDot inDot hbody_of_atoms d3_prf_of_dotted_atoms
)

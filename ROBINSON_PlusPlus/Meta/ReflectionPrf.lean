/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DerivCondPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.ReflectionPrf

/-!
## META — NIVEL D real: hacia D3 finitaria (Σ₁-completitud provable) y Gödel II en `Prf`

Porte de `Meta/Reflection.lean` (ω) al cálculo finitario `Prf`. La D3 finitaria
`d3_prf : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))` se descompone igual que en ω:

* **Combinadores lógicos internos** (`pcc_*_prf`, FÁCILES): de `provCodeC' X` para las
  premisas sale `provCodeC' Y` para la conclusión, vía **`d2_prf`** (D2 finitaria) y
  **`repr_pos'_prf`** (D1 finitaria) sobre los axiomas lógicos del cálculo `Prf`. Versión
  `PrfH` (operan bajo el contexto del `∃`-elim).
* **Núcleo duro** (Σ₁/Δ₀-completitud provable del VERIFICADOR): `Prf (X ⇒ provCodeC' X)`
  para `X = chainOk nil p` y `X = In x L`. Requiere inducción object sobre el testigo.

`d3_prf_of_sigma1` REDUCE `d3_prf` a esos dos lemas (hipótesis `hC`/`hI`), aislando el
núcleo duro claramente especificado (igual que `d3_of_sigma1` en ω; sin `sorry`).
-/

/-! ### Combinadores lógicos internos de la demostrabilidad (versión `PrfH`) -/

/-- **MP interno** en `PrfH` (vía `d2_prf`): de `provCodeC'(A⇒B)` y `provCodeC' A`
    sale `provCodeC' B`. -/
theorem PrfH_pcc_mp {Γ : List Formula} {A B : Formula}
    (h1 : PrfH Γ (provCodeC' (A ⇒ B))) (h2 : PrfH Γ (provCodeC' A)) : PrfH Γ (provCodeC' B) :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (prf_to_prfH (d2_prf A B) Γ) h1) h2

/-- Toda demostración de Hilbert se internaliza (`repr_pos'_prf` = D1), en `PrfH`. -/
theorem PrfH_pcc_prf {Γ : List Formula} {φ : Formula} (h : Prf φ) : PrfH Γ (provCodeC' φ) :=
  prf_to_prfH (repr_pos'_prf h) Γ

/-- **∧-intro interno** en `PrfH` (vía `c1` + dos MP internos). -/
theorem PrfH_pcc_andIntro {Γ : List Formula} {A B : Formula}
    (hA : PrfH Γ (provCodeC' A)) (hB : PrfH Γ (provCodeC' B)) : PrfH Γ (provCodeC' (A ∧ B)) :=
  PrfH_pcc_mp (PrfH_pcc_mp (PrfH_pcc_prf (Prf.incl (Prf₀.c1 A B))) hA) hB

/-- **∃-intro interno** en `PrfH` (vía `q2` + MP interno): de `provCodeC' (A[t])` sale
    `provCodeC' (∃A)`. -/
theorem PrfH_pcc_exIntro {Γ : List Formula} (A : Formula) (t : Term)
    (h : PrfH Γ (provCodeC' (substFormula 0 t A))) : PrfH Γ (provCodeC' (Formula.ex A)) :=
  PrfH_pcc_mp (PrfH_pcc_prf (Prf.incl (Prf₀.q2 A t))) h

/-! ### Reducción de `d3_prf` a la Σ₁-completitud provable del verificador -/

/-- **D3 finitaria reducida**: dadas la **Σ₁-completitud provable** de `chainOk` (`hC`)
    y de `In` (`hI`) —`Prf (X ⇒ provCodeC' X)`—, se obtiene **`d3_prf`**
    `Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))`.

    Elimina el `∃` de la hipótesis (testigo `p = #0`, con `chainOk nil p` e
    `In ⌜φ⌝ (runFn nil p)`); promueve ambos hechos Δ₀ a demostrabilidad (`hC`/`hI`);
    los combina con `PrfH_pcc_andIntro` y los `∃`-introduce con `PrfH_pcc_exIntro`. -/
theorem d3_prf_of_sigma1 (φ : Formula)
    (hC : ∀ p : Term, Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p)))
    (hI : ∀ x L : Term, Prf (In x L ⇒ provCodeC' (In x L))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_provCodeC']
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, liftTerm_formCode]
  -- ctx: [chainOk nil #0 ∧ In ⌜φ⌝ (runFn nil #0)] ; goal: provCodeC' (provCodeC' φ)
  let Γ : List Formula := [land (chainOk nil (.var 0)) (In (formCode φ) (runFn nil (.var 0)))]
  have hChain : PrfH Γ (chainOk nil (.var 0)) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hIn : PrfH Γ (In (formCode φ) (runFn nil (.var 0))) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  have hPC : PrfH Γ (provCodeC' (chainOk nil (.var 0))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hC (.var 0)) _) hChain
  have hPI : PrfH Γ (provCodeC' (In (formCode φ) (runFn nil (.var 0)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hI (formCode φ) (runFn nil (.var 0))) _) hIn
  have hAnd := PrfH_pcc_andIntro hPC hPI
  exact PrfH_pcc_exIntro
    (land (chainOk nil (.var 0)) (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0)))) (.var 0)
    (by simpa only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
          FOL.substTerm_liftTerm] using hAnd)

end ROBINSON_PlusPlus.Meta.ReflectionPrf

export ROBINSON_PlusPlus.Meta.ReflectionPrf (
  PrfH_pcc_mp PrfH_pcc_prf PrfH_pcc_andIntro PrfH_pcc_exIntro d3_prf_of_sigma1
)

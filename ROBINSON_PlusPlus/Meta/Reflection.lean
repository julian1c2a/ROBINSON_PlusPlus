/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DerivCond
import ROBINSON_PlusPlus.Meta.Representability2

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.DerivCond
open ROBINSON_PlusPlus.Meta.Representability2

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Reflection

/-!
## META — NIVEL D real: hacia D3 (Σ₁-completitud provable) y Gödel II

**Estrategia (descomposición de D3).** D3 `⊢ provCodeC' φ ⇒ provCodeC' (provCodeC' φ)`
es la Σ₁-completitud *provable*. El hallazgo clave es que se separa en:

* **Combinadores lógicos internos** (este archivo, FÁCILES): de `⊢ provCodeC' X`
  para las premisas se obtiene `⊢ provCodeC' Y` para la conclusión, usando **D2**
  (`d2`) y **D1** (`repr_pos'`) sobre los axiomas lógicos del cálculo de Hilbert
  (`pcc_mp`, `pcc_andIntro`, `pcc_exIntro`). Honestos (solo D1/D2 + ω-reglas).
* **Núcleo duro** (Σ₁/Δ₀-completitud provable del VERIFICADOR): `⊢ X ⇒ ⊢ provCodeC' X`
  para `X = chainOk nil p` y `X = In x L`. Requiere construir, por inducción object
  sobre el testigo, un código de prueba Hilbert de esos hechos Δ₀ verdaderos. Es la
  internalización de `repr_pos'`/`chainOk_track` un nivel meta más arriba.

`d3_of_sigma1` REDUCE D3 a esos dos lemas de completitud (hipótesis `hC`/`hI`),
dejando el núcleo aislado y claramente especificado. (Sin `sorry`.)
-/

/-! ### Combinadores lógicos internos de la demostrabilidad -/

/-- **MP interno**: de `⊢ provCodeC'(A⇒B)` y `⊢ provCodeC' A` sale `⊢ provCodeC' B`
    (vía `d2`). -/
theorem pcc_mp {A B : Formula} (h1 : axioms ⊢ provCodeC' (A ⇒ B)) (h2 : axioms ⊢ provCodeC' A) :
    axioms ⊢ provCodeC' B :=
  mp (mp (d2 A B) h1) h2

/-- Toda demostración de Hilbert se internaliza (= `repr_pos'`, re-expuesto como
    "axioma lógico interno"). -/
theorem pcc_prf {φ : Formula} (h : Prf φ) : axioms ⊢ provCodeC' φ := repr_pos' h

/-- **∧-intro interno** (vía C1 + dos MP internos). -/
theorem pcc_andIntro {A B : Formula} (hA : axioms ⊢ provCodeC' A) (hB : axioms ⊢ provCodeC' B) :
    axioms ⊢ provCodeC' (A ∧ B) :=
  pcc_mp (pcc_mp (pcc_prf (Prf.incl (Prf₀.c1 A B))) hA) hB

/-- **∃-intro interno** (vía Q2 + MP interno): de `⊢ provCodeC' (A[t])` sale
    `⊢ provCodeC' (∃A)`. -/
theorem pcc_exIntro (A : Formula) (t : Term) (h : axioms ⊢ provCodeC' (substFormula 0 t A)) :
    axioms ⊢ provCodeC' (Formula.ex A) :=
  pcc_mp (pcc_prf (Prf.incl (Prf₀.q2 A t))) h

/-! ### Reducción de D3 a la Σ₁-completitud provable del verificador -/

/-- **D3 reducida**: dadas la **Σ₁-completitud provable** de `chainOk` (`hC`) y de
    `In` (`hI`) —que `⊢ X` implica `⊢ provCodeC' X`—, se obtiene
    **D3** `⊢ provCodeC' φ ⇒ provCodeC' (provCodeC' φ)`.

    Prueba: elimina el `∃` de la hipótesis (testigo `p`, con `⊢ chainOk nil p` y
    `⊢ In ⌜φ⌝ (runFn nil p)`); promueve ambos hechos Δ₀ a demostrabilidad (hC/hI);
    los combina con `pcc_andIntro` (cuerpo del `∃`) y los `∃`-introduce con
    `pcc_exIntro` para concluir `provCodeC' (provCodeC' φ)`. -/
theorem d3_of_sigma1 (φ : Formula)
    (hC : ∀ p : Term, axioms ⊢ chainOk nil p → axioms ⊢ provCodeC' (chainOk nil p))
    (hI : ∀ x L : Term, axioms ⊢ In x L → axioms ⊢ provCodeC' (In x L)) :
    axioms ⊢ (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) := by
  apply Minimal.Axioms.imp_intro; intro hpf
  refine provCodeC'_elim hpf (fun p hpChain hpIn => ?_)
  -- cuerpo `ψ(p) = chainOk nil p ∧ In ⌜φ⌝ (runFn nil p)` es demostrable
  have hψ : axioms ⊢ provCodeC' (land (chainOk nil p) (In (formCode φ) (runFn nil p))) :=
    pcc_andIntro (hC p hpChain) (hI (formCode φ) (runFn nil p) hpIn)
  -- `provCodeC' φ = ∃ (cuerpo)`; `∃`-intro con testigo `p`
  have hbody : provCodeC' φ =
      Formula.ex (land (chainOk nil (.var 0)) (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0)))) := by
    simp [provCodeC', provFormulaC', substFormula, substTerm, substTerms, land, chainOk, In, runFn,
      nil, zero, FOL.substTerm_liftTerm]
  rw [hbody]
  refine pcc_exIntro _ p ?_
  have hsubst : substFormula 0 p (land (chainOk nil (.var 0)) (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0))))
      = land (chainOk nil p) (In (formCode φ) (runFn nil p)) := by
    simp [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
      FOL.substTerm_liftTerm]
  rw [hsubst]
  exact hψ

end ROBINSON_PlusPlus.Meta.Reflection

export ROBINSON_PlusPlus.Meta.Reflection (
  pcc_mp
  pcc_prf
  pcc_andIntro
  pcc_exIntro
  d3_of_sigma1
)

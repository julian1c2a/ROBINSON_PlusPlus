/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
import ROBINSON_PlusPlus.Meta.ReflectionPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.ReflectionPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Sigma1BoundedPrf

/-!
## META — NIVEL D real (§12‑A FASE 3, arranque): D3 reducida a la reflexión de la forma Δ₀

Con la **fase 2 completa** el verificador ya está en forma acotada Δ₀:

* `prf_In_iff_boundedIn`      : `In x L ⇔ boundedIn x L`      (`∃ i < lenc L. nthc L i =eq x`)
* `prf_chainOk_iff_chainOkB`  : `chainOk c p ⇔ chainOkB c p`  (sin acumulador)

Este módulo cierra el **puente arquitectónico** de la fase 3: la D3 reducida
`d3_prf_of_sigma1` pedía la Σ₁‑completitud provable de `In`/`chainOk` (`hI`/`hC`); aquí se
reduce a la de sus **formas acotadas** (`boundedIn`/`chainOkB`), transportando por `pcc_imp`
(que sube implicaciones object a `provCodeC'`, vía D2+D1) a través de las dos direcciones de
los `⇔` de la fase 1/2.

**Payoff:** `d3_prf_of_reflect_bounded` — D3 queda reducida a reflejar las formas **Δ₀ acotadas**.
Ahí es donde entran las fases 3‑4 restantes (reflexión de átomos `<`/`=eq`/`lineWF` vía
`num`/`substfc`‑var‑equations + reflexión de cuantificadores acotados) y la fase 5 (inducción
estructural). Este módulo **no** postula `hbI`/`hbC`: son hipótesis, exactamente como `hI`/`hC`
lo eran en `d3_prf_of_sigma1`.
-/

/-- **Reducción de `hI`**: la Σ₁‑completitud provable de `In` se sigue de la de su forma acotada
    `boundedIn`. Vía las dos direcciones de `prf_In_iff_boundedIn` + `pcc_imp`. -/
theorem prf_hI_of_reflect_boundedIn
    (hbI : ∀ x L : Term, Prf (boundedIn x L ⇒ provCodeC' (boundedIn x L))) :
    ∀ x L : Term, Prf (In x L ⇒ provCodeC' (In x L)) := by
  intro x L
  refine prf_deduction ?_
  -- ctx: [In x L].  In x L → boundedIn x L → provCodeC'(boundedIn x L) → provCodeC'(In x L)
  have hbnd : PrfH [In x L] (boundedIn x L) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x L)) _)
      (prfH_hyp_self _)
  have hpc : PrfH [In x L] (provCodeC' (boundedIn x L)) :=
    PrfH.mp _ _ _ (prf_to_prfH (hbI x L) _) hbnd
  exact PrfH.mp _ _ _
    (prf_to_prfH (pcc_imp (prf_and_elim_right (prf_In_iff_boundedIn x L))) _) hpc

/-- **Reducción de `hC`**: la Σ₁‑completitud provable de `chainOk nil p` se sigue de la de su
    forma acotada `chainOkB nil p`. Vía `prf_chainOk_iff_chainOkB` + `pcc_imp`. -/
theorem prf_hC_of_reflect_chainOkB
    (hbC : ∀ p : Term, Prf (chainOkB nil p ⇒ provCodeC' (chainOkB nil p))) :
    ∀ p : Term, Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p)) := by
  intro p
  refine prf_deduction ?_
  have hbnd : PrfH [chainOk nil p] (chainOkB nil p) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_chainOk_iff_chainOkB nil p)) _)
      (prfH_hyp_self _)
  have hpc : PrfH [chainOk nil p] (provCodeC' (chainOkB nil p)) :=
    PrfH.mp _ _ _ (prf_to_prfH (hbC p) _) hbnd
  exact PrfH.mp _ _ _
    (prf_to_prfH (pcc_imp (prf_and_elim_right (prf_chainOk_iff_chainOkB nil p))) _) hpc

/-- **D3 reducida a la reflexión de la forma Δ₀ ACOTADA** (payoff de la fase 3, arranque):
    dadas la Σ₁‑completitud provable de `chainOkB` (`hbC`) y de `boundedIn` (`hbI`), se obtiene
    `d3_prf`. Compone las dos reducciones con `d3_prf_of_sigma1`.

    A partir de aquí, `hbC`/`hbI` se atacan por reflexión de los **átomos** (`<`, `=eq`, `lineWF`,
    `nthc`, `carc`) con `num`/`substfc`‑var‑equations (fase 3‑4) y por **inducción estructural**
    sobre la forma acotada (fase 5). -/
theorem d3_prf_of_reflect_bounded (φ : Formula)
    (hbC : ∀ p : Term, Prf (chainOkB nil p ⇒ provCodeC' (chainOkB nil p)))
    (hbI : ∀ x L : Term, Prf (boundedIn x L ⇒ provCodeC' (boundedIn x L))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_sigma1 φ (prf_hC_of_reflect_chainOkB hbC) (prf_hI_of_reflect_boundedIn hbI)

end ROBINSON_PlusPlus.Meta.Sigma1BoundedPrf

export ROBINSON_PlusPlus.Meta.Sigma1BoundedPrf (
  prf_hI_of_reflect_boundedIn prf_hC_of_reflect_chainOkB d3_prf_of_reflect_bounded
)

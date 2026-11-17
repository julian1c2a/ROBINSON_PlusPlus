/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf

namespace ROBINSON_PlusPlus.Meta.NumListPrf

/-!
## META — NIVEL D real (D3 vía Σ₁-completitud, §12‑A fase 1): capa numérica de listas en `Prf`

Ecuaciones a nivel `Prf` de la longitud `lenc` y el índice `nthc` de una lista‑código
(re‑derivadas de `Minimal.axioms` vía `prf_ax`+`prf_spec`, patrón `prf_carc_cons`). Son el
cimiento de la caracterización acotada `In x L ⇔ ∃ i < lenc L. nthc L i =eq x`, primer ladrillo
de la Σ₁‑completitud provable estándar (plan `GODEL-D3-TRACKED-DESIGN.md` §12‑A). -/

/-- `lenc nil = 0` en `Prf`. -/
theorem prf_lenc_nil : Prf (lenc nil =eq zero) := by
  have hh := prf_ax (show ax_lenc_nil ∈ axioms by simp [axioms])
  simpa [ax_lenc_nil] using hh

/-- `lenc (cons h t) = σ (lenc t)` en `Prf`. -/
theorem prf_lenc_cons (h t : Term) : Prf (lenc (cons h t) =eq succ (lenc t)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lenc_cons ∈ axioms by simp [axioms])) h) t
  simp [substFormula, substTerm, substTerms, lenc, cons, succ,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `nthc (cons h t) 0 = h` en `Prf`. -/
theorem prf_nthc_zero (h t : Term) : Prf (nthc (cons h t) zero =eq h) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_nthc_zero ∈ axioms by simp [axioms])) h) t
  simp [substFormula, substTerm, substTerms, nthc, cons, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `nthc (cons h t) (σ i) = nthc t i` en `Prf`. -/
theorem prf_nthc_succ (h t i : Term) : Prf (nthc (cons h t) (succ i) =eq nthc t i) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax_nthc_succ ∈ axioms by simp [axioms])) h) t) i
  simp [substFormula, substTerm, substTerms, nthc, cons, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `cons`: la cola, y la forma `X = cons (carc X) (cdrc X)`

✏️ 2026‑11‑18 (ADR‑270): de `Meta/CodeWitnessPrf.lean` (`SinWTs`), donde estaban. Los necesita
`Meta/ListIndAdmisible.lean` (todo código no nulo es un `cons`), que está por debajo de `CodeWitnessPrf`. -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-- La FORMA de un `cons`: `X = cons (carc X) (cdrc X)`. -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

end ROBINSON_PlusPlus.Meta.NumListPrf

export ROBINSON_PlusPlus.Meta.NumListPrf (
  prf_lenc_nil prf_lenc_cons prf_nthc_zero prf_nthc_succ
  -- ✏️ 2026‑11‑18 (ADR‑270): de `Meta/CodeWitnessPrf.lean`
  consOk prf_cdrc_cons prf_consOk_cons
)

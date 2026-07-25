/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CantorMonoPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open FOL

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.StrongInductionPrf

/-!
## META — NIVEL D real: INDUCCIÓN FUERTE en `Prf` (entregable **ii** de la ruta 1a)

Con `prf_cantor_mono` (i‑c) ya se sabe que **sub‑código < código**. Falta el principio que lo
consume: inducción **fuerte** (por curso de valores), derivada de la ordinaria
(`prf_nat_induction`, que es `Prf.ind`) sin axiomas nuevos.

**Destino:** `pcc_eval_substfc` (iii), que recurre sobre los constructores de una fórmula
codificada — o sea sobre sub‑códigos, que son estrictamente menores pero **no** el predecesor.
-/

/-! ### Paso ii.1 — `m < σn ⟹ m ≤ n`

⚠️ **La vía corta.** El camino «natural» es analizar casos sobre el testigo (`k = 0` ⟹ igualdad,
`k = σj` ⟹ desigualdad estricta), pero eso obliga a **anidar** una eliminación de `∃` dentro de
otra ya levantada, con dos niveles de De Bruijn.

No hace falta: del testigo sale directamente `m + k = n`, y `prf_le_self_add` ya dice
`m ≤ m + k`; basta **reescribir el lado derecho**. Una sola eliminación de `∃` y ningún caso. -/

/-- **`m < σn ⟹ m ≤ n`** — discreción del orden, sin análisis de casos. -/
theorem prf_le_of_lt_succ (m n : Term) : Prf (lt m (succ n) ⇒ le m n) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 m) (succ (.var 0)))
      (liftTerm 0 (succ n))) ⇒ le m n) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (succ (liftTerm 0 n))]
      (le (liftTerm 0 m) (liftTerm 0 n))
    -- de `↑m + σ#0 = σ↑n` sale `σ(↑m + #0) = σ↑n`, luego `↑m + #0 = ↑n`
    have hsucc : PrfH [Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (succ (liftTerm 0 n))]
        (succ (add (liftTerm 0 m) (.var 0)) =eq succ (liftTerm 0 n)) :=
      PrfH_eq_trans
        (prf_to_prfH (prf_eq_symm (prf_add_succ_t (liftTerm 0 m) (.var 0))) _)
        (prfH_hyp_self _)
    have heq : PrfH [Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (succ (liftTerm 0 n))]
        (add (liftTerm 0 m) (.var 0) =eq liftTerm 0 n) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj (add (liftTerm 0 m) (.var 0)) (liftTerm 0 n)) _)
        hsucc
    -- y `m ≤ m + k` reescrito por esa igualdad da `m ≤ n`
    exact PrfH_le_subst2 heq (prf_to_prfH (prf_le_self_add (liftTerm 0 m) (.var 0)) _)
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff m (succ n)) (prfH_hyp_self _)))

/-! ### Paso ii.2 — el motivo auxiliar `PSI` y sus lemas de sustitución

Guion de `Full/StrongInduction.lean` portado a `Prf`. `PSI Φ := ∀m. m<#1 ⇒ ↑Φ` es el «curso de
valores». `substFormula_liftFormula` es de nivel FOL (no usa el cálculo) pero vive en `Full`; se
re‑declara aquí para no acoplar `Meta → Full`. -/

/-- `substFormula c s (liftFormula c φ) = φ` — cancelación lift/subst a nivel fórmula (copia local
    de `Full.substFormula_liftFormula`; lema de FOL puro, independiente del cálculo). -/
theorem substFormula_liftFormula (φ : Formula) (c : Nat) (s : Term) :
    substFormula c s (liftFormula c φ) = φ := by
  induction φ generalizing c s with
  | bottom => rfl
  | atom p ts => simp only [liftFormula, substFormula]; rw [FOL.substTerms_liftTerms]
  | eq t u => simp only [liftFormula, substFormula]; rw [FOL.substTerm_liftTerm, FOL.substTerm_liftTerm]
  | impl a b iha ihb => simp only [liftFormula, substFormula]; rw [iha c s, ihb c s]
  | «forall» a iha => simp only [liftFormula, substFormula]; rw [iha (c + 1) (liftTerm 0 s)]
  | and a b iha ihb => simp only [liftFormula, substFormula]; rw [iha c s, ihb c s]
  | or a b iha ihb => simp only [liftFormula, substFormula]; rw [iha c s, ihb c s]
  | ex a iha => simp only [liftFormula, substFormula]; rw [iha (c + 1) (liftTerm 0 s)]

/-- Motivo auxiliar `ψ(k) := ∀m. m < k ⇒ φ(m)` (con `k = #1` libre bajo el binder). -/
def PSI (Φ : Formula) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (.var 1)) (liftFormula 1 Φ))

/-- `ψ(t) = ∀m. m < t ⇒ φ(m)`. -/
theorem psi_at (Φ : Formula) (t : Term) :
    substFormula 0 t (PSI Φ)
      = Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 t)) Φ) := by
  simp only [PSI, substFormula, substTerm, substTerms, lt]
  rw [substFormula_liftFormula]
  simp [substTerm]

/-- **Extracción**: de `ψ(t)` y `m < t` deriva `φ(m)`, a nivel `Prf`. -/
theorem prf_psi_elim (Φ : Formula) (t m : Term)
    (h_psi : Prf (substFormula 0 t (PSI Φ))) (h_lt : Prf (lt m t)) :
    Prf (substFormula 0 m Φ) := by
  rw [psi_at] at h_psi
  have hspec := prf_spec h_psi m
  simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hspec
  exact prf_mp hspec h_lt

/-! ### Paso ii.3a — lift‑swap De Bruijn (`liftFormula (c+1)∘liftFormula c = liftFormula c²`)

La pieza que faltaba para el paso de la inducción: `substFormula 0 (σ#0) (liftFormula 1 (PSI Φ))`
(la forma del paso de `prf_nat_induction`) no reducía porque el lift externo deja
`liftFormula 2 (liftFormula 1 Φ)`, y ningún lema FOL cubría esa disposición (subst por DEBAJO del
lift). Se cierra con este **lift‑swap** + `substFormula_liftFormula`. -/

mutual
/-- Swap de lifts a nivel término (mutual con listas, patrón de `substTerm_liftLift`). -/
theorem liftTerm_swap (t : Term) (c : Nat) :
    liftTerm (c+1) (liftTerm c t) = liftTerm c (liftTerm c t) := by
  cases t with
  | var n =>
      by_cases h : n < c
      · simp [liftTerm, h, show n < c+1 from by omega]
      · simp [liftTerm, h, show ¬ n+1 < c from by omega, show ¬ n+1 < c+1 from by omega]
  | func f ts => simp only [liftTerm]; congr 1; exact liftTerms_swap ts c
/-- Swap de lifts a nivel lista de términos. -/
theorem liftTerms_swap (ts : List Term) (c : Nat) :
    liftTerms (c+1) (liftTerms c ts) = liftTerms c (liftTerms c ts) := by
  cases ts with
  | nil => simp [liftTerms]
  | cons t ts' =>
      simp only [liftTerms, List.cons.injEq]; exact ⟨liftTerm_swap t c, liftTerms_swap ts' c⟩
end

/-- **Swap de lifts a nivel fórmula**: `liftFormula (c+1) (liftFormula c Φ) = liftFormula c (liftFormula c Φ)`. -/
theorem liftFormula_swap (Φ : Formula) (c : Nat) :
    liftFormula (c+1) (liftFormula c Φ) = liftFormula c (liftFormula c Φ) := by
  induction Φ generalizing c with
  | bottom => rfl
  | atom p ts => simp only [liftFormula]; congr 1; exact liftTerms_swap ts c
  | eq a b => simp only [liftFormula]; rw [liftTerm_swap, liftTerm_swap]
  | impl a b iha ihb => simp only [liftFormula]; rw [iha, ihb]
  | «forall» a ih => simp only [liftFormula]; rw [ih]
  | and a b iha ihb => simp only [liftFormula]; rw [iha, ihb]
  | or a b iha ihb => simp only [liftFormula]; rw [iha, ihb]
  | ex a ih => simp only [liftFormula]; rw [ih]

/-- **La reducción del motivo del paso**: `substFormula 0 (σ#0) (liftFormula 1 (PSI Φ)) = ψ(σ#0)`
    con el cuerpo `liftFormula 1 Φ`. Cierra con el lift‑swap + `substFormula_liftFormula`. -/
theorem psi_step_motive (Φ : Formula) :
    substFormula 0 (succ (.var 0)) (liftFormula 1 (PSI Φ))
      = Formula.forall (Formula.impl (lt (.var 0) (succ (.var 1))) (liftFormula 1 Φ)) := by
  simp only [PSI, lt, liftFormula, substFormula, liftTerms, liftTerm, substTerms, substTerm,
    Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, reduceIte, Nat.reduceAdd, Nat.reduceSub, succ]
  rw [liftFormula_swap Φ 1, substFormula_liftFormula]

/-! ### Paso ii.3b — ENSAMBLADURA de `prf_strong_induction` (PENDIENTE, pieza acotada)

Con las piezas ii.1/ii.2/ii.3a **todas verdes**, el teorema final
`prf_strong_induction (Φ) (step : Prf (∀ (PSI Φ ⇒ Φ))) : ∀ t, Prf (substFormula 0 t Φ)`
está a UNA ensambladura. Estructura (traducción de `Full.strong_induction`):
* `hall : Prf (∀ (PSI Φ))` por `prf_nat_induction (PSI Φ)`:
  - **base** ✅ resuelta: `rw [psi_at]`, `Prf.gen`, `lt #0 0 → ⊥` por `prf_not_lt_zero` + `efq`.
  - **paso**: `Prf.gen`, `rw [psi_step_motive]`, `prf_deduction`, `PrfH.gen`, `deduction_aux`.
    GOAL INTERNO EXACTO (verificado con `trace_state`):
      `PrfH [lt #0 (succ #1), liftFormula 0 (PSI Φ)] (liftFormula 1 Φ)`   (#0 = m, #1 = n)
    Falta: `or_elim` del split `prf_le_of_lt_succ #0 #1` (`m<n ∨ m=n`); rama `m<n` extrae de la
    hipótesis `↑(PSI Φ)` vía instanciación bajo contexto; rama `m=n` usa `step` en `#1`. ⚠️ Requiere
    una **variante `PrfH` de `prf_psi_elim`** (el actual es `Prf` cerrado) y matching De Bruijn del
    cuerpo `liftFormula 1 Φ` — trabajo INTERACTIVO, no a ciegas.
* **conclusión** ✅ clara: `intro t; prf_psi_elim Φ (σt) t (prf_spec hall (σt)) (prf_lt_succ_self_cm t)`.
-/

end ROBINSON_PlusPlus.Meta.StrongInductionPrf

export ROBINSON_PlusPlus.Meta.StrongInductionPrf (
  prf_le_of_lt_succ
  substFormula_liftFormula PSI psi_at prf_psi_elim
  liftTerm_swap liftTerms_swap liftFormula_swap psi_step_motive
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.ArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.NatArithPrf

/-!
## META — NIVEL D real (D3 vía Σ₁-completitud, §12‑A): toolkit aritmético de `<` en `Prf`

Hacia la caracterización acotada `In x L ⇔ ∃ i < lenc L. nthc L i =eq x` (§12‑A fase 1b), que
descansa sobre lemas generales de `<` a nivel del cálculo finitario `Prf`. Como `<` se define
`a < b ⇔ ∃k. a + σk = b` (`ax13_lt_def`) y `add` recurre por la derecha (`add a 0 = a`,
`add a (σb) = σ(add a b)`), la identidad izquierda `0 + n = n` **no es teorema de Q**
(independiente sin inducción); se prueba con la regla `Prf.ind`.

Este módulo entrega el **eliminador de inducción natural** `prf_nat_induction` (análogo de
`prf_list_induction`, envolviendo `Prf.ind`) y la **identidad izquierda** `prf_add_zero_left`,
primer cimiento del toolkit. -/

/-- Congruencia de `succ` en `PrfH` (Leibniz object, patrón `PrfH_congr_cons_head`). -/
theorem PrfH_eq_congr_succ {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (succ t₁ =eq succ t₂) := by
  let f : Formula := Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (succ t₁) (succ s) := by
    intro s; simp only [f, succ, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (succ t₁)) Γ)

/-- **Eliminador de inducción natural en `Prf`**: de `Prf (Φ[0])` y
    `Prf (∀n (Φ[n] ⇒ Φ[σn]))` sale `Prf (∀n Φ[n])`. Envuelve `Prf.ind` (regla del verificador). -/
theorem prf_nat_induction (Φ : Formula)
    (base : Prf (substFormula 0 zero Φ))
    (step : Prf (Formula.forall (Formula.impl Φ
              (substFormula 0 (succ (.var 0)) (liftFormula 1 Φ)))))
    : Prf (Formula.forall Φ) :=
  prf_mp (prf_mp (Prf.ind Φ) base) step

/-- **Identidad izquierda de `add`** en `Prf`: `0 + n = n` (por `prf_nat_induction`;
    NO derivable sin inducción). -/
theorem prf_add_zero_left (n : Term) : Prf (add zero n =eq n) := by
  have key : Prf (Formula.forall (Formula.eq (add zero (.var 0)) (.var 0))) := by
    refine prf_nat_induction (Formula.eq (add zero (.var 0)) (.var 0)) ?base ?step
    · show Prf (add zero zero =eq zero)
      exact prf_add_zero_t zero
    · refine Prf.gen _ ?_
      simp only [substFormula, substTerm, substTerms, add, succ, liftFormula, liftTerm, liftTerms,
        zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction ?_
      have ih : PrfH [Formula.eq (add zero (.var 0)) (.var 0)] (add zero (.var 0) =eq (.var 0)) :=
        prfH_hyp_self _
      exact PrfH_eq_trans (prf_to_prfH (prf_add_succ_t zero (.var 0)) _) (PrfH_eq_congr_succ ih)
  have hn := prf_spec key n
  simpa only [substFormula, substTerm, substTerms, add, zero, Nat.reduceEqDiff, Nat.reduceGT,
    reduceIte, if_true, FOL.substTerm_liftTerm] using hn

/-- Normalización De Bruijn de un binder: el parámetro `t` (protegido por `liftTerm 0`)
    vuelve intacto tras `substTerm 0 s (liftTerm 1 ·)` del `step` de `prf_nat_induction`. -/
theorem norm11 (s t : Term) : substTerm 0 s (liftTerm 1 (liftTerm 0 t)) = liftTerm 0 t := by
  rw [(FOL.liftTerm_comm_zero t 0).symm]
  exact FOL.substTerm_liftTerm (liftTerm 0 t) 0 s

/-- **`σm + n = σ(m + n)`** en `Prf` (add por la izquierda; inducción sobre `n`, NO
    derivable sin inducción). -/
theorem prf_add_succ_left (m n : Term) : Prf (add (succ m) n =eq succ (add m n)) := by
  have key : Prf (Formula.forall (Formula.eq
      (add (succ (liftTerm 0 m)) (.var 0)) (succ (add (liftTerm 0 m) (.var 0))))) := by
    refine prf_nat_induction _ ?base ?step
    · simp only [substFormula, substTerm, substTerms, add, succ, zero, Nat.reduceEqDiff,
        reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact prf_eq_trans (prf_add_zero_t (succ m))
        (prf_eq_symm (prf_eq_congr_succ (prf_add_zero_t m)))
    · refine Prf.gen _ ?_
      simp only [substFormula, substTerm, substTerms, add, succ, liftFormula, liftTerm, liftTerms,
        zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, if_true,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift, norm11]
      refine prf_deduction ?_
      have ih : PrfH [Formula.eq (add (succ (liftTerm 0 m)) (.var 0)) (succ (add (liftTerm 0 m) (.var 0)))]
          (add (succ (liftTerm 0 m)) (.var 0) =eq succ (add (liftTerm 0 m) (.var 0))) := prfH_hyp_self _
      exact PrfH_eq_trans (prf_to_prfH (prf_add_succ_t (succ (liftTerm 0 m)) (.var 0)) _)
        (PrfH_eq_trans (PrfH_eq_congr_succ ih)
          (prf_to_prfH (prf_eq_symm (prf_eq_congr_succ (prf_add_succ_t (liftTerm 0 m) (.var 0)))) _))
  have hn := prf_spec key n
  simpa only [substFormula, substTerm, substTerms, add, succ, Nat.reduceEqDiff, Nat.reduceGT,
    reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hn

/-- **`0 < σn`** en `Prf` (testigo `k = n` en `∃k. 0 + σk = σn`, cerrado con
    `prf_add_succ_t` + `prf_add_zero_left`). Patrón `prf_numeral_lt`. -/
theorem prf_zero_lt_succ (n : Term) : Prf (lt zero (succ n)) := by
  have h13 := prf_ax (show ax13_lt_def ∈ axioms by simp [axioms])
  have hiff := prf_spec (prf_spec h13 zero) (succ n)
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  refine prf_iff_mpr hiff ?_
  refine prf_ex_intro n ?_
  simp [substFormula, substTerm, substTerms, add, succ, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  show Prf (add zero (succ n) =eq succ n)
  exact prf_eq_trans (prf_add_succ_t zero n) (prf_eq_congr_succ (prf_add_zero_left n))

end ROBINSON_PlusPlus.Meta.NatArithPrf

export ROBINSON_PlusPlus.Meta.NatArithPrf (
  PrfH_eq_congr_succ prf_nat_induction prf_add_zero_left prf_zero_lt_succ
)

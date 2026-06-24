/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.HilbertDeduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ChainPrf

/-!
## META — NIVEL D real: lemas de cadena a nivel `Prf` (paso 8)

Port de los lemas de compositividad/monotonía de cadenas (`runFn_concat`,
`chainOk_concat`, `In_mono`, …) al cálculo finitario `Prf`, usando la regla
`Prf.listInd` (inducción de listas) vía el eliminador `prf_list_induction`.
Son los ingredientes de `d2_prf` (concatenación de pruebas + `mp` interno).
-/

/-- **Eliminador de inducción de listas en `Prf`**: de `Prf (Φ[nil])` y
    `Prf (∀h∀t (Φ[t] ⇒ Φ[cons h t]))` sale `Prf (∀L Φ[L])`. -/
theorem prf_list_induction (Φ : Formula)
    (base : Prf (substFormula 0 nil Φ))
    (step : Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 Φ)
              (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 Φ)))))))
    : Prf (Formula.forall Φ) :=
  prf_mp (prf_mp (Prf.listInd Φ) base) step

/-! ### Helpers ecuacionales a nivel `PrfH` (para los cuerpos del `step`, que usan la IH) -/

/-- Leibniz en `PrfH`: de `PrfH Γ (t₁ ≐ t₂)` y `PrfH Γ A[t₁]` sale `PrfH Γ A[t₂]`. -/
theorem PrfH_leibniz_subst {Γ : List Formula} {A : Formula} {t₁ t₂ : Term}
    (h : PrfH Γ (t₁ =eq t₂)) (hA : PrfH Γ (substFormula 0 t₁ A)) : PrfH Γ (substFormula 0 t₂ A) :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.leibniz A t₁ t₂)) h) hA

/-- Transitividad de `=eq` en `PrfH`. -/
theorem PrfH_eq_trans {Γ : List Formula} {a b c : Term}
    (h1 : PrfH Γ (a =eq b)) (h2 : PrfH Γ (b =eq c)) : PrfH Γ (a =eq c) := by
  let f : Formula := Formula.eq (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq a s := by
    intro s; simp only [f, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c) ▸ PrfH_leibniz_subst (A := f) h2 ((hS b) ▸ h1)

/-- Congruencia de `cons` en la cola, en `PrfH`. -/
theorem PrfH_congr_cons_tail {Γ : List Formula} {hd t₁ t₂ : Term}
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (cons hd t₁ =eq cons hd t₂) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 hd) (liftTerm 0 t₁)) (cons (liftTerm 0 hd) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons hd t₁) (cons hd s) := by
    intro s; simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (cons hd t₁)) Γ)

/-! ### Lemas de cadena en `Prf` -/

/-- `concat X nil =eq X` en `Prf` (inducción de listas sobre `X`). -/
theorem prf_concat_nil_right (X : Term) : Prf (concat X nil =eq X) := by
  have key : Prf (Formula.forall (Formula.eq (concat (.var 0) nil) (.var 0))) := by
    refine prf_list_induction (Formula.eq (concat (.var 0) nil) (.var 0)) ?base ?step
    · show Prf (concat nil nil =eq nil); exact prf_concat_nil_eq nil
    · refine Prf.gen _ (Prf.gen _ ?_)
      show Prf (Formula.impl (Formula.eq (concat (.var 0) nil) (.var 0))
        (Formula.eq (concat (cons (.var 1) (.var 0)) nil) (cons (.var 1) (.var 0))))
      refine prf_deduction ?_
      have IH : PrfH [Formula.eq (concat (.var 0) nil) (.var 0)]
          (concat (.var 0) nil =eq (.var 0)) := prfH_hyp_self _
      have hcc : PrfH [Formula.eq (concat (.var 0) nil) (.var 0)]
          (concat (cons (.var 1) (.var 0)) nil =eq cons (.var 1) (concat (.var 0) nil)) :=
        prf_to_prfH (prf_concat_cons_eq (.var 1) (.var 0) nil) _
      exact PrfH_eq_trans hcc (PrfH_congr_cons_tail IH)
  have hX := prf_spec key X
  show Prf (concat X nil =eq X)
  simpa [substFormula, substTerm, substTerms, concat, nil, FOL.substTerm_liftTerm] using hX

end ROBINSON_PlusPlus.Meta.ChainPrf

export ROBINSON_PlusPlus.Meta.ChainPrf (prf_list_induction prf_concat_nil_right)

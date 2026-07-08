/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.NatArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.BoundedInPrf

/-!
## META — NIVEL D real (D3 vía Σ₁-completitud, §12‑A fase 1b): caracterización acotada de `In`

Objetivo: **`In x L ⇔ ∃ i < lenc L. nthc L i =eq x`** — poner la pertenencia en forma
**Δ₀ acotada** (∃ acotado sobre índices), primer paso para que la Σ₁‑completitud provable
estándar se aplique al verificador.

**Patrón estructural (lección De Bruijn):** los `∃`‑elim se hacen en **lemas `Prf` autónomos**
(vía `prf_ex_elim_imp`, lift simple) y se aplican con `PrfH.mp` dentro de la inducción; así se
evita `PrfH_ex_elim`, que liftea también el contexto (doble lift).
-/

/-- Fórmula acotada `∃ i < lenc L. nthc L i =eq x` (con `i = #0` bajo el `∃`). -/
def boundedIn (x L : Term) : Formula :=
  Formula.ex (land (lt (.var 0) (liftTerm 0 (lenc L)))
                   (Formula.eq (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 x)))

/-- Clausura De Bruijn de `boundedIn` bajo `liftFormula 0`. NO es defeq: bajo el `∃`, el
    `liftFormula 1` produce `liftTerm 1 (liftTerm 0 ·)` mientras que `boundedIn ↑x ↑L` produce
    `liftTerm 0 (liftTerm 0 ·)`; los iguala `FOL.liftTerm_comm_zero` (teorema, no defeq). -/
theorem liftFormula_boundedIn (x L : Term) :
    liftFormula 0 (boundedIn x L) = boundedIn (liftTerm 0 x) (liftTerm 0 L) := by
  simp only [boundedIn, liftFormula, liftTerm, liftTerms, land, lt, nthc, lenc,
    Nat.reduceAdd, Nat.reduceLT, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

/-! ### Congruencias de `lt` (Leibniz object) -/

/-- Congruencia de `lt` en el 2º argumento (cota). -/
theorem prf_lt_subst2 {a b₁ b₂ : Term} (h : Prf (b₁ =eq b₂)) (hlt : Prf (lt a b₁)) :
    Prf (lt a b₂) := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b₂) ▸ prf_leibniz_subst (A := f) h ((hS b₁) ▸ hlt)

/-- Congruencia de `lt` en el 2º argumento, en `PrfH`. -/
theorem PrfH_lt_subst2 {Γ : List Formula} {a b₁ b₂ : Term} (h : PrfH Γ (b₁ =eq b₂))
    (hlt : PrfH Γ (lt a b₁)) : PrfH Γ (lt a b₂) := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b₂) ▸ PrfH_leibniz_subst (A := f) h ((hS b₁) ▸ hlt)

/-! ### Dirección ⇒ : los dos casos del paso `cons` -/

/-- **Caso cabeza (⇒)**: si `x =eq hd` entonces `boundedIn x (cons hd t)` (testigo `i = 0`).
    `0 < lenc (cons hd t) = σ(lenc t)` (`prf_zero_lt_succ`) y `nthc (cons hd t) 0 = hd = x`. -/
theorem prf_boundedIn_head (x hd t : Term) : Prf ((x =eq hd) ⇒ boundedIn x (cons hd t)) := by
  refine prf_deduction ?_
  refine PrfH_ex_intro zero ?_
  simp only [boundedIn, substFormula, substTerm, substTerms, land, lt, nthc, lenc, cons, nil, zero,
    Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm]
  refine PrfH_and_intro ?_ ?_
  · exact prf_to_prfH
      (prf_lt_subst2 (prf_eq_symm (prf_lenc_cons hd t)) (prf_zero_lt_succ (lenc t))) _
  · exact PrfH_eq_trans (prf_to_prfH (prf_nthc_zero hd t) _) (PrfH_eq_symm (prfH_hyp_self _))

/-- **Caso cola (⇒)**: `boundedIn x t ⇒ boundedIn x (cons hd t)` (testigo `i = σj`).
    `σj < σ(lenc t) = lenc (cons hd t)` (`prf_succ_lt_succ_of_lt`) y
    `nthc (cons hd t) (σj) = nthc t j = x` (`prf_nthc_succ`).
    El `∃`-elim va por `prf_ex_elim_imp` (lift simple). -/
theorem prf_boundedIn_tail (x hd t : Term) : Prf (boundedIn x t ⇒ boundedIn x (cons hd t)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_boundedIn]
  have hlt : PrfH [land (lt (.var 0) (liftTerm 0 (lenc t)))
      (Formula.eq (nthc (liftTerm 0 t) (.var 0)) (liftTerm 0 x))]
      (lt (.var 0) (liftTerm 0 (lenc t))) := PrfH_and_elim_left (prfH_hyp_self _)
  have heq : PrfH [land (lt (.var 0) (liftTerm 0 (lenc t)))
      (Formula.eq (nthc (liftTerm 0 t) (.var 0)) (liftTerm 0 x))]
      (Formula.eq (nthc (liftTerm 0 t) (.var 0)) (liftTerm 0 x)) :=
    PrfH_and_elim_right (prfH_hyp_self _)
  refine PrfH_ex_intro (succ (.var 0)) ?_
  simp only [boundedIn, substFormula, substTerm, substTerms, land, lt, nthc, lenc, cons, succ,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  refine PrfH_and_intro ?_ ?_
  · refine PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_cons (liftTerm 0 hd) (liftTerm 0 t))) _) ?_
    exact PrfH.mp _ _ _
      (prf_to_prfH (prf_succ_lt_succ_of_lt (.var 0) (lenc (liftTerm 0 t))) _) hlt
  · exact PrfH_eq_trans
      (prf_to_prfH (prf_nthc_succ (liftTerm 0 hd) (liftTerm 0 t) (.var 0)) _) heq

end ROBINSON_PlusPlus.Meta.BoundedInPrf

export ROBINSON_PlusPlus.Meta.BoundedInPrf (
  boundedIn prf_lt_subst2 PrfH_lt_subst2 prf_boundedIn_head prf_boundedIn_tail
)

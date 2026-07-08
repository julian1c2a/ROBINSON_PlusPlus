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

/-! ### Predecesor: case-split del índice SIN `∃` (evita el `∃`-elim anidado bajo `PrfH`) -/

/-- `pred (σn) = n` en `Prf` (`ax26_pred_succ`). -/
theorem prf_pred_succ (n : Term) : Prf (pred (succ n) =eq n) := by
  have hh := prf_spec (prf_ax (show ax26_pred_succ ∈ axioms by simp [axioms])) n
  simp [ax26_pred_succ, substFormula, substTerm, substTerms, pred, succ,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- Congruencia de `pred` en `Prf` (Leibniz object). -/
theorem prf_eq_congr_pred {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (pred t₁ =eq pred t₂) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 t₁)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred t₁) (pred s) := by
    intro s; simp only [f, pred, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (pred t₁))

/-- Congruencia de `pred` en `PrfH`. -/
theorem PrfH_eq_congr_pred {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (pred t₁ =eq pred t₂) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 t₁)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred t₁) (pred s) := by
    intro s; simp only [f, pred, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (pred t₁)) Γ)

/-- **`n = 0 ∨ n = σ(pred n)`** en `Prf`. Reformulación de `prf_zero_or_succ` **sin `∃`**
    (usando el predecesor de la teoría), para poder partir por casos un índice dentro de un
    contexto `PrfH` sin recurrir a `PrfH_ex_elim` (doble lift). -/
theorem prf_zero_or_eq_succ_pred (n : Term) :
    Prf (lor (Formula.eq n zero) (Formula.eq n (succ (pred n)))) := by
  have himp : Prf (Formula.ex (Formula.eq (liftTerm 0 n) (succ (.var 0)))
      ⇒ Formula.eq n (succ (pred n))) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (liftTerm 0 n) (succ (.var 0))]
      (Formula.eq (liftTerm 0 n) (succ (pred (liftTerm 0 n))))
    have hp : PrfH [Formula.eq (liftTerm 0 n) (succ (.var 0))]
        (pred (liftTerm 0 n) =eq (.var 0)) :=
      PrfH_eq_trans (PrfH_eq_congr_pred (prfH_hyp_self _))
        (prf_to_prfH (prf_pred_succ (.var 0)) _)
    exact PrfH_eq_trans (prfH_hyp_self _) (PrfH_eq_congr_succ (PrfH_eq_symm hp))
  refine prf_mp (prf_mp (prf_mp (Prf.incl (Prf₀.j3 _ _ _)) (prf_zero_or_succ n)) ?_) ?_
  · exact prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (prfH_hyp_self _))
  · exact prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
      (PrfH.mp _ _ _ (prf_to_prfH himp _) (prfH_hyp_self _)))

/-! ### Dirección ⇐ : base `nil` -/

/-- **Base `nil` (⇐)**: `boundedIn x nil` es falso (`lenc nil = 0`, y `¬ i < 0`). -/
theorem prf_boundedIn_nil (x : Term) : Prf (boundedIn x nil ⇒ Formula.bottom) := by
  refine prf_ex_elim_imp ?_
  show PrfH [land (lt (.var 0) (liftTerm 0 (lenc nil)))
              (Formula.eq (nthc (liftTerm 0 nil) (.var 0)) (liftTerm 0 x))] Formula.bottom
  have hlt0 : PrfH [land (lt (.var 0) (liftTerm 0 (lenc nil)))
      (Formula.eq (nthc (liftTerm 0 nil) (.var 0)) (liftTerm 0 x))] (lt (.var 0) zero) :=
    PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) (PrfH_and_elim_left (prfH_hyp_self _))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hlt0

/-- Congruencia de `lt` en el 1er argumento, en `PrfH`. -/
theorem PrfH_lt_subst1 {Γ : List Formula} {a₁ a₂ b : Term} (h : PrfH Γ (a₁ =eq a₂))
    (hlt : PrfH Γ (lt a₁ b)) : PrfH Γ (lt a₂ b) := by
  let f : Formula := lt (.var 0) (liftTerm 0 b)
  have hS : ∀ s : Term, substFormula 0 s f = lt s b := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS a₂) ▸ PrfH_leibniz_subst (A := f) h ((hS a₁) ▸ hlt)

/-- Congruencia de `nthc` en el índice (2º argumento), en `PrfH`. -/
theorem PrfH_eq_congr_nthc2 {Γ : List Formula} {L i j : Term} (h : PrfH Γ (i =eq j)) :
    PrfH Γ (nthc L i =eq nthc L j) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 L) (liftTerm 0 i)) (nthc (liftTerm 0 L) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc L i) (nthc L s) := by
    intro s; simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS j) ▸ PrfH_leibniz_subst (A := f) h ((hS i) ▸ prf_to_prfH (prf_refl (nthc L i)) Γ)

/-! ### Dirección ⇐ : paso `cons` (descomposición) -/

/-- **Paso `cons` (⇐)**: `boundedIn x (cons hd t) ⇒ (x =eq hd) ∨ boundedIn x t`.
    Case-split del índice `i` con `prf_zero_or_eq_succ_pred` (sin `∃`): si `i = 0`,
    `nthc (cons hd t) 0 = hd`; si `i = σ(pred i)`, el testigo para `t` es `pred i`
    (`prf_lt_of_succ_lt_succ` para la cota, `prf_nthc_succ` para el valor). -/
theorem prf_boundedIn_cons (x hd t : Term) :
    Prf (boundedIn x (cons hd t) ⇒ lor (Formula.eq x hd) (boundedIn x t)) := by
  refine prf_ex_elim_imp ?_
  show PrfH [land (lt (.var 0) (liftTerm 0 (lenc (cons hd t))))
              (Formula.eq (nthc (liftTerm 0 (cons hd t)) (.var 0)) (liftTerm 0 x))]
    (lor (Formula.eq (liftTerm 0 x) (liftTerm 0 hd)) (liftFormula 0 (boundedIn x t)))
  rw [liftFormula_boundedIn]
  let A : Formula := land (lt (.var 0) (liftTerm 0 (lenc (cons hd t))))
    (Formula.eq (nthc (liftTerm 0 (cons hd t)) (.var 0)) (liftTerm 0 x))
  let Z : Formula := Formula.eq (.var 0) zero
  let S : Formula := Formula.eq (.var 0) (succ (pred (.var 0)))
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?_ ?_
  · -- i = 0  ⇒  x = hd
    have hz : PrfH [Z, A] (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hand : PrfH [Z, A] A := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have heq : PrfH [Z, A] (Formula.eq (nthc (liftTerm 0 (cons hd t)) (.var 0)) (liftTerm 0 x)) :=
      PrfH_and_elim_right hand
    have h1 : PrfH [Z, A] (nthc (liftTerm 0 (cons hd t)) (.var 0) =eq liftTerm 0 hd) :=
      PrfH_eq_trans (PrfH_eq_congr_nthc2 hz)
        (prf_to_prfH (prf_nthc_zero (liftTerm 0 hd) (liftTerm 0 t)) _)
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (PrfH_eq_trans (PrfH_eq_symm heq) h1)
  · -- i = σ(pred i)  ⇒  boundedIn x t con testigo `pred i`
    have hs : PrfH [S, A] (Formula.eq (.var 0) (succ (pred (.var 0)))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hand : PrfH [S, A] A := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hlt : PrfH [S, A] (lt (.var 0) (liftTerm 0 (lenc (cons hd t)))) :=
      PrfH_and_elim_left hand
    have heq : PrfH [S, A] (Formula.eq (nthc (liftTerm 0 (cons hd t)) (.var 0)) (liftTerm 0 x)) :=
      PrfH_and_elim_right hand
    refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
    refine PrfH_ex_intro (pred (.var 0)) ?_
    simp only [boundedIn, substFormula, substTerm, substTerms, land, lt, nthc, lenc, pred, cons,
      succ, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
    refine PrfH_and_intro ?_ ?_
    · have h2 : PrfH _ (lt (succ (pred (.var 0))) (succ (lenc (liftTerm 0 t)))) :=
        PrfH_lt_subst2 (prf_to_prfH (prf_lenc_cons (liftTerm 0 hd) (liftTerm 0 t)) _)
          (PrfH_lt_subst1 hs hlt)
      exact PrfH.mp _ _ _
        (prf_to_prfH (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (liftTerm 0 t))) _) h2
    · exact PrfH_eq_trans
        (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_nthc2 hs)
          (prf_to_prfH (prf_nthc_succ (liftTerm 0 hd) (liftTerm 0 t) (pred (.var 0))) _)))
        heq

end ROBINSON_PlusPlus.Meta.BoundedInPrf

export ROBINSON_PlusPlus.Meta.BoundedInPrf (
  boundedIn liftFormula_boundedIn prf_lt_subst2 PrfH_lt_subst2 PrfH_lt_subst1
  PrfH_eq_congr_nthc2
  prf_boundedIn_head prf_boundedIn_tail
  prf_pred_succ prf_eq_congr_pred PrfH_eq_congr_pred prf_zero_or_eq_succ_pred
  prf_boundedIn_nil prf_boundedIn_cons
)

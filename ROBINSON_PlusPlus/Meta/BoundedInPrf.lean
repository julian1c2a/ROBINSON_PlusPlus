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

/-- `liftFormula` atraviesa `boundedIn` (general en el nivel `k`). Vía `liftTerm_comm_zero`. -/
theorem liftFormula_boundedIn_gen (k : Nat) (x L : Term) :
    liftFormula k (boundedIn x L) = boundedIn (liftTerm k x) (liftTerm k L) := by
  simp only [boundedIn, liftFormula, liftTerm, liftTerms, land, lt, nthc, lenc,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

/-- `substFormula` atraviesa `boundedIn`. Vía `FOL.substTerm_lift_comm_zero`. -/
theorem substFormula_boundedIn (v : Nat) (s x L : Term) :
    substFormula v s (boundedIn x L) = boundedIn (substTerm v s x) (substTerm v s L) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [boundedIn, substFormula, substTerm, substTerms, land, lt, nthc, lenc, liftTerm,
    liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

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

/-! ### Ley de sucesor de `<` : `i < σb ⇒ i < b ∨ i = b`

Necesaria para el paso inductivo de la **introducción del `∀` acotado** (`∀i<σb ⇔ ∀i<b ∧ ·(b)`).
El testigo `k` de `i + σk = σb` decide el caso: `k = 0` da `i = b`; `k = σ(pred k)` da `i < b`
(testigo `pred k`). Sin `∃`‑elim interno (usa `prf_zero_or_eq_succ_pred`). -/

/-- Auxiliar: del testigo `k` con `i + σk = σb`, decide `i < b ∨ i = b`. -/
theorem prf_lt_succ_helper (i b k : Term) :
    Prf ((add i (succ k) =eq succ b) ⇒ lor (lt i b) (Formula.eq i b)) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred k) _) ?zc ?sc
  · -- k = 0  ⇒  i = b
    have hk0 := (PrfH.hyp [Formula.eq k zero, add i (succ k) =eq succ b] _ (List.Mem.head _))
    have hadd := (PrfH.hyp [Formula.eq k zero, add i (succ k) =eq succ b] _
      (List.Mem.tail _ (List.Mem.head _)))
    have hadd0 : PrfH [Formula.eq k zero, add i (succ k) =eq succ b]
        (add i (succ zero) =eq succ b) := by
      have hL := PrfH_leibniz_subst
        (A := Formula.eq (add (liftTerm 0 i) (succ (.var 0))) (succ (liftTerm 0 b))) hk0
        (show PrfH _ (substFormula 0 k
          (Formula.eq (add (liftTerm 0 i) (succ (.var 0))) (succ (liftTerm 0 b)))) by
          simpa only [substFormula, substTerm, substTerms, add, succ, Nat.reduceEqDiff,
            Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] using hadd)
      simpa only [substFormula, substTerm, substTerms, add, succ, Nat.reduceEqDiff,
        Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] using hL
    have hcomp : Prf (add i (succ zero) =eq succ i) :=
      prf_eq_trans (prf_add_succ_t i zero)
        (prfH_nil_to_prf (PrfH_eq_congr_succ (prf_to_prfH (prf_add_zero_t i) [])) rfl)
    have hsi : PrfH [Formula.eq k zero, add i (succ k) =eq succ b] (succ i =eq succ b) :=
      PrfH_eq_trans (prf_to_prfH (prf_eq_symm hcomp) _) hadd0
    have hib : PrfH [Formula.eq k zero, add i (succ k) =eq succ b] (Formula.eq i b) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj i b) _) hsi
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 (lt i b) (Formula.eq i b))) hib
  · -- k = σ(pred k)  ⇒  lt i b  (testigo pred k)
    have hks := (PrfH.hyp [Formula.eq k (succ (pred k)), add i (succ k) =eq succ b] _
      (List.Mem.head _))
    have hadd := (PrfH.hyp [Formula.eq k (succ (pred k)), add i (succ k) =eq succ b] _
      (List.Mem.tail _ (List.Mem.head _)))
    have hadd2 : PrfH [Formula.eq k (succ (pred k)), add i (succ k) =eq succ b]
        (add i (succ (succ (pred k))) =eq succ b) := by
      have hL := PrfH_leibniz_subst
        (A := Formula.eq (add (liftTerm 0 i) (succ (.var 0))) (succ (liftTerm 0 b))) hks
        (show PrfH _ (substFormula 0 k
          (Formula.eq (add (liftTerm 0 i) (succ (.var 0))) (succ (liftTerm 0 b)))) by
          simpa only [substFormula, substTerm, substTerms, add, succ, Nat.reduceEqDiff,
            Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] using hadd)
      simpa only [substFormula, substTerm, substTerms, add, succ, Nat.reduceEqDiff,
        Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] using hL
    have hsplit : PrfH [Formula.eq k (succ (pred k)), add i (succ k) =eq succ b]
        (succ (add i (succ (pred k))) =eq succ b) :=
      PrfH_eq_trans (prf_to_prfH (prf_eq_symm (prf_add_succ_t i (succ (pred k)))) _) hadd2
    have hib : PrfH [Formula.eq k (succ (pred k)), add i (succ k) =eq succ b]
        (add i (succ (pred k)) =eq b) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj (add i (succ (pred k))) b) _) hsplit
    have hlt : PrfH [Formula.eq k (succ (pred k)), add i (succ k) =eq succ b] (lt i b) :=
      PrfH_lt_intro i b (pred k) hib
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 (lt i b) (Formula.eq i b))) hlt

/-- **`i < σb ⇒ i < b ∨ i = b`** (ley de sucesor de `<`). -/
theorem prf_lt_succ_split (i b : Term) :
    Prf (lt i (succ b) ⇒ lor (lt i b) (Formula.eq i b)) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 i) (succ (.var 0)))
      (liftTerm 0 (succ b))) ⇒ lor (lt i b) (Formula.eq i b)) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 i) (succ (.var 0))) (succ (liftTerm 0 b))]
      (lor (lt (liftTerm 0 i) (liftTerm 0 b)) (Formula.eq (liftTerm 0 i) (liftTerm 0 b)))
    exact PrfH.mp _ _ _
      (prf_to_prfH (prf_lt_succ_helper (liftTerm 0 i) (liftTerm 0 b) (.var 0)) _)
      (prfH_hyp_self _)
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff i (succ b)) (prfH_hyp_self _)))

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

/-! ### Las dos inducciones de listas y el `⇔` -/

/-- **Dirección ⇒**: `In x L ⇒ ∃ i < lenc L. nthc L i =eq x`. Inducción de listas sobre `L`
    (`prf_list_induction`); base `nil` por explosión, paso `cons` por `ax_L2` + los helpers
    cabeza/cola. El parámetro `x` va con `liftTerm 0` y se normaliza con `norm21`. -/
theorem prf_boundedIn_of_In (x L : Term) : Prf (In x L ⇒ boundedIn x L) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 x) (.var 0))
      (boundedIn (liftTerm 0 x) (.var 0)))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (In x nil) (boundedIn x nil)) :=
        prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq (boundedIn x nil)))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil x) _) (prfH_hyp_self _)))
      simpa only [substFormula, substTerm, substTerms, In, substFormula_boundedIn,
        FOL.substTerm_liftTerm, if_true] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms, In,
        cons, liftFormula_boundedIn_gen, substFormula_boundedIn, norm21,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction (deduction_aux ?_
        (In (liftTerm 1 (liftTerm 0 x)) (cons (.var 1) (.var 0)))
        [Formula.impl (In (liftTerm 1 (liftTerm 0 x)) (.var 0))
          (boundedIn (liftTerm 1 (liftTerm 0 x)) (.var 0))] rfl)
      let X : Term := liftTerm 1 (liftTerm 0 x)
      let IHf : Formula := Formula.impl (In X (.var 0)) (boundedIn X (.var 0))
      let A : Formula := In X (cons (.var 1) (.var 0))
      have hsplit : PrfH [A, IHf] (lor (X =eq (.var 1)) (In X (.var 0))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_iff X (.var 1) (.var 0))) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_head X (.var 1) (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      · exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_tail X (.var 1) (.var 0)) _)
          (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            (PrfH.hyp _ _ (List.Mem.head _)))
  have hL := prf_spec key L
  simpa only [substFormula, substTerm, substTerms, In, substFormula_boundedIn,
    FOL.substTerm_liftTerm, if_true] using hL

/-- **Dirección ⇐**: `(∃ i < lenc L. nthc L i =eq x) ⇒ In x L`. Inducción de listas;
    base `nil` por explosión (`prf_boundedIn_nil`), paso `cons` por `prf_boundedIn_cons`. -/
theorem prf_In_of_boundedIn (x L : Term) : Prf (boundedIn x L ⇒ In x L) := by
  have key : Prf (Formula.forall (Formula.impl (boundedIn (liftTerm 0 x) (.var 0))
      (In (liftTerm 0 x) (.var 0)))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (boundedIn x nil) (In x nil)) :=
        prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq (In x nil)))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_nil x) _) (prfH_hyp_self _)))
      simpa only [substFormula, substTerm, substTerms, In, substFormula_boundedIn,
        FOL.substTerm_liftTerm, if_true] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms, In,
        cons, liftFormula_boundedIn_gen, substFormula_boundedIn, norm21,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction (deduction_aux ?_
        (boundedIn (liftTerm 1 (liftTerm 0 x)) (cons (.var 1) (.var 0)))
        [Formula.impl (boundedIn (liftTerm 1 (liftTerm 0 x)) (.var 0))
          (In (liftTerm 1 (liftTerm 0 x)) (.var 0))] rfl)
      let X : Term := liftTerm 1 (liftTerm 0 x)
      let IHf : Formula := Formula.impl (boundedIn X (.var 0)) (In X (.var 0))
      let A : Formula := boundedIn X (cons (.var 1) (.var 0))
      have hsplit : PrfH [A, IHf] (lor (Formula.eq X (.var 1)) (boundedIn X (.var 0))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_cons X (.var 1) (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · exact PrfH_eq_subst_in (PrfH_congr_cons_head (PrfH.hyp _ _ (List.Mem.head _)))
          (prf_to_prfH (prf_in_cons_head X (.var 0)) _)
      · exact PrfH_in_cons_tail (.var 1)
          (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            (PrfH.hyp _ _ (List.Mem.head _)))
  have hL := prf_spec key L
  simpa only [substFormula, substTerm, substTerms, In, substFormula_boundedIn,
    FOL.substTerm_liftTerm, if_true] using hL

/-- **CARACTERIZACIÓN ACOTADA DE `In`** (§12‑A fase 1b, objetivo):
    `In x L ⇔ ∃ i < lenc L. nthc L i =eq x`. Pone la pertenencia en forma **Δ₀ acotada**. -/
theorem prf_In_iff_boundedIn (x L : Term) : Prf (In x L ⇔ boundedIn x L) :=
  prf_and_intro (prf_boundedIn_of_In x L) (prf_In_of_boundedIn x L)

end ROBINSON_PlusPlus.Meta.BoundedInPrf

export ROBINSON_PlusPlus.Meta.BoundedInPrf (
  boundedIn liftFormula_boundedIn liftFormula_boundedIn_gen substFormula_boundedIn
  prf_lt_subst2 PrfH_lt_subst2 PrfH_lt_subst1 PrfH_eq_congr_nthc2
  prf_boundedIn_head prf_boundedIn_tail
  prf_pred_succ prf_eq_congr_pred PrfH_eq_congr_pred prf_zero_or_eq_succ_pred
  prf_lt_succ_helper prf_lt_succ_split
  prf_boundedIn_nil prf_boundedIn_cons
  prf_boundedIn_of_In prf_In_of_boundedIn prf_In_iff_boundedIn
)

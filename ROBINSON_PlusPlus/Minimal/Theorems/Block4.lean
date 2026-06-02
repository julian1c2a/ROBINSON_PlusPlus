/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block3

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Theorems.Eq
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block3

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4

/-!
## BLOQUE IV — FUNCIÓN DE CANTOR
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 6: Lema de Paridad
-/

-- Helper definition for w*(w+1)
def w_w_plus_1 (w : Term) : Term :=
  mul w (succ w)

-- Teo 6.1: ∀ w, w*(w+1) = w² + w
theorem w_mul_w_plus_one_eq_sq_w_add_w (w : Term) : Γ ⊢ (mul w (succ w) =eq add (sq w) w) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- Define f3 como la fórmula con (liftTerm 0 w) en posiciones fijas y .var 0 como m
  let f3 : Formula := Formula.eq
    (mul (liftTerm 0 w) (succ (.var 0)))
    (add (mul (liftTerm 0 w) (.var 0)) (liftTerm 0 w))
  -- hS3: reducción de substFormula 0 s f3 = fórmula con s
  have hS3 : ∀ s : Term, substFormula 0 s f3 =
      Formula.eq (mul w (succ s)) (add (mul w s) w) := by
    intro s
    simp only [f3, substFormula, mul, succ, add, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  -- hbody_eq: reducción del primer spec de ax9 con w al tipo .forall f3
  have hbody_eq : substFormula 0 w
      (.forall (mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1)))
      = Formula.forall f3 := rfl
  -- Obtenemos ∀m, mul w (succ m) = add (mul w m) w
  have h_forall_f3 : Γ ⊢ Formula.forall f3 := hbody_eq ▸ spec h_ax9 w
  -- Especializamos con m = w y obtenemos la ecuación deseada
  have h_result : Γ ⊢ Formula.eq (mul w (succ w)) (add (mul w w) w) :=
    (hS3 w) ▸ spec h_forall_f3 w
  -- sq w = mul w w por definición
  simp only [sq]
  exact h_result

-- Teo 6.2: mod2(w) = 0 ⇒ ∃ k, w*(w+1) = 2*k
-- Formula body uses liftTerm so that ex_intro is definitionally computable for abstract w.
theorem parity_lemma_case_even (w : Term) :
    Γ ⊢ (mod2 w =eq zero) ⇒ ex (mul (liftTerm 0 w) (succ (liftTerm 0 w)) =eq mul two (.var 0)) := by
  apply Axioms.imp_intro; intro h
  have hS : ∀ s : Term,
      substFormula 0 s (mul (liftTerm 0 w) (succ (liftTerm 0 w)) =eq mul two (.var 0))
      = (mul w (succ w) =eq mul two s) := fun s => by
    simp only [substFormula, substTerm, substTerms, mul, succ, two, one, zero,
               FOL.substTerm_liftTerm, if_true]
  have h17 : Γ ⊢ (add (mul (div2 w) two) (mod2 w) =eq w) := by
    have hh := spec (ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)) w
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, two, one] at hh; exact hh
  have hca : Γ ⊢ (add (mul (div2 w) two) (mod2 w) =eq add (mul (div2 w) two) zero) :=
    eq_congr_add_left h
  have h3 : Γ ⊢ (add (mul (div2 w) two) zero =eq w) := eq_trans hca h17
  have h4 : Γ ⊢ (add (mul (div2 w) two) zero =eq mul (div2 w) two) := by
    have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) (mul (div2 w) two)
    simp [substFormula, substTerm, substTerms, add, mul, div2, two, one] at hh; exact hh
  have h5 : Γ ⊢ (mul (div2 w) two =eq w) := eq_trans h4 h3
  have h6 : Γ ⊢ (mul (div2 w) two =eq mul two (div2 w)) := by
    have hh := spec (spec (ax (by simp [axioms] : ax10_mul_comm ∈ axioms)) (div2 w)) two
    simp [substFormula, substTerm, substTerms, mul, div2, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h7 : Γ ⊢ (mul two (div2 w) =eq w) := eq_trans h6 h5
  have h8 : Γ ⊢ (mul (mul two (div2 w)) (succ w) =eq mul w (succ w)) := eq_congr_mul_right h7
  have h9 : Γ ⊢ (mul (mul two (div2 w)) (succ w) =eq mul two (mul (div2 w) (succ w))) := by
    have hh := spec (spec (spec (ax (by simp [axioms] : ax11_mul_assoc ∈ axioms)) two) (div2 w)) (succ w)
    simp [substFormula, substTerm, substTerms, mul, div2, succ, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h10 : Γ ⊢ (mul w (succ w) =eq mul two (mul (div2 w) (succ w))) := eq_trans h8 h9
  exact ex_intro (mul (div2 w) (succ w)) ((hS (mul (div2 w) (succ w))).symm ▸ h10)

-- Teo 6.3: mod2(w) = 1 ⇒ ∃ k, w*(w+1) = 2*k
theorem parity_lemma_case_odd (w : Term) :
    Γ ⊢ (mod2 w =eq one) ⇒ ex (mul (liftTerm 0 w) (succ (liftTerm 0 w)) =eq mul two (.var 0)) := by
  apply Axioms.imp_intro; intro h
  have hS : ∀ s : Term,
      substFormula 0 s (mul (liftTerm 0 w) (succ (liftTerm 0 w)) =eq mul two (.var 0))
      = (mul w (succ w) =eq mul two s) := fun s => by
    simp only [substFormula, substTerm, substTerms, mul, succ, two, one, zero,
               FOL.substTerm_liftTerm, if_true]
  have h17 : Γ ⊢ (add (mul (div2 w) two) (mod2 w) =eq w) := by
    have hh := spec (ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)) w
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, two, one] at hh; exact hh
  have hca : Γ ⊢ (add (mul (div2 w) two) (mod2 w) =eq add (mul (div2 w) two) one) :=
    eq_congr_add_left h
  have h3 : Γ ⊢ (add (mul (div2 w) two) one =eq w) := eq_trans hca h17
  have h4 : Γ ⊢ (mul (div2 w) two =eq mul two (div2 w)) := by
    have hh := spec (spec (ax (by simp [axioms] : ax10_mul_comm ∈ axioms)) (div2 w)) two
    simp [substFormula, substTerm, substTerms, mul, div2, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h5 : Γ ⊢ (add (mul (div2 w) two) one =eq add (mul two (div2 w)) one) :=
    eq_congr_add_right h4
  have h6 : Γ ⊢ (add (mul two (div2 w)) one =eq w) := eq_trans h5 h3
  have h7 : Γ ⊢ (mul two (succ (div2 w)) =eq add (mul two (div2 w)) two) := by
    have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) two) (div2 w)
    simp [substFormula, substTerm, substTerms, mul, add, succ, div2, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h8 : Γ ⊢ (add (mul two (div2 w)) two =eq succ (add (mul two (div2 w)) one)) := by
    have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) (mul two (div2 w))) one
    simp [substFormula, substTerm, substTerms, add, mul, succ, div2, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h9 : Γ ⊢ (succ (add (mul two (div2 w)) one) =eq succ w) := eq_congr_succ h6
  have h10 : Γ ⊢ (add (mul two (div2 w)) two =eq succ w) := FOL.derive_eq_trans h8 h9
  have h11 : Γ ⊢ (mul two (succ (div2 w)) =eq succ w) := FOL.derive_eq_trans h7 h10
  have h12 : Γ ⊢ (mul (mul two (succ (div2 w))) w =eq mul (succ w) w) := eq_congr_mul_right h11
  have h13 : Γ ⊢ (mul (succ w) w =eq mul w (succ w)) := by
    have hh := spec (spec (ax (by simp [axioms] : ax10_mul_comm ∈ axioms)) (succ w)) w
    simp [substFormula, substTerm, substTerms, mul, succ, FOL.substTerm_liftTerm] at hh; exact hh
  have h14 : Γ ⊢ (mul (mul two (succ (div2 w))) w =eq mul w (succ w)) :=
    FOL.derive_eq_trans h12 h13
  have h15 : Γ ⊢ (mul (mul two (succ (div2 w))) w =eq mul two (mul (succ (div2 w)) w)) := by
    have hh := spec (spec (spec (ax (by simp [axioms] : ax11_mul_assoc ∈ axioms)) two) (succ (div2 w))) w
    simp [substFormula, substTerm, substTerms, mul, succ, div2, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h16 : Γ ⊢ (mul w (succ w) =eq mul two (mul (succ (div2 w)) w)) := eq_trans h14 h15
  exact ex_intro (mul (succ (div2 w)) w) ((hS (mul (succ (div2 w)) w)).symm ▸ h16)

-- Lema P1: ∀ w, ∃ k, w*(w+1) = 2*k
theorem parity_lemma (w : Term) :
    Γ ⊢ ex (mul (liftTerm 0 w) (succ (liftTerm 0 w)) =eq mul two (.var 0)) :=
  or_elim (mod2_range w) (mp (parity_lemma_case_even w)) (mp (parity_lemma_case_odd w))

/-!
### Fase 7: Polinomio de Cantor y Totalidad
-/

-- Teo 7.1 (Lema C1): ∀ x,y, (x+y)*(x+y+1) = (x+y)² + (x+y)
theorem cantor_poly_term1_eq_sq_add (x y : Term) : Γ ⊢ (w_w_plus_1 (add x y) =eq add (sq (add x y)) (add x y)) :=
  w_mul_w_plus_one_eq_sq_w_add_w (add x y)

-- Teo 7.2: ∀ x,y, ∃ k, cantor_poly(x,y) = 2*k
theorem cantor_poly_is_even (x y : Term) :
    Γ ⊢ ex (liftTerm 0 (cantor_poly x y) =eq mul two (.var 0)) := by
  have hS : ∀ s : Term,
      substFormula 0 s (liftTerm 0 (cantor_poly x y) =eq mul two (.var 0))
      = (cantor_poly x y =eq mul two s) := fun s => by
    simp only [substFormula, substTerm, substTerms, mul, succ, two, one, zero,
               FOL.substTerm_liftTerm, if_true]
  have hSp : ∀ k : Term,
      substFormula 0 k (mul (liftTerm 0 (add x y)) (succ (liftTerm 0 (add x y))) =eq mul two (.var 0))
      = (mul (add x y) (succ (add x y)) =eq mul two k) := fun k => by
    simp only [substFormula, substTerm, substTerms, mul, succ, two, one, zero,
               FOL.substTerm_liftTerm, if_true]
  apply ex_elim (parity_lemma (add x y))
  intro k h_raw
  have h_sq : Γ ⊢ (mul (add x y) (succ (add x y)) =eq mul two k) := hSp k ▸ h_raw
  have h_add : Γ ⊢ (add (mul (add x y) (succ (add x y))) (mul two y) =eq add (mul two k) (mul two y)) :=
    eq_congr_add_right h_sq
  have h12 : Γ ⊢ (mul two (add k y) =eq add (mul two k) (mul two y)) := by
    have hh := spec (spec (spec (ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)) two) k) y
    simp [substFormula, substTerm, substTerms, mul, add, two, one,
          FOL.substTerm_liftTerm] at hh; exact hh
  have h_cantor : Γ ⊢ (cantor_poly x y =eq mul two (add k y)) :=
    FOL.derive_eq_trans h_add (eq_symm h12)
  exact ex_intro (add k y) ((hS (add k y)).symm ▸ h_cantor)

-- Teo C2: ∀ x,y, ∃ c, Cantor(x,y,c)  (Totalidad)
theorem cantor_totality (x y : Term) :
    Γ ⊢ ex (mul two (.var 0) =eq liftTerm 0 (cantor_poly x y)) := by
  have hS : ∀ s : Term,
      substFormula 0 s (mul two (.var 0) =eq liftTerm 0 (cantor_poly x y))
      = (mul two s =eq cantor_poly x y) := fun s => by
    simp only [substFormula, substTerm, substTerms, mul, succ, two, one, zero,
               FOL.substTerm_liftTerm, if_true]
  have hS_even : ∀ s : Term,
      substFormula 0 s (liftTerm 0 (cantor_poly x y) =eq mul two (.var 0))
      = (cantor_poly x y =eq mul two s) := fun s => by
    simp only [substFormula, substTerm, substTerms, mul, succ, two, one, zero,
               FOL.substTerm_liftTerm, if_true]
  apply ex_elim (cantor_poly_is_even x y)
  intro k h_raw
  have h_k : Γ ⊢ (cantor_poly x y =eq mul two k) := hS_even k ▸ h_raw
  exact ex_intro k ((hS k).symm ▸ (eq_symm h_k))

/-!
### Fase 8: Inyectividad de Cantor
-/

-- Teo C4: Cantor(x,y,c) ∧ Cantor(x,y,c') ⇒ c = c'
theorem cantor_injective_c (x y c c' : Term) : Γ ⊢ land (is_cantor x y c) (is_cantor x y c') ⇒ (c =eq c') := by
  apply Axioms.imp_intro; intro h_land
  have h_c  := Axioms.and_elim_left h_land
  have h_c' := Axioms.and_elim_right h_land
  have h_eq : Γ ⊢ (mul two c =eq mul two c') :=
    FOL.derive_eq_trans h_c (eq_symm h_c')
  have h28 : Γ ⊢ ((mul two c =eq mul two c') ⇒ (c =eq c')) := by
    have hh := spec (spec teo_2_11 c) c'
    simp [substFormula, substTerm, substTerms, mul, two, one,
          FOL.substTerm_liftTerm] at hh
    exact hh
  exact mp h28 h_eq

end ROBINSON_PlusPlus.Minimal.Theorems.Block4

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4 (
  w_mul_w_plus_one_eq_sq_w_add_w
  parity_lemma_case_even
  parity_lemma_case_odd
  parity_lemma
  cantor_poly_term1_eq_sq_add
  cantor_poly_is_even
  cantor_totality
  cantor_injective_c
)

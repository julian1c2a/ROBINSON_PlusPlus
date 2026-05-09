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
import FOL.Metamath.Deduction

open FOL.FOL
open FOL.Tactics
open FOL.Theorems
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block3

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4

/-!
## BLOQUE IV — FUNCIÓN DE CANTOR
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 6: Lema de Paridad
-/

-- Teo 6.1: ∀ w, w*(w+1) = w² + w
theorem w_mul_w_plus_one_eq_sq_w_add_w (w : Term) : Γ ⊢ mul w (succ w) =eq add (sq w) w := by
  have h_w_plus_1 : Γ ⊢ succ w =eq add w one := spec teo_2_8 (t := w)
  have h_lhs : Γ ⊢ mul w (succ w) =eq mul w (add w one) := eq_congr_mul_left h_w_plus_1
  have h_distrib := spec (spec (spec (ax ax12_mul_distrib) (t := one)) (t := w)) (t := w)
  have h_mul_one := spec teo_2_5 (t := w)
  have h_rhs_expand : Γ ⊢ add (mul w w) (mul w one) =eq add (sq w) w := by
    simp [sq]; exact eq_congr_add_left h_mul_one
  exact eq_trans (eq_trans h_lhs h_distrib) h_rhs_expand

-- Teo 6.2: mod2(w) = 0 ⇒ ∃ k, w*(w+1) = 2*k
theorem parity_lemma_case_even (w : Term) : Γ ⊢ (mod2 w =eq zero) ⇒ ex (mul w (succ w) =eq mul two (.var 0)) := by
  apply deduction_theorem; intro h_mod2_w_eq_zero
  have h_ax17_spec := spec (ax ax17_div_mod_eq) (t := w)
  have h_step1 : Γ ⊢ add (mul (div2 w) two) zero =eq w := eq_trans (eq_congr_add_left h_mod2_w_eq_zero) h_ax17_spec
  have h_lhs_eq_mul : Γ ⊢ add (mul (div2 w) two) zero =eq mul (div2 w) two := spec (ax ax4_add_zero) (t := mul (div2 w) two)
  have h_w_eq_div2w_mul_2 : Γ ⊢ w =eq mul (div2 w) two := eq_trans (eq_symm h_lhs_eq_mul) h_step1
  have h_subst_w : Γ ⊢ mul w (succ w) =eq mul (mul (div2 w) two) (succ w) := eq_congr_mul_right h_w_eq_div2w_mul_2
  have h_assoc := spec (spec (spec (ax ax11_mul_assoc) (t := succ w)) (t := two)) (t := div2 w)
  have h_comm := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 w)
  have h_reorder : Γ ⊢ mul (mul (div2 w) two) (succ w) =eq mul two (mul (div2 w) (succ w)) := by
    have h1 := eq_trans h_assoc (eq_congr_mul_left (eq_symm h_comm))
    exact eq_trans h1 (eq_symm (spec (spec (spec (ax ax11_mul_assoc) (t := succ w)) (t := div2 w)) (t := two)))
  have h_final_eq : Γ ⊢ mul w (succ w) =eq mul two (mul (div2 w) (succ w)) := eq_trans h_subst_w h_reorder
  exact ex_intro (mul (div2 w) (succ w)) h_final_eq

-- Teo 6.3: mod2(w) = 1 ⇒ ∃ k, w*(w+1) = 2*k
theorem parity_lemma_case_odd (w : Term) : Γ ⊢ (mod2 w =eq one) ⇒ ex (mul w (succ w) =eq mul two (.var 0)) := by
  apply deduction_theorem; intro h_mod2_w_eq_one
  have h_ax17_spec := spec (ax ax17_div_mod_eq) (t := w)
  have h_w_eq_div2w_mul_2_add_1 : Γ ⊢ w =eq add (mul (div2 w) two) one := eq_trans (eq_symm (eq_congr_add_left h_mod2_w_eq_one)) (eq_symm h_ax17_spec)
  have h_sw_eq_s_... : Γ ⊢ succ w =eq succ (add (mul (div2 w) two) one) := eq_congr_succ h_w_eq_div2w_mul_2_add_1
  have h_s_X1_eq_X2 (X: Term) : Γ ⊢ succ (add X one) =eq add X two := by
    have h1 := eq_symm (spec teo_2_8 (t := add X one))
    have h2 := eq_congr_add_left (spec teo_1_3)
    have h3 := eq_trans h1 (eq_congr_add_left (eq_symm (spec teo_2_8 (t := X))))
    have h4 := spec (spec (spec ax7_add_assoc (t:=one))(t:=one))(t:=X)
    have h5 := eq_congr_add_right (spec teo_1_3)
    exact eq_trans (eq_trans h3 h4) h5
  have h_sw_eq_div2w2_add_2 : Γ ⊢ succ w =eq add (mul (div2 w) two) two := eq_trans h_sw_eq_s_... (h_s_X1_eq_X2 (mul (div2 w) two))
  have h_distrib := spec (spec (spec ax12_mul_distrib (t:=one))(t:=div2 w))(t:=two)
  have h_mul_one := spec teo_2_6 (t:=two)
  have h_rhs : Γ ⊢ mul two (add (div2 w) one) =eq add (mul two (div2 w)) two := by
    have h1 := eq_congr_add_left (spec teo_2_6 (t:=two))
    exact eq_trans h_distrib (eq_congr_add_left (eq_symm h1))
  have h_comm_mul := spec (spec ax10_mul_comm (t:=div2 w))(t:=two)
  have h_rhs_final : Γ ⊢ mul two (add (div2 w) one) =eq add (mul (div2 w) two) two := eq_trans h_rhs (eq_congr_add_right h_comm_mul)
  have h_sw_eq_2_... : Γ ⊢ succ w =eq mul two (add (div2 w) one) := eq_trans h_sw_eq_div2w2_add_2 (eq_symm h_rhs_final)
  have h_subst_sw : Γ ⊢ mul w (succ w) =eq mul w (mul two (add (div2 w) one)) := eq_congr_mul_left h_sw_eq_2_...
  have h_assoc := spec (spec (spec ax11_mul_assoc (t:=add (div2 w) one))(t:=two))(t:=w)
  have h_comm := spec (spec ax10_mul_comm (t:=two))(t:=w)
  have h_reorder : Γ ⊢ mul w (mul two (add (div2 w) one)) =eq mul two (mul w (add (div2 w) one)) := by
    have h1 := eq_trans h_assoc (eq_congr_mul_left (eq_symm h_comm))
    exact eq_trans h1 (eq_symm (spec (spec (spec ax11_mul_assoc (t:=add (div2 w) one))(t:=w))(t:=two)))
  have h_final_eq : Γ ⊢ mul w (succ w) =eq mul two (mul w (add (div2 w) one)) := eq_trans h_subst_sw h_reorder
  exact ex_intro (mul w (add (div2 w) one)) h_final_eq

-- Lema P1: ∀ w, ∃ k, w*(w+1) = 2*k
theorem parity_lemma (w : Term) : Γ ⊢ ex (mul w (succ w) =eq mul two (.var 0)) := by
  have h_range := spec mod2_range (t := w)
  apply or_elim h_range
  · intro h_mod2_eq_0
    exact parity_lemma_case_even w h_mod2_eq_0
  · intro h_mod2_eq_1
    exact parity_lemma_case_odd w h_mod2_eq_1

end ROBINSON_PlusPlus.Minimal.Theorems.Block4

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4 (
  w_mul_w_plus_one_eq_sq_w_add_w
  parity_lemma_case_even
  parity_lemma_case_odd
  parity_lemma
)

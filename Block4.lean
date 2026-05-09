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

-- Helper definition for w*(w+1)
def w_w_plus_1 (w : Term) : Term :=
  mul w (succ w)

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
theorem parity_lemma_case_even (w : Term) : Γ ⊢ (mod2 w =eq zero) ⇒ ex (w_w_plus_1 w =eq mul two (.var 0)) := by
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
theorem parity_lemma_case_odd (w : Term) : Γ ⊢ (mod2 w =eq one) ⇒ ex (w_w_plus_1 w =eq mul two (.var 0)) := by
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
theorem parity_lemma (w : Term) : Γ ⊢ ex (w_w_plus_1 w =eq mul two (.var 0)) := by
  have h_range := spec mod2_range (t := w)
  apply or_elim h_range
  · intro h_mod2_eq_0
    exact parity_lemma_case_even w h_mod2_eq_0
  · intro h_mod2_eq_1
    exact parity_lemma_case_odd w h_mod2_eq_1

/-!
### Fase 7: Polinomio de Cantor y Totalidad
-/

-- Teo 7.1 (Lema C1): ∀ x,y, (x+y)*(x+y+1) = (x+y)² + (x+y)
theorem cantor_poly_term1_eq_sq_add (x y : Term) : Γ ⊢ w_w_plus_1 (add x y) =eq add (sq (add x y)) (add x y) :=
  w_mul_w_plus_one_eq_sq_w_add_w (add x y)

-- Teo 7.2: ∀ x,y, ∃ k, (x+y)*(x+y+1) + 2*y = 2*k
theorem cantor_poly_is_even (x y : Term) : Γ ⊢ ex (cantor_poly x y =eq mul two (.var 0)) := by
  let w := add x y
  have h_parity := parity_lemma w
  apply ex_elim h_parity; intro j; intro h_ww1_eq_2j
  have h_poly_def : Γ ⊢ cantor_poly x y =eq add (w_w_plus_1 w) (mul two y) := by simp [cantor_poly, w_w_plus_1]
  have h_subst : Γ ⊢ cantor_poly x y =eq add (mul two j) (mul two y) := eq_trans h_poly_def (eq_congr_add_left h_ww1_eq_2j)
  have h_distrib := spec (spec (spec (ax ax12_mul_distrib) (t := y)) (t := j)) (t := two)
  have h_final : Γ ⊢ cantor_poly x y =eq mul two (add j y) := eq_trans h_subst h_distrib
  exact ex_intro (add j y) h_final

-- Teo C2: ∀ x,y, ∃ c, Cantor(x,y,c) (Totalidad)
theorem cantor_totality (x y : Term) : Γ ⊢ ex (is_cantor x y (.var 0)) := by
  have h_poly_even := cantor_poly_is_even x y
  apply ex_elim h_poly_even; intro k; intro h_poly_eq_2k
  -- The goal is `ex (mul two (.var 0) =eq cantor_poly x y)`
  -- We have `cantor_poly x y =eq mul two k`. By symmetry, this is what we need.
  exact ex_intro k (eq_symm h_poly_eq_2k)

/-!
### Fase 8: Inyectividad de Cantor
-/

-- Teo C4: Cantor(x,y,c) ∧ Cantor(x,y,c') ⇒ c = c'
theorem cantor_injective_c (x y c c' : Term) : Γ ⊢ land (is_cantor x y c) (is_cantor x y c') ⇒ (c =eq c') := by
  apply deduction_theorem; intro h_and
  have h_cantor_c : Γ ⊢ is_cantor x y c := and_elim_left h_and
  have h_cantor_c' : Γ ⊢ is_cantor x y c' := and_elim_right h_and
  simp [is_cantor] at h_cantor_c h_cantor_c'
  have h_2c_eq_2c' : Γ ⊢ mul two c =eq mul two c' := eq_trans h_cantor_c (eq_symm h_cantor_c')
  let h_cancel := spec (spec teo_2_11 (t := c')) (t := c)
  exact mp h_cancel h_2c_eq_2c'

/-!
### Fase 9: Proyecciones de Cantor
-/

-- Lema Auxiliar: n = 2*k ⇒ mod2(n) = 0
private theorem mod2_of_even {n k : Term} (h : Γ ⊢ n =eq mul two k) : Γ ⊢ mod2 n =eq zero := by
  -- Esta prueba requiere inducción sobre k, que no está disponible en `Minimal`.
  -- La estrategia sería:
  -- Base k=0: n=0, mod2(0)=0. (Teo 5.1)
  -- Paso k -> k+1: n = 2*(k+1) = 2k+2. mod2(2k+2) = mod2(σ(2k+1)).
  -- Por Ax 16, esto es 0 si mod2(2k+1)=1.
  -- mod2(2k+1) = mod2(σ(2k)). Por Ax 16, esto es 1 si mod2(2k)=0.
  -- Esto último es la hipótesis de inducción.
  sorry

-- Teo C8: [⟨x,y⟩].1 = x
theorem cantor_proj1_eq_x (x y : Term) : Γ ⊢ proj1 (cantor_func x y) =eq x := by
  let c := cantor_func x y
  let P := cantor_poly x y
  -- 1. `is_cantor x y c` holds.
  have h_is_cantor_xyc : Γ ⊢ is_cantor x y c := by
    simp [is_cantor, c, cantor_func] -- Goal: 2 * div2(P) = P
    have h_poly_even := cantor_poly_is_even x y
    apply ex_elim h_poly_even; intro k; intro h_poly_eq_2k
    have h_mod2_poly_is_0 : Γ ⊢ mod2 P =eq zero := mod2_of_even (eq_symm h_poly_eq_2k)
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := P)
    have h_div2_mul_2_eq_P : Γ ⊢ mul (div2 P) two =eq P := by rw [←h_ax17, h_mod2_poly_is_0, ax4_add_zero]
    exact h_div2_mul_2_eq_P
  -- 2. `is_cantor (proj1 c) (proj2 c) c` holds by axiom.
  have h_is_cantor_proj : Γ ⊢ is_cantor (proj1 c) (proj2 c) c := spec (ax ax22_cantor_proj_exists) (t := c)
  -- 3. By uniqueness axiom, the components must be equal.
  let h_uniq := spec (spec (spec (spec (spec (ax ax23_cantor_proj_uniq) (t:=c)) (t:=x)) (t:=y)) (t:=proj1 c)) (t:=proj2 c)
  have h_eqs := mp h_uniq (and_intro h_is_cantor_xyc h_is_cantor_proj)
  exact and_elim_left h_eqs

-- Teo C9: [⟨x,y⟩].2 = y
theorem cantor_proj2_eq_y (x y : Term) : Γ ⊢ proj2 (cantor_func x y) =eq y := by
  let c := cantor_func x y
  let P := cantor_poly x y
  have h_is_cantor_xyc : Γ ⊢ is_cantor x y c := by
    simp [is_cantor, c, cantor_func]
    have h_poly_even := cantor_poly_is_even x y
    apply ex_elim h_poly_even; intro k; intro h_poly_eq_2k
    have h_mod2_poly_is_0 : Γ ⊢ mod2 P =eq zero := mod2_of_even (eq_symm h_poly_eq_2k)
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := P)
    have h_div2_mul_2_eq_P : Γ ⊢ mul (div2 P) two =eq P := by rw [←h_ax17, h_mod2_poly_is_0, ax4_add_zero]
    exact h_div2_mul_2_eq_P
  have h_is_cantor_proj : Γ ⊢ is_cantor (proj1 c) (proj2 c) c := spec (ax ax22_cantor_proj_exists) (t := c)
  let h_uniq := spec (spec (spec (spec (spec (ax ax23_cantor_proj_uniq) (t:=c)) (t:=x)) (t:=y)) (t:=proj1 c)) (t:=proj2 c)
  have h_eqs := mp h_uniq (and_intro h_is_cantor_xyc h_is_cantor_proj)
  exact and_elim_right h_eqs

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
  cantor_proj1_eq_x
  cantor_proj2_eq_y
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block3
import ROBINSON_PlusPlus.Minimal.Theorems.Block4

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
open ROBINSON_PlusPlus.Minimal.Theorems.Block4

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block5

/-!
## BLOQUE V — TUPLAS Y PROYECCIONES
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 11: Isomorfismo de Tuplas
-/

-- Lema Auxiliar: n = 2*k ⇒ mod2(n) = 0
private theorem mod2_of_even {n k : Term} (h : Γ ⊢ n =eq mul two k) : Γ ⊢ mod2 n =eq zero := by
  have h_ax24 := ax (by simp [axioms, ax24_mod2_of_even])
  let h_spec_k := spec h_ax24 (t := k)
  let h_spec_n := spec h_spec_k (t := n)
  exact mp h_spec_n h

-- Teo C8: [⟨x,y⟩].1 = x
theorem proj1_pair_eq_x (x y : Term) : Γ ⊢ proj1 (pair x y) =eq x := by
  let c := pair x y
  let P := cantor_poly x y
  have h_is_cantor_xyc : Γ ⊢ is_cantor x y c := by
    simp [is_cantor, c, pair, cantor_func]
    have h_poly_even := cantor_poly_is_even x y
    apply ex_elim h_poly_even; intro k; intro h_poly_eq_2k
    have h_mod2_poly_is_0 : Γ ⊢ mod2 P =eq zero := mod2_of_even (eq_symm h_poly_eq_2k)
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := P)
    have h_div2_mul_2_eq_P : Γ ⊢ mul (div2 P) two =eq P := by rw [←h_ax17, h_mod2_poly_is_0, ax4_add_zero]
    exact h_div2_mul_2_eq_P
  have h_is_cantor_proj : Γ ⊢ is_cantor (proj1 c) (proj2 c) c := spec (ax ax22_cantor_proj_exists) (t := c)
  let h_uniq := spec (spec (spec (spec (spec (ax ax23_cantor_proj_uniq) (t:=c)) (t:=x)) (t:=y)) (t:=proj1 c)) (t:=proj2 c)
  have h_eqs := mp h_uniq (and_intro h_is_cantor_xyc h_is_cantor_proj)
  exact and_elim_left h_eqs

-- Teo C9: [⟨x,y⟩].2 = y
theorem proj2_pair_eq_y (x y : Term) : Γ ⊢ proj2 (pair x y) =eq y := by
  let c := pair x y
  let P := cantor_poly x y
  have h_is_cantor_xyc : Γ ⊢ is_cantor x y c := by
    simp [is_cantor, c, pair, cantor_func]
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

-- Teo C10: ⟨[c].1, [c].2⟩ = c
theorem pair_proj_eq_c (c : Term) : Γ ⊢ pair (proj1 c) (proj2 c) =eq c := by
  let P' := cantor_poly (proj1 c) (proj2 c)
  have h_is_cantor_proj : Γ ⊢ is_cantor (proj1 c) (proj2 c) c :=
    spec (ax ax22_cantor_proj_exists) (t := c)
  have h_2c_eq_P' : Γ ⊢ mul two c =eq P' := by simp [is_cantor] at h_is_cantor_proj; exact h_is_cantor_proj
  have h_ax17 := spec (ax ax17_div_mod_eq) (t := P')
  have h_mod2_P'_eq_0 : Γ ⊢ mod2 P' =eq zero := mod2_of_even (eq_symm h_2c_eq_P')
  have h_div2P'_mul_2_eq_P' : Γ ⊢ mul (div2 P') two =eq P' := by
    rw [←h_ax17, h_mod2_P'_eq_0, ax4_add_zero]
  have h_div2P'_mul_2_eq_2c : Γ ⊢ mul (div2 P') two =eq mul two c := eq_trans h_div2P'_mul_2_eq_P' h_2c_eq_P'
  have h_comm := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 P')
  have h_2_mul_div2P'_eq_2c : Γ ⊢ mul two (div2 P') =eq mul two c := eq_trans h_comm h_div2P'_mul_2_eq_2c
  have h_cancel := mp (spec (spec teo_2_11 (t := c)) (t := div2 P')) h_2_mul_div2P'_eq_2c
  simp [pair, cantor_func]; exact h_cancel

-- Teo C11: ⟨x,y⟩ = ⟨x',y'⟩ ⇒ x = x' ∧ y = y'
theorem pair_inj {x y x' y' : Term} : Γ ⊢ (pair x y =eq pair x' y') ⇒ land (x =eq x') (y =eq y') := by
  apply deduction_theorem; intro h_c_eq_c'
  have h_x_eq_proj1_c : Γ ⊢ x =eq proj1 (pair x y) := eq_symm (proj1_pair_eq_x x y)
  have h_y_eq_proj2_c : Γ ⊢ y =eq proj2 (pair x y) := eq_symm (proj2_pair_eq_y x y)
  have h_x'_eq_proj1_c' : Γ ⊢ x' =eq proj1 (pair x' y') := eq_symm (proj1_pair_eq_x x' y')
  have h_y'_eq_proj2_c' : Γ ⊢ y' =eq proj2 (pair x' y') := eq_symm (proj2_pair_eq_y x' y')
  have h_x_eq_x' : Γ ⊢ x =eq x' := by
    rw [h_c_eq_c'] at h_x_eq_proj1_c
    exact eq_trans h_x_eq_proj1_c h_x'_eq_proj1_c'
  have h_y_eq_y' : Γ ⊢ y =eq y' := by
    rw [h_c_eq_c'] at h_y_eq_proj2_c
    exact eq_trans h_y_eq_proj2_c h_y'_eq_proj2_c'
  exact and_intro h_x_eq_x' h_y_eq_y'

end ROBINSON_PlusPlus.Minimal.Theorems.Block5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block5 (
  proj1_pair_eq_x
  proj2_pair_eq_y
  pair_proj_eq_c
  pair_inj
)

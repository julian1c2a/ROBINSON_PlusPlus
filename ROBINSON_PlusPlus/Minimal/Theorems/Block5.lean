/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block3
import ROBINSON_PlusPlus.Minimal.Theorems.Block4
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block3
open ROBINSON_PlusPlus.Minimal.Theorems.Block4
open ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5
open ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block5

/-!
## BLOQUE V — TUPLAS Y PROYECCIONES
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 11: Isomorfismo de Tuplas
-/

-- Lema Auxiliar `mod2_of_even` movido a Block4_C6_C7 el 2026-06-03 para evitar
-- dependencia circular (lo necesita `proj_is_cantor` allí). Sigue disponible
-- aquí vía `open Block4_C6_C7`.

-- Lema clave: is_cantor x y (pair x y), i.e. 2·pair(x,y) = cantor_poly(x,y).
-- Idea: cantor_poly es par (cantor_poly_is_even) ⇒ mod2 = 0 ⇒ por ax17
-- div2(cantor_poly)·2 = cantor_poly, y mul_comm da 2·div2(cantor_poly) = cantor_poly.
-- Por definición pair x y = div2 (cantor_poly x y).
theorem is_cantor_pair (x y : Term) :
    Γ ⊢ (mul two (pair x y) =eq cantor_poly x y) := by
  -- 1. cantor_poly x y es par: ∃ k, cantor_poly x y =eq mul two k
  have h_even := cantor_poly_is_even x y
  apply ex_elim h_even
  intro k h_k_raw
  simp [substFormula, substTerm, substTerms, mul, succ, add, two, one, zero,
        FOL.substTerm_liftTerm] at h_k_raw
  -- h_k_raw : cantor_poly x y =eq mul two k
  -- 2. mod2 (cantor_poly x y) = 0
  have h_mod0 : Γ ⊢ (mod2 (cantor_poly x y) =eq zero) := mod2_of_even h_k_raw
  -- 3. ax17 spec'd en cantor_poly x y
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  have h17 : Γ ⊢ (add (mul (div2 (cantor_poly x y)) two) (mod2 (cantor_poly x y)) =eq cantor_poly x y) := by
    have hh := spec h_ax17 (cantor_poly x y)
    simp [substFormula, substTerm, substTerms, div2, mul, add, mod2, two,
          FOL.substTerm_liftTerm] at hh
    exact hh
  -- 4. Sustituir mod2 = 0 en h17
  have h_sum0 : Γ ⊢ (add (mul (div2 (cantor_poly x y)) two) zero =eq cantor_poly x y) :=
    FOL.derive_eq_trans (eq_symm (eq_congr_add_left h_mod0)) h17
  -- 5. ax4: a + 0 = a
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h4 : Γ ⊢ (add (mul (div2 (cantor_poly x y)) two) zero =eq mul (div2 (cantor_poly x y)) two) := by
    have hh := spec h_ax4 (mul (div2 (cantor_poly x y)) two)
    simp [substFormula, substTerm, substTerms, mul, add, div2, two, zero] at hh
    exact hh
  -- 6. div2(...)·2 = cantor_poly
  have h_div_eq : Γ ⊢ (mul (div2 (cantor_poly x y)) two =eq cantor_poly x y) :=
    FOL.derive_eq_trans (eq_symm h4) h_sum0
  -- 7. mul_comm: 2·div2(...) = div2(...)·2 = cantor_poly
  have h_comm : Γ ⊢ (mul two (div2 (cantor_poly x y)) =eq mul (div2 (cantor_poly x y)) two) :=
    mul_comm' two (div2 (cantor_poly x y))
  -- pair x y reduce defeq a div2 (cantor_poly x y), cantor_func reduce defeq igual
  exact FOL.derive_eq_trans h_comm h_div_eq

-- Teo C8: [⟨x,y⟩].1 = x
-- Vía cantor_uniqueness con is_cantor_pair y proj_is_cantor (este último
-- reemplaza al antiguo ax22, eliminado 2026-06-02).
theorem proj1_pair_eq_x (x y : Term) : Γ ⊢ (proj1 (pair x y) =eq x) := by
  -- is_cantor (proj1 (pair x y))(proj2 (pair x y))(pair x y)
  have h_proj : Γ ⊢ (mul two (pair x y) =eq cantor_poly (proj1 (pair x y)) (proj2 (pair x y))) :=
    proj_is_cantor (pair x y)
  -- is_cantor x y (pair x y)
  have h_xy : Γ ⊢ (mul two (pair x y) =eq cantor_poly x y) := is_cantor_pair x y
  -- cantor_uniqueness: x = proj1 (pair x y) ∧ y = proj2 (pair x y)
  have h_uniq := cantor_uniqueness x y (proj1 (pair x y)) (proj2 (pair x y)) (pair x y)
  have h_eqs : Γ ⊢ land (x =eq proj1 (pair x y)) (y =eq proj2 (pair x y)) :=
    mp h_uniq (Axioms.and_intro h_xy h_proj)
  exact eq_symm (Axioms.and_elim_left h_eqs)

-- Teo C9: [⟨x,y⟩].2 = y
theorem proj2_pair_eq_y (x y : Term) : Γ ⊢ (proj2 (pair x y) =eq y) := by
  have h_proj : Γ ⊢ (mul two (pair x y) =eq cantor_poly (proj1 (pair x y)) (proj2 (pair x y))) :=
    proj_is_cantor (pair x y)
  have h_xy : Γ ⊢ (mul two (pair x y) =eq cantor_poly x y) := is_cantor_pair x y
  have h_uniq := cantor_uniqueness x y (proj1 (pair x y)) (proj2 (pair x y)) (pair x y)
  have h_eqs : Γ ⊢ land (x =eq proj1 (pair x y)) (y =eq proj2 (pair x y)) :=
    mp h_uniq (Axioms.and_intro h_xy h_proj)
  exact eq_symm (Axioms.and_elim_right h_eqs)

-- Teo C10: ⟨[c].1, [c].2⟩ = c
-- Vía cantor_injective_c con proj_is_cantor e is_cantor_pair (sobre proj1 c, proj2 c).
theorem pair_proj_eq_c (c : Term) : Γ ⊢ (pair (proj1 c) (proj2 c) =eq c) := by
  -- is_cantor (proj1 c)(proj2 c) c
  have h_axc : Γ ⊢ (mul two c =eq cantor_poly (proj1 c) (proj2 c)) := proj_is_cantor c
  -- is_cantor (proj1 c)(proj2 c) (pair (proj1 c)(proj2 c))
  have h_pair : Γ ⊢ (mul two (pair (proj1 c) (proj2 c)) =eq cantor_poly (proj1 c) (proj2 c)) :=
    is_cantor_pair (proj1 c) (proj2 c)
  -- cantor_injective_c: c =eq pair (proj1 c)(proj2 c)
  have h_inj := cantor_injective_c (proj1 c) (proj2 c) c (pair (proj1 c) (proj2 c))
  have h_eq : Γ ⊢ (c =eq pair (proj1 c) (proj2 c)) := mp h_inj (Axioms.and_intro h_axc h_pair)
  exact eq_symm h_eq

-- Teo C11: ⟨x,y⟩ = ⟨x',y'⟩ ⇒ x = x' ∧ y = y'
theorem pair_inj {x y x' y' : Term} :
    Γ ⊢ (pair x y =eq pair x' y') ⇒ land (x =eq x') (y =eq y') := by
  apply Axioms.imp_intro; intro h_pair_eq
  have h_xy : Γ ⊢ (mul two (pair x y) =eq cantor_poly x y) := is_cantor_pair x y
  have h_x'y' : Γ ⊢ (mul two (pair x' y') =eq cantor_poly x' y') := is_cantor_pair x' y'
  -- Transportar h_x'y' al c = pair x y vía h_pair_eq
  have h_x'y'_at_xy : Γ ⊢ (mul two (pair x y) =eq cantor_poly x' y') :=
    FOL.derive_eq_trans (eq_congr_mul_left h_pair_eq) h_x'y'
  have h_uniq := cantor_uniqueness x y x' y' (pair x y)
  exact mp h_uniq (Axioms.and_intro h_xy h_x'y'_at_xy)

end ROBINSON_PlusPlus.Minimal.Theorems.Block5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block5 (
  is_cantor_pair
  proj1_pair_eq_x
  proj2_pair_eq_y
  pair_proj_eq_c
  pair_inj
)

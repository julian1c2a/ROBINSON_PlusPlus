/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block5

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
open ROBINSON_PlusPlus.Minimal.Theorems.Block5

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block6

/-!
## BLOQUE VI — LISTAS
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 12: Nil y Cons
-/

-- Teo L1: ∀ h,t, Cons(h,t) ≠ Nil
theorem cons_neq_nil (h t : Term) : Γ ⊢ neg (Cons h t =eq Nil) := by
  have h_cons_def := spec (spec (ax ax_L0_cons_def) (t := t)) (t := h)
  have h_pair_0_0_eq_0 : Γ ⊢ pair zero zero =eq zero := pair_proj_eq_c zero -- This is a bit circular, let's prove it directly.
  have h_pair_0_0_eq_0' : Γ ⊢ pair zero zero =eq zero := by simp [pair, cantor_func, cantor_poly, sq, ax8_mul_zero, ax4_add_zero]; exact div2_zero
  apply raa; intro h_cons_eq_nil
  have h_pair_eq_0 : Γ ⊢ pair h (succ t) =eq zero := by rwa [←h_cons_def]
  have h_pair_eq_pair_0_0 : Γ ⊢ pair h (succ t) =eq pair zero zero := eq_trans h_pair_eq_0 (eq_symm h_pair_0_0')
  have h_inj := mp (pair_inj (x := h) (y := succ t) (x' := zero) (y' := zero)) h_pair_eq_pair_0_0
  have h_st_eq_0 := and_elim_right h_inj
  exact (spec (ax ax2_peano_succ_neq_zero) (t := t)) h_st_eq_0

-- Teo L2: Cons(h,t) = Cons(h',t') ⇒ h = h' ∧ t = t'
theorem cons_inj {h t h' t' : Term} : Γ ⊢ (Cons h t =eq Cons h' t') ⇒ land (h =eq h') (t =eq t') := by
  have h_cons_def := spec (spec (ax ax_L0_cons_def) (t := t)) (t := h)
  have h_cons'_def := spec (spec (ax ax_L0_cons_def) (t := t')) (t := h')
  apply deduction_theorem; intro h_cons_eq_cons'
  have h_pair_eq_pair : Γ ⊢ pair h (succ t) =eq pair h' (succ t') := by
    rw [←h_cons_def, ←h_cons'_def, h_cons_eq_cons']
  have h_inj := mp (pair_inj (x := h) (y := succ t) (x' := h') (y' := succ t')) h_pair_eq_pair
  have h_h_eq_h' := and_elim_left h_inj
  have h_st_eq_st' := and_elim_right h_inj
  have h_t_eq_t' := mp (spec (spec (ax ax3_peano_succ_inj) (t := t')) (t := t)) h_st_eq_st'
  exact and_intro h_h_eq_h' h_t_eq_t'

/-!
### Fase 13: Pertenencia
-/

-- Teo L4: In(x, Cons(x, Nil))
theorem in_cons_self_nil (x : Term) : Γ ⊢ In x (Cons x Nil) := by
  have h_ax_L2 := ax (by simp [axioms, ax_L2_in_cons])
  let h_spec := spec (spec (spec h_ax_L2 (t := Nil)) (t := x)) (t := x)
  -- h_spec is In x (Cons x Nil) ⇔ (x =eq x ∨ In x Nil)
  have h_rhs : Γ ⊢ lor (x =eq x) (In x Nil) := by
    apply or_intro_left
    exact eq_refl -- x = x
  exact iff_mp h_spec h_rhs

-- Teo L5: In(x, Cons(h, Nil)) ⇒ x = h
theorem in_cons_nil_imp_eq {x h : Term} : Γ ⊢ In x (Cons h Nil) ⇒ (x =eq h) := by
  apply deduction_theorem; intro h_in
  have h_ax_L2 := ax (by simp [axioms, ax_L2_in_cons])
  let h_spec := spec (spec (spec h_ax_L2 (t := Nil)) (t := h)) (t := x)
  have h_disj : Γ ⊢ lor (x =eq h) (In x Nil) := iff_mp h_spec h_in
  have h_ax_L1 := ax (by simp [axioms, ax_L1_in_nil])
  have h_not_in_nil : Γ ⊢ neg (In x Nil) := spec h_ax_L1 (t := x)
  apply or_elim h_disj
  · intro h_x_eq_h; exact h_x_eq_h
  · intro h_in_nil; exact false_elim (h_not_in_nil h_in_nil)

/-!
### Fase 14: Concatenación
-/

-- Teo L6: [x] ⊕ [y] = [x,y]
theorem concat_singletons (x y : Term) : Γ ⊢ concat (Cons x Nil) (Cons y Nil) =eq Cons x (Cons y Nil) := by
  have h_ax_C2 := ax (by simp [axioms, ax_C2_concat_cons])
  let h_spec := spec (spec (spec h_ax_C2 (t := Cons y Nil)) (t := Nil)) (t := x)
  -- h_spec is concat (Cons x Nil) (Cons y Nil) = Cons x (concat Nil (Cons y Nil))
  have h_ax_C1 := ax (by simp [axioms, ax_C1_concat_nil])
  let h_spec_C1 := spec h_ax_C1 (t := Cons y Nil)
  -- h_spec_C1 is concat Nil (Cons y Nil) = Cons y Nil
  have h_rhs_eq : Γ ⊢ Cons x (concat Nil (Cons y Nil)) =eq Cons x (Cons y Nil) :=
    eq_congr_cons_right h_spec_C1
  exact eq_trans h_spec h_rhs_eq

-- Teo L7: (L ⊕ M) ⊕ N = L ⊕ (M ⊕ N)
theorem concat_assoc (L M N : Term) : Γ ⊢ concat (concat L M) N =eq concat L (concat M N) := by
  -- Proof requires induction on L.
  sorry

-- Teo L8: In(x, L ⊕ M) ⇔ In(x,L) ∨ In(x,M)
theorem in_concat_iff (x L M : Term) : Γ ⊢ In x (concat L M) ⇔ lor (In x L) (In x M) := by
  -- Proof requires induction on L.
  sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block6

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block6 (
  cons_neq_nil
  cons_inj
  in_cons_self_nil
  in_cons_nil_imp_eq
  concat_singletons
  concat_assoc
  in_concat_iff
)

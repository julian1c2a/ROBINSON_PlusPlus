/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block4
import ROBINSON_PlusPlus.Minimal.Theorems.Block5

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block4
open ROBINSON_PlusPlus.Minimal.Theorems.Block5

set_option linter.unusedSimpArgs false

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
-- Estrategia: cons h t = pair h (succ t) [ax_L0]. Si esto = nil = zero, entonces
-- pair h (succ t) = 0, luego mul two (pair h (succ t)) = mul two zero = zero. Por
-- `is_cantor_pair`, cantor_poly h (succ t) = 0. Por teo_2_9 (add a b = 0 → a=0 ∧ b=0),
-- mul two (succ t) = 0. Pero mul two (succ t) = succ(succ(mul two t)) ≠ 0 por ax2.
theorem cons_neq_nil (h t : Term) : Γ ⊢ neg (cons h t =eq nil) := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_axL0 := ax (by simp [axioms] : ax_L0_cons_def ∈ axioms)
  apply raa; intro h_eq
  -- cons h t =eq pair h (succ t)  [ax_L0 spec]  -- sin ascripción: deja inferencia
  have h_cons_pair := by
    have hh := spec (spec h_axL0 h) t
    simp [substFormula, substTerm, substTerms, cons, pair, cantor_func, div2,
          cantor_poly, mul, add, succ, two, one, zero,
          liftTerm, liftTerms, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  -- pair h (succ t) =eq zero
  have h_pair_zero := FOL.derive_eq_trans (eq_symm h_cons_pair) h_eq
  -- mul two (pair h (succ t)) =eq mul two zero
  have h_two_pair := eq_congr_mul_left (u := two) h_pair_zero
  -- mul two zero =eq zero  (teo_2_3 spec)
  have h_mul_two_zero : Γ ⊢ (mul two zero =eq zero) := by
    have hh := spec teo_2_3 two
    simp [substFormula, substTerm, substTerms, mul, zero] at hh
    exact hh
  -- cantor_poly h (succ t) =eq zero, vía is_cantor_pair
  have h_isc := is_cantor_pair h (succ t)
  have h_cp_zero : Γ ⊢ (cantor_poly h (succ t) =eq zero) :=
    FOL.derive_eq_trans (eq_symm h_isc) (FOL.derive_eq_trans h_two_pair h_mul_two_zero)
  -- teo_2_9: add a b = 0 ⇒ a=0 ∧ b=0; cantor_poly = add ... (mul two (succ t))
  have h_t29 := by
    have hh := spec (spec teo_2_9 (mul (add h (succ t)) (succ (add h (succ t))))) (mul two (succ t))
    simp [substFormula, substTerm, substTerms, add, mul, succ, zero,
          liftTerm, liftTerms, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  have h_split := mp h_t29 h_cp_zero
  have h_2st_zero : Γ ⊢ (mul two (succ t) =eq zero) := Axioms.and_elim_right h_split
  -- mul two (succ t) =eq add (mul two t) two  [ax9]
  have h9 : Γ ⊢ (mul two (succ t) =eq add (mul two t) two) := by
    have hh := spec (spec h_ax9 two) t
    simp [substFormula, substTerm, substTerms, mul, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at hh
    exact hh
  -- add x two = succ(succ x): ax5(x,succ zero) + ax5(x,zero) + ax4
  have h_add_two_eq_succsucc : Γ ⊢ (add (mul two t) two =eq succ (succ (mul two t))) := by
    have h_a := spec (spec h_ax5 (mul two t)) one
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h_a
    have h_b := spec (spec h_ax5 (mul two t)) zero
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h_b
    have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
    have h_c := spec h_ax4 (mul two t)
    simp [substFormula, substTerm, substTerms, add, zero] at h_c
    exact FOL.derive_eq_trans h_a
      (eq_congr_succ (FOL.derive_eq_trans h_b (eq_congr_succ h_c)))
  have h_2st_succsucc : Γ ⊢ (mul two (succ t) =eq succ (succ (mul two t))) :=
    FOL.derive_eq_trans h9 h_add_two_eq_succsucc
  have h_succsucc_zero : Γ ⊢ (succ (succ (mul two t)) =eq zero) :=
    FOL.derive_eq_trans (eq_symm h_2st_succsucc) h_2st_zero
  have h_neq : Γ ⊢ neg (succ (succ (mul two t)) =eq zero) := by
    have hh := spec h_ax2 (succ (mul two t))
    simp [substFormula, substTerm, substTerms, succ, zero, FOL.substTerm_liftTerm] at hh
    exact hh
  exact mp h_neq h_succsucc_zero

-- Teo L2: Cons(h,t) = Cons(h',t') ⇒ h = h' ∧ t = t'
-- Vía ax_L0 (cons = pair h (succ t)) + pair_inj + ax3 (succ inyectivo).
theorem cons_inj {h t h' t' : Term} : Γ ⊢ (cons h t =eq cons h' t') ⇒ land (h =eq h') (t =eq t') := by
  apply Axioms.imp_intro; intro h_eq
  have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_axL0 := ax (by simp [axioms] : ax_L0_cons_def ∈ axioms)
  -- cons h t = pair h (succ t)  (sin ascripción)
  have h_l0_ht := by
    have hh := spec (spec h_axL0 h) t
    simp [substFormula, substTerm, substTerms, cons, pair, cantor_func, div2,
          cantor_poly, mul, add, succ, two, one, zero,
          liftTerm, liftTerms, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  have h_l0_h't' := by
    have hh := spec (spec h_axL0 h') t'
    simp [substFormula, substTerm, substTerms, cons, pair, cantor_func, div2,
          cantor_poly, mul, add, succ, two, one, zero,
          liftTerm, liftTerms, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  have h_pair_eq :=
    FOL.derive_eq_trans (eq_symm h_l0_ht) (FOL.derive_eq_trans h_eq h_l0_h't')
  have h_inj := mp pair_inj h_pair_eq
  have h_h_eq := Axioms.and_elim_left h_inj
  have h_st_eq := Axioms.and_elim_right h_inj
  have h_succ_imp : Γ ⊢ ((succ t =eq succ t') ⇒ (t =eq t')) := by
    have hh := spec (spec h_ax3 t) t'
    simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  exact Axioms.and_intro h_h_eq (mp h_succ_imp h_st_eq)

/-!
### Fase 13: Pertenencia
-/

-- Teo L4: In(x, Cons(x, Nil))
-- Vía ax_L2: In x (cons x nil) ⇔ ((x=x) ∨ In x nil). iff_mpr con or_intro_left.
theorem in_cons_self_nil (x : Term) : Γ ⊢ In x (cons x nil) := by
  have h_axL2 := ax (by simp [axioms] : ax_L2_in_cons ∈ axioms)
  have h_iff := by
    have hh := spec (spec (spec h_axL2 x) x) nil
    simp [substFormula, substTerm, substTerms, In, cons, succ, zero, nil, lor, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at hh
    exact hh
  exact iff_mpr h_iff (Axioms.or_intro_left (eq_refl x))

-- Teo L5: In(x, Cons(h, Nil)) ⇒ x = h
-- ax_L2 + or_elim (caso In x nil contradice ax_L1).
theorem in_cons_nil_imp_eq {x h : Term} : Γ ⊢ In x (cons h nil) ⇒ (x =eq h) := by
  apply Axioms.imp_intro; intro h_in
  have h_axL1 := ax (by simp [axioms] : ax_L1_in_nil ∈ axioms)
  have h_axL2 := ax (by simp [axioms] : ax_L2_in_cons ∈ axioms)
  have h_iff := by
    have hh := spec (spec (spec h_axL2 x) h) nil
    simp [substFormula, substTerm, substTerms, In, cons, succ, zero, nil, lor, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at hh
    exact hh
  have h_disj := iff_mp h_iff h_in
  apply Axioms.or_elim h_disj
  · intro h_eq; exact h_eq
  · intro h_in_nil
    apply false_elim
    have h_not_in_nil : Γ ⊢ neg (In x nil) := by
      have hh := spec h_axL1 x
      simp [substFormula, substTerm, substTerms, In, nil, zero, FOL.substTerm_liftTerm] at hh
      exact hh
    exact mp h_not_in_nil h_in_nil

/-!
### Fase 14: Concatenación
-/

-- Helper: congruencia de cons en su argumento derecho.
private theorem eq_congr_cons_right (x : Term) {a b : Term}
    (h : Γ ⊢ (a =eq b)) : Γ ⊢ (cons x a =eq cons x b) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 x) (liftTerm 0 a)) (cons (liftTerm 0 x) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons x a) (cons x s) := by
    intro s
    simp only [f, substFormula, cons, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst Γ a b f h ((hS a) ▸ Derives.refl Γ (cons x a))

-- Teo L6: [x] ⊕ [y] = [x,y]
-- ax_C2 (concat (cons x t) y = cons x (concat t y)) + ax_C1 (concat nil x = x).
theorem concat_singletons (x y : Term) :
    Γ ⊢ (concat (cons x nil) (cons y nil) =eq cons x (cons y nil)) := by
  have h_axC1 := ax (by simp [axioms] : ax_C1_concat_nil ∈ axioms)
  have h_axC2 := ax (by simp [axioms] : ax_C2_concat_cons ∈ axioms)
  -- concat (cons x nil)(cons y nil) =eq cons x (concat nil (cons y nil))  [ax_C2]
  have h_c2 := by
    have hh := spec (spec (spec h_axC2 x) nil) (cons y nil)
    simp [substFormula, substTerm, substTerms, concat, cons, nil, zero,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at hh
    exact hh
  -- concat nil (cons y nil) =eq cons y nil  [ax_C1]
  have h_c1 : Γ ⊢ (concat nil (cons y nil) =eq cons y nil) := by
    have hh := spec h_axC1 (cons y nil)
    simp [substFormula, substTerm, substTerms, concat, cons, nil, zero,
          FOL.substTerm_liftTerm] at hh
    exact hh
  exact FOL.derive_eq_trans h_c2 (eq_congr_cons_right x h_c1)

-- Teo L7: (L ⊕ M) ⊕ N = L ⊕ (M ⊕ N)
-- Postulado en Minimal como ax_C3_concat_assoc (siguiendo el patrón de
-- ax21/ax24/ax27/ax28: teoremas en sistemas con inducción, axiomas en Minimal).
theorem concat_assoc (L M N : Term) :
    Γ ⊢ (concat (concat L M) N =eq concat L (concat M N)) := by
  have h_axC3 := ax (by simp [axioms] : ax_C3_concat_assoc ∈ axioms)
  have hh := spec (spec (spec h_axC3 L) M) N
  simp [substFormula, substTerm, substTerms, concat, nil, zero,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_liftLift] at hh
  exact hh

-- Teo L8: In(x, L ⊕ M) ⇔ In(x,L) ∨ In(x,M)
-- Postulado en Minimal como ax_L3_in_concat (requiere inducción sobre L).
theorem in_concat_iff (x L M : Term) :
    Γ ⊢ In x (concat L M) ⇔ lor (In x L) (In x M) := by
  have h_axL3 := ax (by simp [axioms] : ax_L3_in_concat ∈ axioms)
  have hh := spec (spec (spec h_axL3 x) L) M
  simp [substFormula, substTerm, substTerms, In, concat, nil, zero, lor, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_liftLift] at hh
  exact hh

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

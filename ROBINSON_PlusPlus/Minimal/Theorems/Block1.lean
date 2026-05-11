/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import FOL.FOL
import FOL.Tactics

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block1

open ROBINSON_PlusPlus.Minimal.Axioms

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

-- Local definitions from TuplasFuncionesYListas.md Def 3-4
def three : Term := succ two
def four : Term := succ three

/-!
## BLOQUE I — ARITMÉTICA BÁSICA
### Fase 1: Evaluación de Constantes
-/

-- Teo 1.1: 1 + 0 = 1
-- Prueba: Ax 4 (∀ n, n + 0 = n) con n := 1.
theorem teo_1_1 : Γ ⊢ (add one zero =eq one) := by
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  exact spec h_ax4 (t := one)

-- Teo 1.2: 0 + 1 = 1
-- Prueba: 0 + 1 = 1 + 0 (Ax 6) y 1 + 0 = 1 (Teo 1.1).
theorem teo_1_2 : Γ ⊢ (add zero one =eq one) := by
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m := spec h_ax6 (t := one)
  let h_spec_n := spec h_spec_m (t := zero)
  exact eq_trans h_spec_n teo_1_1

-- Teo 1.3: 1 + 1 = 2
-- Prueba: ax5(one,zero): 1+σ(0)=σ(1+0); ax4(one): 1+0=1; congr+trans → 1+1=2.
theorem teo_1_3 : Γ ⊢ (add one one =eq two) := by
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  exact eq_trans (eq_symm (spec (spec h_ax5 one) zero)) (eq_congr_succ (spec h_ax4 one))

-- Teo 1.4: 2 + 1 = 3
-- Prueba: ax5(two,zero): 2+1=σ(2+0); ax4(two): 2+0=2; congr → σ(2)=3.
theorem teo_1_4 : Γ ⊢ (add two one =eq three) := by
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  exact eq_trans (eq_symm (spec (spec h_ax5 two) zero)) (eq_congr_succ (spec h_ax4 two))

-- Teo 1.5: 1 + 2 = 3
-- Prueba: ax5(one,one): 1+σ(1)=σ(1+1); teo_1_3: 1+1=2; congr → σ(2)=3.
theorem teo_1_5 : Γ ⊢ (add one two =eq three) := by
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  exact eq_trans (eq_symm (spec (spec h_ax5 one) one)) (eq_congr_succ teo_1_3)

-- Teo 1.6: 3 + 1 = 4
-- Prueba: ax5(three,zero): 3+1=σ(3+0); ax4(three): 3+0=3; congr → σ(3)=4.
theorem teo_1_6 : Γ ⊢ (add three one =eq four) := by
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  exact eq_trans (eq_symm (spec (spec h_ax5 three) zero)) (eq_congr_succ (spec h_ax4 three))

-- Teo 1.7: 2 + 2 = 4
-- Prueba: ax5(two,one): 2+σ(1)=σ(2+1); teo_1_4: 2+1=3; congr → σ(3)=4.
theorem teo_1_7 : Γ ⊢ (add two two =eq four) := by
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  exact eq_trans (eq_symm (spec (spec h_ax5 two) one)) (eq_congr_succ teo_1_4)

-- Teo 1.8: 1 * 1 = 1
-- Prueba: ax9(one,zero): 1*1=(1*0)+1; ax8(one): 1*0=0; teo_1_2: 0+1=1.
theorem teo_1_8 : Γ ⊢ (mul one one =eq one) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax8 := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
  -- mul one one = add(mul one zero) one
  have h1 := spec (spec h_ax9 one) zero
  -- add(mul one zero) one = add zero one
  have h2 := eq_congr_add_right (u := one) (spec h_ax8 one)
  -- mul one one = add zero one
  have step1 := eq_trans (eq_symm h1) h2
  -- mul one one = one  (via teo_1_2: 0+1=1)
  exact eq_trans (eq_symm step1) teo_1_2

-- Teo 1.9: 2 * 1 = 2
-- Prueba: ax9(two,zero): 2*1=(2*0)+2; ax8(two): 2*0=0; ax6+ax4: 0+2=2.
theorem teo_1_9 : Γ ⊢ (mul two one =eq two) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax8 := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
  have h_ax6 := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  -- mul two one = add(mul two zero) two
  have h1 := spec (spec h_ax9 two) zero
  -- add(mul two zero) two = add zero two
  have h2 := eq_congr_add_right (u := two) (spec h_ax8 two)
  -- add zero two = two  (via add zero two = add two zero = two)
  have h_zero_two : Γ ⊢ (add zero two =eq two) :=
    eq_trans (eq_symm (spec (spec h_ax6 zero) two)) (spec h_ax4 two)
  -- mul two one = add zero two
  have step1 := eq_trans (eq_symm h1) h2
  -- mul two one = two
  exact eq_trans (eq_symm step1) h_zero_two

-- Teo 1.10: 2 * 2 = 4
-- Prueba: ax9(two,one): 2*2=(2*1)+2; teo_1_9: 2*1=2; teo_1_7: 2+2=4.
theorem teo_1_10 : Γ ⊢ (mul two two =eq four) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- mul two two = add(mul two one) two
  have h1 := spec (spec h_ax9 two) one
  -- add(mul two one) two = add two two
  have h2 := eq_congr_add_right (u := two) teo_1_9
  -- mul two two = add two two
  have step1 := eq_trans (eq_symm h1) h2
  -- mul two two = four  (via teo_1_7: 2+2=4)
  exact eq_trans (eq_symm step1) teo_1_7

-- Teo 1.11: 0 ≠ 1
-- Prueba: ax2(zero): σ(0)≠0, i.e., 1≠0; eq_symm_neg → 0≠1.
theorem teo_1_11 : Γ ⊢ neg (zero =eq one) := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  exact eq_symm_neg (spec h_ax2 zero)

-- Teo 1.12: 1 ≠ 2
-- Prueba: si 1=2 entonces ax3 da 0=1, contradicción con teo_1_11.
theorem teo_1_12 : Γ ⊢ neg (one =eq two) := by
  have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  -- neg A = A ⇒ ⊥; construimos la derivación en el contexto extendido
  refine Derives.intro_impl Γ (Formula.eq one two) Formula.bottom ?_
  -- En contexto Γ' = one=two :: Γ:
  have h_hyp := Derives.hyp (Formula.eq one two :: Γ) (Formula.eq one two) (List.Mem.head _)
  -- ax3(zero,one): (one=two) ⇒ (zero=one)
  have h_imp := Derives.weakening Γ (Formula.eq one two :: Γ) _
    (spec (spec h_ax3 zero) one) (fun _ hx => List.Mem.tail _ hx)
  -- teo_1_11 debilitado: neg(zero=one) en Γ'
  have h_neg := Derives.weakening Γ (Formula.eq one two :: Γ) _
    teo_1_11 (fun _ hx => List.Mem.tail _ hx)
  exact mp h_neg (mp h_imp h_hyp)

-- Teo 1.13: Desigualdades entre constantes

-- 0 ≠ 2: ax2(one): σ(1)≠0, i.e., 2≠0; eq_symm_neg → 0≠2.
theorem teo_1_13_1 : Γ ⊢ neg (zero =eq two) := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  exact eq_symm_neg (spec h_ax2 one)

-- 0 ≠ 3: ax2(two): σ(2)≠0, i.e., 3≠0; eq_symm_neg → 0≠3.
theorem teo_1_13_2 : Γ ⊢ neg (zero =eq three) := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  exact eq_symm_neg (spec h_ax2 two)

-- 1 ≠ 3: si 1=3 entonces ax3 da 0=2, contradicción con teo_1_13_1.
theorem teo_1_13_3 : Γ ⊢ neg (one =eq three) := by
  have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  refine Derives.intro_impl Γ (Formula.eq one three) Formula.bottom ?_
  have h_hyp := Derives.hyp (Formula.eq one three :: Γ) (Formula.eq one three) (List.Mem.head _)
  -- ax3(zero,two): (one=three) ⇒ (zero=two)
  have h_imp := Derives.weakening Γ (Formula.eq one three :: Γ) _
    (spec (spec h_ax3 zero) two) (fun _ hx => List.Mem.tail _ hx)
  have h_neg := Derives.weakening Γ (Formula.eq one three :: Γ) _
    teo_1_13_1 (fun _ hx => List.Mem.tail _ hx)
  exact mp h_neg (mp h_imp h_hyp)

-- 2 ≠ 3: si 2=3 entonces ax3 da 1=2, contradicción con teo_1_12.
theorem teo_1_13_4 : Γ ⊢ neg (two =eq three) := by
  have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  refine Derives.intro_impl Γ (Formula.eq two three) Formula.bottom ?_
  have h_hyp := Derives.hyp (Formula.eq two three :: Γ) (Formula.eq two three) (List.Mem.head _)
  -- ax3(one,two): (two=three) ⇒ (one=two)
  have h_imp := Derives.weakening Γ (Formula.eq two three :: Γ) _
    (spec (spec h_ax3 one) two) (fun _ hx => List.Mem.tail _ hx)
  have h_neg := Derives.weakening Γ (Formula.eq two three :: Γ) _
    teo_1_12 (fun _ hx => List.Mem.tail _ hx)
  exact mp h_neg (mp h_imp h_hyp)


/-!
### Fase 2: Identidades del 0 y del 1
-/

-- Teo 2.1: ∀ n, n + 0 = n
-- Prueba: Ax 4.
theorem teo_2_1 : Γ ⊢ ax4_add_zero :=
  ax (by simp [axioms, ax4_add_zero])

-- Teo 2.2: ∀ n, 0 + n = n
theorem teo_2_2 : Γ ⊢ forall_ (add zero (.var 0) =eq (.var 0)) := by sorry

-- Teo 2.3: ∀ n, n * 0 = 0
-- Prueba: Ax 8.
theorem teo_2_3 : Γ ⊢ ax8_mul_zero :=
  ax (by simp [axioms, ax8_mul_zero])

-- Teo 2.4: ∀ n, 0 * n = 0
theorem teo_2_4 : Γ ⊢ forall_ (mul zero (.var 0) =eq zero) := by sorry

-- Teo 2.5: ∀ n, n * 1 = n
theorem teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := by sorry

-- Teo 2.6: ∀ n, 1 * n = n
theorem teo_2_6 : Γ ⊢ forall_ (mul one (.var 0) =eq (.var 0)) := by sorry

-- Teo 2.7: ∀ n, 2 * n = n + n
theorem teo_2_7 : Γ ⊢ forall_ (mul two (.var 0) =eq add (.var 0) (.var 0)) := by sorry

-- Teo 2.8: ∀ n, σ(n) = n + 1
theorem teo_2_8 : Γ ⊢ forall_ (succ (.var 0) =eq add (.var 0) one) := by sorry

-- Teo 3.11 (Predecessor Axiom as Theorem)
theorem teo_3_11 : Γ ⊢ forall_ (neg ((.var 0) =eq zero) ⇒ ex (succ (.var 0) =eq (.var 1))) := by sorry

-- Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
theorem teo_2_9 : Γ ⊢ forall_2 ( (add (.var 1) (.var 0) =eq zero) ⇒ (land ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by sorry

-- Teo 2.10: a * b = 0 ⇒ a = 0 ∨ b = 0
theorem teo_2_10 : Γ ⊢ forall_2 ( (mul (.var 1) (.var 0) =eq zero) ⇒ (lor ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by sorry

-- Teo 2.11: 2 * a = 2 * b ⇒ a = b
theorem teo_2_11 : Γ ⊢ forall_2 ( (mul two (.var 1) =eq mul two (.var 0)) ⇒ ((.var 1) =eq (.var 0)) ) := by sorry

/-!
### Decidibilidad de la Igualdad
-/

/-- Ax20 convertido en teorema: `∀n,m, n=m ∨ ¬(n=m)`.
    Prueba: por tricotomía (ax19), los casos `n<m` y `m<n` producen `¬(n=m)`
    via irreflexividad (ax18) + `eq_subst`; el caso `n=m` es directo. -/
theorem eq_decidable : Γ ⊢ ax20_eq_decidable := by
  -- ax20_eq_decidable = forall_2 (((.var 1) =eq (.var 0)) ∨ ¬(.var 1) =eq (.var 0))
  -- Estrategia:
  --   1. gen para introducir n (var 1) y m (var 0)
  --   2. or_elim sobre ax19 especializado en n, m:
  --      · Caso n < m: si n=m entonces n<n por eq_subst, contradice ax18 → ¬(n=m)
  --      · Caso n = m: or_intro_left directo
  --      · Caso m < n: simétrico al primer caso
  --   3. gen cierra las cuantificaciones
  sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block1

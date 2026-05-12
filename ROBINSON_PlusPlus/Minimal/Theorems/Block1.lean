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
-- Prueba: ax6(zero,n): 0+n = n+0; ax4(n): n+0 = n.
theorem teo_2_2 : Γ ⊢ forall_ (add zero (.var 0) =eq (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax6 := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_zero := spec h_ax4 n
  simp only [substFormula, substTerm, substTerms, add, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_zero
  have h_comm := spec (spec h_ax6 zero) n
  simp only [substFormula, substTerm, substTerms, add, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_comm
  exact eq_trans h_comm h_zero

-- Teo 2.3: ∀ n, n * 0 = 0
-- Prueba: Ax 8.
theorem teo_2_3 : Γ ⊢ ax8_mul_zero :=
  ax (by simp [axioms, ax8_mul_zero])

-- Teo 2.4: ∀ n, 0 * n = 0
-- Prueba: ax10(zero,n): 0*n = n*0; ax8(n): n*0 = 0.
theorem teo_2_4 : Γ ⊢ forall_ (mul zero (.var 0) =eq zero) := by
  unfold Γ; apply gen; intro n
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax8  := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
  have h_zero := spec h_ax8 n
  simp only [substFormula, substTerm, substTerms, mul, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_zero
  have h_comm := spec (spec h_ax10 zero) n
  simp only [substFormula, substTerm, substTerms, mul, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_comm
  exact eq_trans h_comm h_zero

-- Teo 2.5: ∀ n, n * 1 = n
-- Prueba: ax9(n,0): n*σ(0)=(n*0)+n; ax8(n): n*0=0; teo_2_2(n): 0+n=n.
theorem teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax8 := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
  -- n*1 = (n*0)+n
  have h1 := spec (spec h_ax9 n) zero
  simp only [substFormula, substTerm, substTerms, mul, zero, add, succ, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h1
  -- n*0 = 0
  have h_n0 := spec h_ax8 n
  simp only [substFormula, substTerm, substTerms, mul, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_n0
  -- (n*0)+n = 0+n
  have h2 := eq_congr_add_right (u := n) h_n0
  -- 0+n = n
  have h3 := spec teo_2_2 n
  simp only [substFormula, substTerm, substTerms, add, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h3
  -- n*1 = 0+n via h1, h2; then = n via h3
  exact eq_trans (eq_symm (eq_trans (eq_symm h1) h2)) h3

-- Teo 2.6: ∀ n, 1 * n = n
-- Prueba: ax10(one,n): 1*n = n*1; teo_2_5: n*1=n.
theorem teo_2_6 : Γ ⊢ forall_ (mul one (.var 0) =eq (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_comm := spec (spec h_ax10 one) n
  simp only [substFormula, substTerm, substTerms, mul, zero, succ, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_comm
  have h_n1 := spec teo_2_5 n
  simp only [substFormula, substTerm, substTerms, mul, zero, succ, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_n1
  exact eq_trans h_comm h_n1

-- Teo 2.7: ∀ n, 2 * n = n + n
-- Prueba: ax10(two,n): 2*n=n*2; ax9(n,1): n*2=(n*1)+n; teo_2_5: n*1=n.
theorem teo_2_7 : Γ ⊢ forall_ (mul two (.var 0) =eq add (.var 0) (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- 2*n = n*2
  have h_comm := spec (spec h_ax10 two) n
  simp only [substFormula, substTerm, substTerms, mul, zero, succ, add, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_comm
  -- n*2 = (n*1)+n
  have h_mul2 := spec (spec h_ax9 n) one
  simp only [substFormula, substTerm, substTerms, mul, zero, succ, add, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_mul2
  -- n*1 = n
  have h_n1 := spec teo_2_5 n
  simp only [substFormula, substTerm, substTerms, mul, zero, succ, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_n1
  -- (n*1)+n = n+n
  have h_n1n := eq_congr_add_right (u := n) h_n1
  -- 2*n = n*2 = (n*1)+n = n+n
  exact eq_trans h_comm (eq_trans h_mul2 h_n1n)

-- Teo 2.8: ∀ n, σ(n) = n + 1
-- Prueba: ax5(n,0): n+σ(0)=σ(n+0); ax4(n): n+0=n; congr_succ.
-- Entonces n+1 = n+σ(0) = σ(n+0) = σ(n), luego σ(n)=n+1.
theorem teo_2_8 : Γ ⊢ forall_ (succ (.var 0) =eq add (.var 0) one) := by
  unfold Γ; apply gen; intro n
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  -- n + 1 = σ(n + 0)
  have h1 := spec (spec h_ax5 n) zero
  simp only [substFormula, substTerm, substTerms, add, zero, succ, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h1
  -- n + 0 = n
  have h_n0 := spec h_ax4 n
  simp only [substFormula, substTerm, substTerms, add, zero, liftTerm, liftTerms, FOL.substTerm_liftTerm, if_true, if_false, Nat.reduceEq, Nat.reduceLT, Nat.reduceBEq] at h_n0
  -- σ(n + 0) = σ(n)
  have h2 := eq_congr_succ h_n0
  -- σ(n) = n + 1
  exact eq_symm (eq_trans h1 h2)

-- Teo 3.11 (Predecessor Axiom as Theorem)
-- Para n≠0: tricotomía da n<0 (imposible por ax13+ax2) ∨ n=0 (contradice hip) ∨ 0<n.
-- Caso 0<n: ax13 da ∃k, 0+σ(k)=n; teo_2_2 simplifica a σ(k)=n.
theorem teo_3_11 : Γ ⊢ forall_ (neg ((.var 0) =eq zero) ⇒ ex (succ (.var 0) =eq (.var 1))) := by
  unfold Γ; apply gen; intro n
  simp only [substFormula, substTerm, substTerms, neg]
  apply Axioms.imp_intro; intro h_neq
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : axioms ⊢ (lt n zero ∨ (n =eq zero) ∨ lt zero n) := by
    have h := spec (spec h_ax19 n) zero
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  -- Helper: lt x zero → ⊥ (usando ax13: lt x zero ↔ ∃k, x+σk=0, luego ax5+ax2 dan ⊥)
  have lt_zero_impossible : ∀ x : Term, axioms ⊢ lt x zero → axioms ⊢ ⊥ := fun x h_ltx0 => by
    have hh := spec (spec h_ax13 x) zero
    simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0)
    intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ, zero, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  apply or_elim h_tric
  · intro h_lt; exact false_elim (lt_zero_impossible n h_lt)
  · intro h23; apply or_elim h23
    · intro h_n_zero; exact false_elim (mp h_neq h_n_zero)
    · -- caso 0 < n: ax13 da ∃k, 0+σ(k)=n
      intro h_lt_zero_n
      have hh2 := spec (spec h_ax13 zero) n
      simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
            FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh2
      apply ex_elim (iff_mp hh2 h_lt_zero_n)
      intro k h_k
      simp [substFormula, substTerm, substTerms, add, succ, zero, liftTerm, liftTerms,
            FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at h_k
      have h_zero_add : axioms ⊢ (add zero (succ k) =eq succ k) := by
        have hs := spec teo_2_2 (succ k)
        simp [substFormula, substTerm, substTerms, add, zero, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at hs
        exact hs
      have h_succ_k_n : axioms ⊢ (succ k =eq n) := eq_trans h_zero_add h_k
      apply ex_intro k
      simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm]
      exact h_succ_k_n

-- Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
theorem teo_2_9 : Γ ⊢ forall_2 ( (add (.var 1) (.var 0) =eq zero) ⇒ (land ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by
  unfold Γ; apply gen; intro a; apply gen; intro b
  simp [substFormula, substTerm, substTerms, add, zero, land, FOL.substTerm_liftTerm]
  apply Axioms.imp_intro; intro h_sum
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  -- Helper: lt x zero → ⊥
  have lt_zero_impossible : ∀ x : Term, axioms ⊢ lt x zero → axioms ⊢ ⊥ := fun x h_ltx0 => by
    have hh := spec (spec h_ax13 x) zero
    simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0)
    intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ, zero, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  -- Tricotomía sobre b
  have h_tric_b : axioms ⊢ (lt b zero ∨ (b =eq zero) ∨ lt zero b) := by
    have h := spec (spec h_ax19 b) zero
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  -- Paso 1: b = 0
  have h_b_zero : axioms ⊢ (b =eq zero) := by
    apply or_elim h_tric_b
    · intro h_lt; exact false_elim (lt_zero_impossible b h_lt)
    · intro h23; apply or_elim h23
      · intro h; exact h
      · -- caso 0 < b: ∃k, 0+succ(k) = b, luego succ(k) = b, luego a+succ(k)=succ(a+k)=a+b=0 ⊥
        intro h_lt_0b
        have hh2 := spec (spec h_ax13 zero) b
        simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
              FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh2
        apply ex_elim (iff_mp hh2 h_lt_0b); intro k h_k
        simp [substFormula, substTerm, substTerms, add, succ, zero, liftTerm, liftTerms,
              FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at h_k
        -- h_k : add zero (succ k) = b
        have h_zero_add : axioms ⊢ (add zero (succ k) =eq succ k) := by
          have hs := spec teo_2_2 (succ k)
          simp [substFormula, substTerm, substTerms, add, zero, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at hs
          exact hs
        have h_sk_b : axioms ⊢ (succ k =eq b) := eq_trans h_zero_add h_k
        -- a + succ(k) = succ(a+k) by ax5
        have h_as := spec (spec h_ax5 a) k
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h_as
        -- a + b = a + succ(k) since succ(k) = b
        have h_ab_eq : axioms ⊢ (add a b =eq add a (succ k)) := eq_congr_add_left (eq_symm h_sk_b)
        -- succ(a+k) = a+b = 0
        have h_s0 : axioms ⊢ (succ (add a k) =eq zero) :=
          eq_trans (eq_symm h_as) (eq_trans h_ab_eq h_sum)
        have h_neg := spec h_ax2 (add a k)
        simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h_neg
        exact false_elim (mp h_neg h_s0)
  -- Paso 2: a = 0 usando b = 0 y h_sum
  have h_a_zero : axioms ⊢ (a =eq zero) := by
    have h_a0 := spec h_ax4 a
    simp [substFormula, substTerm, substTerms, add, zero, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h_a0
    -- h_a0 : a + 0 = a; h_b_zero : b = 0; h_sum : a + b = 0
    -- a = a+0 = a+b = 0
    exact eq_trans (eq_symm h_a0) (eq_trans (eq_congr_add_left h_b_zero) h_sum)
  -- Combinar: land (a=0) (b=0)
  simp only [substFormula, substTerm, substTerms, land, liftTerm, liftTerms, FOL.substTerm_liftTerm]
  exact and_intro h_a_zero h_b_zero

-- Teo 2.10: a * b = 0 ⇒ a = 0 ∨ b = 0
theorem teo_2_10 : Γ ⊢ forall_2 ( (mul (.var 1) (.var 0) =eq zero) ⇒ (lor ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by
  unfold Γ; apply gen; intro a; apply gen; intro b
  simp [substFormula, substTerm, substTerms, mul, zero, lor, FOL.substTerm_liftTerm]
  apply Axioms.imp_intro; intro h_mul
  -- h_mul : axioms ⊢ (mul a b =eq zero)
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  -- Helper: lt x zero → ⊥
  have lt_zero_impossible : ∀ x : Term, axioms ⊢ lt x zero → axioms ⊢ ⊥ := fun x h_ltx0 => by
    have hh := spec (spec h_ax13 x) zero
    simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0); intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ, zero, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  -- Helper: obtener predecesor si ≠ 0
  have get_pred : ∀ x : Term, axioms ⊢ neg (x =eq zero) →
      ∃ k : Term, axioms ⊢ (succ k =eq x) := fun x h_neq => by
    have h_tric : axioms ⊢ (lt x zero ∨ (x =eq zero) ∨ lt zero x) := by
      have h := spec (spec h_ax19 x) zero
      simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
      exact h
    -- Solo el caso 0 < x es posible
    have h_lt : axioms ⊢ lt zero x := by
      apply or_elim h_tric
      · intro h_lt; exact false_elim (lt_zero_impossible x h_lt)
      · intro h23; apply or_elim h23
        · intro h_eq; exact false_elim (mp h_neq h_eq)
        · intro h; exact h
    have hh2 := spec (spec h_ax13 zero) x
    simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh2
    have h_ex := iff_mp hh2 h_lt
    -- h_ex : ∃k, add zero (succ k) = x
    -- Usamos ex_elim para extraer k pero necesitamos devolver un ∃ en Lean meta
    -- Esto no se puede hacer directamente con ex_elim ya que el tipo de retorno no es Derives
    -- Usamos una existencia proposicional
    exact ⟨_, by
      apply ex_elim h_ex; intro k h_k
      simp [substFormula, substTerm, substTerms, add, succ, zero, liftTerm, liftTerms,
            FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at h_k
      have h_zero_add : axioms ⊢ (add zero (succ k) =eq succ k) := by
        have hs := spec teo_2_2 (succ k)
        simp [substFormula, substTerm, substTerms, add, zero, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at hs
        exact hs
      exact eq_trans h_zero_add h_k⟩
  -- Tricotomía sobre b
  have h_tric_b : axioms ⊢ (lt b zero ∨ (b =eq zero) ∨ lt zero b) := by
    have h := spec (spec h_ax19 b) zero
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  -- split b = 0 ∨ b ≠ 0
  apply or_elim h_tric_b
  · -- caso lt b zero: imposible
    intro h_lt; exact false_elim (lt_zero_impossible b h_lt)
  · intro h23; apply or_elim h23
    · -- caso b = 0: concluir b = 0
      intro h_b_zero
      simp only [substFormula, substTerm, substTerms, lor, liftTerm, liftTerms, FOL.substTerm_liftTerm]
      exact or_intro_right h_b_zero
    · -- caso 0 < b → b ≠ 0, obtener predecesor k con succ k = b
      intro h_lt_0b
      have h_neq_b : axioms ⊢ neg (b =eq zero) := by
        apply raa; intro h_b_zero
        exact lt_zero_impossible b (by
          have hh2 := spec (spec h_ax13 zero) b
          simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
                FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh2
          rw [show b = zero from by
            have := iff_mpr hh2
            exact absurd h_lt_0b (by
              intro _
              exact mp h_b_zero (eq_refl b))] at h_lt_0b
          exact h_lt_0b)
      obtain ⟨k, h_sk_b⟩ := get_pred b h_neq_b
      -- k with succ k = b
      -- Tricotomía sobre a
      have h_tric_a : axioms ⊢ (lt a zero ∨ (a =eq zero) ∨ lt zero a) := by
        have h := spec (spec h_ax19 a) zero
        simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
        exact h
      apply or_elim h_tric_a
      · intro h_lt; exact false_elim (lt_zero_impossible a h_lt)
      · intro h23a; apply or_elim h23a
        · -- caso a = 0
          intro h_a_zero
          simp only [substFormula, substTerm, substTerms, lor, liftTerm, liftTerms, FOL.substTerm_liftTerm]
          exact or_intro_left h_a_zero
        · -- caso 0 < a → a ≠ 0, obtener j con succ j = a
          intro h_lt_0a
          have h_neq_a : axioms ⊢ neg (a =eq zero) := by
            apply raa; intro h_a_zero
            exact lt_zero_impossible a (by
              have hh2 := spec (spec h_ax13 zero) a
              simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
                    FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh2
              rw [show a = zero from by exact absurd h_lt_0a (by intro _; exact mp h_a_zero (eq_refl a))] at h_lt_0a
              exact h_lt_0a)
          obtain ⟨j, h_sj_a⟩ := get_pred a h_neq_a
          -- j with succ j = a
          -- a * b = succ(j) * succ(k) = succ(j)*k + succ(j) (ax9)
          have h_ax9_inst : axioms ⊢ (mul (succ j) (succ k) =eq add (mul (succ j) k) (succ j)) := by
            have hs := spec (spec h_ax9 (succ j)) k
            simp [substFormula, substTerm, substTerms, mul, add, succ, liftTerm, liftTerms,
                  FOL.substTerm_liftTerm] at hs
            exact hs
          -- mul a b = mul (succ j) (succ k)
          have h_mul_ab : axioms ⊢ (mul a b =eq mul (succ j) (succ k)) := by
            exact eq_congr_mul_left (eq_symm h_sk_b) |>.trans (eq_congr_mul_right (eq_symm h_sj_a))
          -- add (mul (succ j) k) (succ j) = succ (add (mul (succ j) k) j)
          have h_add_succ : axioms ⊢ (add (mul (succ j) k) (succ j) =eq succ (add (mul (succ j) k) j)) := by
            have hs := spec (spec h_ax5 (mul (succ j) k)) j
            simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
                  FOL.substTerm_liftTerm] at hs
            exact hs
          -- succ (...) = 0 is false by ax2
          have h_succ_neq0 : axioms ⊢ neg (succ (add (mul (succ j) k) j) =eq zero) := by
            have hn := spec h_ax2 (add (mul (succ j) k) j)
            simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
                  FOL.substTerm_liftTerm] at hn
            exact hn
          -- chain: 0 = a*b = a*succ(k) = a*k+a = add(a*k)(succ j) = succ(a*k+j) ≠ 0
          have h_chain : axioms ⊢ (succ (add (mul (succ j) k) j) =eq zero) :=
            eq_trans (eq_symm h_add_succ) (eq_trans (eq_symm h_ax9_inst) (eq_trans (eq_symm h_mul_ab) h_mul))
          exact false_elim (mp h_succ_neq0 h_chain)

-- Teo 2.11: 2 * a = 2 * b ⇒ a = b
-- Prueba: teo_2_7 da 2*a = a+a y 2*b = b+b. Luego a+a = b+b.
-- ax27_add_left_cancel especializado con c=a: (a+a = b+a) ⇒ a=b.
-- Usando ax6 (comm): b+a = a+b; y ax27 con c=b: (a+b = b+b) ⇒ a=b.
-- Cadena: a+a = b+b, y ax6: b+b=b+b (trivial). Usamos ax27 con c=b:
-- ax27(a,b,b): (a+b=b+b) ⇒ (a=b). Y sabemos a+a=b+b, ax6(a,b): a+b = b+a,
-- ax6(b,a): b+a = a+b... Necesitamos ax27 con otro argumento.
-- Forma directa: ax27 con var2=a, var1=b, var0=a:
--   (a + a = b + a) ⇒ (a = b); pero tenemos b+b no b+a.
-- Mejor: ax27(a,b,b): (a+b = b+b) ⇒ a=b. Tenemos a+a=b+b.
-- ax6(a,b): a+b = b+a (no directamente a+a, a tiene b en 2° posición)
-- Si tenemos a+a = b+b, y ax6(b,a): b+a = a+b, con ax27:
-- ax27(a,b,b): (a+b = b+b) ⇒ a=b. Necesitamos a+b = b+b.
-- Pero de a+a = b+b y ax6(a,a): a+a = a+a (trivial). Nada nuevo.
-- Por ax6: b+b = b+b (trivial). Hmm.
-- Otra ruta: ax27(a,b,a): (a+a = b+a) ⇒ (a=b). Queremos a+a=b+a de a+a=b+b.
-- Necesitamos b+a=b+b → a=b (ax27 por cancell izq, pero ax27 cancela der).
-- En realidad ax27_add_left_cancel: forall_3 (add var2 var0 =eq add var1 var0) ⇒ var2=var1
-- es CANCELACIÓN POR LA DERECHA: c+a=c+b ⇒ a=b? No: var2+var0=var1+var0 ⇒ var2=var1.
-- Así que: a+c = b+c ⇒ a=b. (cancela c del lado derecho de ambos).
-- Con c=a: a+a = b+a ⇒ a=b. Necesitamos b+a = b+a... no tenemos a+a=b+a.
-- Con c=b: a+b = b+b ⇒ a=b. Necesitamos a+b = b+b desde a+a=b+b.
-- a+b = b+b desde a+a=b+b:
--   ax6(a,b): a+b = b+a; ax6(b,b): b+b = b+b (trivial).
--   Necesitamos b+a = b+b. Desde a+a=b+b y ax6(a,a)=ax6(b,b)... circular.
-- Forma aún más directa: usamos ax27 con c=a (cancela a por la derecha):
--   ax27(a,b,a): a+a = b+a ⇒ a=b.
--   Queremos probar a+a = b+a, que se sigue de a+a=b+b y b+b=b+a?
--   b+b = b+a iff b=a... circular.
-- La prueba directa más simple: ax6(b,b): b+b=b+b; y usamos ax27 con c=b:
--   a+b = b+b ⇒ a=b. Pero necesitamos a+b desde a+a=b+b.
--   a+a = b+b y ax6(a,b): a+b=b+a. No da a+b=b+b directo.
-- Conclusión: sin inducción, necesitamos ax6 de forma asimétrica.
-- Ruta final:
--   a+a=b+b (hipótesis, vía teo_2_7)
--   ax6(a,a): a+a = a+a (trivial)
--   ax6(b,b): b+b = b+b (trivial)
--   No podemos simplificar más.
-- Prueba verdadera: ax27 con var2=a, var1=b, var0=a:
--   (a+a = b+a) ⇒ (a=b)
-- y para probar a+a=b+a desde a+a=b+b, necesitaríamos b=a (circular).
-- Más elegante: usar ax27 con cancelar `a` del lado derecho:
--   ax27(a, b, a): a+a=b+a ⇒ a=b
-- Para obtener a+a=b+a de a+a=b+b: necesitaríamos b+b=b+a... no tenemos.
-- CORRECCIÓN: Vía ax6 (conmutatividad) podemos reescribir:
--   De h: 2*a=2*b, por teo_2_7: a+a = b+b (via eq_trans).
--   Por ax6(a,b): a+b = b+a. Por ax6(b,a): b+a = a+b.
--   NADA DE ESTO da a+a=b+a directamente sin inducción.
-- PRUEBA USANDO AX27 DOS VECES (válida):
--   ax6(a,b): a+b=b+a, ax6(b,b): b+b=b+b (trivial)
--   ax27(a,b,b): a+b=b+b ⇒ a=b. Necesitamos a+b=b+b.
--   De a+a=b+b y por eq_symm: b+b=a+a. Por ax6(b,a): b+a=a+b.
--   ax27(b,a,a): b+a=a+a ⇒ b=a. Esto nos da b=a, luego a=b (eq_symm)!
--   Y ax6 da b+a=a+a (ax6(b,a) instanciado + eq_symm de h).
-- PLAN FINAL:
--   h_2a_eq_2b: 2*a=2*b (hipótesis, de spec teo_2_11)
--   h_aa: 2*a = a+a (teo_2_7 spec a)
--   h_bb: 2*b = b+b (teo_2_7 spec b)
--   h_sum: a+a = b+b (transitivity via eq_trans)
--   h_ax6_ba: b+a = a+b (ax6 spec b, a)
--   h_ax4_rw: a+a = b+b (ya tenemos)
--   queremos: b+a = a+a (← eq_symm h_sum y ax6_ba → b+a = a+b ≠ a+a en general)
--   OOPS, esto no funciona directamente.
--
-- NOTA: Esta prueba requiere inducción o algo más fuerte. Dejamos sorry.
theorem teo_2_11 : Γ ⊢ forall_2 ( (mul two (.var 1) =eq mul two (.var 0)) ⇒ ((.var 1) =eq (.var 0)) ) := by sorry

/-!
### Decidibilidad de la Igualdad
-/

/-- Ax20 convertido en teorema: `∀n,m, n=m ∨ ¬(n=m)`.
    Prueba: por tricotomía (ax19), los casos `n<m` y `m<n` producen `¬(n=m)`
    via irreflexividad (ax18) + sustitución de igualdad; el caso `n=m` es directo. -/
theorem eq_decidable : Γ ⊢ ax20_eq_decidable := by
  unfold Γ; unfold ax20_eq_decidable; unfold forall_2
  apply gen; intro n; apply gen; intro m
  -- Simplificamos el goal (substFormula aplicado) para obtener (n=m) ∨ ¬(n=m)
  simp only [substFormula, substTerm, substTerms, neg, liftTerm, liftTerms,
             FOL.substTerm_liftTerm, if_true, if_false]
  -- Ahora goal: axioms ⊢ (n =eq m) ∨ neg (n =eq m)
  -- Tricotomía: lt n m ∨ n=m ∨ lt m n
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : axioms ⊢ (lt n m ∨ (n =eq m) ∨ lt m n) := by
    have h := spec (spec h_ax19 n) m
    simp only [substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
               FOL.substTerm_liftTerm, if_true, if_false] at h
    exact h
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  -- Helper: derive contradiction from lt x x
  have lt_irrefl : ∀ x : Term, axioms ⊢ lt x x → axioms ⊢ ⊥ := fun x h_ltxx => by
    have h_irr := spec h_ax18 x
    simp only [substFormula, lt, FOL.substTerm_liftTerm] at h_irr
    exact mp h_irr h_ltxx
  -- Para los casos lt n m y lt m n: si n=m entonces lt n n, contradice irrefl
  -- f_n : la fórmula "lt n (.var 0)" con .var 0 como hueco para m
  let f_n := Formula.eq (liftTerm 0 n) (.var 0)
  have hS_m_fn : substFormula 0 m f_n = (n =eq m) := by
    simp only [f_n, substFormula, substTerm, substTerms, liftTerm, liftTerms,
               FOL.substTerm_liftTerm, if_true, if_false]
  have hS_n_fn : substFormula 0 n f_n = (n =eq n) := by
    simp only [f_n, substFormula, substTerm, substTerms, liftTerm, liftTerms,
               FOL.substTerm_liftTerm, if_true, if_false]
  -- Para lt n m caso: de h_eq : n=m y h_lt_nm : lt n m, deriva lt n n
  -- Approach: usando Derives.subst con la fórmula lt n (.var 0)
  let f_lt_n := Formula.atom lt_sym [liftTerm 0 n, .var 0]
  have hS_m_lt : substFormula 0 m f_lt_n = lt n m := by
    simp only [f_lt_n, substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
               FOL.substTerm_liftTerm, if_true, if_false]
  have hS_n_lt : substFormula 0 n f_lt_n = lt n n := by
    simp only [f_lt_n, substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
               FOL.substTerm_liftTerm, if_true, if_false]
  apply or_elim h_tric
  · -- caso lt n m → ¬(n=m)
    intro h_lt_nm
    apply or_intro_right
    apply raa; intro h_eq
    have h_lt_nn : axioms ⊢ lt n n :=
      hS_n_lt ▸ Derives.subst axioms m n f_lt_n (eq_symm h_eq) (hS_m_lt ▸ h_lt_nm)
    exact lt_irrefl n h_lt_nn
  · intro h23
    apply or_elim h23
    · -- caso n=m → n=m ∨ ¬(n=m)
      intro h_eq; exact or_intro_left h_eq
    · -- caso lt m n → ¬(n=m)
      intro h_lt_mn
      apply or_intro_right
      apply raa; intro h_eq
      -- De h_eq: n=m y h_lt_mn: lt m n → lt m m (usando eq_symm h_eq: m=n, subst var 0 en lt m (.var 0))
      let f_lt_m := Formula.atom lt_sym [liftTerm 0 m, .var 0]
      have hS_n_lt_m : substFormula 0 n f_lt_m = lt m n := by
        simp only [f_lt_m, substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
                   FOL.substTerm_liftTerm, if_true, if_false]
      have hS_m_lt_m : substFormula 0 m f_lt_m = lt m m := by
        simp only [f_lt_m, substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
                   FOL.substTerm_liftTerm, if_true, if_false]
      have h_lt_mm : axioms ⊢ lt m m :=
        hS_m_lt_m ▸ Derives.subst axioms n m f_lt_m h_eq (hS_n_lt_m ▸ h_lt_mn)
      exact lt_irrefl m h_lt_mm

end ROBINSON_PlusPlus.Minimal.Theorems.Block1

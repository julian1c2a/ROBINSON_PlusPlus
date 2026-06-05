/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import FOL.FOL
import FOL.Tactics

set_option linter.unusedSimpArgs true

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
  simp [substFormula, substTerm, substTerms, add, zero] at h_zero
  have h_comm := spec (spec h_ax6 zero) n
  simp [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm] at h_comm
  exact eq_trans (eq_symm h_comm) h_zero

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
  simp [substFormula, substTerm, substTerms, mul, zero] at h_zero
  have h_comm := spec (spec h_ax10 zero) n
  simp [substFormula, substTerm, substTerms, mul, zero, FOL.substTerm_liftTerm] at h_comm
  exact eq_trans (eq_symm h_comm) h_zero

-- Teo 2.5: ∀ n, n * 1 = n
-- Prueba: ax9(n,0): n*σ(0)=(n*0)+n; ax8(n): n*0=0; teo_2_2(n): 0+n=n.
theorem teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax8 := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
  -- n*1 = (n*0)+n
  have h1 := spec (spec h_ax9 n) zero
  simp [substFormula, substTerm, substTerms, mul, zero, add, succ, FOL.substTerm_liftTerm] at h1
  -- n*0 = 0
  have h_n0 := spec h_ax8 n
  simp [substFormula, substTerm, substTerms, mul, zero] at h_n0
  -- (n*0)+n = 0+n
  have h2 := eq_congr_add_right (u := n) h_n0
  -- 0+n = n
  have h3 := spec teo_2_2 n
  simp [substFormula, substTerm, substTerms, add, zero] at h3
  -- n*1 = 0+n via h1, h2; then = n via h3
  exact eq_trans (eq_symm (eq_trans (eq_symm h1) h2)) h3

-- Teo 2.6: ∀ n, 1 * n = n
-- Prueba: ax10(one,n): 1*n = n*1; teo_2_5: n*1=n.
theorem teo_2_6 : Γ ⊢ forall_ (mul one (.var 0) =eq (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_comm := spec (spec h_ax10 one) n
  simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at h_comm
  have h_n1 := spec teo_2_5 n
  simp [substFormula, substTerm, substTerms, mul] at h_n1
  exact eq_trans (eq_symm h_comm) h_n1

-- Teo 2.7: ∀ n, 2 * n = n + n
-- Prueba: ax10(two,n): 2*n=n*2; ax9(n,1): n*2=(n*1)+n; teo_2_5: n*1=n.
theorem teo_2_7 : Γ ⊢ forall_ (mul two (.var 0) =eq add (.var 0) (.var 0)) := by
  unfold Γ; apply gen; intro n
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- 2*n = n*2
  have h_comm := spec (spec h_ax10 two) n
  simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at h_comm
  -- n*2 = (n*1)+n
  have h_mul2 := spec (spec h_ax9 n) one
  simp [substFormula, substTerm, substTerms, mul, succ, add, FOL.substTerm_liftTerm] at h_mul2
  -- n*1 = n
  have h_n1 := spec teo_2_5 n
  simp [substFormula, substTerm, substTerms, mul] at h_n1
  -- (n*1)+n = n+n
  have h_n1n := eq_congr_add_right (u := n) h_n1
  -- 2*n = n*2 = (n*1)+n = n+n
  exact eq_trans (eq_symm (eq_trans (eq_symm h_comm) h_mul2)) h_n1n

-- Helper para `teo_2_11`: 2*(σk) ≠ 0
-- 2*(σk) = σk + σk = σ(σk + k) ≠ 0 (ax2). Sin inducción.
theorem mul_two_succ_ne_zero (k : Term) : Γ ⊢ neg (mul two (succ k) =eq zero) := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_t27 : Γ ⊢ (mul two (succ k) =eq add (succ k) (succ k)) := by
    have hh := spec teo_2_7 (succ k)
    simp [substFormula, substTerm, substTerms, mul, add, succ] at hh
    exact hh
  have h_a5 : Γ ⊢ (add (succ k) (succ k) =eq succ (add (succ k) k)) := by
    have hh := spec (spec h_ax5 (succ k)) k
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at hh
    exact hh
  have h_chain : Γ ⊢ (mul two (succ k) =eq succ (add (succ k) k)) :=
    FOL.derive_eq_trans h_t27 h_a5
  apply raa; intro h_eq
  have h_zero : Γ ⊢ (succ (add (succ k) k) =eq zero) :=
    FOL.derive_eq_trans (eq_symm h_chain) h_eq
  have h_neq : Γ ⊢ neg (succ (add (succ k) k) =eq zero) := by
    have hh := spec h_ax2 (add (succ k) k)
    simp [succ, zero] at hh
    exact hh
  exact mp h_neq h_zero

-- Helper para `teo_2_11`: a < b ⇒ 2a < 2b (monotonía estricta de *2)
-- Prueba sin inducción: si a + σk = b, entonces 2b = 2a + 2σk = 2a + σ(σk+k).
-- Testigo para ax13: j := σk+k da 2a + σj = 2b.
theorem mul_two_lt_mono {a b : Term} (h : Γ ⊢ lt a b) : Γ ⊢ lt (mul two a) (mul two b) := by
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax12 := ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  -- a < b: ∃k, a + σk = b
  have h_iff_ab :
      Γ ⊢ ((lt a b) ⇔ ex (add (liftTerm 0 a) (succ (.var 0)) =eq liftTerm 0 b)) := by
    have hh := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at hh
    exact hh
  have h_ex := iff_mp h_iff_ab h
  apply ex_elim h_ex; intro k h_k_raw
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm] at h_k_raw
  -- 2b = 2(a + σk) = 2a + 2σk
  have h_2b_eq : Γ ⊢ (mul two b =eq mul two (add a (succ k))) :=
    eq_congr_mul_left (eq_symm h_k_raw)
  have h_distrib : Γ ⊢
      (mul two (add a (succ k)) =eq add (mul two a) (mul two (succ k))) := by
    have hh := spec (spec (spec h_ax12 two) a) (succ k)
    simp [substFormula, substTerm, substTerms, mul, add, succ,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at hh
    exact hh
  have h_2b_chain : Γ ⊢ (mul two b =eq add (mul two a) (mul two (succ k))) :=
    FOL.derive_eq_trans h_2b_eq h_distrib
  -- 2*(σk) = σ(σk + k)
  have h_2sk_succ : Γ ⊢ (mul two (succ k) =eq succ (add (succ k) k)) := by
    have h_t27 : Γ ⊢ (mul two (succ k) =eq add (succ k) (succ k)) := by
      have hh := spec teo_2_7 (succ k)
      simp [substFormula, substTerm, substTerms, mul, add, succ] at hh
      exact hh
    have h_a5 : Γ ⊢ (add (succ k) (succ k) =eq succ (add (succ k) k)) := by
      have hh := spec (spec h_ax5 (succ k)) k
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans h_t27 h_a5
  -- 2b = 2a + σ(σk + k); testigo j := σk+k para ax13
  have h_2b_succ : Γ ⊢ (mul two b =eq add (mul two a) (succ (add (succ k) k))) :=
    FOL.derive_eq_trans h_2b_chain (eq_congr_add_left h_2sk_succ)
  have h_iff_2a2b :
      Γ ⊢ ((lt (mul two a) (mul two b)) ⇔
            ex (add (liftTerm 0 (mul two a)) (succ (.var 0)) =eq liftTerm 0 (mul two b))) := by
    have hh := spec (spec h_ax13 (mul two a)) (mul two b)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at hh
    exact hh
  apply iff_mpr h_iff_2a2b
  exact ex_intro (add (succ k) k) (by
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm]
    exact eq_symm h_2b_succ)

-- Teo 2.8: ∀ n, σ(n) = n + 1
-- Prueba: ax5(n,0): n+σ(0)=σ(n+0); ax4(n): n+0=n; congr_succ.
-- Entonces n+1 = n+σ(0) = σ(n+0) = σ(n), luego σ(n)=n+1.
theorem teo_2_8 : Γ ⊢ forall_ (succ (.var 0) =eq add (.var 0) one) := by
  unfold Γ; apply gen; intro n
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  -- n + 1 = σ(n + 0)
  have h1 := spec (spec h_ax5 n) zero
  simp [substFormula, substTerm, substTerms, add, zero, succ, FOL.substTerm_liftTerm] at h1
  -- n + 0 = n
  have h_n0 := spec h_ax4 n
  simp [substFormula, substTerm, substTerms, add, zero] at h_n0
  -- σ(n + 0) = σ(n)
  have h2 := eq_congr_succ h_n0
  -- σ(n) = n + 1
  exact eq_symm (eq_trans (eq_symm h1) h2)

-- Teo 3.11 (Predecessor Axiom as Theorem)
-- Para n≠0: tricotomía da n<0 (imposible por ax13+ax2) ∨ n=0 (contradice hip) ∨ 0<n.
-- Caso 0<n: ax13 da ∃k, 0+σ(k)=n; teo_2_2 simplifica a σ(k)=n.
theorem teo_3_11 : Γ ⊢ forall_ (neg ((.var 0) =eq zero) ⇒ ex (succ (.var 0) =eq (.var 1))) := by
  unfold Γ; apply gen; intro n
  simp [substFormula, substTerm, neg]
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
          FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0)
    intro k h_k
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [succ] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  apply or_elim h_tric
  · intro h_lt; exact false_elim (lt_zero_impossible n h_lt)
  · intro h23; apply or_elim h23
    · intro h_n_zero; exact false_elim (mp h_neq h_n_zero)
    · -- caso 0 < n: ax13 da ∃k, 0+σ(k)=n
      intro h_lt_zero_n
      have hh2 := spec (spec h_ax13 zero) n
      simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms] at hh2
      apply ex_elim (iff_mp hh2 h_lt_zero_n)
      intro k h_k
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm] at h_k
      have h_zero_add : axioms ⊢ (add zero (succ k) =eq succ k) := by
        have hs := spec teo_2_2 (succ k)
        simp [substFormula, substTerm, substTerms, add, zero, succ] at hs
        exact hs
      have h_succ_k_n : axioms ⊢ (succ k =eq n) := eq_trans h_zero_add h_k
      apply ex_intro k
      simp [substFormula, substTerm, substTerms, succ,
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
          FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0)
    intro k h_k
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [succ] at hn
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
        simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms] at hh2
        apply ex_elim (iff_mp hh2 h_lt_0b); intro k h_k
        simp [substFormula, substTerm, substTerms,
              FOL.substTerm_liftTerm] at h_k
        -- h_k : add zero (succ k) = b
        have h_zero_add : axioms ⊢ (add zero (succ k) =eq succ k) := by
          have hs := spec teo_2_2 (succ k)
          simp [substFormula, substTerm, substTerms, add, zero, succ] at hs
          exact hs
        have h_sk_b : axioms ⊢ (succ k =eq b) := eq_trans h_zero_add h_k
        -- a + succ(k) = succ(a+k) by ax5
        have h_as := spec (spec h_ax5 a) k
        simp [substFormula, substTerm, substTerms, add, succ,
              FOL.substTerm_liftTerm] at h_as
        -- a + b = a + succ(k) since succ(k) = b
        have h_ab_eq : axioms ⊢ (add a b =eq add a (succ k)) := eq_congr_add_left (eq_symm h_sk_b)
        -- succ(a+k) = a+b = 0
        have h_s0 : axioms ⊢ (succ (add a k) =eq zero) :=
          eq_trans h_as (eq_trans h_ab_eq h_sum)
        have h_neg := spec h_ax2 (add a k)
        simp [succ] at h_neg
        exact false_elim (mp h_neg h_s0)
  -- Paso 2: a = 0 usando b = 0 y h_sum
  have h_a_zero : axioms ⊢ (a =eq zero) := by
    have h_a0 := spec h_ax4 a
    simp [substFormula, substTerm, substTerms, add, zero] at h_a0
    -- h_a0 : a + 0 = a; h_b_zero : b = 0; h_sum : a + b = 0
    -- a = a+0 = a+b = 0
    exact eq_trans h_a0 (eq_trans (eq_congr_add_left h_b_zero) h_sum)
  -- Combinar: land (a=0) (b=0)
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
          FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0); intro k h_k
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [succ] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  -- Tricotomía sobre b
  have h_tric_b : axioms ⊢ (lt b zero ∨ (b =eq zero) ∨ lt zero b) := by
    have h := spec (spec h_ax19 b) zero
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  apply or_elim h_tric_b
  · intro h_lt; exact false_elim (lt_zero_impossible b h_lt)
  · intro h23; apply or_elim h23
    · -- caso b = 0
      intro h_b_zero; exact or_intro_right h_b_zero
    · -- caso 0 < b: extraer predecesor k con succ k = b via ex_elim
      intro h_lt_0b
      have hh2_b := spec (spec h_ax13 zero) b
      simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms] at hh2_b
      apply ex_elim (iff_mp hh2_b h_lt_0b); intro k h_k_raw
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm] at h_k_raw
      have h_zero_add_k : axioms ⊢ (add zero (succ k) =eq succ k) := by
        have hs := spec teo_2_2 (succ k)
        simp [substFormula, substTerm, substTerms, add, zero, succ] at hs
        exact hs
      have h_sk_b : axioms ⊢ (succ k =eq b) := eq_trans h_zero_add_k h_k_raw
      -- Tricotomía sobre a
      have h_tric_a : axioms ⊢ (lt a zero ∨ (a =eq zero) ∨ lt zero a) := by
        have h := spec (spec h_ax19 a) zero
        simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
        exact h
      apply or_elim h_tric_a
      · intro h_lt; exact false_elim (lt_zero_impossible a h_lt)
      · intro h23a; apply or_elim h23a
        · -- caso a = 0
          intro h_a_zero; exact or_intro_left h_a_zero
        · -- caso 0 < a: extraer predecesor j con succ j = a via ex_elim
          intro h_lt_0a
          have hh2_a := spec (spec h_ax13 zero) a
          simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms] at hh2_a
          apply ex_elim (iff_mp hh2_a h_lt_0a); intro j h_j_raw
          simp [substFormula, substTerm, substTerms,
                FOL.substTerm_liftTerm] at h_j_raw
          have h_zero_add_j : axioms ⊢ (add zero (succ j) =eq succ j) := by
            have hs := spec teo_2_2 (succ j)
            simp [substFormula, substTerm, substTerms, add, zero, succ] at hs
            exact hs
          have h_sj_a : axioms ⊢ (succ j =eq a) := eq_trans h_zero_add_j h_j_raw
          -- a * b = succ(j) * succ(k) (ax9)
          have h_ax9_inst : axioms ⊢ (mul (succ j) (succ k) =eq add (mul (succ j) k) (succ j)) := by
            have hs := spec (spec h_ax9 (succ j)) k
            simp [substFormula, substTerm, substTerms, mul, add, succ, liftTerm, liftTerms,
                  FOL.substTerm_liftTerm] at hs
            exact hs
          have h_mul_ab : axioms ⊢ (mul a b =eq mul (succ j) (succ k)) :=
            FOL.derive_eq_trans (eq_congr_mul_left (eq_symm h_sk_b)) (eq_congr_mul_right (eq_symm h_sj_a))
          -- add(sj*k)(sj) = succ(sj*k+j)
          have h_add_succ : axioms ⊢ (add (mul (succ j) k) (succ j) =eq succ (add (mul (succ j) k) j)) := by
            have hs := spec (spec h_ax5 (mul (succ j) k)) j
            simp [substFormula, substTerm, substTerms, add, succ,
                  FOL.substTerm_liftTerm] at hs
            exact hs
          have h_succ_neq0 : axioms ⊢ neg (succ (add (mul (succ j) k) j) =eq zero) := by
            have hn := spec h_ax2 (add (mul (succ j) k) j)
            simp [succ] at hn
            exact hn
          -- chain: succ(sj*k+j) = add(sj*k)(sj) = sj*sk = a*b = 0, contradicts ax2
          have h_chain : axioms ⊢ (succ (add (mul (succ j) k) j) =eq zero) :=
            FOL.derive_eq_trans (FOL.derive_eq_trans (FOL.derive_eq_trans
              (eq_symm h_add_succ) (eq_symm h_ax9_inst)) (eq_symm h_mul_ab)) h_mul
          exact false_elim (mp h_succ_neq0 h_chain)

-- Teo 2.11: 2 * a = 2 * b ⇒ a = b  (Cancelación por 2)
-- Demostrado directamente SIN inducción y SIN el axioma ax28 (eliminado).
-- Estrategia (TuplasFuncionesYListas.md §2.11): tricotomía (ax19) +
-- monotonía estricta de *2 (mul_two_lt_mono) + irreflexividad (ax18).
-- Los casos a<b y b<a llevan a 2a < 2b (resp. 2b < 2a); sustituyendo con
-- h_eq: 2a=2b obtenemos lt 2a 2a, contradiciendo ax18.
theorem teo_2_11 :
    Γ ⊢ forall_2 ( (mul two (.var 1) =eq mul two (.var 0)) ⇒ ((.var 1) =eq (.var 0)) ) := by
  unfold Γ; unfold forall_2
  apply gen; intro a; apply gen; intro b
  simp [substFormula, substTerm, substTerms, mul, two, one, succ,
        FOL.substTerm_liftTerm]
  apply Axioms.imp_intro; intro h_eq
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : axioms ⊢ (lt a b ∨ (a =eq b) ∨ lt b a) := by
    have hh := spec (spec h_ax19 a) b
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
    exact hh
  -- Irreflexividad para 2a
  have h_irr_2a : axioms ⊢ neg (lt (mul two a) (mul two a)) := by
    have hh := spec h_ax18 (mul two a)
    simp [lt] at hh; exact hh
  -- Helpers de sustitución (estilo eq_decidable, ver §Decidibilidad arriba)
  let f_lt_2a : Formula := Formula.atom lt_sym [mul two (liftTerm 0 a), .var 0]
  have hS_2b : substFormula 0 (mul two b) f_lt_2a = lt (mul two a) (mul two b) := by
    simp only [f_lt_2a, substFormula, substTerm, substTerms, lt, mul, two, one, succ, zero,
               FOL.substTerm_liftTerm, if_true]
  have hS_2a : substFormula 0 (mul two a) f_lt_2a = lt (mul two a) (mul two a) := by
    simp only [f_lt_2a, substFormula, substTerm, substTerms, lt, mul, two, one, succ, zero,
               FOL.substTerm_liftTerm, if_true]
  let f_lt_x2a : Formula := Formula.atom lt_sym [.var 0, mul two (liftTerm 0 a)]
  have hS_x2a_2b : substFormula 0 (mul two b) f_lt_x2a = lt (mul two b) (mul two a) := by
    simp only [f_lt_x2a, substFormula, substTerm, substTerms, lt, mul, two, one, succ, zero,
               FOL.substTerm_liftTerm, if_true]
  have hS_x2a_2a : substFormula 0 (mul two a) f_lt_x2a = lt (mul two a) (mul two a) := by
    simp only [f_lt_x2a, substFormula, substTerm, substTerms, lt, mul, two, one, succ, zero,
               FOL.substTerm_liftTerm, if_true]
  apply or_elim h_tric
  · intro h_a_lt_b
    apply false_elim
    have h_2a_lt_2b : axioms ⊢ lt (mul two a) (mul two b) := mul_two_lt_mono h_a_lt_b
    have h_2a_lt_2a : axioms ⊢ lt (mul two a) (mul two a) :=
      hS_2a ▸ Derives.subst axioms (mul two b) (mul two a) f_lt_2a (eq_symm h_eq)
        (hS_2b ▸ h_2a_lt_2b)
    exact mp h_irr_2a h_2a_lt_2a
  · intro h23
    apply or_elim h23
    · intro h_eq_ab; exact h_eq_ab
    · intro h_b_lt_a
      apply false_elim
      have h_2b_lt_2a : axioms ⊢ lt (mul two b) (mul two a) := mul_two_lt_mono h_b_lt_a
      have h_2a_lt_2a : axioms ⊢ lt (mul two a) (mul two a) :=
        hS_x2a_2a ▸ Derives.subst axioms (mul two b) (mul two a) f_lt_x2a (eq_symm h_eq)
          (hS_x2a_2b ▸ h_2b_lt_2a)
      exact mp h_irr_2a h_2a_lt_2a

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
  simp [substFormula, substTerm, neg,
             FOL.substTerm_liftTerm]
  -- Ahora goal: axioms ⊢ (n =eq m) ∨ neg (n =eq m)
  -- Tricotomía: lt n m ∨ n=m ∨ lt m n
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : axioms ⊢ (lt n m ∨ (n =eq m) ∨ lt m n) := by
    have h := spec (spec h_ax19 n) m
    simp [substFormula, substTerm, substTerms, lt,
               FOL.substTerm_liftTerm] at h
    exact h
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  -- Helper: derive contradiction from lt x x
  have lt_irrefl : ∀ x : Term, axioms ⊢ lt x x → axioms ⊢ ⊥ := fun x h_ltxx => by
    have h_irr := spec h_ax18 x
    simp only [lt] at h_irr
    exact mp h_irr h_ltxx
  -- Para los casos lt n m y lt m n: si n=m entonces lt n n, contradice irrefl
  -- f_n : la fórmula "lt n (.var 0)" con .var 0 como hueco para m
  let f_n := Formula.eq (liftTerm 0 n) (.var 0)
  have hS_m_fn : substFormula 0 m f_n = (n =eq m) := by
    simp only [f_n, substFormula, substTerm,
               FOL.substTerm_liftTerm, if_true]
  have hS_n_fn : substFormula 0 n f_n = (n =eq n) := by
    simp only [f_n, substFormula, substTerm,
               FOL.substTerm_liftTerm, if_true]
  -- Para lt n m caso: de h_eq : n=m y h_lt_nm : lt n m, deriva lt n n
  -- Approach: usando Derives.subst con la fórmula lt n (.var 0)
  let f_lt_n := Formula.atom lt_sym [liftTerm 0 n, .var 0]
  have hS_m_lt : substFormula 0 m f_lt_n = lt n m := by
    simp only [f_lt_n, substFormula, substTerm, substTerms, lt,
               FOL.substTerm_liftTerm, if_true]
  have hS_n_lt : substFormula 0 n f_lt_n = lt n n := by
    simp only [f_lt_n, substFormula, substTerm, substTerms, lt,
               FOL.substTerm_liftTerm, if_true]
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
        simp only [f_lt_m, substFormula, substTerm, substTerms, lt,
                   FOL.substTerm_liftTerm, if_true]
      have hS_m_lt_m : substFormula 0 m f_lt_m = lt m m := by
        simp only [f_lt_m, substFormula, substTerm, substTerms, lt,
                   FOL.substTerm_liftTerm, if_true]
      have h_lt_mm : axioms ⊢ lt m m :=
        hS_m_lt_m ▸ Derives.subst axioms n m f_lt_m h_eq (hS_n_lt_m ▸ h_lt_mn)
      exact lt_irrefl m h_lt_mm

end ROBINSON_PlusPlus.Minimal.Theorems.Block1

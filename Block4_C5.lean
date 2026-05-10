/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2
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
open ROBINSON_PlusPlus.Minimal.Theorems.Block2
open ROBINSON_PlusPlus.Minimal.Theorems.Block3

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

/-!
## BLOQUE IV — LEMA C5 (INVERSIÓN DE CANTOR)
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 9.1: Lema C5 - Existencia y Unicidad de `w`
-/

-- Candidate for `w`
def w_candidate (c : Term) : Term :=
  div2 (tau (sqrt (add (mul eight c) one)))

-- Lema Auxiliar: ∀ n, 2*div2(n) ≤ n
private theorem lemma_2_div2_le_n (n : Term) : Γ ⊢ le (mul two (div2 n)) n := by
  have h_range := spec mod2_range (t := n)
  apply or_elim h_range
  · intro h_mod2_eq_0 -- Caso mod2(n) = 0
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := n)
    have h_n_eq_2div2n : Γ ⊢ n =eq mul (div2 n) two := by
      have h1 := eq_trans (eq_congr_add_left h_mod2_eq_0) h_ax17
      have h2 := spec (ax ax4_add_zero) (t := mul (div2 n) two)
      rw [←h2] at h1
      exact eq_symm h1
    have h_comm := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 n)
    have h_2div2n_eq_n : Γ ⊢ mul two (div2 n) =eq n := eq_trans h_comm (eq_symm h_n_eq_2div2n)
    exact or_intro_right _ h_2div2n_eq_n
  · intro h_mod2_eq_1 -- Caso mod2(n) = 1
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := n)
    have h_n_eq_2div2n_add_1 : Γ ⊢ n =eq add (mul (div2 n) two) one := by
      exact eq_symm (eq_trans (eq_congr_add_left h_mod2_eq_1) (eq_symm h_ax17))
    have h_comm := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 n)
    have h_n_eq_add_1 : Γ ⊢ n =eq add (mul two (div2 n)) one := eq_trans h_n_eq_2div2n_add_1 (eq_congr_add_right h_comm)
    have h_teo2_8 := spec teo_2_8 (t := mul two (div2 n))
    have h_n_eq_succ : Γ ⊢ n =eq succ (mul two (div2 n)) := eq_trans h_n_eq_add_1 (eq_symm h_teo2_8)
    have h_lt := spec lt_succ_self (t := mul two (div2 n))
    have h_lt_n : Γ ⊢ lt (mul two (div2 n)) n := by rwa [←h_n_eq_succ]
    exact or_intro_left _ h_lt_n

-- Teo 9.1 (Lema C5): ∀ c, ∃! w, w*(w+1) ≤ 2*c < (w+1)*(w+2)
theorem lemma_C5 (c : Term) : Γ ⊢ ex1 (land (le (mul (.var 0) (succ (.var 0))) (mul two c)) (lt (mul two c) (mul (succ (.var 0)) (succ (succ (.var 0)))))) := by
  -- The proof is highly non-trivial and involves extensive algebraic manipulation
  -- of inequalities, relying on the properties of `sqrt` from Block II.

  -- Part 1: Existence. We show that `w_candidate c` satisfies the inequalities.
  -- The first inequality `w(w+1) ≤ 2c` is equivalent to `(2w+1)² ≤ 8c+1`.
  -- Let s = sqrt(8c+1) and p = τ(s). Then w = div2(p).
  -- We need to prove `(2*div2(p)+1)² ≤ s²`, which simplifies to `2*div2(p)+1 ≤ s`.
  -- Since s = σ(p), this is `2*div2(p)+1 ≤ p+1`, which follows from `2*div2(p) ≤ p`
  -- (our lemma `lemma_2_div2_le_n`) and monotonicity of successor.
  sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5 (
  w_candidate
  lemma_C5
)

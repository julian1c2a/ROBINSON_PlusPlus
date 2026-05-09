/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL -- Assuming this is the import path for the FOL project

namespace ROBINSON_PlusPlus.Minimal.Axioms

/-!
# Axioms of the Minimal Arithmetic System

This module defines the language and the 21 axioms of the minimal arithmetic
system as described in `TuplasFuncionesYListas.md`. This system is strong
enough to develop a theory of pairs (via Cantor's pairing function) and lists,
but it lacks a general induction principle.
-/

-- ## Language Definition

-- ### Function Symbols
def succ_sym : String := "σ"
def add_sym  : String := "+"
def mul_sym  : String := "*"
def sqrt_sym : String := "√"
def div2_sym : String := "div2"
def mod2_sym : String := "mod2"
def proj1_sym : String := "π₁"
def proj2_sym : String := "π₂"
def tau_sym : String := "τ"

-- ### Predicate Symbols
def lt_sym : String := "<"

-- ### Constant Symbols
def zero_sym : String := "0"

-- ## Term Constructors

-- Constant `0`
def zero : Term := .func zero_sym []

-- Helper functions to build terms
def succ (t : Term)   : Term := .func succ_sym [t]
def add (t₁ t₂ : Term) : Term := .func add_sym [t₁, t₂]
def mul (t₁ t₂ : Term) : Term := .func mul_sym [t₁, t₂]
def sqrt (t : Term)   : Term := .func sqrt_sym [t]
def div2 (t : Term)   : Term := .func div2_sym [t]
def mod2 (t : Term)   : Term := .func mod2_sym [t]
def proj1 (t : Term)  : Term := .func proj1_sym [t]
def proj2 (t : Term)  : Term := .func proj2_sym [t]
def tau (t : Term)    : Term := .func tau_sym [t]

-- Derived operation `sq`
def sq (t : Term) : Term := mul t t

-- Derived constants `1` and `2`
def one : Term := succ zero
def two : Term := succ one
def eight : Term := mul two (mul two two) -- 2*4

-- Cantor pairing function components
def cantor_poly (x y : Term) : Term :=
  add (mul (add x y) (succ (add x y))) (mul two y)

def cantor_func (x y : Term) : Term :=
  div2 (cantor_poly x y)

def is_cantor (x y c : Term) : Formula :=
  mul two c =eq cantor_poly x y

-- ## Formula Constructors

-- Helper function to build atomic formulas
def lt (t₁ t₂ : Term) : Formula := .atom lt_sym [t₁, t₂]
def le (t₁ t₂ : Term) : Formula := (lt t₁ t₂) ∨ (t₁ =eq t₂)

-- Helper for universal quantification over 1, 2, or 3 variables
def forall_ (f : Formula) : Formula := .forall f
def forall_2 (f : Formula) : Formula := .forall (.forall f)
def forall_3 (f : Formula) : Formula := .forall (.forall (.forall f))


-- ## Axioms

-- ### Axioms of Peano Puros

-- Ax 1: ∃0
-- This is a meta-axiom stating that the constant '0' exists in our language.
-- It is handled by including `zero : Term` in the language definition.

-- Ax 2: ∀ n, σ(n) ≠ 0
def ax2_peano_succ_neq_zero : Formula :=
  forall_ (
    neg (succ (.var 0) =eq zero)
  )

-- Ax 3: ∀ n, ∀ m, σ(n) = σ(m) ⇒ n = m
def ax3_peano_succ_inj : Formula :=
  forall_2 (
    (succ (.var 1) =eq succ (.var 0)) ⇒ ((.var 1) =eq (.var 0))
  )

-- ### Axioms of the Suma

-- Ax 4: ∀ n, n + 0 = n
def ax4_add_zero : Formula :=
  forall_ (
    add (.var 0) zero =eq (.var 0)
  )

-- Ax 5: ∀ n, ∀ m, n + σ(m) = σ(n + m)
def ax5_add_succ : Formula :=
  forall_2 (
    add (.var 1) (succ (.var 0)) =eq succ (add (.var 1) (.var 0))
  )

-- ### Axiomas Algebraicos de la Suma

-- Ax 6: ∀ n, ∀ m, n + m = m + n
def ax6_add_comm : Formula :=
  forall_2 (
    add (.var 1) (.var 0) =eq add (.var 0) (.var 1)
  )

-- Ax 7: ∀ n, ∀ m, ∀ k, (n + m) + k = n + (m + k)
def ax7_add_assoc : Formula :=
  forall_3 (
    add (add (.var 2) (.var 1)) (.var 0) =eq add (.var 2) (add (.var 1) (.var 0))
  )

-- ### Axioms of the Producto

-- Ax 8: ∀ n, n * 0 = 0
def ax8_mul_zero : Formula :=
  forall_ (
    mul (.var 0) zero =eq zero
  )

-- Ax 9: ∀ n, ∀ m, n * σ(m) = (n * m) + n
def ax9_mul_succ : Formula :=
  forall_2 (
    mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1)
  )

-- ### Axiomas Algebraicos del Producto

-- Ax 10: ∀ n, ∀ m, n * m = m * n
def ax10_mul_comm : Formula :=
  forall_2 (
    mul (.var 1) (.var 0) =eq mul (.var 0) (.var 1)
  )

-- Ax 11: ∀ n, ∀ m, ∀ k, (n * m) * k = n * (m * k)
def ax11_mul_assoc : Formula :=
  forall_3 (
    mul (mul (.var 2) (.var 1)) (.var 0) =eq mul (.var 2) (mul (.var 1) (.var 0))
  )

-- Ax 12: ∀ n, ∀ m, ∀ k, n * (m + k) = (n * m) + (n * k)
def ax12_mul_distrib : Formula :=
  forall_3 (
    mul (.var 2) (add (.var 1) (.var 0)) =eq add (mul (.var 2) (.var 1)) (mul (.var 2) (.var 0))
  )

-- ### Axioma del Orden Estricto

-- Ax 13: ∀ n, ∀ m, n < m ⇔ ∃ k, n + σ(k) = m
def ax13_lt_def : Formula :=
  forall_2 (
    (lt (.var 1) (.var 0)) -- n < m
    ⇔
    (ex (add (.var 2) (succ (.var 0)) =eq (.var 1))) -- ∃k, n + σ(k) = m
  )

-- ### Axiomas de la Raíz Cuadrada

-- Ax 14: ∀ n, (√n)² ≤ n
def ax14_sqrt_le : Formula :=
  forall_ (
    le (sq (sqrt (.var 0))) (.var 0)
  )

-- Ax 15: ∀ n, n < (σ(√n))²
def ax15_lt_succ_sqrt : Formula :=
  forall_ (
    lt (.var 0) (sq (succ (sqrt (.var 0))))
  )

-- ### Axiomas de la División Entera por 2

-- Ax 16: ∀ n, mod2(n) = 0 ⇔ mod2(σ(n)) = 1
def ax16_mod2_succ : Formula :=
  forall_ (
    (mod2 (.var 0) =eq zero) ⇔ (mod2 (succ (.var 0)) =eq one)
  )

-- Ax 17: ∀ n, (div2(n) * 2) + mod2(n) = n
def ax17_div_mod_eq : Formula :=
  forall_ (
    add (mul (div2 (.var 0)) two) (mod2 (.var 0)) =eq (.var 0)
  )

-- ### Axiomas del Orden Total

-- Ax 18: ∀ n, ¬(n < n)
def ax18_lt_irrefl : Formula :=
  forall_ (
    neg (lt (.var 0) (.var 0))
  )

-- Ax 19: ∀ a, ∀ b, a < b ∨ a = b ∨ b < a
def ax19_lt_trichotomy : Formula :=
  forall_2 (
    (lt (.var 1) (.var 0))  -- a < b
    ∨ ((.var 1) =eq (.var 0)) -- a = b
    ∨ (lt (.var 0) (.var 1))  -- b < a
  )

-- Ax 20: ∀ n, ∀ m, n = m ∨ n ≠ m
def ax20_eq_decidable : Formula :=
  forall_2 (
    ((.var 1) =eq (.var 0)) ∨ (neg ((.var 1) =eq (.var 0)))
  )

-- Ax 21: ∀ n, mod2(n) = 0 ∨ mod2(n) = 1
def ax21_mod2_range : Formula :=
  forall_ (
    (mod2 (.var 0) =eq zero) ∨ (mod2 (.var 0) =eq one)
  )

-- ### Axioms of Cantor Projections (temporary, until C6 and C7 are proven)

-- Ax 22 (Surjectivity): ∀ c, ∃ x, y, Cantor(x, y, c)
-- We postulate the existence of projection functions π₁ and π₂ that witness this.
def ax22_cantor_proj_exists : Formula :=
  forall_ (
    is_cantor (proj1 (.var 0)) (proj2 (.var 0)) (.var 0)
  )

-- Ax 23 (Uniqueness): Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y'
def ax23_cantor_proj_uniq : Formula :=
  forall_ (forall_2 (forall_2 (
    (land (is_cantor (.var 3) (.var 2) (.var 4)) (is_cantor (.var 1) (.var 0) (.var 4)))
    ⇒
    (land ((.var 3) =eq (.var 1)) ((.var 2) =eq (.var 0)))
  )))

-- Ax 24 (mod2 of even): ∀ n, k, n = 2*k → mod2(n) = 0
-- This is a theorem in a system with induction, but required here.
def ax24_mod2_of_even : Formula :=
  forall_2 (
    ((.var 1) =eq (mul two (.var 0))) ⇒ (mod2 (.var 1) =eq zero)
  )

-- ### Axioms of Predecessor Function

-- Ax 25: τ(0) = 0
def ax25_tau_zero : Formula :=
  tau zero =eq zero

-- Ax 26: ∀n, τ(σ(n)) = n
def ax26_tau_succ : Formula :=
  forall_ (tau (succ (.var 0)) =eq (.var 0))

-- ## Axiom Set

/-- The complete list of axioms for the Minimal system. -/
def axioms : List Formula := [
  ax2_peano_succ_neq_zero,
  ax3_peano_succ_inj,
  ax4_add_zero,
  ax5_add_succ,
  ax6_add_comm,
  ax7_add_assoc,
  ax8_mul_zero,
  ax9_mul_succ,
  ax10_mul_comm,
  ax11_mul_assoc,
  ax12_mul_distrib,
  ax13_lt_def,
  ax14_sqrt_le,
  ax15_lt_succ_sqrt,
  ax16_mod2_succ,
  ax17_div_mod_eq,
  ax18_lt_irrefl,
  ax19_lt_trichotomy,
  ax20_eq_decidable,
  ax21_mod2_range,
  ax22_cantor_proj_exists,
  ax23_cantor_proj_uniq,
  ax24_mod2_of_even,
  ax25_tau_zero,
  ax26_tau_succ
]

end ROBINSON_PlusPlus.Minimal.Axioms

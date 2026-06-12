/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Full.Induction

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — Numerales: el puente meta↔object

`numeral : ℕ → Term` envía el natural meta `n` al término object `σⁿ(0)`.
Demostramos que la aritmética object sobre numerales **refleja** la aritmética
meta de `ℕ`:

  `axioms ⊢ numeral a + numeral b = numeral (a + b)`     (homomorfismo +)
  `axioms ⊢ numeral a · numeral b = numeral (a · b)`     (homomorfismo ·)
  `a < b → axioms ⊢ lt (numeral a) (numeral b)`           (orden)
  `a ≠ b → axioms ⊢ neg (numeral a =eq numeral b)`        (separación)

Este es el **cimiento de la representabilidad**: permite *computar* en `ℕ`
(meta, reutilizando `Peano` si conviene) y *transferir* el resultado a la
derivabilidad formal `axioms ⊢ …`. Disuelve los dos muros (extracción de
testigos y case-split) porque todo el trabajo decisional/constructivo ocurre
en `ℕ`, donde sí hay decidibilidad y elección.

Base para `Division`, `Representability`, TFA y Gödel Nivel D.
-/

/-! ### Definición de `numeral` -/

/-- `numeral n = σⁿ(0)`: el término object que representa al natural meta `n`. -/
def numeral : Nat → Term
  | 0     => zero
  | n + 1 => succ (numeral n)

@[simp] theorem numeral_zero : numeral 0 = zero := rfl
@[simp] theorem numeral_succ (n : Nat) : numeral (n + 1) = succ (numeral n) := rfl

/-! ### Helpers aritméticos object-level -/

private theorem add_zero_t (a : Term) : axioms ⊢ (add a zero =eq a) := by
  have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
  simp [substFormula, substTerm, substTerms, add, zero] at hh; exact hh

private theorem add_succ_t (a b : Term) : axioms ⊢ (add a (succ b) =eq succ (add a b)) := by
  have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem mul_zero_t (a : Term) : axioms ⊢ (mul a zero =eq zero) := by
  have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) a
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

private theorem mul_succ_t (a b : Term) : axioms ⊢ (mul a (succ b) =eq add (mul a b) a) := by
  have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

/-! ### Homomorfismo de la suma -/

/-- `axioms ⊢ numeral a + numeral b = numeral (a + b)`. Por inducción meta en `b`. -/
theorem numeral_add (a b : Nat) :
    axioms ⊢ (add (numeral a) (numeral b) =eq numeral (a + b)) := by
  induction b with
  | zero =>
    -- add (numeral a) zero =eq numeral a  (= numeral (a + 0))
    exact add_zero_t (numeral a)
  | succ k ih =>
    -- numeral (k+1) = succ (numeral k); a + (k+1) = (a+k)+1 (defeq)
    show axioms ⊢ (add (numeral a) (succ (numeral k)) =eq succ (numeral (a + k)))
    exact FOL.derive_eq_trans (add_succ_t (numeral a) (numeral k)) (eq_congr_succ ih)

/-! ### Homomorfismo del producto -/

/-- `axioms ⊢ numeral a · numeral b = numeral (a · b)`. Por inducción meta en `b`. -/
theorem numeral_mul (a b : Nat) :
    axioms ⊢ (mul (numeral a) (numeral b) =eq numeral (a * b)) := by
  induction b with
  | zero =>
    -- mul (numeral a) zero =eq zero  (= numeral (a * 0) = numeral 0)
    exact mul_zero_t (numeral a)
  | succ k ih =>
    -- mul (numeral a) (succ (numeral k)) =eq add (mul (numeral a)(numeral k)) (numeral a)
    -- = add (numeral (a*k)) (numeral a) = numeral (a*k + a) = numeral (a*(k+1))
    show axioms ⊢ (mul (numeral a) (succ (numeral k)) =eq numeral (a * k + a))
    have h9 : axioms ⊢ (mul (numeral a) (succ (numeral k)) =eq
                        add (mul (numeral a) (numeral k)) (numeral a)) :=
      mul_succ_t (numeral a) (numeral k)
    have hcongr : axioms ⊢ (add (mul (numeral a) (numeral k)) (numeral a) =eq
                            add (numeral (a * k)) (numeral a)) :=
      eq_congr_add_right (u := numeral a) ih
    have hhom : axioms ⊢ (add (numeral (a * k)) (numeral a) =eq numeral (a * k + a)) :=
      numeral_add (a * k) a
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h9 hcongr) hhom

/-! ### Homomorfismo de la potencia -/

private theorem pow_zero_t (a : Term) : axioms ⊢ (pow a zero =eq one) := by
  have hh := spec (ax (by simp [axioms] : ax_pow_zero ∈ axioms)) a
  simp [substFormula, substTerm, substTerms, pow, zero, one, succ] at hh; exact hh

private theorem pow_succ_t (a b : Term) :
    axioms ⊢ (pow a (succ b) =eq mul (pow a b) a) := by
  have hh := spec (spec (ax (by simp [axioms] : ax_pow_succ ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, pow, mul, succ, FOL.substTerm_liftTerm] at hh
  exact hh

/-- `axioms ⊢ numeral a ^ numeral b = numeral (a ^ b)`. Por inducción meta en `b`.
    Base de la codificación primorial de secuencias para Gödel. -/
theorem numeral_pow (a b : Nat) :
    axioms ⊢ (pow (numeral a) (numeral b) =eq numeral (a ^ b)) := by
  induction b with
  | zero =>
    -- pow (numeral a) zero =eq one = numeral 1 = numeral (a^0)
    exact pow_zero_t (numeral a)
  | succ k ih =>
    -- pow (numeral a)(succ (numeral k)) =eq mul (pow (numeral a)(numeral k)) (numeral a)
    -- = mul (numeral (a^k)) (numeral a) = numeral (a^k * a) = numeral (a^(k+1))
    show axioms ⊢ (pow (numeral a) (succ (numeral k)) =eq numeral (a ^ k * a))
    have hps : axioms ⊢ (pow (numeral a) (succ (numeral k)) =eq
                         mul (pow (numeral a) (numeral k)) (numeral a)) :=
      pow_succ_t (numeral a) (numeral k)
    have hcongr : axioms ⊢ (mul (pow (numeral a) (numeral k)) (numeral a) =eq
                            mul (numeral (a ^ k)) (numeral a)) :=
      eq_congr_mul_right (u := numeral a) ih
    have hhom : axioms ⊢ (mul (numeral (a ^ k)) (numeral a) =eq numeral (a ^ k * a)) :=
      numeral_mul (a ^ k) a
    exact FOL.derive_eq_trans (FOL.derive_eq_trans hps hcongr) hhom

/-! ### Orden: `a < b` meta ⇒ `lt (numeral a) (numeral b)` object -/

/-- `a < b` (meta) ⇒ `axioms ⊢ lt (numeral a) (numeral b)`.

    `a < b` significa `b = a + (k+1)` para `k = b - a - 1`; el testigo del
    `∃` de `ax13` es `numeral k`. -/
theorem numeral_lt {a b : Nat} (h : a < b) :
    axioms ⊢ lt (numeral a) (numeral b) := by
  -- b = a + (k+1) con k := b - a - 1
  obtain ⟨k, hk⟩ : ∃ k : Nat, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
  subst hk
  have h13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have hiff := spec (spec h13 (numeral a)) (numeral (a + (k + 1)))
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply iff_mpr hiff
  apply ex_intro (numeral k)
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- Goal: axioms ⊢ (add (numeral a) (succ (numeral k)) =eq numeral (a + (k+1)))
  -- numeral (a + (k+1)) = numeral ((a+k)+1) = succ (numeral (a+k))
  show axioms ⊢ (add (numeral a) (succ (numeral k)) =eq succ (numeral (a + k)))
  exact FOL.derive_eq_trans (add_succ_t (numeral a) (numeral k)) (eq_congr_succ (numeral_add a k))

/-! ### Separación: `a ≠ b` meta ⇒ `neg (numeral a = numeral b)` object -/

/-- `lt a b → neg (a = b)` (orden estricto separa). Vía `ax18` (irreflexividad). -/
private theorem lt_imp_ne {a b : Term} (h : axioms ⊢ lt a b) :
    axioms ⊢ neg (a =eq b) := by
  apply raa; intro heq
  -- de a = b y lt a b: lt a a (sustituyendo b por a), contradice ax18.
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s
    simp only [f, substFormula, lt, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  have hlt_aa : axioms ⊢ lt a a :=
    (hS a) ▸ Derives.subst axioms b a f (eq_symm heq) ((hS b) ▸ h)
  have hirr : axioms ⊢ neg (lt a a) := by
    have hh := spec lt_irrefl_thm a
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
    exact hh
  exact mp hirr hlt_aa

/-- `a ≠ b` (meta) ⇒ `axioms ⊢ neg (numeral a = numeral b)`. -/
theorem numeral_ne {a b : Nat} (h : a ≠ b) :
    axioms ⊢ neg (numeral a =eq numeral b) := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact lt_imp_ne (numeral_lt hlt)
  · have hlt : b < a := by omega
    exact eq_symm_neg (lt_imp_ne (numeral_lt hlt))

/-! ### Numerales de constantes pequeñas (puente con la notación de Minimal) -/

@[simp] theorem numeral_one : numeral 1 = one := rfl
@[simp] theorem numeral_two : numeral 2 = two := rfl

end ROBINSON_PlusPlus.Full

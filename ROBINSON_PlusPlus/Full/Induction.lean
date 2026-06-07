/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — INDUCCIÓN GENERAL (object-level, lift-aware)

`Full` añade sobre `Minimal` el **esquema de inducción general** como **axioma
object-level** (`ax_induction`). Las demostraciones de los axiomas algebraicos
de `Minimal` (que aquí pasan a teoremas) se hacen por derivación object-level
—`spec`, `mp`, `gen`, `imp_intro`— usando ese axioma.

**Codificación lift-aware**: `φ(σn)` se codifica como
`substFormula 0 (σ#0) (liftFormula 1 φ)`, que preserva las variables-parámetro
de `φ` (la versión ingenua `substFormula 0 (σ#0) φ` las decrementaba, rompiendo
la inducción multivariable). El lema de composición `substTerm_subst_succ_lift`
+ `step_eq_reduce` reducen el paso a la forma `φ(n) ⇒ φ(σn)` con sustituciones
únicas, manejables como en `Minimal`.
-/

/-! ### Lema de composición de sustitución (De Bruijn, offset 0) -/

mutual
theorem substTerm_subst_succ_lift (m t : Term) :
    substTerm 0 m (substTerm 0 (succ (.var 0)) (liftTerm 1 t)) = substTerm 0 (succ m) t := by
  cases t with
  | var j =>
    by_cases hj : j = 0
    · subst hj; simp [liftTerm, substTerm, substTerms, succ]
    · have h1 : ¬ j < 1 := by omega
      have h2 : ¬ (j + 1 = 0) := by omega
      have h3 : j + 1 > 0 := by omega
      have h4 : j > 0 := by omega
      simp [liftTerm, substTerm, substTerms, succ, hj, h1, h2, h3, h4]
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_subst_succ_lift m ts
theorem substTerms_subst_succ_lift (m : Term) (ts : List Term) :
    substTerms 0 m (substTerms 0 (succ (.var 0)) (liftTerms 1 ts)) = substTerms 0 (succ m) ts := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms]
    rw [substTerm_subst_succ_lift m t, substTerms_subst_succ_lift m ts']
end

/-! ### Composición generalizada (offset arbitrario) — para fórmulas con `∀`/`∃` -/

mutual
theorem substTerm_subst_succ_lift_gen (c : Nat) (m t : Term) :
    substTerm c m (substTerm c (succ (.var c)) (liftTerm (c + 1) t)) = substTerm c (succ m) t := by
  cases t with
  | var j =>
    rcases Nat.lt_trichotomy j c with hlt | heq | hgt
    · have e1 : j < c + 1 := by omega
      simp [liftTerm, substTerm, substTerms, succ, e1,
            show ¬ j = c from by omega, show ¬ j > c from by omega, hlt]
    · subst heq
      simp [liftTerm, substTerm, substTerms, succ, show j < j + 1 from by omega]
    · have e1 : ¬ j < c + 1 := by omega
      simp [liftTerm, substTerm, substTerms, succ, e1,
            show ¬ (j + 1 = c) from by omega, show j + 1 > c from by omega,
            show ¬ (j = c) from by omega, hgt]
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_subst_succ_lift_gen c m ts
theorem substTerms_subst_succ_lift_gen (c : Nat) (m : Term) (ts : List Term) :
    substTerms c m (substTerms c (succ (.var c)) (liftTerms (c + 1) ts)) = substTerms c (succ m) ts := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms]
    rw [substTerm_subst_succ_lift_gen c m t, substTerms_subst_succ_lift_gen c m ts']
end

/-- Composición generalizada para **toda** fórmula (cualquier offset). -/
theorem substFormula_succ_lift_gen (c : Nat) (m : Term) (φ : Formula) :
    substFormula c m (substFormula c (succ (.var c)) (liftFormula (c + 1) φ))
      = substFormula c (succ m) φ := by
  induction φ generalizing c m with
  | bottom => rfl
  | atom p ts =>
      simp only [liftFormula, substFormula]
      rw [substTerms_subst_succ_lift_gen]
  | eq t u =>
      simp only [liftFormula, substFormula]
      rw [substTerm_subst_succ_lift_gen, substTerm_subst_succ_lift_gen]
  | impl a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c m, ihb c m]
  | «forall» a iha =>
      exact congrArg Formula.forall (iha (c + 1) (liftTerm 0 m))
  | and a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c m, ihb c m]
  | or a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c m, ihb c m]
  | ex a iha =>
      exact congrArg Formula.ex (iha (c + 1) (liftTerm 0 m))

/-- Composición a offset 0 (la usada por el paso de inducción). -/
theorem substFormula_succ_lift (n : Term) (φ : Formula) :
    substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)) = substFormula 0 (succ n) φ :=
  substFormula_succ_lift_gen 0 n φ

/-- Reduce el cuerpo del paso de inducción para **cualquier** `φ` a `φ(n) ⇒ φ(σn)`. -/
theorem step_reduce (n : Term) (φ : Formula) :
    substFormula 0 n (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))
      = Formula.impl (substFormula 0 n φ) (substFormula 0 (succ n) φ) := by
  show Formula.impl (substFormula 0 n φ)
        (substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))
     = Formula.impl (substFormula 0 n φ) (substFormula 0 (succ n) φ)
  rw [substFormula_succ_lift]

/-- Composición para fórmulas de igualdad (suficiente: las fórmulas de inducción
    algebraica son ecuaciones, sin cuantificadores internos). -/
theorem substFormula_eq_succ_lift (n t u : Term) :
    substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u)))
      = substFormula 0 (succ n) (Formula.eq t u) := by
  show Formula.eq (substTerm 0 n (substTerm 0 (succ (.var 0)) (liftTerm 1 t)))
                  (substTerm 0 n (substTerm 0 (succ (.var 0)) (liftTerm 1 u)))
     = Formula.eq (substTerm 0 (succ n) t) (substTerm 0 (succ n) u)
  rw [substTerm_subst_succ_lift, substTerm_subst_succ_lift]

/-- Reduce el cuerpo del paso de inducción (para `φ` ecuación) a `φ(n) ⇒ φ(σn)`. -/
theorem step_eq_reduce (n t u : Term) :
    substFormula 0 n (Formula.impl (Formula.eq t u)
        (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u))))
      = Formula.impl (substFormula 0 n (Formula.eq t u)) (substFormula 0 (succ n) (Formula.eq t u)) := by
  show Formula.impl (substFormula 0 n (Formula.eq t u))
        (substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u))))
     = Formula.impl (substFormula 0 n (Formula.eq t u)) (substFormula 0 (succ n) (Formula.eq t u))
  rw [substFormula_eq_succ_lift]

/-! ### Esquema de inducción general (axioma object-level) -/

/-- Fórmula de inducción para `φ` (variable libre `0`), lift-aware:
    `φ(0) ⇒ ((∀n. φ(n) ⇒ φ(σn)) ⇒ ∀n. φ(n))` con `φ(σn) = substFormula 0 (σ#0) (liftFormula 1 φ)`. -/
def inductionFormula (φ : Formula) : Formula :=
  Formula.impl (substFormula 0 zero φ)
    (Formula.impl
      (Formula.forall (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ))))
      (Formula.forall φ))

/-- **Esquema de inducción general** como axioma object-level. -/
axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ

/-- Empaquetado object-level (doble `mp` sobre `ax_induction`). No es regla meta. -/
theorem induction_object {φ : Formula}
    (base : axioms ⊢ substFormula 0 zero φ)
    (step : axioms ⊢ Formula.forall
              (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))) :
    axioms ⊢ Formula.forall φ := by
  have hind := ax_induction φ
  simp only [inductionFormula] at hind
  exact mp (mp hind base) step

/-! ### `zero_add` (sin parámetro) -/

theorem zero_add : axioms ⊢ Formula.forall (add zero (.var 0) =eq (.var 0)) := by
  apply induction_object
  · show axioms ⊢ (add zero zero =eq zero)
    have h := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) zero
    simp [substFormula, substTerm, substTerms, add, zero] at h
    exact h
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro hn
    have hn' : axioms ⊢ (add zero n =eq n) := hn
    show axioms ⊢ (add zero (succ n) =eq succ n)
    have h5 : axioms ⊢ (add zero (succ n) =eq succ (add zero n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) zero) n
      simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans h5 (eq_congr_succ hn')

/-! ### `succ_add` (con parámetro) -/

theorem succ_add (a : Term) :
    axioms ⊢ Formula.forall
      (add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))) := by
  apply induction_object
  · -- base: add (σa) 0 = σ(add a 0)
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm]
    have hA : axioms ⊢ (add (succ a) zero =eq succ a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) (succ a)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hh
      exact hh
    have hB : axioms ⊢ (add a zero =eq a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm (eq_congr_succ hB))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have h5sa : axioms ⊢ (add (succ a) (succ n) =eq succ (add (succ a) n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) (succ a)) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h5a : axioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5sa (eq_congr_succ ih))
      (eq_symm (eq_congr_succ h5a))

/-! ### `add_comm` (= `ax6`) por inducción object-level -/

theorem add_comm_ax (a : Term) :
    axioms ⊢ Formula.forall
      (add (liftTerm 0 a) (.var 0) =eq add (.var 0) (liftTerm 0 a)) := by
  apply induction_object
  · -- base: add a 0 = add 0 a
    simp only [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm]
    have hA : axioms ⊢ (add a zero =eq a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have hB : axioms ⊢ (add zero a =eq a) := by
      have hh := spec zero_add a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm hB)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have h5 : axioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have hsucc : axioms ⊢ (add (succ n) a =eq succ (add n a)) := by
      have hh := spec (succ_add n) a
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5 (eq_congr_succ ih)) (eq_symm hsucc)

/-- **`ax6` de `Minimal` es teorema en `Full`**: `⊢ ∀a ∀b, a+b = b+a`. -/
theorem add_comm_thm : axioms ⊢ ax6_add_comm := by
  apply gen; intro a
  exact add_comm_ax a

/-! ### `add_assoc` (= `ax7`) — inducción sobre el tercer argumento, 2 parámetros -/

theorem add_assoc_ax (a b : Term) :
    axioms ⊢ Formula.forall
      (add (add (liftTerm 0 a) (liftTerm 0 b)) (.var 0)
        =eq add (liftTerm 0 a) (add (liftTerm 0 b) (.var 0))) := by
  apply induction_object
  · -- base: (a+b)+0 = a+(b+0)
    simp only [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm]
    have h1 : axioms ⊢ (add (add a b) zero =eq add a b) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) (add a b)
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have hb0 : axioms ⊢ (add b zero =eq b) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) b
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans h1 (eq_symm (eq_congr_add_left hb0))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have hL : axioms ⊢ (add (add a b) (succ n) =eq succ (add a (add b n))) := by
      have h5 : axioms ⊢ (add (add a b) (succ n) =eq succ (add (add a b) n)) := by
        have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) (add a b)) n
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      exact FOL.derive_eq_trans h5 (eq_congr_succ ih)
    have hR : axioms ⊢ (add a (add b (succ n)) =eq succ (add a (add b n))) := by
      have hb5 : axioms ⊢ (add b (succ n) =eq succ (add b n)) := by
        have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) b) n
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      have ha5 : axioms ⊢ (add a (succ (add b n)) =eq succ (add a (add b n))) := by
        have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) (add b n)
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      exact FOL.derive_eq_trans (eq_congr_add_left hb5) ha5
    exact FOL.derive_eq_trans hL (eq_symm hR)

-- NOTA: el empaquetado `⊢ ax7_add_assoc` (∀³) vía `gen` triple topa con el
-- ajuste de niveles `liftTerm` de los parámetros (a/b acumulan lifts distintos
-- a `liftTerm 0`). Pendiente: helper de empaquetado n-ario. `add_assoc_ax` ya
-- es la derivación sustantiva de ax7. (Para ∀² —ax6, ax10— el empaquetado sí
-- sale directo, ver `add_comm_thm`.)

/-! ### `zero_mul` (sin parámetro) — base de la cadena de `mul` -/

theorem zero_mul : axioms ⊢ Formula.forall (mul zero (.var 0) =eq zero) := by
  apply induction_object
  · show axioms ⊢ (mul zero zero =eq zero)
    have h := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) zero
    simp [substFormula, substTerm, substTerms, mul, zero] at h
    exact h
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    have ih' : axioms ⊢ (mul zero n =eq zero) := ih
    show axioms ⊢ (mul zero (succ n) =eq zero)
    have h9 : axioms ⊢ (mul zero (succ n) =eq add (mul zero n) zero) := by
      have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) zero) n
      simp [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm] at hh
      exact hh
    have hz : axioms ⊢ (add zero zero =eq zero) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) zero
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h9 (eq_congr_add_right ih')) hz

/-! ### Helpers de instanciación (axiomas y lemas derivados en términos concretos) -/

private theorem add_zero1 (x : Term) : axioms ⊢ (add x zero =eq x) := by
  have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) x
  simp [substFormula, substTerm, substTerms, add, zero] at hh; exact hh

private theorem add_succ2 (x y : Term) : axioms ⊢ (add x (succ y) =eq succ (add x y)) := by
  have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) x) y
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem add_assoc3 (x y z : Term) :
    axioms ⊢ (add (add x y) z =eq add x (add y z)) := by
  have hh := spec (add_assoc_ax x y) z
  simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh; exact hh

private theorem add_comm2 (x y : Term) : axioms ⊢ (add x y =eq add y x) := by
  have hh := spec (add_comm_ax x) y
  simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh; exact hh

private theorem mul_zero1 (x : Term) : axioms ⊢ (mul x zero =eq zero) := by
  have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) x
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

private theorem mul_succ2 (x y : Term) : axioms ⊢ (mul x (succ y) =eq add (mul x y) x) := by
  have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) x) y
  simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem zero_mul1 (x : Term) : axioms ⊢ (mul zero x =eq zero) := by
  have hh := spec zero_mul x
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

/-! ### `succ_mul` (con parámetro) — `∀n, σa·n = a·n + n` -/

theorem succ_mul (a : Term) :
    axioms ⊢ Formula.forall
      (mul (succ (liftTerm 0 a)) (.var 0) =eq add (mul (liftTerm 0 a) (.var 0)) (.var 0)) := by
  apply induction_object
  · -- base: σa·0 = a·0 + 0
    simp only [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm]
    -- goal: mul (succ a) zero =eq add (mul a zero) zero
    have hR : axioms ⊢ (add (mul a zero) zero =eq zero) :=
      FOL.derive_eq_trans (eq_congr_add_right (mul_zero1 a)) (add_zero1 zero)
    exact FOL.derive_eq_trans (mul_zero1 (succ a)) (eq_symm hR)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    -- ih: σa·n = a·n + n ; goal: σa·σn = a·σn + σn
    have hL : axioms ⊢ (mul (succ a) (succ n) =eq add (mul a n) (succ (add a n))) :=
      FOL.derive_eq_trans (mul_succ2 (succ a) n)
        (FOL.derive_eq_trans (eq_congr_add_right ih)
          (FOL.derive_eq_trans (add_assoc3 (mul a n) n (succ a))
            (FOL.derive_eq_trans (eq_congr_add_left (u := mul a n) (add_succ2 n a))
              (eq_congr_add_left (u := mul a n) (eq_congr_succ (add_comm2 n a))))))
    have hRr : axioms ⊢ (add (mul a (succ n)) (succ n) =eq add (mul a n) (succ (add a n))) :=
      FOL.derive_eq_trans (eq_congr_add_right (mul_succ2 a n))
        (FOL.derive_eq_trans (add_assoc3 (mul a n) a (succ n))
          (eq_congr_add_left (u := mul a n) (add_succ2 a n)))
    exact FOL.derive_eq_trans hL (eq_symm hRr)

private theorem succ_mul2 (x y : Term) : axioms ⊢ (mul (succ x) y =eq add (mul x y) y) := by
  have hh := spec (succ_mul x) y
  simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

/-! ### `mul_comm` (= `ax10`) — `∀n, a·n = n·a` -/

theorem mul_comm_ax (a : Term) :
    axioms ⊢ Formula.forall (mul (liftTerm 0 a) (.var 0) =eq mul (.var 0) (liftTerm 0 a)) := by
  apply induction_object
  · -- base: a·0 = 0·a
    simp only [substFormula, substTerm, substTerms, mul, zero, FOL.substTerm_liftTerm]
    exact FOL.derive_eq_trans (mul_zero1 a) (eq_symm (zero_mul1 a))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    -- ih: a·n = n·a ; goal: a·σn = σn·a
    exact FOL.derive_eq_trans
      (FOL.derive_eq_trans (mul_succ2 a n) (eq_congr_add_right ih))
      (eq_symm (succ_mul2 n a))

/-- **`ax10` (mul_comm)** es teorema en `Full`: `⊢ ∀a ∀b, a·b = b·a`. -/
theorem mul_comm_thm : axioms ⊢ ax10_mul_comm := by
  apply gen; intro a
  exact mul_comm_ax a

/-! ### `mul_distrib` (= `ax12`) — `∀c, a·(b+c) = a·b + a·c` (2 parámetros) -/

theorem mul_distrib_ax (a b : Term) :
    axioms ⊢ Formula.forall
      (mul (liftTerm 0 a) (add (liftTerm 0 b) (.var 0))
        =eq add (mul (liftTerm 0 a) (liftTerm 0 b)) (mul (liftTerm 0 a) (.var 0))) := by
  apply induction_object
  · -- base: a·(b+0) = a·b + a·0
    simp only [substFormula, substTerm, substTerms, mul, add, zero, FOL.substTerm_liftTerm]
    have hLb : axioms ⊢ (mul a (add b zero) =eq mul a b) := eq_congr_mul_left (u := a) (add_zero1 b)
    have hRb : axioms ⊢ (add (mul a b) (mul a zero) =eq mul a b) :=
      FOL.derive_eq_trans (eq_congr_add_left (u := mul a b) (mul_zero1 a)) (add_zero1 (mul a b))
    exact FOL.derive_eq_trans hLb (eq_symm hRb)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have hL : axioms ⊢ (mul a (add b (succ n)) =eq add (mul a b) (add (mul a n) a)) :=
      FOL.derive_eq_trans (eq_congr_mul_left (u := a) (add_succ2 b n))
        (FOL.derive_eq_trans (mul_succ2 a (add b n))
          (FOL.derive_eq_trans (eq_congr_add_right ih)
            (add_assoc3 (mul a b) (mul a n) a)))
    have hR : axioms ⊢ (add (mul a b) (mul a (succ n)) =eq add (mul a b) (add (mul a n) a)) :=
      eq_congr_add_left (u := mul a b) (mul_succ2 a n)
    exact FOL.derive_eq_trans hL (eq_symm hR)

private theorem mul_distrib3 (x y z : Term) :
    axioms ⊢ (mul x (add y z) =eq add (mul x y) (mul x z)) := by
  have hh := spec (mul_distrib_ax x y) z
  simp [substFormula, substTerm, substTerms, mul, add, FOL.substTerm_liftTerm] at hh; exact hh

/-! ### `mul_assoc` (= `ax11`) — `∀c, (a·b)·c = a·(b·c)` (2 parámetros) -/

theorem mul_assoc_ax (a b : Term) :
    axioms ⊢ Formula.forall
      (mul (mul (liftTerm 0 a) (liftTerm 0 b)) (.var 0)
        =eq mul (liftTerm 0 a) (mul (liftTerm 0 b) (.var 0))) := by
  apply induction_object
  · -- base: (a·b)·0 = a·(b·0)
    simp only [substFormula, substTerm, substTerms, mul, zero, FOL.substTerm_liftTerm]
    have hR : axioms ⊢ (mul a (mul b zero) =eq zero) :=
      FOL.derive_eq_trans (eq_congr_mul_left (u := a) (mul_zero1 b)) (mul_zero1 a)
    exact FOL.derive_eq_trans (mul_zero1 (mul a b)) (eq_symm hR)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have hL : axioms ⊢ (mul (mul a b) (succ n) =eq add (mul a (mul b n)) (mul a b)) :=
      FOL.derive_eq_trans (mul_succ2 (mul a b) n) (eq_congr_add_right ih)
    have hR : axioms ⊢ (mul a (mul b (succ n)) =eq add (mul a (mul b n)) (mul a b)) :=
      FOL.derive_eq_trans (eq_congr_mul_left (u := a) (mul_succ2 b n)) (mul_distrib3 a (mul b n) b)
    exact FOL.derive_eq_trans hL (eq_symm hR)

/-! ### `lt_irrefl` (= `ax18`) — primer axioma NO ecuacional, vía `step_reduce` general -/

theorem lt_irrefl_ax : axioms ⊢ Formula.forall (neg (lt (.var 0) (.var 0))) := by
  apply induction_object
  · -- base: ¬(0 < 0)
    show axioms ⊢ neg (lt zero zero)
    apply raa; intro hlt
    have h13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
    have hiff := spec (spec h13 zero) zero
    simp [substFormula, substTerm, substTerms, lt, zero, succ, iff, liftTerm, liftTerms] at hiff
    apply ex_elim (iff_mp hiff hlt); intro k hk
    simp [substFormula, substTerm, substTerms, add, zero, succ] at hk
    -- hk : add zero (succ k) =eq zero
    have hz : axioms ⊢ (add zero (succ k) =eq succ k) := by
      have hh := spec zero_add (succ k)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hh; exact hh
    have hne : axioms ⊢ neg (succ k =eq zero) := by
      have hh := spec (ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)) k
      simp [succ, zero] at hh; exact hh
    exact mp hne (eq_trans hz hk)
  · apply gen; intro n
    rw [step_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    have ih' : axioms ⊢ neg (lt n n) := ih
    show axioms ⊢ neg (lt (succ n) (succ n))
    apply raa; intro hlt
    have h13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
    have hiff := spec (spec h13 (succ n)) (succ n)
    simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
    apply ex_elim (iff_mp hiff hlt); intro k hk
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hk
    -- hk : add (succ n) (succ k) =eq succ n
    have hsa : axioms ⊢ (add (succ n) (succ k) =eq succ (add n (succ k))) := by
      have hh := spec (succ_add n) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh
    have heq1 : axioms ⊢ (succ (add n (succ k)) =eq succ n) := eq_trans hsa hk
    have h3i : axioms ⊢ ((succ (add n (succ k)) =eq succ n) ⇒ (add n (succ k) =eq n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)) (add n (succ k))) n
      simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh; exact hh
    have hnn : axioms ⊢ (add n (succ k) =eq n) := mp h3i heq1
    have hiffn := spec (spec h13 n) n
    simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiffn
    have hltnn : axioms ⊢ lt n n := by
      apply iff_mpr hiffn
      apply ex_intro k
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact hnn
    exact mp ih' hltnn

/-- **`ax18` (lt_irrefl)** es teorema en `Full`: `⊢ ∀a, ¬(a < a)`. -/
theorem lt_irrefl_thm : axioms ⊢ ax18_lt_irrefl := lt_irrefl_ax

end ROBINSON_PlusPlus.Full

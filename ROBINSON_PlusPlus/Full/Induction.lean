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

/-! ### §0bis · ⭐ `primAxioms` — LOS 23 PRIMITIVOS ([ADR‑023](../../DECISIONS.md), 2026‑09‑10h)

El censo de `coreAxioms` (`doc/REFERENCE-Full.md` §3.14.1) lo parte en **23 primitivos** y
**11 derivables**, y los 11 están demostrados en `Full`. Pero se enuncian **`axioms ⊢ axN`** con
`axN ∈ axioms` ⇒ **trivialmente ciertos por `ax`**: el tipo **no certifica** la redundancia.

`primAxioms` es la lista que sí la certifica. ⚠️ **No cambia la teoría**: `axioms` queda intacta y
`primAxioms ⊆ axioms`, así que la frontera de `axiomsCodeT`/`provCodeC'` —y con ella la sentencia
`G`— **no se mueve** (ADR‑015). Lo único que cambia es **qué se afirma** de cada derivación.

⭐ **El debilitamiento es GRATIS**: `Derives.weakening` es un **constructor** de `Derives` en
`FOL/FOL.lean`, no un lema por probar. ⇒ de `primAxioms ⊢ f` se recupera `axioms ⊢ f` en una línea
(`prim_to_axioms`), y **ninguna firma aguas abajo cambia**. -/

/-- Los **23** axiomas **PRIMITIVOS / DEFINITORIOS** de `coreAxioms`: los que **fijan el
    significado de un símbolo** (Peano, las ecuaciones de `+`, `·`, `<`, `√`, `mod2`/`div2`,
    `pred`, listas, `^`, `prod_pairs` y la resta truncada). Ningún esquema de inducción los deriva
    — sin ellos el símbolo no significa nada.

    Los **11 restantes** de `coreAxioms` (ax6, ax7, ax10, ax11, ax12, ax18, ax19, ax21, ax24,
    ax_C3, ax_L3) **deben** ser teoremas en `Full`, y lo son. -/
def primAxioms : List Formula :=
  [ ax2_peano_succ_neq_zero, ax3_peano_succ_inj,
    ax4_add_zero, ax5_add_succ, ax8_mul_zero, ax9_mul_succ,
    ax13_lt_def, ax14_sqrt_le, ax15_lt_succ_sqrt,
    ax16_mod2_succ, ax17_div_mod_eq, ax25_pred_zero, ax26_pred_succ,
    ax_L0_cons_def, ax_L1_in_nil, ax_L2_in_cons,
    ax_C1_concat_nil, ax_C2_concat_cons, ax29_sub_witness,
    ax_pow_zero, ax_pow_succ, ax_prodp_nil, ax_prodp_cons ]

/-- El censo, comprobado por el kernel: **23 + 11 = 34 = `coreAxioms`**. -/
theorem primAxioms_len : primAxioms.length = 23 := rfl

/-- Y son **de verdad** axiomas de la teoría. -/
theorem primAxioms_subset : ∀ f ∈ primAxioms, f ∈ axioms := by
  intro f hf
  simp only [primAxioms, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> simp [axioms]

/-- ⭐ **El puente, en una línea**: `Derives.weakening` es constructor. ⇒ certificar sobre
    `primAxioms` **no cuesta ninguna firma**: la versión `axioms ⊢` se recupera siempre. -/
theorem prim_to_axioms {f : Formula} (h : primAxioms ⊢ f) : axioms ⊢ f :=
  Derives.weakening _ _ _ h primAxioms_subset

/-- El `ax` de `Minimal` está especializado a `axioms`; éste es su gemelo sobre `primAxioms`
    (y es literalmente el constructor `hyp`). -/
theorem axp {f : Formula} (h : f ∈ primAxioms) : primAxioms ⊢ f := Derives.hyp _ _ h

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

/-! #### El esquema, sobre los PRIMITIVOS — [ADR‑023](../../DECISIONS.md), **ratificado 2026‑09‑10h**

⭐ **Esto es lo que `Full` significa, dicho con precisión**: *los 23 primitivos **más** el esquema de
inducción*. Antes el axioma decía `axioms ⊢ inductionFormula φ`, que es **más débil** y además
impedía certificar el censo de `coreAxioms` (los 11 derivables se enunciaban sobre `axioms`, que los
contiene ⇒ **triviales por `ax`**).

⚠️⚠️ **Y la salida fácil estaba CERRADA**: generalizarlo a `∀ {Γ}, Γ ⊢ inductionFormula φ` —la forma
que `ax_list_induction` sí tiene— sería **FALSO**, porque con `Γ = []` diría que el esquema de
inducción es **lógicamente válido**. `ax_list_induction` puede ser genérico porque es una **REGLA**
(lleva `base` y `step` sobre el mismo `Γ`); esto es un **AXIOMA**, y un axioma tiene que **nombrar
su contexto**.

⭐ **No añade un axioma: lo MUEVE.** `ax_induction` deja de ser `axiom` y pasa a **teorema** por
debilitamiento ⇒ **el recuento sigue en 6**, y **ninguna firma aguas abajo cambia**. -/

/-- **Esquema de inducción general** como axioma object-level, **sobre los 23 primitivos**.
    Sancionado por el propietario el 2026‑09‑10h (M‑1). -/
axiom ax_induction_prim (φ : Formula) : primAxioms ⊢ inductionFormula φ

/-- **Esquema de inducción general** sobre `axioms`. 🏁 **Ya NO es un `axiom`**: sale de
    `ax_induction_prim` por debilitamiento (`Derives.weakening`, que es constructor). -/
theorem ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ :=
  prim_to_axioms (ax_induction_prim φ)

/-- Empaquetado object-level **sobre los primitivos** (doble `mp` sobre `ax_induction_prim`).
    Es el que hay que usar para **certificar** un axioma derivable. -/
theorem induction_object_prim {φ : Formula}
    (base : primAxioms ⊢ substFormula 0 zero φ)
    (step : primAxioms ⊢ Formula.forall
              (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))) :
    primAxioms ⊢ Formula.forall φ := by
  have hind := ax_induction_prim φ
  simp only [inductionFormula] at hind
  exact mp (mp hind base) step

/-- Empaquetado object-level (doble `mp` sobre `ax_induction`). No es regla meta. -/
theorem induction_object {φ : Formula}
    (base : axioms ⊢ substFormula 0 zero φ)
    (step : axioms ⊢ Formula.forall
              (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))) :
    axioms ⊢ Formula.forall φ := by
  have hind := ax_induction φ
  simp only [inductionFormula] at hind
  exact mp (mp hind base) step

/-! ### `zero_add_prim` (sin parámetro) -/

theorem zero_add_prim : primAxioms ⊢ Formula.forall (add zero (.var 0) =eq (.var 0)) := by
  apply induction_object_prim
  · show primAxioms ⊢ (add zero zero =eq zero)
    have h := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) zero
    simp [substFormula, substTerm, substTerms, add, zero] at h
    exact h
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro hn
    have hn' : primAxioms ⊢ (add zero n =eq n) := hn
    show primAxioms ⊢ (add zero (succ n) =eq succ n)
    have h5 : primAxioms ⊢ (add zero (succ n) =eq succ (add zero n)) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) zero) n
      simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans h5 (eq_congr_succ hn')

/-! ### `succ_add_prim` (con parámetro) -/

theorem succ_add_prim (a : Term) :
    primAxioms ⊢ Formula.forall
      (add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))) := by
  apply induction_object_prim
  · -- base: add (σa) 0 = σ(add a 0)
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm]
    have hA : primAxioms ⊢ (add (succ a) zero =eq succ a) := by
      have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) (succ a)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hh
      exact hh
    have hB : primAxioms ⊢ (add a zero =eq a) := by
      have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm (eq_congr_succ hB))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have h5sa : primAxioms ⊢ (add (succ a) (succ n) =eq succ (add (succ a) n)) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) (succ a)) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h5a : primAxioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5sa (eq_congr_succ ih))
      (eq_symm (eq_congr_succ h5a))

/-! ### `add_comm` (= `ax6`) por inducción object-level -/

theorem add_comm_ax_prim (a : Term) :
    primAxioms ⊢ Formula.forall
      (add (liftTerm 0 a) (.var 0) =eq add (.var 0) (liftTerm 0 a)) := by
  apply induction_object_prim
  · -- base: add a 0 = add 0 a
    simp only [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm]
    have hA : primAxioms ⊢ (add a zero =eq a) := by
      have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have hB : primAxioms ⊢ (add zero a =eq a) := by
      have hh := spec zero_add_prim a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm hB)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have h5 : primAxioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have hsucc : primAxioms ⊢ (add (succ n) a =eq succ (add n a)) := by
      have hh := spec (succ_add_prim n) a
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5 (eq_congr_succ ih)) (eq_symm hsucc)

/-- **`ax6` de `Minimal` es teorema en `Full`**: `⊢ ∀a ∀b, a+b = b+a`. -/
theorem add_comm_thm_prim : primAxioms ⊢ ax6_add_comm := by
  apply gen; intro a
  exact add_comm_ax_prim a

/-! ### `add_assoc` (= `ax7`) — inducción sobre el tercer argumento, 2 parámetros -/

theorem add_assoc_ax_prim (a b : Term) :
    primAxioms ⊢ Formula.forall
      (add (add (liftTerm 0 a) (liftTerm 0 b)) (.var 0)
        =eq add (liftTerm 0 a) (add (liftTerm 0 b) (.var 0))) := by
  apply induction_object_prim
  · -- base: (a+b)+0 = a+(b+0)
    simp only [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm]
    have h1 : primAxioms ⊢ (add (add a b) zero =eq add a b) := by
      have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) (add a b)
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have hb0 : primAxioms ⊢ (add b zero =eq b) := by
      have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) b
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans h1 (eq_symm (eq_congr_add_left hb0))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have hL : primAxioms ⊢ (add (add a b) (succ n) =eq succ (add a (add b n))) := by
      have h5 : primAxioms ⊢ (add (add a b) (succ n) =eq succ (add (add a b) n)) := by
        have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) (add a b)) n
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      exact FOL.derive_eq_trans h5 (eq_congr_succ ih)
    have hR : primAxioms ⊢ (add a (add b (succ n)) =eq succ (add a (add b n))) := by
      have hb5 : primAxioms ⊢ (add b (succ n) =eq succ (add b n)) := by
        have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) b) n
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      have ha5 : primAxioms ⊢ (add a (succ (add b n)) =eq succ (add a (add b n))) := by
        have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) a) (add b n)
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      exact FOL.derive_eq_trans (eq_congr_add_left hb5) ha5
    exact FOL.derive_eq_trans hL (eq_symm hR)

/-! ⭐ **La NOTA que había aquí era FALSA, y se retira (2026‑09‑10h).**

Decía que el empaquetado `∀³` «topa con el ajuste de niveles `liftTerm`» y que hacía falta un
«helper de empaquetado n‑ario». **No hace falta ninguno.** Tras los dos `gen`, el hueco del
parámetro exterior queda como `substTerm (0+1) ṡ (liftTerm 0 (liftTerm 0 a))`, y eso **ya tenía
lema** desde siempre — `FOL.substTerm_liftLift` (`FOL/Theorems/Eq.lean`), que devuelve
exactamente `liftTerm 0 a`, que es lo que `add_assoc_ax_prim a b` produce. Todo el «ajuste de niveles»
era **un lema ausente del `simp set`**, no un obstáculo estructural.

⚠️ **Y el camino tuvo una trampa que merece quedar escrita**: el primer intento metió en el
`simp set` un lema *propio* `substTerm (c+1) s (liftTerm 0 (liftTerm 0 t)) = liftTerm 0 (liftTerm 0 t)`
dejado en `sorry` «para medir». Los tres empaquetados **compilaron** con él — y el lema es
**FALSO** (la sustitución en `c+1` sí baja un nivel: el verdadero da `liftTerm 0 t`). Un `sorry`
en el `simp set` no mide: **fabrica** el verde. Cf. AI‑GUIDE §27.1. -/

/-- **`ax7` de `Minimal` es teorema en `Full`**: `⊢ ∀a ∀b ∀c, (a+b)+c = a+(b+c)`. -/
theorem add_assoc_thm_prim : primAxioms ⊢ ax7_add_assoc := by
  apply gen; intro a
  apply gen; intro b
  have h := add_assoc_ax_prim a b
  simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftLift] at h ⊢
  exact h

/-! ### `zero_mul_prim` (sin parámetro) — base de la cadena de `mul` -/

theorem zero_mul_prim : primAxioms ⊢ Formula.forall (mul zero (.var 0) =eq zero) := by
  apply induction_object_prim
  · show primAxioms ⊢ (mul zero zero =eq zero)
    have h := spec (axp (by simp [primAxioms] : ax8_mul_zero ∈ primAxioms)) zero
    simp [substFormula, substTerm, substTerms, mul, zero] at h
    exact h
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    have ih' : primAxioms ⊢ (mul zero n =eq zero) := ih
    show primAxioms ⊢ (mul zero (succ n) =eq zero)
    have h9 : primAxioms ⊢ (mul zero (succ n) =eq add (mul zero n) zero) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax9_mul_succ ∈ primAxioms)) zero) n
      simp [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm] at hh
      exact hh
    have hz : primAxioms ⊢ (add zero zero =eq zero) := by
      have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) zero
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h9 (eq_congr_add_right ih')) hz

/-! ### Helpers de instanciación (axiomas y lemas derivados en términos concretos) -/

private theorem add_zero1_prim (x : Term) : primAxioms ⊢ (add x zero =eq x) := by
  have hh := spec (axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)) x
  simp [substFormula, substTerm, substTerms, add, zero] at hh; exact hh

private theorem add_succ2_prim (x y : Term) : primAxioms ⊢ (add x (succ y) =eq succ (add x y)) := by
  have hh := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) x) y
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem add_assoc3_prim (x y z : Term) :
    primAxioms ⊢ (add (add x y) z =eq add x (add y z)) := by
  have hh := spec (add_assoc_ax_prim x y) z
  simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh; exact hh

private theorem add_comm2_prim (x y : Term) : primAxioms ⊢ (add x y =eq add y x) := by
  have hh := spec (add_comm_ax_prim x) y
  simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh; exact hh

private theorem mul_zero1_prim (x : Term) : primAxioms ⊢ (mul x zero =eq zero) := by
  have hh := spec (axp (by simp [primAxioms] : ax8_mul_zero ∈ primAxioms)) x
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

private theorem mul_succ2_prim (x y : Term) : primAxioms ⊢ (mul x (succ y) =eq add (mul x y) x) := by
  have hh := spec (spec (axp (by simp [primAxioms] : ax9_mul_succ ∈ primAxioms)) x) y
  simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem zero_mul1_prim (x : Term) : primAxioms ⊢ (mul zero x =eq zero) := by
  have hh := spec zero_mul_prim x
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

/-! ### `succ_mul_prim` (con parámetro) — `∀n, σa·n = a·n + n` -/

theorem succ_mul_prim (a : Term) :
    primAxioms ⊢ Formula.forall
      (mul (succ (liftTerm 0 a)) (.var 0) =eq add (mul (liftTerm 0 a) (.var 0)) (.var 0)) := by
  apply induction_object_prim
  · -- base: σa·0 = a·0 + 0
    simp only [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm]
    -- goal: mul (succ a) zero =eq add (mul a zero) zero
    have hR : primAxioms ⊢ (add (mul a zero) zero =eq zero) :=
      FOL.derive_eq_trans (eq_congr_add_right (mul_zero1_prim a)) (add_zero1_prim zero)
    exact FOL.derive_eq_trans (mul_zero1_prim (succ a)) (eq_symm hR)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    -- ih: σa·n = a·n + n ; goal: σa·σn = a·σn + σn
    have hL : primAxioms ⊢ (mul (succ a) (succ n) =eq add (mul a n) (succ (add a n))) :=
      FOL.derive_eq_trans (mul_succ2_prim (succ a) n)
        (FOL.derive_eq_trans (eq_congr_add_right ih)
          (FOL.derive_eq_trans (add_assoc3_prim (mul a n) n (succ a))
            (FOL.derive_eq_trans (eq_congr_add_left (u := mul a n) (add_succ2_prim n a))
              (eq_congr_add_left (u := mul a n) (eq_congr_succ (add_comm2_prim n a))))))
    have hRr : primAxioms ⊢ (add (mul a (succ n)) (succ n) =eq add (mul a n) (succ (add a n))) :=
      FOL.derive_eq_trans (eq_congr_add_right (mul_succ2_prim a n))
        (FOL.derive_eq_trans (add_assoc3_prim (mul a n) a (succ n))
          (eq_congr_add_left (u := mul a n) (add_succ2_prim a n)))
    exact FOL.derive_eq_trans hL (eq_symm hRr)

private theorem succ_mul2_prim (x y : Term) : primAxioms ⊢ (mul (succ x) y =eq add (mul x y) y) := by
  have hh := spec (succ_mul_prim x) y
  simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

/-! ### `mul_comm` (= `ax10`) — `∀n, a·n = n·a` -/

theorem mul_comm_ax_prim (a : Term) :
    primAxioms ⊢ Formula.forall (mul (liftTerm 0 a) (.var 0) =eq mul (.var 0) (liftTerm 0 a)) := by
  apply induction_object_prim
  · -- base: a·0 = 0·a
    simp only [substFormula, substTerm, substTerms, mul, zero, FOL.substTerm_liftTerm]
    exact FOL.derive_eq_trans (mul_zero1_prim a) (eq_symm (zero_mul1_prim a))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    -- ih: a·n = n·a ; goal: a·σn = σn·a
    exact FOL.derive_eq_trans
      (FOL.derive_eq_trans (mul_succ2_prim a n) (eq_congr_add_right ih))
      (eq_symm (succ_mul2_prim n a))

/-- **`ax10` (mul_comm)** es teorema en `Full`: `⊢ ∀a ∀b, a·b = b·a`. -/
theorem mul_comm_thm_prim : primAxioms ⊢ ax10_mul_comm := by
  apply gen; intro a
  exact mul_comm_ax_prim a

/-! ### `mul_distrib` (= `ax12`) — `∀c, a·(b+c) = a·b + a·c` (2 parámetros) -/

theorem mul_distrib_ax_prim (a b : Term) :
    primAxioms ⊢ Formula.forall
      (mul (liftTerm 0 a) (add (liftTerm 0 b) (.var 0))
        =eq add (mul (liftTerm 0 a) (liftTerm 0 b)) (mul (liftTerm 0 a) (.var 0))) := by
  apply induction_object_prim
  · -- base: a·(b+0) = a·b + a·0
    simp only [substFormula, substTerm, substTerms, mul, add, zero, FOL.substTerm_liftTerm]
    have hLb : primAxioms ⊢ (mul a (add b zero) =eq mul a b) := eq_congr_mul_left (u := a) (add_zero1_prim b)
    have hRb : primAxioms ⊢ (add (mul a b) (mul a zero) =eq mul a b) :=
      FOL.derive_eq_trans (eq_congr_add_left (u := mul a b) (mul_zero1_prim a)) (add_zero1_prim (mul a b))
    exact FOL.derive_eq_trans hLb (eq_symm hRb)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have hL : primAxioms ⊢ (mul a (add b (succ n)) =eq add (mul a b) (add (mul a n) a)) :=
      FOL.derive_eq_trans (eq_congr_mul_left (u := a) (add_succ2_prim b n))
        (FOL.derive_eq_trans (mul_succ2_prim a (add b n))
          (FOL.derive_eq_trans (eq_congr_add_right ih)
            (add_assoc3_prim (mul a b) (mul a n) a)))
    have hR : primAxioms ⊢ (add (mul a b) (mul a (succ n)) =eq add (mul a b) (add (mul a n) a)) :=
      eq_congr_add_left (u := mul a b) (mul_succ2_prim a n)
    exact FOL.derive_eq_trans hL (eq_symm hR)

private theorem mul_distrib3_prim (x y z : Term) :
    primAxioms ⊢ (mul x (add y z) =eq add (mul x y) (mul x z)) := by
  have hh := spec (mul_distrib_ax_prim x y) z
  simp [substFormula, substTerm, substTerms, mul, add, FOL.substTerm_liftTerm] at hh; exact hh

/-- **`ax12` de `Minimal` es teorema en `Full`**: `⊢ ∀a ∀b ∀c, a·(b+c) = a·b + a·c`.
    Mismo empaquetado que `add_assoc_thm_prim` (2026‑09‑10h). -/
theorem mul_distrib_thm_prim : primAxioms ⊢ ax12_mul_distrib := by
  apply gen; intro a
  apply gen; intro b
  have h := mul_distrib_ax_prim a b
  simp [substFormula, substTerm, substTerms, mul, add, FOL.substTerm_liftLift] at h ⊢
  exact h

/-! ### `mul_assoc` (= `ax11`) — `∀c, (a·b)·c = a·(b·c)` (2 parámetros) -/

theorem mul_assoc_ax_prim (a b : Term) :
    primAxioms ⊢ Formula.forall
      (mul (mul (liftTerm 0 a) (liftTerm 0 b)) (.var 0)
        =eq mul (liftTerm 0 a) (mul (liftTerm 0 b) (.var 0))) := by
  apply induction_object_prim
  · -- base: (a·b)·0 = a·(b·0)
    simp only [substFormula, substTerm, substTerms, mul, zero, FOL.substTerm_liftTerm]
    have hR : primAxioms ⊢ (mul a (mul b zero) =eq zero) :=
      FOL.derive_eq_trans (eq_congr_mul_left (u := a) (mul_zero1_prim b)) (mul_zero1_prim a)
    exact FOL.derive_eq_trans (mul_zero1_prim (mul a b)) (eq_symm hR)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mul, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have hL : primAxioms ⊢ (mul (mul a b) (succ n) =eq add (mul a (mul b n)) (mul a b)) :=
      FOL.derive_eq_trans (mul_succ2_prim (mul a b) n) (eq_congr_add_right ih)
    have hR : primAxioms ⊢ (mul a (mul b (succ n)) =eq add (mul a (mul b n)) (mul a b)) :=
      FOL.derive_eq_trans (eq_congr_mul_left (u := a) (mul_succ2_prim b n)) (mul_distrib3_prim a (mul b n) b)
    exact FOL.derive_eq_trans hL (eq_symm hR)

/-- **`ax11` de `Minimal` es teorema en `Full`**: `⊢ ∀a ∀b ∀c, (a·b)·c = a·(b·c)`.
    Mismo empaquetado que `add_assoc_thm_prim` (2026‑09‑10h). -/
theorem mul_assoc_thm_prim : primAxioms ⊢ ax11_mul_assoc := by
  apply gen; intro a
  apply gen; intro b
  have h := mul_assoc_ax_prim a b
  simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftLift] at h ⊢
  exact h

/-! ### `lt_irrefl` (= `ax18`) — primer axioma NO ecuacional, vía `step_reduce` general -/

theorem lt_irrefl_ax_prim : primAxioms ⊢ Formula.forall (neg (lt (.var 0) (.var 0))) := by
  apply induction_object_prim
  · -- base: ¬(0 < 0)
    show primAxioms ⊢ neg (lt zero zero)
    apply raa; intro hlt
    have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
    have hiff := spec (spec h13 zero) zero
    simp [substFormula, substTerm, substTerms, lt, zero, succ, iff, liftTerm, liftTerms] at hiff
    apply ex_elim (iff_mp hiff hlt); intro k hk
    simp [substFormula, substTerm, substTerms, add, zero, succ] at hk
    -- hk : add zero (succ k) =eq zero
    have hz : primAxioms ⊢ (add zero (succ k) =eq succ k) := by
      have hh := spec zero_add_prim (succ k)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hh; exact hh
    have hne : primAxioms ⊢ neg (succ k =eq zero) := by
      have hh := spec (axp (by simp [primAxioms] : ax2_peano_succ_neq_zero ∈ primAxioms)) k
      simp [succ, zero] at hh; exact hh
    exact mp hne (eq_trans hz hk)
  · apply gen; intro n
    rw [step_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    have ih' : primAxioms ⊢ neg (lt n n) := ih
    show primAxioms ⊢ neg (lt (succ n) (succ n))
    apply raa; intro hlt
    have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
    have hiff := spec (spec h13 (succ n)) (succ n)
    simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
    apply ex_elim (iff_mp hiff hlt); intro k hk
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hk
    -- hk : add (succ n) (succ k) =eq succ n
    have hsa : primAxioms ⊢ (add (succ n) (succ k) =eq succ (add n (succ k))) := by
      have hh := spec (succ_add_prim n) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh
    have heq1 : primAxioms ⊢ (succ (add n (succ k)) =eq succ n) := eq_trans hsa hk
    have h3i : primAxioms ⊢ ((succ (add n (succ k)) =eq succ n) ⇒ (add n (succ k) =eq n)) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax3_peano_succ_inj ∈ primAxioms)) (add n (succ k))) n
      simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh; exact hh
    have hnn : primAxioms ⊢ (add n (succ k) =eq n) := mp h3i heq1
    have hiffn := spec (spec h13 n) n
    simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiffn
    have hltnn : primAxioms ⊢ lt n n := by
      apply iff_mpr hiffn
      apply ex_intro k
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact hnn
    exact mp ih' hltnn

/-- **`ax18` (lt_irrefl)** es teorema en `Full`: `⊢ ∀a, ¬(a < a)`. -/
theorem lt_irrefl_thm_prim : primAxioms ⊢ ax18_lt_irrefl := lt_irrefl_ax_prim

/-! ### Lemas de orden auxiliares (hacia la tricotomía `ax19`) -/

/-- `a < σa` (testigo `k = 0` en ax13: `a + σ0 = σa`). -/
theorem lt_succ_self_prim (a : Term) : primAxioms ⊢ lt a (succ a) := by
  have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
  have hiff := spec (spec h13 a) (succ a)
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply iff_mpr hiff
  apply ex_intro zero
  simp [substFormula, substTerm, substTerms, add, succ, zero,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact FOL.derive_eq_trans (add_succ2_prim a zero) (eq_congr_succ (add_zero1_prim a))

/-- `¬(a < 0)` (nada es menor que cero: `a + σk = 0` contradice `ax2`). -/
theorem not_lt_zero_prim (a : Term) : primAxioms ⊢ neg (lt a zero) := by
  apply raa; intro hlt
  have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
  have hiff := spec (spec h13 a) zero
  simp [substFormula, substTerm, substTerms, lt, zero, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply ex_elim (iff_mp hiff hlt); intro k hk
  simp [substFormula, substTerm, substTerms, add, succ, zero,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hk
  -- hk : add a (succ k) =eq zero
  have h5 : primAxioms ⊢ (add a (succ k) =eq succ (add a k)) := add_succ2_prim a k
  have hne : primAxioms ⊢ neg (succ (add a k) =eq zero) := by
    have hh := spec (axp (by simp [primAxioms] : ax2_peano_succ_neq_zero ∈ primAxioms)) (add a k)
    simp [succ, zero] at hh; exact hh
  exact mp hne (eq_trans h5 hk)

/-- `b < a → b < σa` (testigo `σk` desde el de `b<a`). -/
theorem lt_succ_of_lt_prim (a b : Term) (h : primAxioms ⊢ lt b a) : primAxioms ⊢ lt b (succ a) := by
  have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
  have hiffa := spec (spec h13 b) a
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiffa
  apply ex_elim (iff_mp hiffa h); intro k hk
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hk
  -- hk : add b (succ k) =eq a
  have hiffsa := spec (spec h13 b) (succ a)
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiffsa
  apply iff_mpr hiffsa
  apply ex_intro (succ k)
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- goal: add b (succ (succ k)) =eq succ a
  exact FOL.derive_eq_trans (add_succ2_prim b (succ k)) (eq_congr_succ hk)

/-- `0 < σk` (testigo `k`: `0 + σk = σk` por `zero_add_prim`). -/
theorem zero_lt_succ_prim (k : Term) : primAxioms ⊢ lt zero (succ k) := by
  have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
  have hiff := spec (spec h13 zero) (succ k)
  simp [substFormula, substTerm, substTerms, lt, zero, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply iff_mpr hiff
  apply ex_intro k
  simp [substFormula, substTerm, substTerms, add, zero, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  have hh := spec zero_add_prim (succ k)
  simp [substFormula, substTerm, substTerms, add, zero, succ] at hh
  exact hh

/-- `∀b, b = 0 ∨ ∃k, b = σk` (cero o sucesor) por inducción. -/
theorem zero_or_succ_ax_prim :
    primAxioms ⊢ Formula.forall (lor (.var 0 =eq zero) (ex (.var 1 =eq succ (.var 0)))) := by
  apply induction_object_prim
  · -- base: 0 = 0 ∨ ...
    apply Minimal.Axioms.or_intro_left
    exact Derives.refl primAxioms zero
  · apply gen; intro n
    rw [step_reduce]
    apply Minimal.Axioms.imp_intro; intro _ih
    apply Minimal.Axioms.or_intro_right
    apply ex_intro n
    simp [substFormula, substTerm, substTerms, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
    exact Derives.refl primAxioms (succ n)

private theorem succ_add2_prim (x y : Term) : primAxioms ⊢ (add (succ x) y =eq succ (add x y)) := by
  have hh := spec (succ_add_prim x) y
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

/-- `a < b → σa < b ∨ σa = b` (casando el testigo `k` con `zero_or_succ`). -/
theorem lt_succ_cases_prim (a b : Term) (h : primAxioms ⊢ lt a b) :
    primAxioms ⊢ lor (lt (succ a) b) (succ a =eq b) := by
  have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
  have hiffab := spec (spec h13 a) b
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiffab
  apply ex_elim (iff_mp hiffab h); intro k hk
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hk
  -- hk : add a (succ k) =eq b
  have hzos := spec zero_or_succ_ax_prim k
  simp [substFormula, substTerm, substTerms, zero, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hzos
  apply Minimal.Axioms.or_elim hzos
  · -- k = 0  →  σa = b
    intro hk0
    apply Minimal.Axioms.or_intro_right
    have h1 : primAxioms ⊢ (add a (succ k) =eq succ a) :=
      FOL.derive_eq_trans (eq_congr_add_left (eq_congr_succ hk0))
        (FOL.derive_eq_trans (add_succ2_prim a zero) (eq_congr_succ (add_zero1_prim a)))
    exact eq_trans h1 hk
  · -- k = σj  →  σa < b
    intro hex
    apply ex_elim hex; intro j hj
    simp [substFormula, substTerm, substTerms, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hj
    -- hj : k =eq succ j
    apply Minimal.Axioms.or_intro_left
    have hiffsab := spec (spec h13 (succ a)) b
    simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiffsab
    apply iff_mpr hiffsab
    apply ex_intro j
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
    -- goal: add (succ a) (succ j) =eq b
    have hN : primAxioms ⊢ (add a (succ k) =eq add a (succ (succ j))) :=
      eq_congr_add_left (eq_congr_succ hj)
    have hM : primAxioms ⊢ (add a (succ (succ j)) =eq succ (succ (add a j))) :=
      FOL.derive_eq_trans (add_succ2_prim a (succ j)) (eq_congr_succ (add_succ2_prim a j))
    have hL : primAxioms ⊢ (add (succ a) (succ j) =eq succ (succ (add a j))) :=
      FOL.derive_eq_trans (add_succ2_prim (succ a) j) (eq_congr_succ (succ_add2_prim a j))
    have hAk : primAxioms ⊢ (add a (succ k) =eq succ (succ (add a j))) := FOL.derive_eq_trans hN hM
    exact FOL.derive_eq_trans hL (eq_trans hAk hk)

/-- Construcción de `lt` desde un testigo: `a + σk = b → a < b`. -/
private theorem lt_intro_prim (a b k : Term) (h : primAxioms ⊢ (add a (succ k) =eq b)) :
    primAxioms ⊢ lt a b := by
  have h13 := axp (by simp [primAxioms] : ax13_lt_def ∈ primAxioms)
  have hiff := spec (spec h13 a) b
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply iff_mpr hiff
  apply ex_intro k
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact h

/-! ### `lt_trichotomy` (= `ax19`) — ensamblaje por inducción sobre `a` -/

theorem lt_trichotomy_ax_prim :
    primAxioms ⊢ Formula.forall (Formula.forall
      (lor (lt (.var 1) (.var 0)) (lor (.var 1 =eq .var 0) (lt (.var 0) (.var 1))))) := by
  apply induction_object_prim
  · -- base: ∀b, 0<b ∨ 0=b ∨ b<0
    apply gen; intro b
    simp [substFormula, substTerm, substTerms, lt, lor, zero, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
    have hzos := spec zero_or_succ_ax_prim b
    simp [substFormula, substTerm, substTerms, zero, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hzos
    apply Minimal.Axioms.or_elim hzos
    · -- b = 0  →  0 = b (medio)
      intro hb0
      exact Minimal.Axioms.or_intro_right (Minimal.Axioms.or_intro_left (eq_symm hb0))
    · -- b = σk  →  0 < b (izquierda)
      intro hex
      apply ex_elim hex; intro k hbk
      simp [substFormula, substTerm, substTerms, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hbk
      apply Minimal.Axioms.or_intro_left
      apply lt_intro_prim zero b k
      have hz := spec zero_add_prim (succ k)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hz
      exact FOL.derive_eq_trans hz (eq_symm hbk)
  · -- paso: T(a,·) → T(σa,·)
    apply gen; intro a
    rw [step_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    apply gen; intro b
    simp [substFormula, substTerm, substTerms, lt, lor, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
    have htab := spec ih b
    simp [substFormula, substTerm, substTerms, lt, lor, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at htab
    apply Minimal.Axioms.or_elim htab
    · -- a < b  →  σa < b ∨ σa = b
      intro hab
      apply Minimal.Axioms.or_elim (lt_succ_cases_prim a b hab)
      · intro h; exact Minimal.Axioms.or_intro_left h
      · intro h; exact Minimal.Axioms.or_intro_right (Minimal.Axioms.or_intro_left h)
    · intro hrest
      apply Minimal.Axioms.or_elim hrest
      · -- a = b  →  b < σa (derecha)
        intro hab
        apply Minimal.Axioms.or_intro_right; apply Minimal.Axioms.or_intro_right
        apply lt_intro_prim b (succ a) zero
        exact FOL.derive_eq_trans
          (FOL.derive_eq_trans (add_succ2_prim b zero) (eq_congr_succ (add_zero1_prim b)))
          (eq_congr_succ (eq_symm hab))
      · -- b < a  →  b < σa (derecha)
        intro hba
        apply Minimal.Axioms.or_intro_right; apply Minimal.Axioms.or_intro_right
        exact lt_succ_of_lt_prim a b hba

/-- **`ax19` (tricotomía)** es teorema en `Full`: `⊢ ∀a ∀b, a<b ∨ a=b ∨ b<a`. -/
theorem lt_trichotomy_thm_prim : primAxioms ⊢ ax19_lt_trichotomy := lt_trichotomy_ax_prim


/-! ### 🏁 De vuelta a `axioms` — las firmas de siempre, por DEBILITAMIENTO

Todo lo de arriba se demuestra ahora **sobre los 23 primitivos** ([ADR‑023](../../DECISIONS.md)),
que es lo que **certifica** que los 7 axiomas derivables de `Minimal` lo son de verdad: sus
enunciados `primAxioms ⊢ axN` **no** son triviales, porque `axN ∉ primAxioms`.

`Derives.weakening` es **constructor**, así que recuperar las versiones `axioms ⊢` no cuesta nada,
y **ningún consumidor de aguas abajo cambia**. -/

/-- **`ax6` de `Minimal` es teorema en `Full`** — 🏁 y desde 2026‑09‑10h **certificado**
    (`add_comm_thm_prim`). -/
theorem add_comm_thm : axioms ⊢ ax6_add_comm := prim_to_axioms add_comm_thm_prim

/-- **`ax7`**, ídem. -/
theorem add_assoc_thm : axioms ⊢ ax7_add_assoc := prim_to_axioms add_assoc_thm_prim

/-- **`ax10`**, ídem. -/
theorem mul_comm_thm : axioms ⊢ ax10_mul_comm := prim_to_axioms mul_comm_thm_prim

/-- **`ax11`**, ídem. -/
theorem mul_assoc_thm : axioms ⊢ ax11_mul_assoc := prim_to_axioms mul_assoc_thm_prim

/-- **`ax12`**, ídem. -/
theorem mul_distrib_thm : axioms ⊢ ax12_mul_distrib := prim_to_axioms mul_distrib_thm_prim

/-- **`ax18`**, ídem. -/
theorem lt_irrefl_thm : axioms ⊢ ax18_lt_irrefl := prim_to_axioms lt_irrefl_thm_prim

/-- **`ax19`**, ídem. -/
theorem lt_trichotomy_thm : axioms ⊢ ax19_lt_trichotomy := prim_to_axioms lt_trichotomy_thm_prim

/-! Y los lemas que consumen otros módulos, con su firma `axioms ⊢` intacta. -/

theorem zero_add : axioms ⊢ Formula.forall (add zero (.var 0) =eq (.var 0)) :=
  prim_to_axioms zero_add_prim

theorem succ_add (a : Term) : axioms ⊢ Formula.forall
    (add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))) :=
  prim_to_axioms (succ_add_prim a)

theorem add_comm_ax (a : Term) : axioms ⊢ Formula.forall
    (add (liftTerm 0 a) (.var 0) =eq add (.var 0) (liftTerm 0 a)) :=
  prim_to_axioms (add_comm_ax_prim a)

theorem zero_mul : axioms ⊢ Formula.forall (mul zero (.var 0) =eq zero) :=
  prim_to_axioms zero_mul_prim

theorem succ_mul (a : Term) : axioms ⊢ Formula.forall
    (mul (succ (liftTerm 0 a)) (.var 0) =eq add (mul (liftTerm 0 a) (.var 0)) (.var 0)) :=
  prim_to_axioms (succ_mul_prim a)

theorem mul_comm_ax (a : Term) : axioms ⊢ Formula.forall
    (mul (liftTerm 0 a) (.var 0) =eq mul (.var 0) (liftTerm 0 a)) :=
  prim_to_axioms (mul_comm_ax_prim a)

theorem lt_succ_self (a : Term) : axioms ⊢ lt a (succ a) :=
  prim_to_axioms (lt_succ_self_prim a)

theorem not_lt_zero (a : Term) : axioms ⊢ neg (lt a zero) :=
  prim_to_axioms (not_lt_zero_prim a)

/-- ⚠️ Este toma la hipótesis **en el contexto**, así que el debilitamiento no basta (va en la
    dirección contraria). Se cierra el ángulo: se interna la implicación sobre `primAxioms`, se
    debilita **la implicación**, y se aplica `mp` con la hipótesis sobre `axioms`. -/
theorem lt_succ_of_lt (a b : Term) (h : axioms ⊢ lt b a) : axioms ⊢ lt b (succ a) :=
  mp (prim_to_axioms (Minimal.Axioms.imp_intro (lt_succ_of_lt_prim a b))) h

theorem zero_lt_succ (k : Term) : axioms ⊢ lt zero (succ k) :=
  prim_to_axioms (zero_lt_succ_prim k)

theorem zero_or_succ_ax : axioms ⊢ Formula.forall
    (((.var 0) =eq zero) ∨ (Formula.ex ((.var 1) =eq succ (.var 0)))) :=
  prim_to_axioms zero_or_succ_ax_prim

end ROBINSON_PlusPlus.Full

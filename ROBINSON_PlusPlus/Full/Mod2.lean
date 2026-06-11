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
## FULL — mod2: ax21 y ax24 derivados (Opción C.2)

En `Minimal`, `ax16` (mod2(n)=0 ⇔ mod2(σn)=1) + `ax17` (div2(n)·2+mod2(n)=n)
dejaban `mod2` subdeterminado: modelos no estándar con `mod2(σn) ≥ 2` cumplen
ambos axiomas, y `ax21` (mod2(n) ∈ {0,1}) carga información independiente.

En `Full` añadimos **un único axioma extra** que caracteriza completamente la
recursión de `mod2`:

  ax_mod2_alternation : ∀n, mod2(σn) + mod2(n) = 1

De este + `mod2(0) = 0` (derivable en Minimal de `ax17 + teo_2_9` sin usar
`ax21`) + inducción object-level, salen `ax21` y `ax24` como teoremas.

Esto es **Opción C.2** acordada 2026-06-11 (alternativa a redefinir un símbolo
`mod2_rec` independiente; aquí caracterizamos directamente el `mod2` opaco
existente). Conservativo respecto a `Minimal`: en `Minimal` el nuevo axioma
es derivable de `ax21 + ax16 + teo_1_3`, así que añadirlo en `Full` no
introduce inconsistencia.
-/

/-! ### Helper: congruencia de `mod2` -/

/-- `eq_congr_mod2`: `mod2` respeta la igualdad. -/
theorem eq_congr_mod2 {Γ : List Formula} {t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (mod2 t₁ ≐ mod2 t₂) := by
  let f : Formula := Formula.eq (mod2 (liftTerm 0 t₁)) (mod2 (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mod2 t₁) (mod2 s) := by
    intro s
    simp only [f, substFormula, mod2, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (mod2 t₁))

/-! ### `mod2(0) = 0` re-probado sin `ax21` -/

/-- `mod2(0) = 0` — re-derivado en Full usando sólo `ax17 + teo_2_9`, sin
    `ax21`. La versión en Block3 (`mod2_zero`) usa `ax21` para case-split. -/
theorem mod2_zero_aux : axioms ⊢ (mod2 zero ≐ zero) := by
  -- ax17(0): div2(0)·2 + mod2(0) = 0
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  have h_inst := spec h_ax17 zero
  simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, zero, two, one, succ,
        FOL.substTerm_liftTerm] at h_inst
  -- teo_2_9: ∀a b, a + b = 0 → a = 0 ∧ b = 0. Aplicamos con a := div2(0)·2, b := mod2(0).
  have h_teo := spec (spec teo_2_9 (mul (div2 zero) two)) (mod2 zero)
  simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, zero, two, one, succ,
        land, FOL.substTerm_liftTerm] at h_teo
  exact Minimal.Axioms.and_elim_right (mp h_teo h_inst)

/-! ### Axioma de Full: alternancia explícita de `mod2` -/

/-- **Axioma de Full** (Opción C.2): `∀n, mod2(σn) + mod2(n) = 1`.

    Caracteriza completamente la recursión de `mod2` (Minimal sólo daba
    `ax16` que es media biconditional). De este sale `ax21` por inducción.

    En `Minimal` con `ax21`: derivable como teorema (case-split sobre mod2(n)
    y aplicar `ax16` forward/usar teo_1_3). Por tanto añadirlo en Full es
    **conservativo respecto a Minimal**. -/
axiom ax_mod2_alternation : axioms ⊢ Formula.forall
  (add (mod2 (succ (.var 0))) (mod2 (.var 0)) ≐ one)

/-! ### Helper: `a + 1 = 1 → a = 0` -/

/-- Helper aritmético: `a + 1 = 1 → a = 0`. Derivable de `ax3+ax4+ax5`. -/
private theorem a_plus_one_eq_one (a : Term) (h : axioms ⊢ (add a one ≐ one)) :
    axioms ⊢ (a ≐ zero) := by
  -- one = succ zero. a + succ zero = succ (a + zero) por ax5. ax3 inj: a+zero=zero. ax4: a=0.
  have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  -- ax5 inst: a + succ zero = succ (a + zero)
  have h5 : axioms ⊢ (add a (succ zero) ≐ succ (add a zero)) := by
    have hh := spec (spec h_ax5 a) zero
    simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
    exact hh
  -- h : add a one = one. one = succ zero, así que add a (succ zero) = succ zero.
  have h_one_unfold : axioms ⊢ (add a (succ zero) ≐ succ zero) := h  -- one := succ zero defequationally
  -- combine: succ (add a zero) = succ zero
  have h_succsucc : axioms ⊢ (succ (add a zero) ≐ succ zero) :=
    FOL.derive_eq_trans (eq_symm h5) h_one_unfold
  -- ax3 inj: a + zero = zero
  have h_ax3_inst : axioms ⊢ ((succ (add a zero) ≐ succ zero) ⇒ (add a zero ≐ zero)) := by
    have hh := spec (spec h_ax3 (add a zero)) zero
    simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  have h_az_zero : axioms ⊢ (add a zero ≐ zero) := mp h_ax3_inst h_succsucc
  -- ax4: a + zero = a, así a = zero por eq_trans (no-estándar)
  have h_ax4_inst : axioms ⊢ (add a zero ≐ a) := by
    have hh := spec h_ax4 a
    simp [substFormula, substTerm, substTerms, add, zero] at hh
    exact hh
  exact eq_trans h_ax4_inst h_az_zero  -- (a+0=a) ∧ (a+0=0) → a=0

/-! ### `ax21` derivado: `mod2(n) ∈ {0,1}` -/

/-- Forma "axioma de Full": `∀n, mod2(n) = 0 ∨ mod2(n) = 1`. -/
theorem mod2_range_ax : axioms ⊢ Formula.forall
    (lor (mod2 (.var 0) ≐ zero) (mod2 (.var 0) ≐ one)) := by
  apply induction_object
  · -- base: mod2(0) = 0 ∨ mod2(0) = 1
    simp only [substFormula, substTerm, substTerms, lor, mod2, zero, one, succ,
               FOL.substTerm_liftTerm]
    exact Minimal.Axioms.or_intro_left mod2_zero_aux
  · -- step: ∀n, (mod2(n) ∈ {0,1}) → (mod2(σn) ∈ {0,1})
    apply gen; intro n
    rw [step_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, lor, mod2, zero, one, succ,
               FOL.substTerm_liftTerm] at ih ⊢
    -- ax_mod2_alternation spec'd at n: mod2(σn) + mod2(n) = 1
    have h_alt : axioms ⊢ (add (mod2 (succ n)) (mod2 n) ≐ one) := by
      have hh := spec ax_mod2_alternation n
      simp [substFormula, substTerm, substTerms, add, mod2, one, zero, succ,
            FOL.substTerm_liftTerm] at hh
      exact hh
    -- ax4 spec'd at mod2(σn): mod2(σn) + 0 = mod2(σn)
    have h_ax4_mod2sn : axioms ⊢ (add (mod2 (succ n)) zero ≐ mod2 (succ n)) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) (mod2 (succ n))
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    apply Minimal.Axioms.or_elim ih
    · -- Caso mod2(n) = 0 → mod2(σn) = 1
      intro h_mod2n_zero
      have h_cong : axioms ⊢ (add (mod2 (succ n)) (mod2 n) ≐ add (mod2 (succ n)) zero) :=
        eq_congr_add_left h_mod2n_zero
      have h_sn_plus_zero : axioms ⊢ (add (mod2 (succ n)) zero ≐ one) :=
        FOL.derive_eq_trans (eq_symm h_cong) h_alt
      have h_sn_one : axioms ⊢ (mod2 (succ n) ≐ one) :=
        FOL.derive_eq_trans (eq_symm h_ax4_mod2sn) h_sn_plus_zero
      exact Minimal.Axioms.or_intro_right h_sn_one
    · -- Caso mod2(n) = 1 → mod2(σn) = 0
      intro h_mod2n_one
      have h_cong : axioms ⊢ (add (mod2 (succ n)) (mod2 n) ≐ add (mod2 (succ n)) one) :=
        eq_congr_add_left h_mod2n_one
      have h_sn_plus_one : axioms ⊢ (add (mod2 (succ n)) one ≐ one) :=
        FOL.derive_eq_trans (eq_symm h_cong) h_alt
      have h_sn_zero : axioms ⊢ (mod2 (succ n) ≐ zero) :=
        a_plus_one_eq_one (mod2 (succ n)) h_sn_plus_one
      exact Minimal.Axioms.or_intro_left h_sn_zero

/-- **`ax21` como teorema en Full**: `⊢ ax21_mod2_range`. -/
theorem mod2_range_thm : axioms ⊢ ax21_mod2_range := mod2_range_ax

/-! ### `ax24` derivado: `n = 2k → mod2(n) = 0` -/

/-- Versión por inducción simple: `∀k, mod2(2k) = 0`. -/
theorem mod2_two_k_eq_zero_ax : axioms ⊢ Formula.forall
    (mod2 (mul two (.var 0)) ≐ zero) := by
  apply induction_object
  · -- base: mod2(2·0) = 0. Vía ax8 (n·0=0) + mod2_zero_aux + eq_congr_mod2.
    simp only [substFormula, substTerm, substTerms, mod2, mul, two, one, zero, succ,
               FOL.substTerm_liftTerm]
    have h_ax8_inst : axioms ⊢ (mul two zero ≐ zero) := by
      have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) two
      simp [substFormula, substTerm, substTerms, mul, zero] at hh
      exact hh
    have h_mod2_2_0 : axioms ⊢ (mod2 (mul two zero) ≐ mod2 zero) :=
      eq_congr_mod2 h_ax8_inst
    exact FOL.derive_eq_trans h_mod2_2_0 mod2_zero_aux
  · -- step: assume mod2(2n) = 0. Want mod2(2(σn)) = 0.
    apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, mod2, mul, two, one, zero, succ,
               FOL.substTerm_liftTerm] at ih ⊢
    -- ih : mod2 (mul two n) = zero
    -- goal : mod2 (mul two (succ n)) = zero
    -- Estrategia:
    -- 1) 2·σn = 2n + 2 = σσ(2n)  (ax9 + ax12... mejor: usamos ax9 directamente)
    -- 2) mod2(σ(2n)) = 1  (alternancia + ih)
    -- 3) mod2(σσ(2n)) = 0  (alternancia + paso 2)
    -- 4) mod2(2·σn) = mod2(σσ(2n)) = 0  (eq_congr_mod2)
    -- Paso 1a: 2·σn = (2·n) + 2 por ax9
    have h_ax9_inst : axioms ⊢ (mul two (succ n) ≐ add (mul two n) two) := by
      have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) two) n
      simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    -- Paso 1b: 2n + 2 = σσ(2n). two = succ one = succ (succ zero).
    -- ax5(2n, 1): 2n + succ 1 = succ (2n + 1). 1 = succ 0. So 2n + 2 = succ (2n + 1).
    -- ax5(2n, 0): 2n + succ 0 = succ (2n + 0). ax4: 2n + 0 = 2n. So 2n + 1 = succ (2n).
    -- Combined: 2n + 2 = succ (succ (2n)).
    have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
    have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
    have h_add_2n_2 : axioms ⊢ (add (mul two n) two ≐ succ (succ (mul two n))) := by
      -- two = succ one = succ (succ zero) definitionally
      -- 2n + 2 = 2n + succ one  (def two)
      -- ax5 at (2n, one): 2n + succ one = succ (2n + one)
      have h_step1 : axioms ⊢ (add (mul two n) (succ one) ≐ succ (add (mul two n) one)) := by
        have hh := spec (spec h_ax5 (mul two n)) one
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      -- ax5 at (2n, zero): 2n + succ zero = succ (2n + zero). one = succ zero.
      have h_step2 : axioms ⊢ (add (mul two n) one ≐ succ (add (mul two n) zero)) := by
        have hh := spec (spec h_ax5 (mul two n)) zero
        simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
        exact hh  -- one is definitionally succ zero
      -- ax4 at (2n): 2n + zero = 2n
      have h_step3 : axioms ⊢ (add (mul two n) zero ≐ mul two n) := by
        have hh := spec h_ax4 (mul two n)
        simp [substFormula, substTerm, substTerms, add, zero] at hh
        exact hh
      -- Combine: 2n+1 = succ(2n+0) = succ(2n). 2n+2 = succ(2n+1) = succ(succ(2n)).
      have h_2n_plus_1 : axioms ⊢ (add (mul two n) one ≐ succ (mul two n)) :=
        FOL.derive_eq_trans h_step2 (eq_congr_succ h_step3)
      exact FOL.derive_eq_trans h_step1 (eq_congr_succ h_2n_plus_1)
    -- Combine: 2·σn = succ (succ (2n))
    have h_2sn : axioms ⊢ (mul two (succ n) ≐ succ (succ (mul two n))) :=
      FOL.derive_eq_trans h_ax9_inst h_add_2n_2
    -- Paso 2: mod2(σ(2n)) = 1. Vía alternancia at (2n) + ih (mod2(2n) = 0).
    have h_alt_2n : axioms ⊢ (add (mod2 (succ (mul two n))) (mod2 (mul two n)) ≐ one) := by
      have hh := spec ax_mod2_alternation (mul two n)
      simp [substFormula, substTerm, substTerms, add, mod2, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h_ax4_sn : axioms ⊢ (add (mod2 (succ (mul two n))) zero ≐ mod2 (succ (mul two n))) := by
      have hh := spec h_ax4 (mod2 (succ (mul two n)))
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have h_cong_to_zero : axioms ⊢
        (add (mod2 (succ (mul two n))) (mod2 (mul two n)) ≐
         add (mod2 (succ (mul two n))) zero) :=
      eq_congr_add_left ih
    have h_mod2_sn_plus_zero : axioms ⊢ (add (mod2 (succ (mul two n))) zero ≐ one) :=
      FOL.derive_eq_trans (eq_symm h_cong_to_zero) h_alt_2n
    have h_mod2_sn_one : axioms ⊢ (mod2 (succ (mul two n)) ≐ one) :=
      FOL.derive_eq_trans (eq_symm h_ax4_sn) h_mod2_sn_plus_zero
    -- Paso 3: mod2(σσ(2n)) = 0. Vía alternancia at σ(2n) + paso 2.
    have h_alt_s2n : axioms ⊢
        (add (mod2 (succ (succ (mul two n)))) (mod2 (succ (mul two n))) ≐ one) := by
      have hh := spec ax_mod2_alternation (succ (mul two n))
      simp [substFormula, substTerm, substTerms, add, mod2, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h_cong_to_one : axioms ⊢
        (add (mod2 (succ (succ (mul two n)))) (mod2 (succ (mul two n))) ≐
         add (mod2 (succ (succ (mul two n)))) one) :=
      eq_congr_add_left h_mod2_sn_one
    have h_mod2_ssn_plus_one : axioms ⊢ (add (mod2 (succ (succ (mul two n)))) one ≐ one) :=
      FOL.derive_eq_trans (eq_symm h_cong_to_one) h_alt_s2n
    have h_mod2_ssn_zero : axioms ⊢ (mod2 (succ (succ (mul two n))) ≐ zero) :=
      a_plus_one_eq_one (mod2 (succ (succ (mul two n)))) h_mod2_ssn_plus_one
    -- Paso 4: mod2(2·σn) = mod2(σσ(2n)) = 0.
    have h_mod2_2sn_eq : axioms ⊢ (mod2 (mul two (succ n)) ≐ mod2 (succ (succ (mul two n)))) :=
      eq_congr_mod2 h_2sn
    exact FOL.derive_eq_trans h_mod2_2sn_eq h_mod2_ssn_zero

/-- **`ax24` como teorema en Full**: `⊢ ax24_mod2_of_even`. -/
theorem mod2_of_even_thm : axioms ⊢ ax24_mod2_of_even := by
  -- ax24: ∀n ∀k, (n = 2k) → mod2(n) = 0
  unfold ax24_mod2_of_even forall_2
  apply gen; intro n
  apply gen; intro k
  simp [substFormula, substTerm, substTerms, mul, two, one, mod2, zero, succ,
        FOL.substTerm_liftTerm]
  apply Minimal.Axioms.imp_intro; intro h_n_eq_2k
  -- spec mod2_two_k_eq_zero_ax at k: mod2(2k) = 0
  have h_inner : axioms ⊢ (mod2 (mul two k) ≐ zero) := by
    have hh := spec mod2_two_k_eq_zero_ax k
    simp [substFormula, substTerm, substTerms, mod2, mul, FOL.substTerm_liftTerm] at hh
    exact hh
  -- h_n_eq_2k : n = 2k. eq_congr_mod2: mod2(n) = mod2(2k).
  have h_mod2_eq : axioms ⊢ (mod2 n ≐ mod2 (mul two k)) :=
    eq_congr_mod2 h_n_eq_2k
  exact FOL.derive_eq_trans h_mod2_eq h_inner

end ROBINSON_PlusPlus.Full

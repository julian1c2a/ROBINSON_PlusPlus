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


/-! ### §PRIM — la cadena sobre `primAxioms` ([ADR‑023](../../DECISIONS.md), `ax24`)

⭐ **Por qué esta sección existe y no es duplicación**: `ax24` era el **último** de los diez
derivables de `coreAxioms` sin certificar sobre `primAxioms`. La cadena entera se prueba aquí
**sobre los primitivos**, y las versiones `axioms ⊢` de abajo pasan a ser **envoltorios** por
`prim_to_axioms` — no hay ninguna prueba repetida.

⚠️ **La pieza que decidía si la ruta corta valía** es `add_eq_zero_right_prim`: la versión
`axioms` usaba `teo_2_9` (de `Block1`, que vive sobre `axioms` porque allí `Γ := axioms`), y
portarlo habría arrastrado medio bloque. Se evita con `zero_or_succ_ax_prim`, que ya existía. -/

/-- `a + b = 0 → b = 0`, sobre los primitivos. **Sustituye al uso de `teo_2_9`.**
    Ruta: `zero_or_succ_ax_prim` sobre `b`; el caso `b = σk` da `σ(a+k) = 0`, que contradice `ax2`.
    ⚠️ **Forma‑trampa** (consume la hipótesis): se prueba **directamente** sobre `primAxioms`,
    no se debilita desde `axioms`. -/
theorem add_eq_zero_right_prim (a b : Term) (h : primAxioms ⊢ (add a b ≐ zero)) :
    primAxioms ⊢ (b ≐ zero) := by
  have hzos := spec zero_or_succ_ax_prim b
  simp [zero, succ] at hzos
  apply Minimal.Axioms.or_elim hzos
  · intro hb0; exact hb0
  · intro hex
    apply ex_elim hex; intro k hbk
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm] at hbk
    have hax5 := spec (spec (axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)) a) k
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm] at hax5
    have h1 : primAxioms ⊢ (add a b ≐ succ (add a k)) :=
      FOL.derive_eq_trans (eq_congr_add_left (u := a) hbk) hax5
    have h2 : primAxioms ⊢ (succ (add a k) ≐ zero) :=
      FOL.derive_eq_trans (eq_symm h1) h
    have hax2 := spec (axp (by simp [primAxioms] : ax2_peano_succ_neq_zero ∈ primAxioms)) (add a k)
    simp [substTerm, substTerms, succ, zero,
          FOL.substTerm_liftTerm] at hax2
    exact false_elim (mp hax2 h2)



/-- `0 ≠ 1` sobre los primitivos. -/
theorem teo_1_11_prim : primAxioms ⊢ neg (zero ≐ one) := by
  have h_ax2 := axp (by simp [primAxioms] : ax2_peano_succ_neq_zero ∈ primAxioms)
  exact eq_symm_neg (spec h_ax2 zero)

/-- `mod2(0) = 0` sobre los primitivos. Usa `add_eq_zero_right_prim` en vez de `teo_2_9`
    (que vive sobre `axioms`). -/
theorem mod2_zero_prim : primAxioms ⊢ (mod2 zero ≐ zero) := by
  have h_ax17 := axp (by simp [primAxioms] : ax17_div_mod_eq ∈ primAxioms)
  have h_inst := spec h_ax17 zero
  simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, zero, two, one, succ,
        FOL.substTerm_liftTerm] at h_inst
  exact add_eq_zero_right_prim (mul (div2 zero) two) (mod2 zero) h_inst

theorem ax_mod2_alternation_prim : primAxioms ⊢ Formula.forall
    (add (mod2 (succ (.var 0))) (mod2 (.var 0)) ≐ one) := by
  apply gen; intro n
  simp only [substFormula, substTerm, substTerms, add, mod2, one, zero, succ]
  have h21 := axp (by simp [primAxioms] : ax21_mod2_range ∈ primAxioms)
  have h16 := axp (by simp [primAxioms] : ax16_mod2_succ ∈ primAxioms)
  have h4  := axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)
  have h21n : primAxioms ⊢ lor (mod2 n ≐ zero) (mod2 n ≐ one) := by
    have hh := spec h21 n
    simp [substFormula, substTerm, substTerms, mod2, zero, one, succ] at hh
    exact hh
  have h21sn : primAxioms ⊢ lor (mod2 (succ n) ≐ zero) (mod2 (succ n) ≐ one) := by
    have hh := spec h21 (succ n)
    simp [substFormula, substTerm, substTerms, mod2, zero, one, succ] at hh
    exact hh
  have h16n : primAxioms ⊢ iff (mod2 n ≐ zero) (mod2 (succ n) ≐ one) := by
    have hh := spec h16 n
    simp [substFormula, substTerm, substTerms, iff, mod2, zero, one, succ] at hh
    exact hh
  have h4sn : primAxioms ⊢ (add (mod2 (succ n)) zero ≐ mod2 (succ n)) := by
    have hh := spec h4 (mod2 (succ n))
    simp [substFormula, substTerm, substTerms, add, zero] at hh
    exact hh
  have hz1 : primAxioms ⊢ (add zero one ≐ one) := by
    have hh := spec zero_add_prim one
    simp [substFormula, substTerm, substTerms, add, zero, one, succ] at hh
    exact hh
  refine ROBINSON_PlusPlus.Minimal.Axioms.or_elim h21n ?_ ?_
  · -- mod2 n = 0  ⇒  mod2 (σn) = 1, y `x + 0 = x`
    intro hA
    have hsn1 : primAxioms ⊢ (mod2 (succ n) ≐ one) :=
      mp (ROBINSON_PlusPlus.Minimal.Axioms.and_elim_left h16n) hA
    exact FOL.derive_eq_trans (FOL.derive_eq_trans (eq_congr_add_left hA) h4sn) hsn1
  · -- mod2 n = 1: hay que volver a partir por `ax21` en σn
    intro hB
    refine ROBINSON_PlusPlus.Minimal.Axioms.or_elim h21sn ?_ ?_
    · intro hB1   -- mod2 (σn) = 0  ⇒  `0 + 1 = 1`
      exact FOL.derive_eq_trans
        (FOL.derive_eq_trans (eq_congr_add_right (u := mod2 n) hB1) (eq_congr_add_left hB)) hz1
    · intro hB2   -- mod2 (σn) = 1  ⇒  ax16 hacia atrás da mod2 n = 0, contra hB
      have hn0 : primAxioms ⊢ (mod2 n ≐ zero) :=
        mp (ROBINSON_PlusPlus.Minimal.Axioms.and_elim_right h16n) hB2
      exact ROBINSON_PlusPlus.Minimal.Axioms.false_elim
        (mp (eq_symm_neg teo_1_11_prim) (FOL.derive_eq_trans (eq_symm hB) hn0))


private theorem a_plus_one_eq_one_prim (a : Term) (h : primAxioms ⊢ (add a one ≐ one)) :
    primAxioms ⊢ (a ≐ zero) := by
  -- one = succ zero. a + succ zero = succ (a + zero) por ax5. ax3 inj: a+zero=zero. ax4: a=0.
  have h_ax3 := axp (by simp [primAxioms] : ax3_peano_succ_inj ∈ primAxioms)
  have h_ax4 := axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)
  have h_ax5 := axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)
  -- ax5 inst: a + succ zero = succ (a + zero)
  have h5 : primAxioms ⊢ (add a (succ zero) ≐ succ (add a zero)) := by
    have hh := spec (spec h_ax5 a) zero
    simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
    exact hh
  -- h : add a one = one. one = succ zero, así que add a (succ zero) = succ zero.
  have h_one_unfold : primAxioms ⊢ (add a (succ zero) ≐ succ zero) := h  -- one := succ zero defequationally
  -- combine: succ (add a zero) = succ zero
  have h_succsucc : primAxioms ⊢ (succ (add a zero) ≐ succ zero) :=
    FOL.derive_eq_trans (eq_symm h5) h_one_unfold
  -- ax3 inj: a + zero = zero
  have h_ax3_inst : primAxioms ⊢ ((succ (add a zero) ≐ succ zero) ⇒ (add a zero ≐ zero)) := by
    have hh := spec (spec h_ax3 (add a zero)) zero
    simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  have h_az_zero : primAxioms ⊢ (add a zero ≐ zero) := mp h_ax3_inst h_succsucc
  -- ax4: a + zero = a, así a = zero por eq_trans (no-estándar)
  have h_ax4_inst : primAxioms ⊢ (add a zero ≐ a) := by
    have hh := spec h_ax4 a
    simp [substFormula, substTerm, substTerms, add, zero] at hh
    exact hh
  exact eq_trans h_ax4_inst h_az_zero  -- (a+0=a) ∧ (a+0=0) → a=0

theorem mod2_two_k_eq_zero_prim : primAxioms ⊢ Formula.forall
    (mod2 (mul two (.var 0)) ≐ zero) := by
  apply induction_object_prim
  · -- base: mod2(2·0) = 0. Vía ax8 (n·0=0) + mod2_zero_prim + eq_congr_mod2.
    simp only [substFormula, substTerm, substTerms, mod2, mul, two, one, zero, succ,
               FOL.substTerm_liftTerm]
    have h_ax8_inst : primAxioms ⊢ (mul two zero ≐ zero) := by
      have hh := spec (axp (by simp [primAxioms] : ax8_mul_zero ∈ primAxioms)) two
      simp [substFormula, substTerm, substTerms, mul, zero] at hh
      exact hh
    have h_mod2_2_0 : primAxioms ⊢ (mod2 (mul two zero) ≐ mod2 zero) :=
      eq_congr_mod2 h_ax8_inst
    exact FOL.derive_eq_trans h_mod2_2_0 mod2_zero_prim
  · -- step: assume mod2(2n) = 0. Want mod2(2(σn)) = 0.
    apply gen; intro n
    rw [step_eq_reduce]
    apply ROBINSON_PlusPlus.Minimal.Axioms.imp_intro; intro ih
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
    have h_ax9_inst : primAxioms ⊢ (mul two (succ n) ≐ add (mul two n) two) := by
      have hh := spec (spec (axp (by simp [primAxioms] : ax9_mul_succ ∈ primAxioms)) two) n
      simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    -- Paso 1b: 2n + 2 = σσ(2n). two = succ one = succ (succ zero).
    -- ax5(2n, 1): 2n + succ 1 = succ (2n + 1). 1 = succ 0. So 2n + 2 = succ (2n + 1).
    -- ax5(2n, 0): 2n + succ 0 = succ (2n + 0). ax4: 2n + 0 = 2n. So 2n + 1 = succ (2n).
    -- Combined: 2n + 2 = succ (succ (2n)).
    have h_ax5 := axp (by simp [primAxioms] : ax5_add_succ ∈ primAxioms)
    have h_ax4 := axp (by simp [primAxioms] : ax4_add_zero ∈ primAxioms)
    have h_add_2n_2 : primAxioms ⊢ (add (mul two n) two ≐ succ (succ (mul two n))) := by
      -- two = succ one = succ (succ zero) definitionally
      -- 2n + 2 = 2n + succ one  (def two)
      -- ax5 at (2n, one): 2n + succ one = succ (2n + one)
      have h_step1 : primAxioms ⊢ (add (mul two n) (succ one) ≐ succ (add (mul two n) one)) := by
        have hh := spec (spec h_ax5 (mul two n)) one
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
        exact hh
      -- ax5 at (2n, zero): 2n + succ zero = succ (2n + zero). one = succ zero.
      have h_step2 : primAxioms ⊢ (add (mul two n) one ≐ succ (add (mul two n) zero)) := by
        have hh := spec (spec h_ax5 (mul two n)) zero
        simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
        exact hh  -- one is definitionally succ zero
      -- ax4 at (2n): 2n + zero = 2n
      have h_step3 : primAxioms ⊢ (add (mul two n) zero ≐ mul two n) := by
        have hh := spec h_ax4 (mul two n)
        simp [substFormula, substTerm, substTerms, add, zero] at hh
        exact hh
      -- Combine: 2n+1 = succ(2n+0) = succ(2n). 2n+2 = succ(2n+1) = succ(succ(2n)).
      have h_2n_plus_1 : primAxioms ⊢ (add (mul two n) one ≐ succ (mul two n)) :=
        FOL.derive_eq_trans h_step2 (eq_congr_succ h_step3)
      exact FOL.derive_eq_trans h_step1 (eq_congr_succ h_2n_plus_1)
    -- Combine: 2·σn = succ (succ (2n))
    have h_2sn : primAxioms ⊢ (mul two (succ n) ≐ succ (succ (mul two n))) :=
      FOL.derive_eq_trans h_ax9_inst h_add_2n_2
    -- Paso 2: mod2(σ(2n)) = 1. Vía alternancia at (2n) + ih (mod2(2n) = 0).
    have h_alt_2n : primAxioms ⊢ (add (mod2 (succ (mul two n))) (mod2 (mul two n)) ≐ one) := by
      have hh := spec ax_mod2_alternation_prim (mul two n)
      simp [substFormula, substTerm, substTerms, add, mod2, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h_ax4_sn : primAxioms ⊢ (add (mod2 (succ (mul two n))) zero ≐ mod2 (succ (mul two n))) := by
      have hh := spec h_ax4 (mod2 (succ (mul two n)))
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have h_cong_to_zero : primAxioms ⊢
        (add (mod2 (succ (mul two n))) (mod2 (mul two n)) ≐
         add (mod2 (succ (mul two n))) zero) :=
      eq_congr_add_left ih
    have h_mod2_sn_plus_zero : primAxioms ⊢ (add (mod2 (succ (mul two n))) zero ≐ one) :=
      FOL.derive_eq_trans (eq_symm h_cong_to_zero) h_alt_2n
    have h_mod2_sn_one : primAxioms ⊢ (mod2 (succ (mul two n)) ≐ one) :=
      FOL.derive_eq_trans (eq_symm h_ax4_sn) h_mod2_sn_plus_zero
    -- Paso 3: mod2(σσ(2n)) = 0. Vía alternancia at σ(2n) + paso 2.
    have h_alt_s2n : primAxioms ⊢
        (add (mod2 (succ (succ (mul two n)))) (mod2 (succ (mul two n))) ≐ one) := by
      have hh := spec ax_mod2_alternation_prim (succ (mul two n))
      simp [substFormula, substTerm, substTerms, add, mod2, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h_cong_to_one : primAxioms ⊢
        (add (mod2 (succ (succ (mul two n)))) (mod2 (succ (mul two n))) ≐
         add (mod2 (succ (succ (mul two n)))) one) :=
      eq_congr_add_left h_mod2_sn_one
    have h_mod2_ssn_plus_one : primAxioms ⊢ (add (mod2 (succ (succ (mul two n)))) one ≐ one) :=
      FOL.derive_eq_trans (eq_symm h_cong_to_one) h_alt_s2n
    have h_mod2_ssn_zero : primAxioms ⊢ (mod2 (succ (succ (mul two n))) ≐ zero) :=
      a_plus_one_eq_one_prim (mod2 (succ (succ (mul two n)))) h_mod2_ssn_plus_one
    -- Paso 4: mod2(2·σn) = mod2(σσ(2n)) = 0.
    have h_mod2_2sn_eq : primAxioms ⊢ (mod2 (mul two (succ n)) ≐ mod2 (succ (succ (mul two n)))) :=
      eq_congr_mod2 h_2sn
    exact FOL.derive_eq_trans h_mod2_2sn_eq h_mod2_ssn_zero

theorem mod2_of_even_prim : primAxioms ⊢ ax24_mod2_of_even := by
  -- ax24: ∀n ∀k, (n = 2k) → mod2(n) = 0
  unfold ax24_mod2_of_even forall_2
  apply gen; intro n
  apply gen; intro k
  simp [substFormula, substTerm, substTerms, mul, two, one, mod2, zero, succ,
        FOL.substTerm_liftTerm]
  apply ROBINSON_PlusPlus.Minimal.Axioms.imp_intro; intro h_n_eq_2k
  -- spec mod2_two_k_eq_zero_prim at k: mod2(2k) = 0
  have h_inner : primAxioms ⊢ (mod2 (mul two k) ≐ zero) := by
    have hh := spec mod2_two_k_eq_zero_prim k
    simp [substFormula, substTerm, substTerms, mod2, mul, FOL.substTerm_liftTerm] at hh
    exact hh
  -- h_n_eq_2k : n = 2k. eq_congr_mod2: mod2(n) = mod2(2k).
  have h_mod2_eq : primAxioms ⊢ (mod2 n ≐ mod2 (mul two k)) :=
    eq_congr_mod2 h_n_eq_2k
  exact FOL.derive_eq_trans h_mod2_eq h_inner


/-! ### §WRAP — las firmas `axioms ⊢`, por `prim_to_axioms`

Se conservan porque hay consumidores (y porque el enunciado sobre `axioms` es el que la teoría
usa). **Ninguna repite una prueba**: todas debilitan su gemela `prim`. -/

/-- `mod2(0) = 0`. -/
theorem mod2_zero_aux : axioms ⊢ (mod2 zero ≐ zero) := prim_to_axioms mod2_zero_prim

/-- 🏁 **La alternancia** — teorema desde el 2026‑09‑10h, y certificada sobre los primitivos
    el 2026‑09‑12. -/
theorem ax_mod2_alternation : axioms ⊢ Formula.forall
    (add (mod2 (succ (.var 0))) (mod2 (.var 0)) ≐ one) :=
  prim_to_axioms ax_mod2_alternation_prim

/-- `∀k, mod2(2k) = 0`. -/
theorem mod2_two_k_eq_zero_ax : axioms ⊢ Formula.forall (mod2 (mul two (.var 0)) ≐ zero) :=
  prim_to_axioms mod2_two_k_eq_zero_prim

/-- 🏁 **`ax24` como teorema en Full** — y desde el 2026‑09‑12 **certificado sobre
    `primAxioms`**, que cierra el censo de [ADR‑023](../../DECISIONS.md) en **10 de 10**. -/
theorem mod2_of_even_thm : axioms ⊢ ax24_mod2_of_even := prim_to_axioms mod2_of_even_prim

end ROBINSON_PlusPlus.Full

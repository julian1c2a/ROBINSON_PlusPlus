/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Full.Induction

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
## FULL — Inducción fuerte (course-of-values) derivada de `ax_induction`

Derivamos la **inducción fuerte** sobre predicados object-level
(`φ : Formula` con `var 0` libre) a partir de la inducción ordinaria
`ax_induction`, SIN añadir ningún axioma nuevo. Esto valida formalmente que
`ax_induction` es suficiente para el razonamiento por buen-ordenamiento.

**Forma** (predicado object-level, hipótesis/conclusión meta):

  `strong_induction φ : (∀n, (∀m, m<n → φ(m)) → φ(n)) → ∀n, φ(n)`

donde `φ(t) := substFormula 0 t φ`.

**Estrategia clásica** (motivo auxiliar): se define
`ψ(k) := ∀m, m<k ⇒ φ(m)` como fórmula object-level, se prueba `∀k, ψ(k)` por
inducción ordinaria (base vacua por `not_lt_zero`, paso por `lt_succ_split`), y
de `ψ(σn)` con `n<σn` se concluye `φ(n)`.

**Nota De Bruijn**: el motivo `ψ` mete `φ` bajo un binder nuevo vía
`liftFormula 1 φ`. La reducción se cierra con el lema clave
`substFormula_liftFormula` (subst deshace lift al mismo índice), versión
`Formula` del `FOL.substTerm_liftTerm` ya existente.
-/

/-! ### Lema clave: subst deshace lift (versión Formula) -/

/-- `substFormula c s (liftFormula c φ) = φ` — la sustitución al mismo índice
    que el lift lo deshace. Versión `Formula` de `FOL.substTerm_liftTerm`. -/
theorem substFormula_liftFormula (φ : Formula) (c : Nat) (s : Term) :
    substFormula c s (liftFormula c φ) = φ := by
  induction φ generalizing c s with
  | bottom => rfl
  | atom p ts =>
      simp only [liftFormula, substFormula]
      rw [FOL.substTerms_liftTerms]
  | eq t u =>
      simp only [liftFormula, substFormula]
      rw [FOL.substTerm_liftTerm, FOL.substTerm_liftTerm]
  | impl a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c s, ihb c s]
  | «forall» a iha =>
      simp only [liftFormula, substFormula]
      rw [iha (c + 1) (liftTerm 0 s)]
  | and a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c s, ihb c s]
  | or a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c s, ihb c s]
  | ex a iha =>
      simp only [liftFormula, substFormula]
      rw [iha (c + 1) (liftTerm 0 s)]

/-! ### Helpers aritméticos locales (los de Induction.lean son privados) -/

private theorem add_zero_si (x : Term) : axioms ⊢ (add x zero =eq x) := by
  have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) x
  simp [substFormula, substTerm, substTerms, add, zero] at hh; exact hh

private theorem add_succ_si (x y : Term) : axioms ⊢ (add x (succ y) =eq succ (add x y)) := by
  have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) x) y
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

/-! ### `lt_succ_split`: `m < σn → m < n ∨ m = n` -/

/-- `m < σn → (m < n ∨ m = n)`. Por extracción del testigo (`ax13`),
    cancelación de sucesor (`ax3`+`ax5`) y casos cero/sucesor del testigo. -/
theorem lt_succ_split (m n : Term) (h : axioms ⊢ lt m (succ n)) :
    axioms ⊢ lor (lt m n) (m =eq n) := by
  have h13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  -- ax13 (m, σn): m < σn ⇔ ∃k, m + σk = σn
  have hiff := spec (spec h13 m) (succ n)
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply ex_elim (iff_mp hiff h); intro k hk
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hk
  -- hk : add m (succ k) =eq succ n
  -- ax5: m + σk = σ(m+k). Then σ(m+k) = σn → m+k = n (ax3 inj).
  have hk2 : axioms ⊢ (succ (add m k) =eq succ n) :=
    FOL.derive_eq_trans (eq_symm (add_succ_si m k)) hk
  have h3_inst : axioms ⊢ ((succ (add m k) =eq succ n) ⇒ (add m k =eq n)) := by
    have hh := spec (spec h3 (add m k)) n
    simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  have h_mk_n : axioms ⊢ (add m k =eq n) := mp h3_inst hk2
  -- k = 0 ∨ k = σj
  have hzos := spec zero_or_succ_ax k
  simp [substFormula, substTerm, substTerms, zero, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hzos
  apply Minimal.Axioms.or_elim hzos
  · -- k = 0 → m = n
    intro hk0
    apply Minimal.Axioms.or_intro_right
    -- m + 0 = n ; m + 0 = m → m = n
    have h_m0_n : axioms ⊢ (add m zero =eq n) :=
      FOL.derive_eq_trans (eq_congr_add_left (u := m) (eq_symm hk0)) h_mk_n
    exact eq_trans (add_zero_si m) h_m0_n
  · -- k = σj → m < n
    intro hex
    apply ex_elim hex; intro j hj
    simp [substFormula, substTerm, substTerms, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hj
    -- hj : k =eq σj.  m + σj = n  →  m < n (ax13 backward).
    apply Minimal.Axioms.or_intro_left
    have h_mj_n : axioms ⊢ (add m (succ j) =eq n) :=
      FOL.derive_eq_trans (eq_congr_add_left (u := m) (eq_symm hj)) h_mk_n
    have hiff2 := spec (spec h13 m) n
    simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff2
    apply iff_mpr hiff2
    apply ex_intro j
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
    exact h_mj_n

/-! ### Motivo auxiliar `PSI` y sus lemas -/

/-- Motivo auxiliar `ψ(k) := ∀m, m < k ⇒ φ(m)` (con `k = var 0` libre). -/
private def PSI (φ : Formula) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (.var 1)) (liftFormula 1 φ))

/-- Reducción de `ψ` instanciado: `ψ(t) = ∀m, m < t ⇒ φ(m)`. -/
private theorem psi_at (φ : Formula) (t : Term) :
    substFormula 0 t (PSI φ)
      = Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 t)) φ) := by
  simp only [PSI, substFormula, substTerm, substTerms, lt]
  rw [substFormula_liftFormula]
  simp [substTerm]

/-- Extracción: de `ψ(t)` y `m < t` deriva `φ(m)`. -/
private theorem psi_elim (φ : Formula) (t m : Term)
    (h_psi : axioms ⊢ substFormula 0 t (PSI φ))
    (h_lt : axioms ⊢ lt m t) :
    axioms ⊢ substFormula 0 m φ := by
  rw [psi_at] at h_psi
  have hspec := spec h_psi m
  simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hspec
  exact mp hspec h_lt

/-! ### Inducción fuerte -/

/-- **Inducción fuerte (course-of-values)** derivada de `ax_induction`.

    Para `φ : Formula` (con `var 0` libre), si el paso fuerte
    `∀n, (∀m, m<n → φ(m)) → φ(n)` es derivable meta-nivel para cada `n`,
    entonces `φ(n)` vale para todo `n`. NO añade axiomas. -/
theorem strong_induction (φ : Formula)
    (step : ∀ n : Term,
              (∀ m : Term, axioms ⊢ lt m n → axioms ⊢ substFormula 0 m φ) →
              axioms ⊢ substFormula 0 n φ) :
    ∀ n : Term, axioms ⊢ substFormula 0 n φ := by
  -- Probar ⊢ ∀k, ψ(k) por inducción ordinaria.
  have hall : axioms ⊢ Formula.forall (PSI φ) := by
    apply induction_object
    · -- base: ψ(0) = ∀m, m<0 ⇒ φ(m), vacuamente cierto.
      rw [psi_at]
      apply gen; intro m
      simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm]
      apply Minimal.Axioms.imp_intro; intro h_lt_m_0
      -- h_lt_m_0 : ⊢ lt m (liftTerm 0 zero) = lt m zero
      have h_lt_m_0' : axioms ⊢ lt m zero := h_lt_m_0
      exact false_elim (mp (not_lt_zero m) h_lt_m_0')
    · -- step: ψ(n) → ψ(σn).
      apply gen; intro n
      rw [step_reduce]
      apply Minimal.Axioms.imp_intro; intro h_psi_n
      -- Goal: ⊢ substFormula 0 (σn) (PSI φ) = ψ(σn)
      rw [psi_at]
      apply gen; intro m
      simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm]
      apply Minimal.Axioms.imp_intro; intro h_lt_m_sn
      -- h_lt_m_sn : ⊢ lt m (succ n).  Goal: ⊢ substFormula 0 m φ.
      apply Minimal.Axioms.or_elim (lt_succ_split m n h_lt_m_sn)
      · -- m < n: por ψ(n).
        intro h_lt_mn
        exact psi_elim φ n m h_psi_n h_lt_mn
      · -- m = n: φ(n) por `step`, transportar a φ(m).
        intro h_m_eq_n
        have h_phi_n : axioms ⊢ substFormula 0 n φ :=
          step n (fun m' h' => psi_elim φ n m' h_psi_n h')
        exact Derives.subst axioms n m φ (eq_symm h_m_eq_n) h_phi_n
  -- Concluir φ(n) de ψ(σn) con n < σn.
  intro n
  have hspec := spec hall (succ n)
  exact psi_elim φ (succ n) n hspec (lt_succ_self n)

end ROBINSON_PlusPlus.Full

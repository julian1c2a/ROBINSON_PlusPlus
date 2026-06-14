/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.CodeArith

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.SubstArith

/-!
## META — NIVEL D (real): aritmetización de la sustitución  (Fase 2, sub-paso 2.2)

Núcleo duro: la sustitución De Bruijn `substTerm`/`substFormula` se internaliza
como **funciones object** sobre los códigos, y se demuestra el **lema de cómputo**
`⊢ substtc(⌜v⌝,⌜s⌝,⌜t⌝) = ⌜substTerm v s t⌝` por **inducción meta** sobre la
estructura. Este archivo cubre el **nivel término** (sin binders), que valida el
método completo (funciones object + ecuaciones recursivas + congruencias +
condicionales del caso `var` + inducción mutua). El nivel fórmula (con la
complicación del lift bajo binders) sigue el mismo patrón.

**Estatus de las ecuaciones recursivas** (`substtc_*`, `substtsc_*`): son las
ecuaciones que **definen** las funciones object (extensión definicional
conservadora, estilo `pow`/`prod_pairs`). Aquí se declaran como axiomas sobre
`axioms ⊢`; la **integración final** las mueve a `Minimal.axioms` (entradas de la
lista) para que también `⊢ᴴ` las tenga. Logicamente es el mismo contenido.
-/

/-! ### Congruencias de `cons` (patrón `eq_congr`, vía `Derives.subst`) -/

/-- Congruencia de `cons` en el segundo argumento (cola). -/
theorem congr_cons_tail {h t₁ t₂ : Term} (hh : axioms ⊢ (t₁ =eq t₂)) :
    axioms ⊢ (cons h t₁ =eq cons h t₂) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 h) (liftTerm 0 t₁)) (cons (liftTerm 0 h) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons h t₁) (cons h s) := by
    intro s
    simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst axioms t₁ t₂ f hh ((hS t₁) ▸ Derives.refl axioms (cons h t₁))

/-- Congruencia de `cons` en el primer argumento (cabeza). -/
theorem congr_cons_head {h₁ h₂ t : Term} (hh : axioms ⊢ (h₁ =eq h₂)) :
    axioms ⊢ (cons h₁ t =eq cons h₂ t) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 h₁) (liftTerm 0 t)) (cons (.var 0) (liftTerm 0 t))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons h₁ t) (cons s t) := by
    intro s
    simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS h₂) ▸ Derives.subst axioms h₁ h₂ f hh ((hS h₁) ▸ Derives.refl axioms (cons h₁ t))

/-- `⊢ pred (σⁿ⁺¹0) = σⁿ0` (predecesor de un numeral sucesor). Vía `ax26`. -/
theorem pred_numeral (m : Nat) : axioms ⊢ (pred (numeral (m + 1)) =eq numeral m) := by
  have hh := spec (ax (show ax26_pred_succ ∈ axioms by simp [axioms])) (numeral m)
  simp only [ax26_pred_succ, substFormula, substTerm, substTerms, pred, succ,
    FOL.substTerm_liftTerm] at hh
  exact hh

/- Cancelación de **triple lift** (espejo de `FOL.substTerm_liftLift`, un nivel
   más): sustituir en `c+2` un término triplemente desplazado en `c` devuelve el
   doblemente desplazado. Necesaria para instanciar axiomas `forall_4` (la
   primera variable atraviesa 3 binders ⟹ triple lift). -/
mutual
theorem substTerm_liftLiftLift (t : Term) (c : Nat) (s : Term) :
    substTerm (c + 2) s (liftTerm c (liftTerm c (liftTerm c t))) = liftTerm c (liftTerm c t) := by
  cases t with
  | var n =>
      by_cases h1 : n < c
      · simp [liftTerm, substTerm, h1, show ¬ n = c + 2 from by omega, show ¬ n > c + 2 from by omega]
      · have h2 : ¬ n + 1 < c := by omega
        have h3 : ¬ n + 1 + 1 < c := by omega
        have hgt : n + 1 + 1 + 1 > c + 2 := by omega
        simp [liftTerm, substTerm, h1, h2, h3, hgt]
        omega
  | func f ts =>
      simp only [liftTerm, substTerm]; congr 1; exact substTerms_liftLiftLift ts c s
theorem substTerms_liftLiftLift (ts : List Term) (c : Nat) (s : Term) :
    substTerms (c + 2) s (liftTerms c (liftTerms c (liftTerms c ts))) = liftTerms c (liftTerms c ts) := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨substTerm_liftLiftLift t c s, substTerms_liftLiftLift ts' c s⟩
end

/-! ### Ecuaciones recursivas de la sustitución (TEOREMAS, desde `Minimal.axioms`)

Las funciones `varc`/`funcc`/`substtc`/`substtsc` y sus **ecuaciones recursivas**
viven en `Minimal/Axioms.lean` (extensión definicional, entradas de `axioms`).
Aquí derivamos las formas Lean-parametrizadas instanciando los axiomas object
(`forall_n`) vía `ax` + `spec` (patrón de Block6). Ya **no hay `axiom` local**. -/

theorem substtc_var_eq (v s n : Term) :
    axioms ⊢ ((v =eq n) ⇒ (substtc v s (varc n) =eq s)) := by
  have hh := spec (spec (spec (ax (show ax_substtc_var_eq ∈ axioms by simp [axioms])) v) s) n
  simp [ax_substtc_var_eq, substFormula, substTerm, substTerms, substtc, varc, cons, nil, zero, succ,
    lt, pred, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem substtc_var_gt (v s n : Term) :
    axioms ⊢ ((lt v n) ⇒ (substtc v s (varc n) =eq varc (pred n))) := by
  have hh := spec (spec (spec (ax (show ax_substtc_var_gt ∈ axioms by simp [axioms])) v) s) n
  simp [ax_substtc_var_gt, substFormula, substTerm, substTerms, substtc, varc, cons, nil, zero, succ,
    lt, pred, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem substtc_var_lt (v s n : Term) :
    axioms ⊢ ((lt n v) ⇒ (substtc v s (varc n) =eq varc n)) := by
  have hh := spec (spec (spec (ax (show ax_substtc_var_lt ∈ axioms by simp [axioms])) v) s) n
  simp [ax_substtc_var_lt, substFormula, substTerm, substTerms, substtc, varc, cons, nil, zero, succ,
    lt, pred, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem substtc_func (v s sc tsc : Term) :
    axioms ⊢ (substtc v s (funcc sc tsc) =eq funcc sc (substtsc v s tsc)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substtc_func ∈ axioms by simp [axioms])) v) s) sc) tsc
  simp [ax_substtc_func, substFormula, substTerm, substTerms, substtc, substtsc, funcc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem substtsc_nil (v s : Term) :
    axioms ⊢ (substtsc v s nil =eq nil) := by
  have hh := spec (spec (ax (show ax_substtsc_nil ∈ axioms by simp [axioms])) v) s
  simp [ax_substtsc_nil, substFormula, substTerm, substTerms, substtsc, nil, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem substtsc_cons (v s h t : Term) :
    axioms ⊢ (substtsc v s (cons h t) =eq cons (substtc v s h) (substtsc v s t)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substtsc_cons ∈ axioms by simp [axioms])) v) s) h) t
  simp [ax_substtsc_cons, substFormula, substTerm, substTerms, substtsc, substtc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

/-! ### Lema de cómputo (nivel término), por inducción meta mutua -/

mutual
/-- **Cómputo de `substTerm`**: la función object `substtc` sobre códigos calcula
    el código de `substTerm v s t`. -/
theorem substTerm_arith (v : Nat) (s : Term) : ∀ (t : Term),
    axioms ⊢ (substtc (numeral v) (termCode s) (termCode t) =eq termCode (substTerm v s t))
  | .var n => by
      show axioms ⊢
        (substtc (numeral v) (termCode s) (varc (numeral n)) =eq termCode (substTerm v s (.var n)))
      rcases Nat.lt_trichotomy n v with hlt | heq | hgt
      · have hsub : substTerm v s (.var n) = .var n := by
          simp only [substTerm]; rw [if_neg (by omega), if_neg (by omega)]
        rw [hsub]
        exact mp (substtc_var_lt (numeral v) (termCode s) (numeral n)) (gnum_lt hlt)
      · subst heq
        have hsub : substTerm n s (.var n) = s := by simp [substTerm]
        rw [hsub]
        exact mp (substtc_var_eq (numeral n) (termCode s) (numeral n)) (eq_refl _)
      · have hsub : substTerm v s (.var n) = .var (n - 1) := by
          simp only [substTerm]; rw [if_neg (by omega), if_pos (by omega)]
        rw [hsub]
        have hax := mp (substtc_var_gt (numeral v) (termCode s) (numeral n)) (gnum_lt hgt)
        have hpred : axioms ⊢ (varc (pred (numeral n)) =eq varc (numeral (n - 1))) := by
          apply congr_cons_tail; apply congr_cons_head
          obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          subst hk
          simpa using pred_numeral k
        exact FOL.derive_eq_trans hax hpred
  | .func sym ts => by
      show axioms ⊢ (substtc (numeral v) (termCode s) (funcc (strCode sym) (termsCode ts))
        =eq termCode (substTerm v s (.func sym ts)))
      have hstep := substtc_func (numeral v) (termCode s) (strCode sym) (termsCode ts)
      have hih := substTerms_arith v s ts
      have hcongr : axioms ⊢ (funcc (strCode sym) (substtsc (numeral v) (termCode s) (termsCode ts))
          =eq funcc (strCode sym) (termsCode (substTerms v s ts))) := by
        unfold funcc
        apply congr_cons_tail; apply congr_cons_tail; apply congr_cons_head
        exact hih
      exact FOL.derive_eq_trans hstep hcongr

/-- **Cómputo de `substTerms`** (lista), mutuo con `substTerm_arith`. -/
theorem substTerms_arith (v : Nat) (s : Term) : ∀ (ts : List Term),
    axioms ⊢ (substtsc (numeral v) (termCode s) (termsCode ts) =eq termsCode (substTerms v s ts))
  | [] => substtsc_nil (numeral v) (termCode s)
  | t :: ts => by
      show axioms ⊢ (substtsc (numeral v) (termCode s) (cons (termCode t) (termsCode ts))
        =eq termsCode (substTerms v s (t :: ts)))
      have hstep := substtsc_cons (numeral v) (termCode s) (termCode t) (termsCode ts)
      have ih1 := substTerm_arith v s t
      have ih2 := substTerms_arith v s ts
      exact FOL.derive_eq_trans hstep (FOL.derive_eq_trans (congr_cons_head ih1) (congr_cons_tail ih2))
end

end ROBINSON_PlusPlus.Meta.SubstArith

export ROBINSON_PlusPlus.Meta.SubstArith (
  congr_cons_head
  congr_cons_tail
  pred_numeral
  substtc_var_eq
  substtc_var_gt
  substtc_var_lt
  substtc_func
  substtsc_nil
  substtsc_cons
  substTerm_arith
  substTerms_arith
)

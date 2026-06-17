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

/- Cancelación de **cuádruple lift** (para instanciar axiomas `forall_5`: la
   primera variable atraviesa 4 binders). -/
mutual
theorem substTerm_liftLiftLiftLift (t : Term) (c : Nat) (s : Term) :
    substTerm (c + 3) s (liftTerm c (liftTerm c (liftTerm c (liftTerm c t))))
      = liftTerm c (liftTerm c (liftTerm c t)) := by
  cases t with
  | var n =>
      by_cases h1 : n < c
      · simp [liftTerm, substTerm, h1, show ¬ n = c + 3 from by omega, show ¬ n > c + 3 from by omega]
      · have h2 : ¬ n + 1 < c := by omega
        have h3 : ¬ n + 1 + 1 < c := by omega
        have h4 : ¬ n + 1 + 1 + 1 < c := by omega
        have hgt : n + 1 + 1 + 1 + 1 > c + 3 := by omega
        simp [liftTerm, substTerm, h1, h2, h3, h4, hgt]
        omega
  | func f ts =>
      simp only [liftTerm, substTerm]; congr 1; exact substTerms_liftLiftLiftLift ts c s
theorem substTerms_liftLiftLiftLift (ts : List Term) (c : Nat) (s : Term) :
    substTerms (c + 3) s (liftTerms c (liftTerms c (liftTerms c (liftTerms c ts))))
      = liftTerms c (liftTerms c (liftTerms c ts)) := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨substTerm_liftLiftLiftLift t c s, substTerms_liftLiftLiftLift ts' c s⟩
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

/-! ### `liftTerm` aritmetizado (2.2f-a; necesario para los binders de `substFormula`) -/

theorem liftc_var_lt (c n : Term) :
    axioms ⊢ ((lt n c) ⇒ (liftc c (varc n) =eq varc n)) := by
  have hh := spec (spec (ax (show ax_liftc_var_lt ∈ axioms by simp [axioms])) c) n
  simp [ax_liftc_var_lt, substFormula, substTerm, substTerms, liftc, varc, cons, nil, zero, succ, lt,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftc_var_ge (c n : Term) :
    axioms ⊢ ((lt c (succ n)) ⇒ (liftc c (varc n) =eq varc (succ n))) := by
  have hh := spec (spec (ax (show ax_liftc_var_ge ∈ axioms by simp [axioms])) c) n
  simp [ax_liftc_var_ge, substFormula, substTerm, substTerms, liftc, varc, cons, nil, zero, succ, lt,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftc_func (c sc tsc : Term) :
    axioms ⊢ (liftc c (funcc sc tsc) =eq funcc sc (liftsc c tsc)) := by
  have hh := spec (spec (spec (ax (show ax_liftc_func ∈ axioms by simp [axioms])) c) sc) tsc
  simp [ax_liftc_func, substFormula, substTerm, substTerms, liftc, liftsc, funcc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftsc_nil (c : Term) :
    axioms ⊢ (liftsc c nil =eq nil) := by
  have hh := spec (ax (show ax_liftsc_nil ∈ axioms by simp [axioms])) c
  simp [ax_liftsc_nil, substFormula, substTerm, substTerms, liftsc, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

theorem liftsc_cons (c h t : Term) :
    axioms ⊢ (liftsc c (cons h t) =eq cons (liftc c h) (liftsc c t)) := by
  have hh := spec (spec (spec (ax (show ax_liftsc_cons ∈ axioms by simp [axioms])) c) h) t
  simp [ax_liftsc_cons, substFormula, substTerm, substTerms, liftsc, liftc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

mutual
/-- **Cómputo de `liftTerm`**: `liftc` sobre códigos calcula el código de `liftTerm c t`. -/
theorem liftTerm_arith (c : Nat) : ∀ (t : Term),
    axioms ⊢ (liftc (numeral c) (termCode t) =eq termCode (liftTerm c t))
  | .var n => by
      show axioms ⊢ (liftc (numeral c) (varc (numeral n)) =eq termCode (liftTerm c (.var n)))
      by_cases hlt : n < c
      · have hsub : liftTerm c (.var n) = .var n := by simp [liftTerm, hlt]
        rw [hsub]
        exact mp (liftc_var_lt (numeral c) (numeral n)) (gnum_lt hlt)
      · have hsub : liftTerm c (.var n) = .var (n + 1) := by simp [liftTerm, hlt]
        rw [hsub]
        exact mp (liftc_var_ge (numeral c) (numeral n)) (gnum_lt (by omega : c < n + 1))
  | .func sym ts => by
      show axioms ⊢ (liftc (numeral c) (funcc (strCode sym) (termsCode ts))
        =eq termCode (liftTerm c (.func sym ts)))
      have hstep := liftc_func (numeral c) (strCode sym) (termsCode ts)
      have hih := liftTerms_arith c ts
      have hcongr : axioms ⊢ (funcc (strCode sym) (liftsc (numeral c) (termsCode ts))
          =eq funcc (strCode sym) (termsCode (liftTerms c ts))) := by
        unfold funcc
        apply congr_cons_tail; apply congr_cons_tail; apply congr_cons_head
        exact hih
      exact FOL.derive_eq_trans hstep hcongr

/-- **Cómputo de `liftTerms`** (lista), mutuo con `liftTerm_arith`. -/
theorem liftTerms_arith (c : Nat) : ∀ (ts : List Term),
    axioms ⊢ (liftsc (numeral c) (termsCode ts) =eq termsCode (liftTerms c ts))
  | [] => liftsc_nil (numeral c)
  | t :: ts => by
      show axioms ⊢ (liftsc (numeral c) (cons (termCode t) (termsCode ts))
        =eq termsCode (liftTerms c (t :: ts)))
      have hstep := liftsc_cons (numeral c) (termCode t) (termsCode ts)
      have ih1 := liftTerm_arith c t
      have ih2 := liftTerms_arith c ts
      exact FOL.derive_eq_trans hstep (FOL.derive_eq_trans (congr_cons_head ih1) (congr_cons_tail ih2))
end

/-! ### `substFormula` aritmetizado (2.2f-b): ecuaciones (teoremas) -/

theorem substfc_bottom (v t : Term) :
    axioms ⊢ (substfc v t botc =eq botc) := by
  have hh := spec (spec (ax (show ax_substfc_bottom ∈ axioms by simp [axioms])) v) t
  simp [ax_substfc_bottom, substFormula, substTerm, substTerms, substfc, botc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem substfc_atom (v t pc tsc : Term) :
    axioms ⊢ (substfc v t (atomc pc tsc) =eq atomc pc (substtsc v t tsc)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substfc_atom ∈ axioms by simp [axioms])) v) t) pc) tsc
  simp [ax_substfc_atom, substFormula, substTerm, substTerms, substfc, substtsc, atomc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem substfc_eq (v t a b : Term) :
    axioms ⊢ (substfc v t (eqc a b) =eq eqc (substtc v t a) (substtc v t b)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substfc_eq ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_eq, substFormula, substTerm, substTerms, substfc, substtc, eqc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem substfc_impl (v t a b : Term) :
    axioms ⊢ (substfc v t (implc a b) =eq implc (substfc v t a) (substfc v t b)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substfc_impl ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_impl, substFormula, substTerm, substTerms, substfc, implc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem substfc_and (v t a b : Term) :
    axioms ⊢ (substfc v t (andc a b) =eq andc (substfc v t a) (substfc v t b)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substfc_and ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_and, substFormula, substTerm, substTerms, substfc, andc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem substfc_or (v t a b : Term) :
    axioms ⊢ (substfc v t (orc a b) =eq orc (substfc v t a) (substfc v t b)) := by
  have hh := spec (spec (spec (spec (ax (show ax_substfc_or ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_or, substFormula, substTerm, substTerms, substfc, orc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem substfc_forall (v t a : Term) :
    axioms ⊢ (substfc v t (forallc a) =eq forallc (substfc (succ v) (liftc zero t) a)) := by
  have hh := spec (spec (spec (ax (show ax_substfc_forall ∈ axioms by simp [axioms])) v) t) a
  simp [ax_substfc_forall, substFormula, substTerm, substTerms, substfc, liftc, forallc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem substfc_ex (v t a : Term) :
    axioms ⊢ (substfc v t (exc a) =eq exc (substfc (succ v) (liftc zero t) a)) := by
  have hh := spec (spec (spec (ax (show ax_substfc_ex ∈ axioms by simp [axioms])) v) t) a
  simp [ax_substfc_ex, substFormula, substTerm, substTerms, substfc, liftc, exc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Congruencias para los constructores de código (vía `cons`) y `substfc` -/

/-- Congruencia en el 1er argumento de un constructor binario `cons T (cons · (cons _ nil))`. -/
theorem congr_bin1 {T x x' y : Term} (h : axioms ⊢ (x =eq x')) :
    axioms ⊢ (cons T (cons x (cons y nil)) =eq cons T (cons x' (cons y nil))) :=
  congr_cons_tail (congr_cons_head h)
/-- Congruencia en el 2º argumento de un constructor binario. -/
theorem congr_bin2 {T x y y' : Term} (h : axioms ⊢ (y =eq y')) :
    axioms ⊢ (cons T (cons x (cons y nil)) =eq cons T (cons x (cons y' nil))) :=
  congr_cons_tail (congr_cons_tail (congr_cons_head h))
/-- Congruencia en el argumento de un constructor unario `cons T (cons · nil)`. -/
theorem congr_un {T x x' : Term} (h : axioms ⊢ (x =eq x')) :
    axioms ⊢ (cons T (cons x nil) =eq cons T (cons x' nil)) :=
  congr_cons_tail (congr_cons_head h)

/-- Congruencia de `substfc` en el 2º argumento (el substituyendo). -/
theorem congr_substfc_arg2 {x z a b : Term} (h : axioms ⊢ (a =eq b)) :
    axioms ⊢ (substfc x a z =eq substfc x b z) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 x) (liftTerm 0 a) (liftTerm 0 z))
                                 (substfc (liftTerm 0 x) (.var 0) (liftTerm 0 z))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc x a z) (substfc x s z) := by
    intro s
    simp only [f, substFormula, substfc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst axioms a b f h ((hS a) ▸ Derives.refl axioms (substfc x a z))

/-! ### Lema de cómputo de `substFormula` (nivel fórmula), por recursión en `f` -/

/-- **Cómputo de `substFormula`**: la función object `substfc` calcula el código de
    `substFormula v s f`. Recursión estructural en `f`; los binders ∀/∃ recurren
    con nivel `v+1` y substituyendo `liftTerm 0 s` (vía `liftTerm_arith`). -/
theorem substFormula_arith : ∀ (v : Nat) (s : Term) (f : Formula),
    axioms ⊢ (substfc (numeral v) (termCode s) (formCode f) =eq formCode (substFormula v s f))
  | v, s, .bottom => substfc_bottom (numeral v) (termCode s)
  | v, s, .atom p ts =>
      FOL.derive_eq_trans (substfc_atom (numeral v) (termCode s) (strCode p) (termsCode ts))
        (congr_bin2 (substTerms_arith v s ts))
  | v, s, .eq a b =>
      FOL.derive_eq_trans (substfc_eq (numeral v) (termCode s) (termCode a) (termCode b))
        (FOL.derive_eq_trans (congr_bin1 (substTerm_arith v s a)) (congr_bin2 (substTerm_arith v s b)))
  | v, s, .impl a b =>
      FOL.derive_eq_trans (substfc_impl (numeral v) (termCode s) (formCode a) (formCode b))
        (FOL.derive_eq_trans (congr_bin1 (substFormula_arith v s a)) (congr_bin2 (substFormula_arith v s b)))
  | v, s, .and a b =>
      FOL.derive_eq_trans (substfc_and (numeral v) (termCode s) (formCode a) (formCode b))
        (FOL.derive_eq_trans (congr_bin1 (substFormula_arith v s a)) (congr_bin2 (substFormula_arith v s b)))
  | v, s, .or a b =>
      FOL.derive_eq_trans (substfc_or (numeral v) (termCode s) (formCode a) (formCode b))
        (FOL.derive_eq_trans (congr_bin1 (substFormula_arith v s a)) (congr_bin2 (substFormula_arith v s b)))
  | v, s, .forall a =>
      FOL.derive_eq_trans (substfc_forall (numeral v) (termCode s) (formCode a))
        (congr_un (FOL.derive_eq_trans
          (congr_substfc_arg2 (x := succ (numeral v)) (z := formCode a) (liftTerm_arith 0 s))
          (substFormula_arith (v + 1) (liftTerm 0 s) a)))
  | v, s, .ex a =>
      FOL.derive_eq_trans (substfc_ex (numeral v) (termCode s) (formCode a))
        (congr_un (FOL.derive_eq_trans
          (congr_substfc_arg2 (x := succ (numeral v)) (z := formCode a) (liftTerm_arith 0 s))
          (substFormula_arith (v + 1) (liftTerm 0 s) a)))

/-! ### `liftFormula` aritmetizado (para el esquema Q3) -/

theorem liftfc_bottom (c : Term) :
    axioms ⊢ (liftfc c botc =eq botc) := by
  have hh := spec (ax (show ax_liftfc_bottom ∈ axioms by simp [axioms])) c
  simp [ax_liftfc_bottom, substFormula, substTerm, substTerms, liftfc, botc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm] at hh
  exact hh

theorem liftfc_atom (c pc tsc : Term) :
    axioms ⊢ (liftfc c (atomc pc tsc) =eq atomc pc (liftsc c tsc)) := by
  have hh := spec (spec (spec (ax (show ax_liftfc_atom ∈ axioms by simp [axioms])) c) pc) tsc
  simp [ax_liftfc_atom, substFormula, substTerm, substTerms, liftfc, liftsc, atomc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftfc_eq (c a b : Term) :
    axioms ⊢ (liftfc c (eqc a b) =eq eqc (liftc c a) (liftc c b)) := by
  have hh := spec (spec (spec (ax (show ax_liftfc_eq ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_eq, substFormula, substTerm, substTerms, liftfc, liftc, eqc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftfc_impl (c a b : Term) :
    axioms ⊢ (liftfc c (implc a b) =eq implc (liftfc c a) (liftfc c b)) := by
  have hh := spec (spec (spec (ax (show ax_liftfc_impl ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_impl, substFormula, substTerm, substTerms, liftfc, implc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftfc_and (c a b : Term) :
    axioms ⊢ (liftfc c (andc a b) =eq andc (liftfc c a) (liftfc c b)) := by
  have hh := spec (spec (spec (ax (show ax_liftfc_and ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_and, substFormula, substTerm, substTerms, liftfc, andc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftfc_or (c a b : Term) :
    axioms ⊢ (liftfc c (orc a b) =eq orc (liftfc c a) (liftfc c b)) := by
  have hh := spec (spec (spec (ax (show ax_liftfc_or ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_or, substFormula, substTerm, substTerms, liftfc, orc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftfc_forall (c a : Term) :
    axioms ⊢ (liftfc c (forallc a) =eq forallc (liftfc (succ c) a)) := by
  have hh := spec (spec (ax (show ax_liftfc_forall ∈ axioms by simp [axioms])) c) a
  simp [ax_liftfc_forall, substFormula, substTerm, substTerms, liftfc, forallc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem liftfc_ex (c a : Term) :
    axioms ⊢ (liftfc c (exc a) =eq exc (liftfc (succ c) a)) := by
  have hh := spec (spec (ax (show ax_liftfc_ex ∈ axioms by simp [axioms])) c) a
  simp [ax_liftfc_ex, substFormula, substTerm, substTerms, liftfc, exc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- **Cómputo de `liftFormula`**: `liftfc` calcula el código de `liftFormula c f`. -/
theorem liftFormula_arith : ∀ (c : Nat) (f : Formula),
    axioms ⊢ (liftfc (numeral c) (formCode f) =eq formCode (liftFormula c f))
  | c, .bottom => liftfc_bottom (numeral c)
  | c, .atom p ts =>
      FOL.derive_eq_trans (liftfc_atom (numeral c) (strCode p) (termsCode ts))
        (congr_bin2 (liftTerms_arith c ts))
  | c, .eq a b =>
      FOL.derive_eq_trans (liftfc_eq (numeral c) (termCode a) (termCode b))
        (FOL.derive_eq_trans (congr_bin1 (liftTerm_arith c a)) (congr_bin2 (liftTerm_arith c b)))
  | c, .impl a b =>
      FOL.derive_eq_trans (liftfc_impl (numeral c) (formCode a) (formCode b))
        (FOL.derive_eq_trans (congr_bin1 (liftFormula_arith c a)) (congr_bin2 (liftFormula_arith c b)))
  | c, .and a b =>
      FOL.derive_eq_trans (liftfc_and (numeral c) (formCode a) (formCode b))
        (FOL.derive_eq_trans (congr_bin1 (liftFormula_arith c a)) (congr_bin2 (liftFormula_arith c b)))
  | c, .or a b =>
      FOL.derive_eq_trans (liftfc_or (numeral c) (formCode a) (formCode b))
        (FOL.derive_eq_trans (congr_bin1 (liftFormula_arith c a)) (congr_bin2 (liftFormula_arith c b)))
  | c, .forall a =>
      FOL.derive_eq_trans (liftfc_forall (numeral c) (formCode a))
        (congr_un (liftFormula_arith (c + 1) a))
  | c, .ex a =>
      FOL.derive_eq_trans (liftfc_ex (numeral c) (formCode a))
        (congr_un (liftFormula_arith (c + 1) a))

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
  liftc_var_lt
  liftc_var_ge
  liftc_func
  liftsc_nil
  liftsc_cons
  liftTerm_arith
  liftTerms_arith
  substfc_bottom
  substfc_atom
  substfc_eq
  substfc_impl
  substfc_and
  substfc_or
  substfc_forall
  substfc_ex
  congr_bin1
  congr_bin2
  congr_un
  congr_substfc_arg2
  substFormula_arith
  liftfc_bottom
  liftfc_atom
  liftfc_eq
  liftfc_impl
  liftfc_and
  liftfc_or
  liftfc_forall
  liftfc_ex
  liftFormula_arith
)

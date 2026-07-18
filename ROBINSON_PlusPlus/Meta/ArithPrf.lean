/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.StepArith
import ROBINSON_PlusPlus.Meta.Induction

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeArith
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.StepArith
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ArithPrf

/-!
## META — NIVEL D real: aritmetización de la sustitución, re-nivelada a `Prf`

Porte finitario (`Prf`) de toda la cadena aritmética de `CodeArith`/`SubstArith`/
`StepArith`/`Induction` necesaria para `repr_pos'_prf`. Cada lema espeja su versión
`axioms ⊢` reemplazando `ax`→`prf_ax`, `spec`→`prf_spec`, `mp`→`prf_mp`,
`Derives.refl`→`prf_refl`, `FOL.derive_eq_trans`→`prf_eq_trans`, las congruencias
`congr_*`→`prf_congr_*` y `Derives.subst`→`prf_leibniz_subst`. Todas las pruebas
fuente son **finitarias** (thy/q1/q2/mp/leibniz/eqrefl/gen; sin regla ω), de modo
que el porte es directo. Los pasos meta (`simp`, `induction`, `rcases`, `rw`) se
conservan literalmente.
-/

/-! ### Primitivos lógicos extra en `Prf` -/

/-- Introducción del `∃` en `Prf` (esquema `q2` + mp). -/
theorem prf_ex_intro {A : Formula} (t : Term) (h : Prf (substFormula 0 t A)) :
    Prf (Formula.ex A) :=
  prf_mp (Prf.incl (Prf₀.q2 A t)) h

/-- Congruencia de `succ` respecto de `=eq` en `Prf`. -/
theorem prf_eq_congr_succ {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (succ t₁ =eq succ t₂) := by
  let f : Formula := Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (succ t₁) (succ s) := by
    intro s; simp only [f, substFormula, succ, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (succ t₁))

/-! ### Congruencias de constructor en `Prf` (vía `cons`) y `substfc` -/

-- `prf_congr_bin1`/`prf_congr_bin2`/`prf_congr_un` se movieron a `Meta/ReprPrf.lean` (§44), donde los
-- necesitan las re-pruebas de `prf_lineWF_<tag>` en forma de accesores. Aquí se heredan por el import.

/-- Congruencia de `substfc` en el 2º argumento (el substituyendo). -/
theorem prf_congr_substfc_arg2 {x z a b : Term} (h : Prf (a =eq b)) :
    Prf (substfc x a z =eq substfc x b z) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 x) (liftTerm 0 a) (liftTerm 0 z))
                                 (substfc (liftTerm 0 x) (.var 0) (liftTerm 0 z))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc x a z) (substfc x s z) := by
    intro s; simp only [f, substFormula, substfc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (substfc x a z))

/-- Congruencia de `substfc` en el 3er argumento (la fórmula sustituida). -/
theorem prf_congr_substfc_arg3 {x t a b : Term} (h : Prf (a =eq b)) :
    Prf (substfc x t a =eq substfc x t b) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 x) (liftTerm 0 t) (liftTerm 0 a))
                                 (substfc (liftTerm 0 x) (liftTerm 0 t) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc x t a) (substfc x t s) := by
    intro s; simp only [f, substfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (substfc x t a))

/-! ### Numerales en `Prf`: `pred`, `add`, orden -/

theorem prf_pred_numeral (m : Nat) : Prf (pred (numeral (m + 1)) =eq numeral m) := by
  have hh := prf_spec (prf_ax (show ax26_pred_succ ∈ axioms by simp [axioms])) (numeral m)
  simp only [ax26_pred_succ, substFormula, substTerm, substTerms, pred, succ,
    FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_add_zero_t (a : Term) : Prf (add a zero =eq a) := by
  have hh := prf_spec (prf_ax (show ax4_add_zero ∈ axioms by simp [axioms])) a
  simp [substFormula, substTerm, substTerms, add, zero] at hh; exact hh

theorem prf_add_succ_t (a b : Term) : Prf (add a (succ b) =eq succ (add a b)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax5_add_succ ∈ axioms by simp [axioms])) a) b
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

/-- Homomorfismo aditivo en `Prf` (inducción meta en `b`). -/
theorem prf_numeral_add (a b : Nat) :
    Prf (add (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral b)
      =eq ROBINSON_PlusPlus.Full.numeral (a + b)) := by
  induction b with
  | zero => exact prf_add_zero_t (ROBINSON_PlusPlus.Full.numeral a)
  | succ k ih =>
    show Prf (add (ROBINSON_PlusPlus.Full.numeral a) (succ (ROBINSON_PlusPlus.Full.numeral k))
      =eq succ (ROBINSON_PlusPlus.Full.numeral (a + k)))
    exact prf_eq_trans (prf_add_succ_t (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral k))
      (prf_eq_congr_succ ih)

/-- Orden estricto en `Prf` (sobre `Full.numeral`; espejo de `numeral_lt`). -/
theorem prf_numeral_lt {a b : Nat} (h : a < b) :
    Prf (lt (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral b)) := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
  subst hk
  have h13 := prf_ax (show ax13_lt_def ∈ axioms by simp [axioms])
  have hiff := prf_spec (prf_spec h13 (ROBINSON_PlusPlus.Full.numeral a))
    (ROBINSON_PlusPlus.Full.numeral (a + (k + 1)))
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply prf_iff_mpr hiff
  apply prf_ex_intro (ROBINSON_PlusPlus.Full.numeral k)
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  show Prf (add (ROBINSON_PlusPlus.Full.numeral a) (succ (ROBINSON_PlusPlus.Full.numeral k))
    =eq succ (ROBINSON_PlusPlus.Full.numeral (a + k)))
  exact prf_eq_trans (prf_add_succ_t (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral k))
    (prf_eq_congr_succ (prf_numeral_add a k))

/-- Orden estricto para códigos numéricos (`Godel.numeral`), vía `numeral_bridge`. -/
theorem prf_gnum_lt {a b : Nat} (h : a < b) : Prf (lt (numeral a) (numeral b)) := by
  rw [numeral_bridge, numeral_bridge]
  exact prf_numeral_lt h

/-! ### Ecuaciones recursivas de la sustitución (nivel término) en `Prf` -/

theorem prf_substtc_var_eq (v s n : Term) :
    Prf ((v =eq n) ⇒ (substtc v s (varc n) =eq s)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_substtc_var_eq ∈ axioms by simp [axioms])) v) s) n
  simp [ax_substtc_var_eq, substFormula, substTerm, substTerms, substtc, varc, cons, nil, zero, succ,
    lt, pred, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_substtc_var_gt (v s n : Term) :
    Prf ((lt v n) ⇒ (substtc v s (varc n) =eq varc (pred n))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_substtc_var_gt ∈ axioms by simp [axioms])) v) s) n
  simp [ax_substtc_var_gt, substFormula, substTerm, substTerms, substtc, varc, cons, nil, zero, succ,
    lt, pred, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_substtc_var_lt (v s n : Term) :
    Prf ((lt n v) ⇒ (substtc v s (varc n) =eq varc n)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_substtc_var_lt ∈ axioms by simp [axioms])) v) s) n
  simp [ax_substtc_var_lt, substFormula, substTerm, substTerms, substtc, varc, cons, nil, zero, succ,
    lt, pred, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_substtc_func (v s sc tsc : Term) :
    Prf (substtc v s (funcc sc tsc) =eq funcc sc (substtsc v s tsc)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substtc_func ∈ axioms by simp [axioms])) v) s) sc) tsc
  simp [ax_substtc_func, substFormula, substTerm, substTerms, substtc, substtsc, funcc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem prf_substtsc_nil (v s : Term) :
    Prf (substtsc v s nil =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_substtsc_nil ∈ axioms by simp [axioms])) v) s
  simp [ax_substtsc_nil, substFormula, substTerm, substTerms, substtsc, nil, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_substtsc_cons (v s h t : Term) :
    Prf (substtsc v s (cons h t) =eq cons (substtc v s h) (substtsc v s t)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substtsc_cons ∈ axioms by simp [axioms])) v) s) h) t
  simp [ax_substtsc_cons, substFormula, substTerm, substTerms, substtsc, substtc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

/-! ### Lema de cómputo (nivel término) en `Prf`, por inducción meta mutua -/

mutual
theorem prf_substTerm_arith (v : Nat) (s : Term) : ∀ (t : Term),
    Prf (substtc (numeral v) (termCode s) (termCode t) =eq termCode (substTerm v s t))
  | .var n => by
      show Prf
        (substtc (numeral v) (termCode s) (varc (numeral n)) =eq termCode (substTerm v s (.var n)))
      rcases Nat.lt_trichotomy n v with hlt | heq | hgt
      · have hsub : substTerm v s (.var n) = .var n := by
          simp only [substTerm]; rw [if_neg (by omega), if_neg (by omega)]
        rw [hsub]
        exact prf_mp (prf_substtc_var_lt (numeral v) (termCode s) (numeral n)) (prf_gnum_lt hlt)
      · subst heq
        have hsub : substTerm n s (.var n) = s := by simp [substTerm]
        rw [hsub]
        exact prf_mp (prf_substtc_var_eq (numeral n) (termCode s) (numeral n)) (prf_refl _)
      · have hsub : substTerm v s (.var n) = .var (n - 1) := by
          simp only [substTerm]; rw [if_neg (by omega), if_pos (by omega)]
        rw [hsub]
        have hax := prf_mp (prf_substtc_var_gt (numeral v) (termCode s) (numeral n)) (prf_gnum_lt hgt)
        have hpred : Prf (varc (pred (numeral n)) =eq varc (numeral (n - 1))) := by
          apply prf_congr_cons_tail; apply prf_congr_cons_head
          obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          subst hk
          simpa using prf_pred_numeral k
        exact prf_eq_trans hax hpred
  | .func sym ts => by
      show Prf (substtc (numeral v) (termCode s) (funcc (strCode sym) (termsCode ts))
        =eq termCode (substTerm v s (.func sym ts)))
      have hstep := prf_substtc_func (numeral v) (termCode s) (strCode sym) (termsCode ts)
      have hih := prf_substTerms_arith v s ts
      have hcongr : Prf (funcc (strCode sym) (substtsc (numeral v) (termCode s) (termsCode ts))
          =eq funcc (strCode sym) (termsCode (substTerms v s ts))) := by
        unfold funcc
        apply prf_congr_cons_tail; apply prf_congr_cons_tail; apply prf_congr_cons_head
        exact hih
      exact prf_eq_trans hstep hcongr

theorem prf_substTerms_arith (v : Nat) (s : Term) : ∀ (ts : List Term),
    Prf (substtsc (numeral v) (termCode s) (termsCode ts) =eq termsCode (substTerms v s ts))
  | [] => prf_substtsc_nil (numeral v) (termCode s)
  | t :: ts => by
      show Prf (substtsc (numeral v) (termCode s) (cons (termCode t) (termsCode ts))
        =eq termsCode (substTerms v s (t :: ts)))
      have hstep := prf_substtsc_cons (numeral v) (termCode s) (termCode t) (termsCode ts)
      have ih1 := prf_substTerm_arith v s t
      have ih2 := prf_substTerms_arith v s ts
      exact prf_eq_trans hstep (prf_eq_trans (prf_congr_cons_head ih1) (prf_congr_cons_tail ih2))
end

/-! ### `liftTerm` aritmetizado en `Prf` -/

theorem prf_liftc_var_lt (c n : Term) :
    Prf ((lt n c) ⇒ (liftc c (varc n) =eq varc n)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_liftc_var_lt ∈ axioms by simp [axioms])) c) n
  simp [ax_liftc_var_lt, substFormula, substTerm, substTerms, liftc, varc, cons, nil, zero, succ, lt,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftc_var_ge (c n : Term) :
    Prf ((lt c (succ n)) ⇒ (liftc c (varc n) =eq varc (succ n))) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_liftc_var_ge ∈ axioms by simp [axioms])) c) n
  simp [ax_liftc_var_ge, substFormula, substTerm, substTerms, liftc, varc, cons, nil, zero, succ, lt,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftc_func (c sc tsc : Term) :
    Prf (liftc c (funcc sc tsc) =eq funcc sc (liftsc c tsc)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftc_func ∈ axioms by simp [axioms])) c) sc) tsc
  simp [ax_liftc_func, substFormula, substTerm, substTerms, liftc, liftsc, funcc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftsc_nil (c : Term) :
    Prf (liftsc c nil =eq nil) := by
  have hh := prf_spec (prf_ax (show ax_liftsc_nil ∈ axioms by simp [axioms])) c
  simp [ax_liftsc_nil, substFormula, substTerm, substTerms, liftsc, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_liftsc_cons (c h t : Term) :
    Prf (liftsc c (cons h t) =eq cons (liftc c h) (liftsc c t)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftsc_cons ∈ axioms by simp [axioms])) c) h) t
  simp [ax_liftsc_cons, substFormula, substTerm, substTerms, liftsc, liftc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

mutual
theorem prf_liftTerm_arith (c : Nat) : ∀ (t : Term),
    Prf (liftc (numeral c) (termCode t) =eq termCode (liftTerm c t))
  | .var n => by
      show Prf (liftc (numeral c) (varc (numeral n)) =eq termCode (liftTerm c (.var n)))
      by_cases hlt : n < c
      · have hsub : liftTerm c (.var n) = .var n := by simp [liftTerm, hlt]
        rw [hsub]
        exact prf_mp (prf_liftc_var_lt (numeral c) (numeral n)) (prf_gnum_lt hlt)
      · have hsub : liftTerm c (.var n) = .var (n + 1) := by simp [liftTerm, hlt]
        rw [hsub]
        exact prf_mp (prf_liftc_var_ge (numeral c) (numeral n)) (prf_gnum_lt (by omega : c < n + 1))
  | .func sym ts => by
      show Prf (liftc (numeral c) (funcc (strCode sym) (termsCode ts))
        =eq termCode (liftTerm c (.func sym ts)))
      have hstep := prf_liftc_func (numeral c) (strCode sym) (termsCode ts)
      have hih := prf_liftTerms_arith c ts
      have hcongr : Prf (funcc (strCode sym) (liftsc (numeral c) (termsCode ts))
          =eq funcc (strCode sym) (termsCode (liftTerms c ts))) := by
        unfold funcc
        apply prf_congr_cons_tail; apply prf_congr_cons_tail; apply prf_congr_cons_head
        exact hih
      exact prf_eq_trans hstep hcongr

theorem prf_liftTerms_arith (c : Nat) : ∀ (ts : List Term),
    Prf (liftsc (numeral c) (termsCode ts) =eq termsCode (liftTerms c ts))
  | [] => prf_liftsc_nil (numeral c)
  | t :: ts => by
      show Prf (liftsc (numeral c) (cons (termCode t) (termsCode ts))
        =eq termsCode (liftTerms c (t :: ts)))
      have hstep := prf_liftsc_cons (numeral c) (termCode t) (termsCode ts)
      have ih1 := prf_liftTerm_arith c t
      have ih2 := prf_liftTerms_arith c ts
      exact prf_eq_trans hstep (prf_eq_trans (prf_congr_cons_head ih1) (prf_congr_cons_tail ih2))
end

/-! ### `substFormula` aritmetizado en `Prf`: ecuaciones -/

theorem prf_substfc_bottom (v t : Term) :
    Prf (substfc v t botc =eq botc) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_substfc_bottom ∈ axioms by simp [axioms])) v) t
  simp [ax_substfc_bottom, substFormula, substTerm, substTerms, substfc, botc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_substfc_atom (v t pc tsc : Term) :
    Prf (substfc v t (atomc pc tsc) =eq atomc pc (substtsc v t tsc)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_atom ∈ axioms by simp [axioms])) v) t) pc) tsc
  simp [ax_substfc_atom, substFormula, substTerm, substTerms, substfc, substtsc, atomc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem prf_substfc_eq (v t a b : Term) :
    Prf (substfc v t (eqc a b) =eq eqc (substtc v t a) (substtc v t b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_eq ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_eq, substFormula, substTerm, substTerms, substfc, substtc, eqc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem prf_substfc_impl (v t a b : Term) :
    Prf (substfc v t (implc a b) =eq implc (substfc v t a) (substfc v t b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_impl ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_impl, substFormula, substTerm, substTerms, substfc, implc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem prf_substfc_and (v t a b : Term) :
    Prf (substfc v t (andc a b) =eq andc (substfc v t a) (substfc v t b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_and ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_and, substFormula, substTerm, substTerms, substfc, andc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem prf_substfc_or (v t a b : Term) :
    Prf (substfc v t (orc a b) =eq orc (substfc v t a) (substfc v t b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_or ∈ axioms by simp [axioms])) v) t) a) b
  simp [ax_substfc_or, substFormula, substTerm, substTerms, substfc, orc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift] at hh
  exact hh

theorem prf_substfc_forall (v t a : Term) :
    Prf (substfc v t (forallc a) =eq forallc (substfc (succ v) (liftc zero t) a)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_forall ∈ axioms by simp [axioms])) v) t) a
  simp [ax_substfc_forall, substFormula, substTerm, substTerms, substfc, liftc, forallc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_substfc_ex (v t a : Term) :
    Prf (substfc v t (exc a) =eq exc (substfc (succ v) (liftc zero t) a)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_substfc_ex ∈ axioms by simp [axioms])) v) t) a
  simp [ax_substfc_ex, substFormula, substTerm, substTerms, substfc, liftc, exc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- **Cómputo de `substFormula`** en `Prf` (recursión estructural en `f`). -/
theorem prf_substFormula_arith : ∀ (v : Nat) (s : Term) (f : Formula),
    Prf (substfc (numeral v) (termCode s) (formCode f) =eq formCode (substFormula v s f))
  | v, s, .bottom => prf_substfc_bottom (numeral v) (termCode s)
  | v, s, .atom p ts =>
      prf_eq_trans (prf_substfc_atom (numeral v) (termCode s) (strCode p) (termsCode ts))
        (prf_congr_bin2 (prf_substTerms_arith v s ts))
  | v, s, .eq a b =>
      prf_eq_trans (prf_substfc_eq (numeral v) (termCode s) (termCode a) (termCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substTerm_arith v s a)) (prf_congr_bin2 (prf_substTerm_arith v s b)))
  | v, s, .impl a b =>
      prf_eq_trans (prf_substfc_impl (numeral v) (termCode s) (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substFormula_arith v s a)) (prf_congr_bin2 (prf_substFormula_arith v s b)))
  | v, s, .and a b =>
      prf_eq_trans (prf_substfc_and (numeral v) (termCode s) (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substFormula_arith v s a)) (prf_congr_bin2 (prf_substFormula_arith v s b)))
  | v, s, .or a b =>
      prf_eq_trans (prf_substfc_or (numeral v) (termCode s) (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substFormula_arith v s a)) (prf_congr_bin2 (prf_substFormula_arith v s b)))
  | v, s, .forall a =>
      prf_eq_trans (prf_substfc_forall (numeral v) (termCode s) (formCode a))
        (prf_congr_un (prf_eq_trans
          (prf_congr_substfc_arg2 (x := succ (numeral v)) (z := formCode a) (prf_liftTerm_arith 0 s))
          (prf_substFormula_arith (v + 1) (liftTerm 0 s) a)))
  | v, s, .ex a =>
      prf_eq_trans (prf_substfc_ex (numeral v) (termCode s) (formCode a))
        (prf_congr_un (prf_eq_trans
          (prf_congr_substfc_arg2 (x := succ (numeral v)) (z := formCode a) (prf_liftTerm_arith 0 s))
          (prf_substFormula_arith (v + 1) (liftTerm 0 s) a)))

/-! ### `liftFormula` aritmetizado en `Prf` (esquema Q3) -/

theorem prf_liftfc_bottom (c : Term) :
    Prf (liftfc c botc =eq botc) := by
  have hh := prf_spec (prf_ax (show ax_liftfc_bottom ∈ axioms by simp [axioms])) c
  simp [ax_liftfc_bottom, substFormula, substTerm, substTerms, liftfc, botc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_liftfc_atom (c pc tsc : Term) :
    Prf (liftfc c (atomc pc tsc) =eq atomc pc (liftsc c tsc)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftfc_atom ∈ axioms by simp [axioms])) c) pc) tsc
  simp [ax_liftfc_atom, substFormula, substTerm, substTerms, liftfc, liftsc, atomc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftfc_eq (c a b : Term) :
    Prf (liftfc c (eqc a b) =eq eqc (liftc c a) (liftc c b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftfc_eq ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_eq, substFormula, substTerm, substTerms, liftfc, liftc, eqc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftfc_impl (c a b : Term) :
    Prf (liftfc c (implc a b) =eq implc (liftfc c a) (liftfc c b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftfc_impl ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_impl, substFormula, substTerm, substTerms, liftfc, implc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftfc_and (c a b : Term) :
    Prf (liftfc c (andc a b) =eq andc (liftfc c a) (liftfc c b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftfc_and ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_and, substFormula, substTerm, substTerms, liftfc, andc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftfc_or (c a b : Term) :
    Prf (liftfc c (orc a b) =eq orc (liftfc c a) (liftfc c b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_liftfc_or ∈ axioms by simp [axioms])) c) a) b
  simp [ax_liftfc_or, substFormula, substTerm, substTerms, liftfc, orc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftfc_forall (c a : Term) :
    Prf (liftfc c (forallc a) =eq forallc (liftfc (succ c) a)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_liftfc_forall ∈ axioms by simp [axioms])) c) a
  simp [ax_liftfc_forall, substFormula, substTerm, substTerms, liftfc, forallc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_liftfc_ex (c a : Term) :
    Prf (liftfc c (exc a) =eq exc (liftfc (succ c) a)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_liftfc_ex ∈ axioms by simp [axioms])) c) a
  simp [ax_liftfc_ex, substFormula, substTerm, substTerms, liftfc, exc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- **Cómputo de `liftFormula`** en `Prf`. -/
theorem prf_liftFormula_arith : ∀ (c : Nat) (f : Formula),
    Prf (liftfc (numeral c) (formCode f) =eq formCode (liftFormula c f))
  | c, .bottom => prf_liftfc_bottom (numeral c)
  | c, .atom p ts =>
      prf_eq_trans (prf_liftfc_atom (numeral c) (strCode p) (termsCode ts))
        (prf_congr_bin2 (prf_liftTerms_arith c ts))
  | c, .eq a b =>
      prf_eq_trans (prf_liftfc_eq (numeral c) (termCode a) (termCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_liftTerm_arith c a)) (prf_congr_bin2 (prf_liftTerm_arith c b)))
  | c, .impl a b =>
      prf_eq_trans (prf_liftfc_impl (numeral c) (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_liftFormula_arith c a)) (prf_congr_bin2 (prf_liftFormula_arith c b)))
  | c, .and a b =>
      prf_eq_trans (prf_liftfc_and (numeral c) (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_liftFormula_arith c a)) (prf_congr_bin2 (prf_liftFormula_arith c b)))
  | c, .or a b =>
      prf_eq_trans (prf_liftfc_or (numeral c) (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_liftFormula_arith c a)) (prf_congr_bin2 (prf_liftFormula_arith c b)))
  | c, .forall a =>
      prf_eq_trans (prf_liftfc_forall (numeral c) (formCode a))
        (prf_congr_un (prf_liftFormula_arith (c + 1) a))
  | c, .ex a =>
      prf_eq_trans (prf_liftfc_ex (numeral c) (formCode a))
        (prf_congr_un (prf_liftFormula_arith (c + 1) a))

/-! ### Reconstrucción de códigos de conclusión en `Prf` (StepArith + Induction) -/

theorem prf_q1_concl_code (A : Formula) (t : Term) :
    Prf (implc (forallc (formCode A)) (substfc (numeral 0) (termCode t) (formCode A))
      =eq formCode (Formula.impl (Formula.forall A) (substFormula 0 t A))) :=
  prf_congr_bin2 (prf_substFormula_arith 0 t A)

theorem prf_q2_concl_code (A : Formula) (t : Term) :
    Prf (implc (substfc (numeral 0) (termCode t) (formCode A)) (exc (formCode A))
      =eq formCode (Formula.impl (substFormula 0 t A) (Formula.ex A))) :=
  prf_congr_bin1 (prf_substFormula_arith 0 t A)

theorem prf_leibniz_concl_code (A : Formula) (t₁ t₂ : Term) :
    Prf (implc (eqc (termCode t₁) (termCode t₂))
        (implc (substfc (numeral 0) (termCode t₁) (formCode A))
               (substfc (numeral 0) (termCode t₂) (formCode A)))
      =eq formCode (Formula.impl (Formula.eq t₁ t₂)
            (Formula.impl (substFormula 0 t₁ A) (substFormula 0 t₂ A)))) :=
  prf_congr_bin2 (prf_eq_trans
    (prf_congr_bin1 (prf_substFormula_arith 0 t₁ A))
    (prf_congr_bin2 (prf_substFormula_arith 0 t₂ A)))

/-- Reconstrucción del código de la instancia de inducción para `φ` en `Prf`. -/
theorem prf_ind_concl_code (φ : Formula) :
    Prf (
      implc (substfc (numeral 0) (termCode zero) (formCode φ))
        (implc (forallc (implc (formCode φ)
                  (substfc (numeral 0) (termCode (succ (.var 0))) (liftfc (numeral 1) (formCode φ)))))
               (forallc (formCode φ)))
      =eq formCode (Full.inductionFormula φ)) := by
  have base_eq : Prf
      (substfc (numeral 0) (termCode zero) (formCode φ) =eq formCode (substFormula 0 zero φ)) :=
    prf_substFormula_arith 0 zero φ
  have step_eq : Prf
      (substfc (numeral 0) (termCode (succ (.var 0))) (liftfc (numeral 1) (formCode φ)) =eq
        formCode (substFormula 0 (succ (.var 0)) (liftFormula 1 φ))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_liftFormula_arith 1 φ))
      (prf_substFormula_arith 0 (succ (.var 0)) (liftFormula 1 φ))
  exact prf_eq_trans (prf_congr_bin1 base_eq)
    (prf_congr_bin2 (prf_congr_bin1 (prf_congr_un (prf_congr_bin2 step_eq))))

/-- Congruencia de `liftfc` en su 2º argumento, en `Prf`. -/
theorem prf_congr_liftfc_arg2 {c a b : Term} (h : Prf (a =eq b)) :
    Prf (liftfc c a =eq liftfc c b) := by
  let f : Formula := Formula.eq (liftfc (liftTerm 0 c) (liftTerm 0 a)) (liftfc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftfc c a) (liftfc c s) := by
    intro s; simp only [f, liftfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (liftfc c a))

/-- Reconstrucción del código de la inducción de listas para `A`, en `Prf`. -/
theorem prf_listInd_concl_code (A : Formula) :
    Prf (
      implc (substfc (numeral 0) (termCode nil) (formCode A))
        (implc (forallc (forallc (implc (liftfc (numeral 1) (formCode A))
                  (substfc (numeral 0) (termCode (cons (.var 1) (.var 0)))
                    (liftfc (numeral 2) (liftfc (numeral 1) (formCode A)))))))
               (forallc (formCode A)))
      =eq formCode (listInductionFormula A)) := by
  have base_eq : Prf
      (substfc (numeral 0) (termCode nil) (formCode A) =eq formCode (substFormula 0 nil A)) :=
    prf_substFormula_arith 0 nil A
  have ante_eq : Prf
      (liftfc (numeral 1) (formCode A) =eq formCode (liftFormula 1 A)) :=
    prf_liftFormula_arith 1 A
  have lift2_eq : Prf
      (liftfc (numeral 2) (liftfc (numeral 1) (formCode A)) =eq formCode (liftFormula 2 (liftFormula 1 A))) :=
    prf_eq_trans (prf_congr_liftfc_arg2 (prf_liftFormula_arith 1 A)) (prf_liftFormula_arith 2 (liftFormula 1 A))
  have conseq_eq : Prf
      (substfc (numeral 0) (termCode (cons (.var 1) (.var 0)))
          (liftfc (numeral 2) (liftfc (numeral 1) (formCode A)))
        =eq formCode (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 lift2_eq)
      (prf_substFormula_arith 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))
  exact prf_eq_trans (prf_congr_bin1 base_eq)
    (prf_congr_bin2 (prf_congr_bin1 (prf_congr_un (prf_congr_un
      (prf_eq_trans (prf_congr_bin1 ante_eq) (prf_congr_bin2 conseq_eq))))))

end ROBINSON_PlusPlus.Meta.ArithPrf

export ROBINSON_PlusPlus.Meta.ArithPrf (
  prf_ex_intro
  prf_eq_congr_succ
  prf_congr_substfc_arg2
  prf_congr_substfc_arg3
  prf_gnum_lt
  prf_substTerm_arith
  prf_substTerms_arith
  prf_liftTerm_arith
  prf_liftTerms_arith
  prf_substFormula_arith
  prf_liftFormula_arith
  prf_q1_concl_code
  prf_q2_concl_code
  prf_leibniz_concl_code
  prf_ind_concl_code
  prf_listInd_concl_code
)

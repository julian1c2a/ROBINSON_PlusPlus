/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.ArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.NatArithPrf

/-!
## META — NIVEL D real (D3 vía Σ₁-completitud, §12‑A): toolkit aritmético de `<` en `Prf`

Hacia la caracterización acotada `In x L ⇔ ∃ i < lenc L. nthc L i =eq x` (§12‑A fase 1b), que
descansa sobre lemas generales de `<` a nivel del cálculo finitario `Prf`. Como `<` se define
`a < b ⇔ ∃k. a + σk = b` (`ax13_lt_def`) y `add` recurre por la derecha (`add a 0 = a`,
`add a (σb) = σ(add a b)`), la identidad izquierda `0 + n = n` **no es teorema de Q**
(independiente sin inducción); se prueba con la regla `Prf.ind`.

Este módulo entrega el **eliminador de inducción natural** `prf_nat_induction` (análogo de
`prf_list_induction`, envolviendo `Prf.ind`) y la **identidad izquierda** `prf_add_zero_left`,
primer cimiento del toolkit. -/

/-- Congruencia de `succ` en `PrfH` (Leibniz object, patrón `PrfH_congr_cons_head`). -/
theorem PrfH_eq_congr_succ {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (succ t₁ =eq succ t₂) := by
  let f : Formula := Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (succ t₁) (succ s) := by
    intro s; simp only [f, succ, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (succ t₁)) Γ)

/-- **Eliminador de inducción natural en `Prf`**: de `Prf (Φ[0])` y
    `Prf (∀n (Φ[n] ⇒ Φ[σn]))` sale `Prf (∀n Φ[n])`. Envuelve `Prf.ind` (regla del verificador). -/
theorem prf_nat_induction (Φ : Formula)
    (base : Prf (substFormula 0 zero Φ))
    (step : Prf (Formula.forall (Formula.impl Φ
              (substFormula 0 (succ (.var 0)) (liftFormula 1 Φ)))))
    : Prf (Formula.forall Φ) :=
  prf_mp (prf_mp (Prf.ind Φ) base) step

/-- **Identidad izquierda de `add`** en `Prf`: `0 + n = n` (por `prf_nat_induction`;
    NO derivable sin inducción). -/
theorem prf_add_zero_left (n : Term) : Prf (add zero n =eq n) := by
  have key : Prf (Formula.forall (Formula.eq (add zero (.var 0)) (.var 0))) := by
    refine prf_nat_induction (Formula.eq (add zero (.var 0)) (.var 0)) ?base ?step
    · show Prf (add zero zero =eq zero)
      exact prf_add_zero_t zero
    · refine Prf.gen _ ?_
      simp only [substFormula, substTerm, substTerms, add, succ, liftFormula, liftTerm, liftTerms,
        zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction ?_
      have ih : PrfH [Formula.eq (add zero (.var 0)) (.var 0)] (add zero (.var 0) =eq (.var 0)) :=
        prfH_hyp_self _
      exact PrfH_eq_trans (prf_to_prfH (prf_add_succ_t zero (.var 0)) _) (PrfH_eq_congr_succ ih)
  have hn := prf_spec key n
  simpa only [substFormula, substTerm, substTerms, add, zero, Nat.reduceEqDiff, Nat.reduceGT,
    reduceIte, if_true, FOL.substTerm_liftTerm] using hn

/-- Normalización De Bruijn de un binder: el parámetro `t` (protegido por `liftTerm 0`)
    vuelve intacto tras `substTerm 0 s (liftTerm 1 ·)` del `step` de `prf_nat_induction`. -/
theorem norm11 (s t : Term) : substTerm 0 s (liftTerm 1 (liftTerm 0 t)) = liftTerm 0 t := by
  rw [(FOL.liftTerm_comm_zero t 0).symm]
  exact FOL.substTerm_liftTerm (liftTerm 0 t) 0 s

/-- **`σm + n = σ(m + n)`** en `Prf` (add por la izquierda; inducción sobre `n`, NO
    derivable sin inducción). -/
theorem prf_add_succ_left (m n : Term) : Prf (add (succ m) n =eq succ (add m n)) := by
  have key : Prf (Formula.forall (Formula.eq
      (add (succ (liftTerm 0 m)) (.var 0)) (succ (add (liftTerm 0 m) (.var 0))))) := by
    refine prf_nat_induction _ ?base ?step
    · simp only [substFormula, substTerm, substTerms, add, succ, zero, Nat.reduceEqDiff,
        reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact prf_eq_trans (prf_add_zero_t (succ m))
        (prf_eq_symm (prf_eq_congr_succ (prf_add_zero_t m)))
    · refine Prf.gen _ ?_
      simp only [substFormula, substTerm, substTerms, add, succ, liftFormula, liftTerm, liftTerms,
        zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, if_true,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift, norm11]
      refine prf_deduction ?_
      have ih : PrfH [Formula.eq (add (succ (liftTerm 0 m)) (.var 0)) (succ (add (liftTerm 0 m) (.var 0)))]
          (add (succ (liftTerm 0 m)) (.var 0) =eq succ (add (liftTerm 0 m) (.var 0))) := prfH_hyp_self _
      exact PrfH_eq_trans (prf_to_prfH (prf_add_succ_t (succ (liftTerm 0 m)) (.var 0)) _)
        (PrfH_eq_trans (PrfH_eq_congr_succ ih)
          (prf_to_prfH (prf_eq_symm (prf_eq_congr_succ (prf_add_succ_t (liftTerm 0 m) (.var 0)))) _))
  have hn := prf_spec key n
  simpa only [substFormula, substTerm, substTerms, add, succ, Nat.reduceEqDiff, Nat.reduceGT,
    reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hn

/-- **Introducción de `<` desde un testigo** en `PrfH`: de `add a (σk) =eq b` sale `lt a b`
    (`k` es el testigo del `∃k. a + σk = b` de `ax13_lt_def`). -/
theorem PrfH_lt_intro {Γ : List Formula} (a b k : Term)
    (h : PrfH Γ (add a (succ k) =eq b)) : PrfH Γ (lt a b) := by
  have hiff := prf_spec (prf_spec (prf_ax (show ax13_lt_def ∈ axioms by simp [axioms])) a) b
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  refine PrfH_iff_mpr hiff ?_
  refine PrfH_ex_intro k ?_
  simp only [substFormula, substTerm, substTerms, add, succ, zero, Nat.reduceEqDiff, reduceIte,
    if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact h

/-- Introducción de `<` desde un testigo, versión `Prf` (cerrada). -/
theorem prf_lt_intro (a b k : Term) (h : Prf (add a (succ k) =eq b)) : Prf (lt a b) :=
  prfH_nil_to_prf (PrfH_lt_intro (Γ := []) a b k (prf_to_prfH h [])) rfl

/-- **`0 < σn`** en `Prf` (testigo `k = n`; `add 0 (σn) = σ(0+n) = σn`). -/
theorem prf_zero_lt_succ (n : Term) : Prf (lt zero (succ n)) :=
  prf_lt_intro zero (succ n) n
    (prf_eq_trans (prf_add_succ_t zero n) (prf_eq_congr_succ (prf_add_zero_left n)))

/-- **Desplegado de `<`**: `lt a b ⇔ ∃k. a + σk = b` (instancia de `ax13_lt_def`, con el
    cuerpo del `∃` ya reducido: bajo el binder, `a`,`b` aparecen con un `liftTerm 0`). -/
theorem prf_lt_iff (a b : Term) :
    Prf (lt a b ⇔ Formula.ex (Formula.eq (add (liftTerm 0 a) (succ (.var 0))) (liftTerm 0 b))) := by
  have hiff := prf_spec (prf_spec (prf_ax (show ax13_lt_def ∈ axioms by simp [axioms])) a) b
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff, liftTerm, liftTerms,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  exact hiff

/-- **`m < n ⇒ σm < σn`** en `Prf`. Mismo testigo `k`: de `m + σk = n` sale
    `σm + σk = σ(m + σk) = σn` (`prf_add_succ_left` + congruencia `succ`).
    El `∃`-elim va por **`prf_ex_elim_imp`** (lift simple, casa con el `↑m`/`↑n` del cuerpo);
    `PrfH_ex_elim` NO sirve aquí porque liftea además el contexto (doble lift). -/
theorem prf_succ_lt_succ_of_lt (m n : Term) : Prf (lt m n ⇒ lt (succ m) (succ n)) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (liftTerm 0 n))
      ⇒ lt (succ m) (succ n)) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (liftTerm 0 n)]
      (lt (succ (liftTerm 0 m)) (succ (liftTerm 0 n)))
    refine PrfH_lt_intro (succ (liftTerm 0 m)) (succ (liftTerm 0 n)) (.var 0) ?_
    -- add (σ↑m) (σ#0) =eq σ(add ↑m (σ#0)) =eq σ↑n
    exact PrfH_eq_trans
      (prf_to_prfH (prf_add_succ_left (liftTerm 0 m) (succ (.var 0))) _)
      (PrfH_eq_congr_succ (prfH_hyp_self _))
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff m n) (prfH_hyp_self _)))

/-! ### Peano 2/3 en `Prf` (σ ≠ 0, σ inyectiva) y las dos piezas restantes de `<` -/

/-- `σn ≠ 0` en `Prf` (`ax2_peano_succ_neq_zero`). -/
theorem prf_succ_ne_zero (n : Term) : Prf (neg (succ n =eq zero)) := by
  have hh := prf_spec (prf_ax (show ax2_peano_succ_neq_zero ∈ axioms by simp [axioms])) n
  simp [ax2_peano_succ_neq_zero, substFormula, substTerm, substTerms, neg, succ, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `σa = σb ⇒ a = b` en `Prf` (`ax3_peano_succ_inj`). -/
theorem prf_succ_inj (a b : Term) : Prf ((succ a =eq succ b) ⇒ (a =eq b)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax3_peano_succ_inj ∈ axioms by simp [axioms])) a) b
  simp [ax3_peano_succ_inj, substFormula, substTerm, substTerms, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- **`¬ (n < 0)`** en `Prf`: de `n + σk = 0` sale `σ(n+k) = 0`, contra `ax2`. -/
theorem prf_not_lt_zero (n : Term) : Prf (lt n zero ⇒ Formula.bottom) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 n) (succ (.var 0))) (liftTerm 0 zero))
      ⇒ Formula.bottom) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 n) (succ (.var 0))) zero] Formula.bottom
    have hsz : PrfH [Formula.eq (add (liftTerm 0 n) (succ (.var 0))) zero]
        (succ (add (liftTerm 0 n) (.var 0)) =eq zero) :=
      PrfH_eq_trans (prf_to_prfH (prf_eq_symm (prf_add_succ_t (liftTerm 0 n) (.var 0))) _)
        (prfH_hyp_self _)
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (add (liftTerm 0 n) (.var 0))) _) hsz
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff n zero) (prfH_hyp_self _)))

/-- **`σm < σn ⇒ m < n`** (converso de `prf_succ_lt_succ_of_lt`): de `σm + σk = σn` sale
    `σ(m + σk) = σn` (`prf_add_succ_left`), y por inyectividad de `σ`, `m + σk = n`. -/
theorem prf_lt_of_succ_lt_succ (m n : Term) : Prf (lt (succ m) (succ n) ⇒ lt m n) := by
  have himp : Prf (Formula.ex (Formula.eq
      (add (liftTerm 0 (succ m)) (succ (.var 0))) (liftTerm 0 (succ n))) ⇒ lt m n) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (succ (liftTerm 0 m)) (succ (.var 0))) (succ (liftTerm 0 n))]
      (lt (liftTerm 0 m) (liftTerm 0 n))
    have hs : PrfH [Formula.eq (add (succ (liftTerm 0 m)) (succ (.var 0))) (succ (liftTerm 0 n))]
        (succ (add (liftTerm 0 m) (succ (.var 0))) =eq succ (liftTerm 0 n)) :=
      PrfH_eq_trans
        (prf_to_prfH (prf_eq_symm (prf_add_succ_left (liftTerm 0 m) (succ (.var 0)))) _)
        (prfH_hyp_self _)
    refine PrfH_lt_intro (liftTerm 0 m) (liftTerm 0 n) (.var 0) ?_
    exact PrfH.mp _ _ _
      (prf_to_prfH (prf_succ_inj (add (liftTerm 0 m) (succ (.var 0))) (liftTerm 0 n)) _) hs
  exact prf_deduction (PrfH.mp _ _ _ (prf_to_prfH himp _)
    (PrfH_iff_mp (prf_lt_iff (succ m) (succ n)) (prfH_hyp_self _)))

end ROBINSON_PlusPlus.Meta.NatArithPrf

export ROBINSON_PlusPlus.Meta.NatArithPrf (
  PrfH_eq_congr_succ prf_nat_induction norm11
  prf_add_zero_left prf_add_succ_left
  prf_lt_iff PrfH_lt_intro prf_lt_intro
  prf_succ_ne_zero prf_succ_inj
  prf_zero_lt_succ prf_succ_lt_succ_of_lt prf_lt_of_succ_lt_succ prf_not_lt_zero
)

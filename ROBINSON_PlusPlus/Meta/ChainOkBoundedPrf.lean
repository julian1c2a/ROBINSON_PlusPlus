/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

/-!
## META — NIVEL D real (§12‑A FASE 2, lado `chainOk`): sub‑lemas (b) y (c)

Hacia `chainOk c p ⇔ chainOkB c p` (plan `GODEL-D3-TRACKED-DESIGN.md` §14.2‑14.3), donde el
acumulador se elimina **generalizando en `c`**: cada premisa está o bien ya en el contexto
inicial `c`, o bien es la conclusión de una línea **anterior** (`∃ k < i`).

Este módulo entrega, **independientes entre sí**:

* **(b)** `In y (concat c [x]) ⇔ In y c ∨ y =eq x` — el paso que absorbe una conclusión nueva
  en el acumulador (pura álgebra de listas, de `ax_L3_in_concat` + `ax_L2`).
* **(0)** `boundedCarcLt y p b` — el `∃ k < b. carc (nthc p k) =eq y` con **cota arbitraria**
  (generaliza `boundedCarcIn`, que la fijaba a `lenc p`).
* **(c)** el split del `∃ k < σj` sobre una lista `cons`.
-/

/-! ### (b) Absorción de una conclusión en el acumulador -/

/-- `In x (L ++ M) ⇔ In x L ∨ In x M` en `Prf` (cierre de `ax_L3_in_concat`). -/
theorem prf_in_concat_iff (x L M : Term) :
    Prf (In x (concat L M) ⇔ lor (In x L) (In x M)) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax_L3_in_concat ∈ axioms by simp [axioms])) x) L) M
  simp [ax_L3_in_concat, substFormula, substTerm, substTerms, In, concat, cons, nil, zero,
    lor, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- `In y [x] ⇔ y =eq x` (la lista unitaria). -/
theorem prf_in_cons_nil_iff (y x : Term) : Prf (In y (cons x nil) ⇔ (y =eq x)) := by
  refine prf_and_intro ?_ ?_
  · refine prf_deduction ?_
    have hor : PrfH [In y (cons x nil)] (lor (y =eq x) (In y nil)) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_iff y x nil)) _)
        (prfH_hyp_self _)
    refine PrfH_or_elim hor ?_ ?_
    · exact PrfH.hyp _ _ (List.Mem.head _)
    · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil y) _) (PrfH.hyp _ _ (List.Mem.head _)))
  · refine prf_deduction ?_
    exact PrfH_eq_subst_in (PrfH_congr_cons_head (prfH_hyp_self _))
      (prf_to_prfH (prf_in_cons_head y nil) _)

/-- **(b)** `In y (c ++ [x]) ⇔ In y c ∨ y =eq x`. Es el paso que absorbe la conclusión de la
    línea actual en el acumulador de `chainOk`. -/
theorem prf_in_concat_singleton_iff (y c x : Term) :
    Prf (In y (concat c (cons x nil)) ⇔ lor (In y c) (Formula.eq y x)) := by
  refine prf_and_intro ?_ ?_
  · refine prf_deduction ?_
    have hor : PrfH [In y (concat c (cons x nil))] (lor (In y c) (In y (cons x nil))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_concat_iff y c (cons x nil))) _)
        (prfH_hyp_self _)
    refine PrfH_or_elim hor ?_ ?_
    · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (PrfH.hyp _ _ (List.Mem.head _))
    · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_nil_iff y x)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  · refine prf_deduction ?_
    refine PrfH_or_elim (prfH_hyp_self (lor (In y c) (Formula.eq y x))) ?_ ?_
    · exact PrfH.mp _ _ _
        (prf_to_prfH (prf_and_elim_right (prf_in_concat_iff y c (cons x nil))) _)
        (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (PrfH.hyp _ _ (List.Mem.head _)))
    · exact PrfH.mp _ _ _
        (prf_to_prfH (prf_and_elim_right (prf_in_concat_iff y c (cons x nil))) _)
        (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_right (prf_in_cons_nil_iff y x)) _)
            (PrfH.hyp _ _ (List.Mem.head _))))

/-! ### (0) Cota arbitraria: `boundedCarcLt`

`boundedCarcIn` fijaba la cota a `lenc p`. Para `chainOk` la cota es el índice de la línea
actual (`∃ k < i`), así que se generaliza a una cota `b` arbitraria. -/

/-- `∃ k < b. carc (nthc p k) =eq y` (cota `b` **arbitraria**; `k = #0` bajo el `∃`). -/
def boundedCarcLt (y p b : Term) : Formula :=
  Formula.ex (land (lt (.var 0) (liftTerm 0 b))
                   (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y)))

/-- `boundedCarcIn` es la instancia con cota `lenc p` (definicional). -/
theorem boundedCarcIn_eq_boundedCarcLt (y p : Term) :
    boundedCarcIn y p = boundedCarcLt y p (lenc p) := rfl

/-- Clausura De Bruijn de `boundedCarcLt` (vía `liftTerm_comm_zero`; NO es defeq). -/
theorem liftFormula_boundedCarcLt (y p b : Term) :
    liftFormula 0 (boundedCarcLt y p b) = boundedCarcLt (liftTerm 0 y) (liftTerm 0 p) (liftTerm 0 b) := by
  simp only [boundedCarcLt, liftFormula, liftTerm, liftTerms, land, lt, nthc, carc,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

/-! ### (c) Split del `∃ k < σj` sobre una lista `cons` -/

/-- Cola → todo: `(∃ k < j. carc (nthc rest k) =eq y) ⇒ (∃ k < σj. carc (nthc (cons line rest) k) =eq y)`
    (reindexa `k ↦ σk`). -/
theorem prf_boundedCarcLt_cons_of_tail (y line rest j : Term) :
    Prf (boundedCarcLt y rest j ⇒ boundedCarcLt y (cons line rest) (succ j)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_boundedCarcLt]
  let C : Formula := land (lt (.var 0) (liftTerm 0 j))
    (Formula.eq (carc (nthc (liftTerm 0 rest) (.var 0))) (liftTerm 0 y))
  show PrfH [C] (boundedCarcLt (liftTerm 0 y) (liftTerm 0 (cons line rest)) (liftTerm 0 (succ j)))
  have hlt : PrfH [C] (lt (.var 0) (liftTerm 0 j)) := PrfH_and_elim_left (prfH_hyp_self C)
  have heq : PrfH [C] (Formula.eq (carc (nthc (liftTerm 0 rest) (.var 0))) (liftTerm 0 y)) :=
    PrfH_and_elim_right (prfH_hyp_self C)
  refine PrfH_ex_intro (succ (.var 0)) ?_
  simp only [boundedCarcLt, substFormula, substTerm, substTerms, land, lt, nthc, carc, cons, succ,
    Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm]
  refine PrfH_and_intro ?_ ?_
  · exact PrfH.mp _ _ _
      (prf_to_prfH (prf_succ_lt_succ_of_lt (.var 0) (liftTerm 0 j)) _) hlt
  · exact PrfH_eq_trans
      (PrfH_eq_congr_carc (prf_to_prfH
        (prf_nthc_succ (liftTerm 0 line) (liftTerm 0 rest) (.var 0)) _)) heq

/-- Cabeza → todo: `carc line =eq y ⇒ (∃ k < σj. carc (nthc (cons line rest) k) =eq y)` (testigo `0`). -/
theorem prf_boundedCarcLt_cons_of_head (y line rest j : Term) :
    Prf ((Formula.eq (carc line) y) ⇒ boundedCarcLt y (cons line rest) (succ j)) := by
  refine prf_deduction ?_
  refine PrfH_ex_intro zero ?_
  simp only [boundedCarcLt, substFormula, substTerm, substTerms, land, lt, nthc, carc, cons, succ,
    zero, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm]
  refine PrfH_and_intro (prf_to_prfH (prf_zero_lt_succ j) _) ?_
  exact PrfH_eq_trans (PrfH_eq_congr_carc (prf_to_prfH (prf_nthc_zero line rest) _))
    (prfH_hyp_self _)

/-- **(c)** Split del `∃ k < σj` sobre `cons`:
    `(∃ k < σj. carc (nthc (cons line rest) k) =eq y) ⇔ (carc line =eq y ∨ ∃ k < j. carc (nthc rest k) =eq y)`.
    ⇒ por `prf_ex_elim_imp` + case‑split de `k` con `prf_zero_or_eq_succ_pred`;
    ⇐ por los dos lemas de reintroducción. -/
theorem prf_boundedCarcLt_cons_succ_iff (y line rest j : Term) :
    Prf (boundedCarcLt y (cons line rest) (succ j)
      ⇔ lor (Formula.eq (carc line) y) (boundedCarcLt y rest j)) := by
  refine prf_and_intro ?_ ?_
  · -- ⇒
    refine prf_ex_elim_imp ?_
    have hlor : liftFormula 0 (lor (Formula.eq (carc line) y) (boundedCarcLt y rest j))
        = lor (Formula.eq (carc (liftTerm 0 line)) (liftTerm 0 y))
              (liftFormula 0 (boundedCarcLt y rest j)) := rfl
    rw [hlor, liftFormula_boundedCarcLt]
    let C : Formula := land (lt (.var 0) (liftTerm 0 (succ j)))
      (Formula.eq (carc (nthc (liftTerm 0 (cons line rest)) (.var 0))) (liftTerm 0 y))
    let Z : Formula := Formula.eq (.var 0) zero
    let S : Formula := Formula.eq (.var 0) (succ (pred (.var 0)))
    show PrfH [C] (lor (Formula.eq (carc (liftTerm 0 line)) (liftTerm 0 y))
      (boundedCarcLt (liftTerm 0 y) (liftTerm 0 rest) (liftTerm 0 j)))
    refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?_ ?_
    · -- k = 0  ⇒  carc line = y
      have hz : PrfH [Z, C] Z := PrfH.hyp _ _ (List.Mem.head _)
      have heq : PrfH [Z, C]
          (Formula.eq (carc (nthc (liftTerm 0 (cons line rest)) (.var 0))) (liftTerm 0 y)) :=
        PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) ?_
      exact PrfH_eq_trans
        (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_carc (PrfH_eq_congr_nthc2 hz))
          (PrfH_eq_congr_carc (prf_to_prfH
            (prf_nthc_zero (liftTerm 0 line) (liftTerm 0 rest)) _))))
        heq
    · -- k = σ(pred k)  ⇒  cola con testigo pred k
      have hs : PrfH [S, C] S := PrfH.hyp _ _ (List.Mem.head _)
      have hC : PrfH [S, C] C := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hlt : PrfH [S, C] (lt (.var 0) (liftTerm 0 (succ j))) := PrfH_and_elim_left hC
      have heq : PrfH [S, C]
          (Formula.eq (carc (nthc (liftTerm 0 (cons line rest)) (.var 0))) (liftTerm 0 y)) :=
        PrfH_and_elim_right hC
      have hltJ : PrfH [S, C] (lt (pred (.var 0)) (liftTerm 0 j)) :=
        PrfH.mp _ _ _
          (prf_to_prfH (prf_lt_of_succ_lt_succ (pred (.var 0)) (liftTerm 0 j)) _)
          (PrfH_lt_subst1 hs hlt)
      refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
      refine PrfH_ex_intro (pred (.var 0)) ?_
      simp only [boundedCarcLt, substFormula, substTerm, substTerms, land, lt, nthc, carc, cons,
        pred, succ, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm]
      refine PrfH_and_intro hltJ ?_
      exact PrfH_eq_trans
        (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_carc (PrfH_eq_congr_nthc2 hs))
          (PrfH_eq_congr_carc (prf_to_prfH
            (prf_nthc_succ (liftTerm 0 line) (liftTerm 0 rest) (pred (.var 0))) _))))
        heq
  · -- ⇐
    refine prf_deduction ?_
    refine PrfH_or_elim (prfH_hyp_self (lor (Formula.eq (carc line) y) (boundedCarcLt y rest j)))
      ?_ ?_
    · exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedCarcLt_cons_of_head y line rest j) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    · exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedCarcLt_cons_of_tail y line rest j) _)
        (PrfH.hyp _ _ (List.Mem.head _))

end ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

export ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf (
  prf_in_concat_iff prf_in_cons_nil_iff prf_in_concat_singleton_iff
  boundedCarcLt boundedCarcIn_eq_boundedCarcLt liftFormula_boundedCarcLt
  prf_boundedCarcLt_cons_of_tail prf_boundedCarcLt_cons_of_head
  prf_boundedCarcLt_cons_succ_iff
)

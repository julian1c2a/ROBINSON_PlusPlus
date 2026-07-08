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

/-- `liftFormula` atraviesa `boundedCarcLt` (general en el nivel `k`). -/
theorem liftFormula_boundedCarcLt_gen (k : Nat) (y p b : Term) :
    liftFormula k (boundedCarcLt y p b)
      = boundedCarcLt (liftTerm k y) (liftTerm k p) (liftTerm k b) := by
  simp only [boundedCarcLt, liftFormula, liftTerm, liftTerms, land, lt, nthc, carc,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

/-- `substFormula` atraviesa `boundedCarcLt` (vía `substTerm_lift_comm_zero`). -/
theorem substFormula_boundedCarcLt (v : Nat) (s y p b : Term) :
    substFormula v s (boundedCarcLt y p b)
      = boundedCarcLt (substTerm v s y) (substTerm v s p) (substTerm v s b) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [boundedCarcLt, substFormula, substTerm, substTerms, land, lt, nthc, carc, liftTerm,
    liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

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

/-! ### (a) Forma acotada de `allIn`

`allIn c L ⇔ ∀ j < lenc L. In (nthc L j) c`.

Todo el manejo del `∀j` (introducción por **`Prf.qconf`**, eliminación por `PrfH_spec`) se confina
en cuatro lemas `Prf` autónomos sobre `boundedAllIn`; las dos inducciones de lista quedan entonces
triviales — mismo reparto que `prf_boundedIn_head/tail/nil/cons` en la fase 1b. -/

/-- Congruencia de `In` en el **primer** argumento (elemento). -/
theorem PrfH_eq_subst_in1 {Γ : List Formula} {x₁ x₂ L : Term}
    (h : PrfH Γ (x₁ =eq x₂)) (hin : PrfH Γ (In x₁ L)) : PrfH Γ (In x₂ L) := by
  let f : Formula := In (.var 0) (liftTerm 0 L)
  have hS : ∀ s : Term, substFormula 0 s f = In s L := by
    intro s; simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS x₂) ▸ PrfH_leibniz_subst (A := f) h ((hS x₁) ▸ hin)

/-- `∀ j < lenc L. In (nthc L j) c` (el `j` es `#0` bajo el `∀`). -/
def boundedAllIn (c L : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
    (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 c)))

/-- Clausura De Bruijn de `boundedAllIn` (vía `liftTerm_comm_zero`; NO es defeq). -/
theorem liftFormula_boundedAllIn_gen (k : Nat) (c L : Term) :
    liftFormula k (boundedAllIn c L) = boundedAllIn (liftTerm k c) (liftTerm k L) := by
  simp only [boundedAllIn, liftFormula, liftTerm, liftTerms, lt, nthc, lenc, In,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

/-- `substFormula` atraviesa `boundedAllIn` (vía `substTerm_lift_comm_zero`). -/
theorem substFormula_boundedAllIn (v : Nat) (s c L : Term) :
    substFormula v s (boundedAllIn c L) = boundedAllIn (substTerm v s c) (substTerm v s L) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [boundedAllIn, substFormula, substTerm, substTerms, lt, nthc, lenc, In, liftTerm,
    liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

/-- Base: `boundedAllIn c nil` es vacuamente cierto (`¬ j < lenc nil = 0`). -/
theorem prf_boundedAllIn_nil (c : Term) : Prf (boundedAllIn c nil) := by
  refine Prf.gen _ ?_
  simp only [boundedAllIn, lt, lenc, nthc, In, nil, zero, liftTerm, liftTerms]
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
      (PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) (prfH_hyp_self _)))

/-- Proyección cabeza: instancia el `∀j` en `j = 0` (`0 < σ(lenc t)`, `nthc (cons hd t) 0 = hd`). -/
theorem prf_boundedAllIn_cons_head (c hd t : Term) :
    Prf (boundedAllIn c (cons hd t) ⇒ In hd c) := by
  refine prf_deduction ?_
  have hA : PrfH [boundedAllIn c (cons hd t)] (boundedAllIn c (cons hd t)) := prfH_hyp_self _
  have h0 := PrfH_spec hA zero
  simp only [boundedAllIn, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] at h0
  have hb : PrfH [boundedAllIn c (cons hd t)] (lt zero (lenc (cons hd t))) :=
    prf_to_prfH (prf_lt_subst2 (prf_eq_symm (prf_lenc_cons hd t)) (prf_zero_lt_succ (lenc t))) _
  exact PrfH_eq_subst_in1 (prf_to_prfH (prf_nthc_zero hd t) _) (PrfH.mp _ _ _ h0 hb)

/-- Proyección cola: reindexa `j ↦ σj` (usa `Prf.qconf` para el `∀` del consecuente). -/
theorem prf_boundedAllIn_cons_tail (c hd t : Term) :
    Prf (boundedAllIn c (cons hd t) ⇒ boundedAllIn c t) := by
  have hq := Prf.qconf (boundedAllIn c (cons hd t))
    (Formula.impl (lt (.var 0) (liftTerm 0 (lenc t)))
      (In (nthc (liftTerm 0 t) (.var 0)) (liftTerm 0 c)))
  refine prf_mp hq (Prf.gen _ ?_)
  rw [liftFormula_boundedAllIn_gen]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc t))) _ rfl)
  let Ac : Formula := boundedAllIn (liftTerm 0 c) (liftTerm 0 (cons hd t))
  let B : Formula := lt (.var 0) (liftTerm 0 (lenc t))
  have hA : PrfH [B, Ac] Ac := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hB : PrfH [B, Ac] B := PrfH.hyp _ _ (List.Mem.head _)
  have hs := PrfH_spec hA (succ (.var 0))
  simp only [Ac, boundedAllIn, substFormula, substTerm, substTerms, lt, lenc, nthc, In, succ,
    Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] at hs
  have hlt : PrfH [B, Ac] (lt (succ (.var 0)) (lenc (liftTerm 0 (cons hd t)))) :=
    PrfH_lt_subst2 (prf_to_prfH (prf_eq_symm (prf_lenc_cons (liftTerm 0 hd) (liftTerm 0 t))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_lt_succ_of_lt (.var 0) (lenc (liftTerm 0 t))) _) hB)
  exact PrfH_eq_subst_in1
    (prf_to_prfH (prf_nthc_succ (liftTerm 0 hd) (liftTerm 0 t) (.var 0)) _)
    (PrfH.mp _ _ _ hs hlt)

/-- Reintroducción: `In hd c ∧ boundedAllIn c t ⇒ boundedAllIn c (cons hd t)`.
    `Prf.qconf` para el `∀j` del consecuente; case-split de `j` con `prf_zero_or_eq_succ_pred`. -/
theorem prf_boundedAllIn_cons (c hd t : Term) :
    Prf (land (In hd c) (boundedAllIn c t) ⇒ boundedAllIn c (cons hd t)) := by
  have hq := Prf.qconf (land (In hd c) (boundedAllIn c t))
    (Formula.impl (lt (.var 0) (liftTerm 0 (lenc (cons hd t))))
      (In (nthc (liftTerm 0 (cons hd t)) (.var 0)) (liftTerm 0 c)))
  refine prf_mp hq (Prf.gen _ ?_)
  have hland : liftFormula 0 (land (In hd c) (boundedAllIn c t))
      = land (In (liftTerm 0 hd) (liftTerm 0 c)) (liftFormula 0 (boundedAllIn c t)) := rfl
  rw [hland, liftFormula_boundedAllIn_gen]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc (cons hd t)))) _ rfl)
  let P : Formula :=
    land (In (liftTerm 0 hd) (liftTerm 0 c)) (boundedAllIn (liftTerm 0 c) (liftTerm 0 t))
  let B : Formula := lt (.var 0) (liftTerm 0 (lenc (cons hd t)))
  let Z : Formula := Formula.eq (.var 0) zero
  let S : Formula := Formula.eq (.var 0) (succ (pred (.var 0)))
  show PrfH [B, P] (In (nthc (liftTerm 0 (cons hd t)) (.var 0)) (liftTerm 0 c))
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?_ ?_
  · -- j = 0 : la cabeza
    have hz : PrfH [Z, B, P] Z := PrfH.hyp _ _ (List.Mem.head _)
    have hIn : PrfH [Z, B, P] (In (liftTerm 0 hd) (liftTerm 0 c)) :=
      PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    exact PrfH_eq_subst_in1
      (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_nthc2 hz)
        (prf_to_prfH (prf_nthc_zero (liftTerm 0 hd) (liftTerm 0 t)) _))) hIn
  · -- j = σ(pred j) : la cola, vía la hipótesis acotada instanciada en `pred j`
    have hs : PrfH [S, B, P] S := PrfH.hyp _ _ (List.Mem.head _)
    have hB : PrfH [S, B, P] B := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hP : PrfH [S, B, P] P :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hbAI : PrfH [S, B, P] (boundedAllIn (liftTerm 0 c) (liftTerm 0 t)) :=
      PrfH_and_elim_right hP
    have hltJ : PrfH [S, B, P] (lt (pred (.var 0)) (lenc (liftTerm 0 t))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (liftTerm 0 t))) _)
        (PrfH_lt_subst2 (prf_to_prfH (prf_lenc_cons (liftTerm 0 hd) (liftTerm 0 t)) _)
          (PrfH_lt_subst1 hs hB))
    have hspec := PrfH_spec hbAI (pred (.var 0))
    simp only [boundedAllIn, substFormula, substTerm, substTerms, lt, lenc, nthc, In, pred,
      Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] at hspec
    exact PrfH_eq_subst_in1
      (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_nthc2 hs)
        (prf_to_prfH (prf_nthc_succ (liftTerm 0 hd) (liftTerm 0 t) (pred (.var 0))) _)))
      (PrfH.mp _ _ _ hspec hltJ)

/-- `liftFormula`/`substFormula` atraviesan `allIn` (definicional: es un átomo). -/
theorem liftFormula_allIn (k : Nat) (c L : Term) :
    liftFormula k (allIn c L) = allIn (liftTerm k c) (liftTerm k L) := rfl

theorem substFormula_allIn (v : Nat) (s c L : Term) :
    substFormula v s (allIn c L) = allIn (substTerm v s c) (substTerm v s L) := rfl

/-- Dirección ⇒ : `allIn c L ⇒ ∀ j < lenc L. In (nthc L j) c` (inducción de listas sobre `L`). -/
theorem prf_boundedAllIn_of_allIn (c L : Term) : Prf (allIn c L ⇒ boundedAllIn c L) := by
  have key : Prf (Formula.forall (Formula.impl (allIn (liftTerm 0 c) (.var 0))
      (boundedAllIn (liftTerm 0 c) (.var 0)))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (allIn c nil) (boundedAllIn c nil)) :=
        prf_deduction (prf_to_prfH (prf_boundedAllIn_nil c) _)
      simpa only [substFormula, substFormula_allIn, substFormula_boundedAllIn, substTerm,
        substTerms, nil, zero, reduceIte, if_true, FOL.substTerm_liftTerm] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftFormula_allIn, liftFormula_boundedAllIn_gen, substFormula,
        substFormula_allIn, substFormula_boundedAllIn, liftTerm, liftTerms, substTerm, substTerms,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, norm21]
      let C : Term := liftTerm 1 (liftTerm 0 c)
      refine prf_deduction (deduction_aux ?_ (allIn C (cons (.var 1) (.var 0))) _ rfl)
      let A : Formula := allIn C (cons (.var 1) (.var 0))
      let IH : Formula := Formula.impl (allIn C (.var 0)) (boundedAllIn C (.var 0))
      have hsplit : PrfH [A, IH] (land (In (.var 1) C) (allIn C (.var 0))) :=
        PrfH_iff_mp (prf_allIn_cons C (.var 1) (.var 0)) (PrfH.hyp _ _ (List.Mem.head _))
      have hTail : PrfH [A, IH] (boundedAllIn C (.var 0)) :=
        PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
          (PrfH_and_elim_right hsplit)
      exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedAllIn_cons C (.var 1) (.var 0)) _)
        (PrfH_and_intro (PrfH_and_elim_left hsplit) hTail)
  have hkey := prf_spec key L
  simpa only [substFormula, substFormula_allIn, substFormula_boundedAllIn, substTerm, substTerms,
    reduceIte, if_true, FOL.substTerm_liftTerm] using hkey

/-- Dirección ⇐ : `(∀ j < lenc L. In (nthc L j) c) ⇒ allIn c L` (inducción de listas sobre `L`). -/
theorem prf_allIn_of_boundedAllIn (c L : Term) : Prf (boundedAllIn c L ⇒ allIn c L) := by
  have key : Prf (Formula.forall (Formula.impl (boundedAllIn (liftTerm 0 c) (.var 0))
      (allIn (liftTerm 0 c) (.var 0)))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (boundedAllIn c nil) (allIn c nil)) :=
        prf_deduction (prf_to_prfH (prf_allIn_nil c) _)
      simpa only [substFormula, substFormula_allIn, substFormula_boundedAllIn, substTerm,
        substTerms, nil, zero, reduceIte, if_true, FOL.substTerm_liftTerm] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftFormula_allIn, liftFormula_boundedAllIn_gen, substFormula,
        substFormula_allIn, substFormula_boundedAllIn, liftTerm, liftTerms, substTerm, substTerms,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, norm21]
      let C : Term := liftTerm 1 (liftTerm 0 c)
      refine prf_deduction (deduction_aux ?_ (boundedAllIn C (cons (.var 1) (.var 0))) _ rfl)
      let A : Formula := boundedAllIn C (cons (.var 1) (.var 0))
      let IH : Formula := Formula.impl (boundedAllIn C (.var 0)) (allIn C (.var 0))
      have hA : PrfH [A, IH] A := PrfH.hyp _ _ (List.Mem.head _)
      have hHead : PrfH [A, IH] (In (.var 1) C) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_boundedAllIn_cons_head C (.var 1) (.var 0)) _) hA
      have hTail : PrfH [A, IH] (allIn C (.var 0)) :=
        PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_boundedAllIn_cons_tail C (.var 1) (.var 0)) _) hA)
      exact PrfH_iff_mpr (prf_allIn_cons C (.var 1) (.var 0)) (PrfH_and_intro hHead hTail)
  have hkey := prf_spec key L
  simpa only [substFormula, substFormula_allIn, substFormula_boundedAllIn, substTerm, substTerms,
    reduceIte, if_true, FOL.substTerm_liftTerm] using hkey

/-- **(a)** `allIn c L ⇔ ∀ j < lenc L. In (nthc L j) c` — la forma acotada de `allIn`,
    con la que `lineOk` se vuelve Δ₀ sobre índices. -/
theorem prf_allIn_iff_boundedAllIn (c L : Term) : Prf (allIn c L ⇔ boundedAllIn c L) :=
  prf_and_intro (prf_boundedAllIn_of_allIn c L) (prf_allIn_of_boundedAllIn c L)

/-! ### (d) La forma acotada de `chainOk` — escalón 1: piezas puntuales y definiciones

Objetivo final: `chainOk c p ⇔ chainOkB c p`, donde el **acumulador desaparece**: una premisa de
la línea `i` está o bien en el contexto inicial `c`, o bien es la conclusión (`carc`) de alguna
línea **anterior** (`∃ k < i`). Es la formulación Δ₀ clásica de «demostración».

Este escalón entrega las piezas que **no** necesitan inducción: el `∃k<0` vacío, y el **lema
puntual** que fusiona (b) y (c) — el corazón aritmético del paso `cons`. -/

/-- `∃ k < 0. …` es falso. -/
theorem prf_boundedCarcLt_zero (y p : Term) :
    Prf (boundedCarcLt y p zero ⇒ Formula.bottom) := by
  refine prf_ex_elim_imp ?_
  show PrfH [land (lt (.var 0) (liftTerm 0 zero))
      (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))] Formula.bottom
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
    (PrfH_and_elim_left (prfH_hyp_self _))

/-- **Lema puntual (b)+(c)** — el corazón del paso `cons` de (d).

`y` es una premisa admisible para la línea `σi` de `line :: rest` con contexto `c`
**syss** lo es para la línea `i` de `rest` con el contexto ampliado `c ++ [carc line]`:

`In y c ∨ (∃k<σi. carc (nthc (line::rest) k) =eq y)
   ⇔  In y (c ++ [carc line]) ∨ (∃k<i. carc (nthc rest k) =eq y)`

⇒ usa (c) para partir el `∃k<σi` y (b) para absorber `carc line` en el contexto;
⇐ usa (b) para extraer `carc line` y las reintroducciones de (c). -/
theorem prf_premOk_cons_iff (y c line rest i : Term) :
    Prf (lor (In y c) (boundedCarcLt y (cons line rest) (succ i))
      ⇔ lor (In y (concat c (cons (carc line) nil))) (boundedCarcLt y rest i)) := by
  let cx : Term := concat c (cons (carc line) nil)
  refine prf_and_intro ?_ ?_
  · -- ⇒
    refine prf_deduction ?_
    refine PrfH_or_elim (prfH_hyp_self
      (lor (In y c) (boundedCarcLt y (cons line rest) (succ i)))) ?_ ?_
    · -- In y c : va al contexto ampliado
      refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) ?_
      refine PrfH_iff_mpr (prf_in_concat_singleton_iff y c (carc line)) ?_
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (PrfH.hyp _ _ (List.Mem.head _))
    · -- ∃k<σi : se parte por (c)
      let Hb : Formula := boundedCarcLt y (cons line rest) (succ i)
      let H : Formula := lor (In y c) Hb
      have hsplit : PrfH [Hb, H] (lor (Formula.eq (carc line) y) (boundedCarcLt y rest i)) :=
        PrfH_iff_mp (prf_boundedCarcLt_cons_succ_iff y line rest i)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · -- carc line =eq y : entra en el contexto ampliado (por (b))
        refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) ?_
        refine PrfH_iff_mpr (prf_in_concat_singleton_iff y c (carc line)) ?_
        exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
          (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
      · -- ∃k<i sobre rest
        exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) (PrfH.hyp _ _ (List.Mem.head _))
  · -- ⇐
    refine prf_deduction ?_
    refine PrfH_or_elim (prfH_hyp_self (lor (In y cx) (boundedCarcLt y rest i))) ?_ ?_
    · -- In y (c ++ [carc line]) : se abre por (b)
      let Hi : Formula := In y cx
      let H : Formula := lor Hi (boundedCarcLt y rest i)
      have hsplit : PrfH [Hi, H] (lor (In y c) (Formula.eq y (carc line))) :=
        PrfH_iff_mp (prf_in_concat_singleton_iff y c (carc line))
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (PrfH.hyp _ _ (List.Mem.head _))
      · refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
        exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedCarcLt_cons_of_head y line rest i) _)
          (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
    · -- ∃k<i sobre rest : se reindexa k ↦ σk
      refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
      exact PrfH.mp _ _ _ (prf_to_prfH (prf_boundedCarcLt_cons_of_tail y line rest i) _)
        (PrfH.hyp _ _ (List.Mem.head _))

/-! #### Definiciones de la capa acotada -/

/-- `∀ j < lenc L. (In (nthc L j) c ∨ ∃ k < i. carc (nthc p k) =eq nthc L j)`:
    todas las premisas de la lista `L` son admisibles para la línea `i` de `p` bajo `c`. -/
def boundedPremsIn (c p i L : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
    (lor (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 c))
         (boundedCarcLt (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 p) (liftTerm 0 i))))

/-- La línea `i`-ésima de `p` es válida bajo `c` **sin acumulador**. -/
def lineOkB (c p i : Term) : Formula :=
  land (lineWF (nthc p i)) (boundedPremsIn c p i (premsOf (nthc p i)))

/-- **`chainOkB c p`** := `∀ i < lenc p. lineOkB c p i`. Forma Δ₀ de `chainOk c p`. -/
def chainOkB (c p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc p)))
    (lineOkB (liftTerm 0 c) (liftTerm 0 p) (.var 0)))

/-! #### Clausuras De Bruijn de la capa acotada -/

theorem liftFormula_boundedPremsIn (k : Nat) (c p i L : Term) :
    liftFormula k (boundedPremsIn c p i L)
      = boundedPremsIn (liftTerm k c) (liftTerm k p) (liftTerm k i) (liftTerm k L) := by
  simp only [boundedPremsIn, liftFormula, liftFormula_boundedCarcLt_gen, liftTerm, liftTerms,
    lt, lenc, nthc, In, lor, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substFormula_boundedPremsIn (v : Nat) (s c p i L : Term) :
    substFormula v s (boundedPremsIn c p i L)
      = boundedPremsIn (substTerm v s c) (substTerm v s p) (substTerm v s i) (substTerm v s L) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [boundedPremsIn, substFormula, substFormula_boundedCarcLt, substTerm, substTerms,
    lt, lenc, nthc, In, lor, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem liftFormula_lineOkB (k : Nat) (c p i : Term) :
    liftFormula k (lineOkB c p i) = lineOkB (liftTerm k c) (liftTerm k p) (liftTerm k i) := by
  simp only [lineOkB, land, liftFormula, liftFormula_boundedPremsIn, liftTerm, liftTerms,
    lineWF, nthc, premsOf]

theorem substFormula_lineOkB (v : Nat) (s c p i : Term) :
    substFormula v s (lineOkB c p i)
      = lineOkB (substTerm v s c) (substTerm v s p) (substTerm v s i) := by
  simp only [lineOkB, land, substFormula, substFormula_boundedPremsIn, substTerm, substTerms,
    lineWF, nthc, premsOf]

theorem liftFormula_chainOkB (k : Nat) (c p : Term) :
    liftFormula k (chainOkB c p) = chainOkB (liftTerm k c) (liftTerm k p) := by
  simp only [chainOkB, liftFormula, liftFormula_lineOkB, liftTerm, liftTerms, lt, lenc,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substFormula_chainOkB (v : Nat) (s c p : Term) :
    substFormula v s (chainOkB c p) = chainOkB (substTerm v s c) (substTerm v s p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [chainOkB, substFormula, substFormula_lineOkB, substTerm, substTerms, lt, lenc,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

/-- Base: `chainOkB c nil` es vacuamente cierto (`¬ i < lenc nil = 0`). -/
theorem prf_chainOkB_nil (c : Term) : Prf (chainOkB c nil) := by
  refine Prf.gen _ ?_
  simp only [chainOkB, lt, lenc, nil, zero, liftTerm, liftTerms]
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
      (PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) (prfH_hyp_self _)))

end ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

export ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf (
  prf_in_concat_iff prf_in_cons_nil_iff prf_in_concat_singleton_iff
  boundedCarcLt boundedCarcIn_eq_boundedCarcLt liftFormula_boundedCarcLt
  liftFormula_boundedCarcLt_gen substFormula_boundedCarcLt
  prf_boundedCarcLt_cons_of_tail prf_boundedCarcLt_cons_of_head
  prf_boundedCarcLt_cons_succ_iff prf_boundedCarcLt_zero
  PrfH_eq_subst_in1 boundedAllIn liftFormula_boundedAllIn_gen substFormula_boundedAllIn
  prf_boundedAllIn_nil prf_boundedAllIn_cons_head prf_boundedAllIn_cons_tail
  prf_boundedAllIn_cons prf_boundedAllIn_of_allIn prf_allIn_of_boundedAllIn
  prf_allIn_iff_boundedAllIn
  prf_premOk_cons_iff boundedPremsIn lineOkB chainOkB
  liftFormula_boundedPremsIn substFormula_boundedPremsIn
  liftFormula_lineOkB substFormula_lineOkB
  liftFormula_chainOkB substFormula_chainOkB prf_chainOkB_nil
)

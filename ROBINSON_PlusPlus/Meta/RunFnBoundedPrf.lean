/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.BoundedInPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

/-!
## META — NIVEL D real (§12‑A FASE 2, SONDEO): ¿es `runFn` Δ₀‑izable sin β‑función?

**Pregunta del sondeo.** El diseño (§12.3) temía que `runFn`, al ser **recursión con
acumulador**, exigiera codificación de secuencias (β‑función) para expresarse con
cuantificadores acotados.

**Hipótesis a contrastar.** `runFn nil p` no es más que el *map* de `carc` sobre `p`:

* `runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest)`  ← **lema decisivo**
* de ahí `lenc (runFn nil p) =eq lenc p` y `nthc (runFn nil p) i =eq carc (nthc p i)`

Si es así, **el acumulador nunca hay que construirlo**: `In x (runFn nil p)` se reduce a
`∃ i < lenc p. carc (nthc p i) =eq x` (acotado sobre `p` directamente), y en `chainOk` el
acumulador se sustituye por «∃ k < i» (la conclusión de una línea anterior). **Sin β‑función.**
-/

/-- Congruencia de `lenc` (Leibniz object). -/
theorem prf_eq_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s; simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (lenc t₁))

/-- Congruencia de `lenc` en `PrfH`. -/
theorem PrfH_eq_congr_lenc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s; simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) Γ)

/-! ### El lema decisivo: `runFn nil` es un `map carc` estructural -/

/-- **`runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest)`**.
    Cadena: `prf_runFn_cons` (acumulador `nil ++ [carc line]`) → `prf_concat_nil_eq`
    → `prf_runFn_weaken` (saca el acumulador fuera) → `prf_concat_cons_eq` + `prf_concat_nil_eq`.
    **Consecuencia:** el acumulador de `runFn` NO necesita codificarse; `runFn nil` es un map. -/
theorem prf_runFn_nil_cons (line rest : Term) :
    Prf (runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest)) := by
  have h1 : Prf (runFn nil (cons line rest)
      =eq runFn (concat nil (cons (carc line) nil)) rest) := prf_runFn_cons nil line rest
  have h2 : Prf (runFn (concat nil (cons (carc line) nil)) rest
      =eq runFn (cons (carc line) nil) rest) :=
    prf_congr_runFn_1 (prf_concat_nil_eq (cons (carc line) nil))
  have h3 : Prf (runFn (cons (carc line) nil) rest
      =eq concat (cons (carc line) nil) (runFn nil rest)) :=
    prf_runFn_weaken (cons (carc line) nil) rest
  have h4 : Prf (concat (cons (carc line) nil) (runFn nil rest)
      =eq cons (carc line) (runFn nil rest)) :=
    prf_eq_trans (prf_concat_cons_eq (carc line) nil (runFn nil rest))
      (prf_congr_cons_tail (prf_concat_nil_eq (runFn nil rest)))
  exact prf_eq_trans h1 (prf_eq_trans h2 (prf_eq_trans h3 h4))

/-- **`lenc (runFn nil p) =eq lenc p`** (el map preserva la longitud). Inducción de listas. -/
theorem prf_lenc_runFn (p : Term) : Prf (lenc (runFn nil p) =eq lenc p) := by
  have key : Prf (Formula.forall (Formula.eq (lenc (runFn nil (.var 0))) (lenc (.var 0)))) := by
    refine prf_list_induction _ ?base ?step
    · show Prf (lenc (runFn nil nil) =eq lenc nil)
      exact prf_eq_congr_lenc (prf_runFn_nil nil)
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        lenc, runFn, cons, nil, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction ?_
      -- IH : lenc (runFn nil #0) =eq lenc #0
      -- meta: lenc (runFn nil (cons #1 #0)) =eq lenc (cons #1 #0)
      refine PrfH_eq_trans
        (PrfH_eq_congr_lenc (prf_to_prfH (prf_runFn_nil_cons (.var 1) (.var 0)) _)) ?_
      -- lenc (cons (carc #1) (runFn nil #0)) =eq σ (lenc (runFn nil #0)) =eq σ (lenc #0) =eq lenc (cons #1 #0)
      refine PrfH_eq_trans (prf_to_prfH (prf_lenc_cons (carc (.var 1)) (runFn nil (.var 0))) _) ?_
      exact PrfH_eq_trans (PrfH_eq_congr_succ (prfH_hyp_self _))
        (prf_to_prfH (prf_eq_symm (prf_lenc_cons (.var 1) (.var 0))) _)
  have hp := prf_spec key p
  simpa only [substFormula, substTerm, substTerms, lenc, runFn, nil, zero,
    Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm] using hp

/-! ### Congruencias de `carc` y `nthc` (1er arg) -/

/-- Congruencia de `carc` en `PrfH`. -/
theorem PrfH_eq_congr_carc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (carc t₁ =eq carc t₂) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 t₁)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc t₁) (carc s) := by
    intro s; simp only [f, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (carc t₁)) Γ)

/-- Congruencia de `nthc` en la lista (1er argumento), en `PrfH`. -/
theorem PrfH_eq_congr_nthc1 {Γ : List Formula} {L₁ L₂ i : Term} (h : PrfH Γ (L₁ =eq L₂)) :
    PrfH Γ (nthc L₁ i =eq nthc L₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 L₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc L₁ i) (nthc s i) := by
    intro s; simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS L₂) ▸ PrfH_leibniz_subst (A := f) h ((hS L₁) ▸ prf_to_prfH (prf_refl (nthc L₁ i)) Γ)

/-! ### `nthc (runFn nil p) i = carc (nthc p i)` — inducción con `∀i` INTERNO

El predicado inductivo cuantifica `i` **dentro** (la HI se usa en `pred i`, no en `i`), así que
el `step` anida tres binders (`#2`=cabeza, `#1`=cola del esquema de listas + `#0`=`i` interno) y
se cierra con **confinación `qconf`** + `PrfH_spec` — mismo patrón que `prf_runFn_concat`
(`ChainPrf.lean`). Aquí NO hay parámetro externo, así que no hace falta `norm32`. -/

/-- Predicado inductivo: `Ψ(p) = ∀i. (i < lenc p ⇒ nthc (runFn nil p) i = carc (nthc p i))`
    (lista `p` = `#1` bajo el `∀i`; `i` = `#0`). -/
def nthRunPred : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 1)))
    (Formula.eq (nthc (runFn nil (.var 1)) (.var 0)) (carc (nthc (.var 1) (.var 0)))))

/-- Caso base del predicado: `p = nil` (por explosión, `i < lenc nil = 0`). -/
theorem nthRunPred_base : Prf (substFormula 0 nil nthRunPred) := by
  refine Prf.gen _ ?_
  simp only [nthRunPred, substFormula, substTerm, substTerms, lt, lenc, nthc, runFn, carc,
    nil, zero, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
      (PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) (prfH_hyp_self _)))

/-- Paso `cons` del predicado. Confinación `qconf` (la HI es `∀i`, sin `i` libre) + `PrfH_spec`
    para instanciar la HI en `pred i`; case-split de `i` con `prf_zero_or_eq_succ_pred`. -/
theorem nthRunPred_step :
    Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 nthRunPred)
      (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nthRunPred)))))) := by
  refine Prf.gen _ (Prf.gen _ ?_)
  simp only [nthRunPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
    lt, lenc, nthc, runFn, carc, cons, nil, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (lenc (cons (.var 2) (.var 1)))) _ rfl)
  -- ctx: [ A0 , P0 ] ; #0=i, #1=cola, #2=cabeza
  let P0 : Formula := Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 2)))
    (Formula.eq (nthc (runFn nil (.var 2)) (.var 0)) (carc (nthc (.var 2) (.var 0)))))
  let A0 : Formula := lt (.var 0) (lenc (cons (.var 2) (.var 1)))
  let Z0 : Formula := Formula.eq (.var 0) zero
  let S0 : Formula := Formula.eq (.var 0) (succ (pred (.var 0)))
  have hRun := prf_runFn_nil_cons (.var 2) (.var 1)
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?_ ?_
  · -- i = 0
    have hz : PrfH [Z0, A0, P0] Z0 := PrfH.hyp _ _ (List.Mem.head _)
    refine PrfH_eq_trans
      (PrfH_eq_trans (PrfH_eq_congr_nthc1 (prf_to_prfH hRun _))
        (PrfH_eq_trans (PrfH_eq_congr_nthc2 hz)
          (prf_to_prfH (prf_nthc_zero (carc (.var 2)) (runFn nil (.var 1))) _)))
      (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_carc (PrfH_eq_congr_nthc2 hz))
        (PrfH_eq_congr_carc (prf_to_prfH (prf_nthc_zero (.var 2) (.var 1)) _))))
  · -- i = σ(pred i) : testigo pred i, se usa la HI en pred i
    have hs : PrfH [S0, A0, P0] S0 := PrfH.hyp _ _ (List.Mem.head _)
    have hlt : PrfH [S0, A0, P0] A0 := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hP : PrfH [S0, A0, P0] P0 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have ihj := PrfH_spec hP (pred (.var 0))
    simp only [P0, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
      lt, lenc, nthc, runFn, carc, pred, cons, nil, zero, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at ihj
    -- cota: i < lenc (cons h t) = σ(lenc t) e i = σ(pred i) ⇒ pred i < lenc t
    have hltJ : PrfH [S0, A0, P0] (lt (pred (.var 0)) (lenc (.var 1))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (.var 1))) _)
        (PrfH_lt_subst2 (prf_to_prfH (prf_lenc_cons (.var 2) (.var 1)) _)
          (PrfH_lt_subst1 hs hlt))
    have hEq := PrfH.mp _ _ _ ihj hltJ
    refine PrfH_eq_trans
      (PrfH_eq_trans (PrfH_eq_congr_nthc1 (prf_to_prfH hRun _))
        (PrfH_eq_trans (PrfH_eq_congr_nthc2 hs)
          (PrfH_eq_trans
            (prf_to_prfH (prf_nthc_succ (carc (.var 2)) (runFn nil (.var 1)) (pred (.var 0))) _)
            hEq)))
      (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_carc (PrfH_eq_congr_nthc2 hs))
        (PrfH_eq_congr_carc (prf_to_prfH (prf_nthc_succ (.var 2) (.var 1) (pred (.var 0))) _))))

/-- **`i < lenc p ⇒ nthc (runFn nil p) i =eq carc (nthc p i)`** — el índice del map. -/
theorem prf_nthc_runFn (p i : Term) :
    Prf (lt i (lenc p) ⇒ (nthc (runFn nil p) i =eq carc (nthc p i))) := by
  have key : Prf (Formula.forall nthRunPred) :=
    prf_list_induction nthRunPred nthRunPred_base nthRunPred_step
  have hp := prf_spec key p
  have hi := prf_spec hp i
  simpa only [nthRunPred, substFormula, substTerm, substTerms, lt, lenc, nthc, runFn, carc,
    nil, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub,
    reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hi

end ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

export ROBINSON_PlusPlus.Meta.RunFnBoundedPrf (
  prf_eq_congr_lenc PrfH_eq_congr_lenc prf_runFn_nil_cons prf_lenc_runFn
  PrfH_eq_congr_carc PrfH_eq_congr_nthc1 nthRunPred nthRunPred_base nthRunPred_step
  prf_nthc_runFn
)

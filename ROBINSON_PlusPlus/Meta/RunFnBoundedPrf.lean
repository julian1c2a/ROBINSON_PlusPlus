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

end ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

export ROBINSON_PlusPlus.Meta.RunFnBoundedPrf (
  prf_eq_congr_lenc PrfH_eq_congr_lenc prf_runFn_nil_cons prf_lenc_runFn
)

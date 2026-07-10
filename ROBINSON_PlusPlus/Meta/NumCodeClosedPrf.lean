/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.NatArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

/-!
## META — NIVEL D real (§23): **el código de un numeral es CERRADO** (`tcFn a`)

Ladrillo **(A)** de §22.4. `tcFn` es la función object «numeral‑de»: `tcFn a` es el **código** del
numeral `σ^a 0`. Ese código no contiene variables del lenguaje **codificado**, luego `liftc` y
`substtc` deben dejarlo invariante:

```lean
prf_liftc_tcFn   (a)   : Prf (liftc zero (tcFn a) =eq tcFn a)
prf_substtc_tcFn (W a) : Prf (substtc zero W (tcFn a) =eq tcFn a)
```

**No hay axioma** que lo diga (`tcFn` sólo tiene `ax_tc_zero`/`ax_tc_succ`/`ax_tc_cons`), pero **sí es
derivable por inducción interna** (`prf_nat_induction`):

* **base** `tcFn 0 = ⌜0⌝` (`prf_tc_zero`) — un código **concreto** y cerrado;
* **paso** `tcFn (σx) = succc (tcFn x)` (`prf_tc_succ`) — el `liftc`/`substtc` atraviesa el `funcc`
  (`prf_liftc_func`/`prf_substtc_func`) y baja a la HI.

Es el hecho estándar «`num a` es un término cerrado del lenguaje codificado». Lo necesita el paso
inductivo de la evaluación provable de `+`, donde `prf_substfc_forall` deja `liftc zero (tcFn a)`.
-/

/-! ### Congruencias (Leibniz object) -/

/-- Congruencia de `liftc` en el código. -/
theorem prf_congr_liftc {c a b : Term} (h : Prf (a =eq b)) :
    Prf (liftc c a =eq liftc c b) := by
  let f : Formula := Formula.eq (liftc (liftTerm 0 c) (liftTerm 0 a)) (liftc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftc c a) (liftc c s) := by
    intro s
    simp only [f, liftc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (liftc c a))

/-- Congruencia de `liftc` en el código, en `PrfH`. -/
theorem PrfH_congr_liftc {Γ : List Formula} {c a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (liftc c a =eq liftc c b) := by
  let f : Formula := Formula.eq (liftc (liftTerm 0 c) (liftTerm 0 a)) (liftc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftc c a) (liftc c s) := by
    intro s
    simp only [f, liftc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (liftc c a)) Γ)

/-- Congruencia de `substtc` en el código (3er argumento), en `PrfH`. -/
theorem PrfH_congr_substtc3 {Γ : List Formula} {v s a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (substtc v s a =eq substtc v s b) := by
  let f : Formula := Formula.eq (substtc (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 a))
                                (substtc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
  have hS : ∀ u : Term, substFormula 0 u f = Formula.eq (substtc v s a) (substtc v s u) := by
    intro u
    simp only [f, substtc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (substtc v s a)) Γ)

/-- Congruencia de `substtc` en el código (3er argumento). -/
theorem prf_congr_substtc3 {v s a b : Term} (h : Prf (a =eq b)) :
    Prf (substtc v s a =eq substtc v s b) :=
  prfH_nil_to_prf (PrfH_congr_substtc3 (Γ := []) (prf_to_prfH h [])) rfl

/-- Congruencia de `funcc` en la lista de argumentos. -/
theorem prf_congr_funcc2 {sc a b : Term} (h : Prf (a =eq b)) :
    Prf (funcc sc a =eq funcc sc b) := by
  unfold funcc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head h))

/-- Congruencia de `funcc` en la lista de argumentos, en `PrfH`. -/
theorem PrfH_congr_funcc2 {Γ : List Formula} {sc a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (funcc sc a =eq funcc sc b) := by
  unfold funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head h))

/-! ### `liftc` deja invariante el código de un numeral -/

/-- Base: `liftc zero (tcFn 0) =eq tcFn 0` (el código de `0` es concreto y cerrado). -/
theorem prf_liftc_tcFn_zero : Prf (liftc zero (tcFn zero) =eq tcFn zero) :=
  prf_eq_trans (prf_congr_liftc prf_tc_zero)
    (prf_eq_trans (prf_liftc_func zero (strCode zero_sym) nil)
      (prf_eq_trans (prf_congr_funcc2 (prf_liftsc_nil zero)) (prf_eq_symm prf_tc_zero)))

/-- Paso: `liftc` atraviesa `tcFn (σx) = succc (tcFn x)` y baja a la HI. -/
theorem prf_liftc_tcFn_succ_imp (x : Term) :
    Prf ((liftc zero (tcFn x) =eq tcFn x) ⇒ (liftc zero (tcFn (succ x)) =eq tcFn (succ x))) := by
  refine prf_deduction ?_
  have ih : PrfH [liftc zero (tcFn x) =eq tcFn x] (liftc zero (tcFn x) =eq tcFn x) :=
    prfH_hyp_self _
  have hsucc : Prf (tcFn (succ x) =eq funcc (strCode succ_sym) (cons (tcFn x) nil)) :=
    prf_tc_succ x
  refine PrfH_eq_trans (PrfH_congr_liftc (prf_to_prfH hsucc _)) ?_
  refine PrfH_eq_trans (prf_to_prfH (prf_liftc_func zero (strCode succ_sym) (cons (tcFn x) nil)) _) ?_
  refine PrfH_eq_trans (PrfH_congr_funcc2 ?_) (prf_to_prfH (prf_eq_symm hsucc) _)
  refine PrfH_eq_trans (prf_to_prfH (prf_liftsc_cons zero (tcFn x) nil) _) ?_
  exact PrfH_eq_trans (PrfH_congr_cons_head ih)
    (PrfH_congr_cons_tail (prf_to_prfH (prf_liftsc_nil zero) _))

/-- Predicado inductivo: `liftc zero (tcFn #0) =eq tcFn #0`. -/
def liftcTcPred : Formula := Formula.eq (liftc zero (tcFn (.var 0))) (tcFn (.var 0))

/-- **`liftc` deja invariante el código de un numeral** (∀ object, por inducción interna). -/
theorem prf_liftc_tcFn_all : Prf (Formula.forall liftcTcPred) := by
  refine prf_nat_induction liftcTcPred ?base ?step
  · simpa only [liftcTcPred, substFormula, substTerm, substTerms, liftc, tcFn, zero,
      reduceIte, if_true] using prf_liftc_tcFn_zero
  · refine Prf.gen _ ?_
    simpa only [liftcTcPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
      liftc, tcFn, zero, succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
      reduceIte, if_true] using prf_liftc_tcFn_succ_imp (.var 0)

/-- **`liftc zero (tcFn a) =eq tcFn a`** para todo término `a` (instancia del ∀). -/
theorem prf_liftc_tcFn (a : Term) : Prf (liftc zero (tcFn a) =eq tcFn a) := by
  have h := prf_spec prf_liftc_tcFn_all a
  simpa only [liftcTcPred, substFormula, substTerm, substTerms, liftc, tcFn, zero,
    reduceIte, if_true] using h

/-! ### `substtc` deja invariante el código de un numeral -/

/-- Base: `substtc zero W (tcFn 0) =eq tcFn 0`. Usa `prf_substtc_arith_open` (§20) sobre el código
    **concreto** `⌜0⌝ = termCode zero`, con testigo `W` arbitrario. -/
theorem prf_substtc_tcFn_zero (W : Term) : Prf (substtc zero W (tcFn zero) =eq tcFn zero) :=
  prf_eq_trans (prf_congr_substtc3 prf_tc_zero)
    (prf_eq_trans (prf_substtc_arith_open 0 W zero) (prf_eq_symm prf_tc_zero))

/-- Paso: `substtc` atraviesa `tcFn (σx) = succc (tcFn x)` y baja a la HI. -/
theorem prf_substtc_tcFn_succ_imp (W x : Term) :
    Prf ((substtc zero W (tcFn x) =eq tcFn x)
      ⇒ (substtc zero W (tcFn (succ x)) =eq tcFn (succ x))) := by
  refine prf_deduction ?_
  have ih : PrfH [substtc zero W (tcFn x) =eq tcFn x] (substtc zero W (tcFn x) =eq tcFn x) :=
    prfH_hyp_self _
  have hsucc : Prf (tcFn (succ x) =eq funcc (strCode succ_sym) (cons (tcFn x) nil)) :=
    prf_tc_succ x
  refine PrfH_eq_trans (PrfH_congr_substtc3 (prf_to_prfH hsucc _)) ?_
  refine PrfH_eq_trans
    (prf_to_prfH (prf_substtc_func zero W (strCode succ_sym) (cons (tcFn x) nil)) _) ?_
  refine PrfH_eq_trans (PrfH_congr_funcc2 ?_) (prf_to_prfH (prf_eq_symm hsucc) _)
  refine PrfH_eq_trans (prf_to_prfH (prf_substtsc_cons zero W (tcFn x) nil) _) ?_
  exact PrfH_eq_trans (PrfH_congr_cons_head ih)
    (PrfH_congr_cons_tail (prf_to_prfH (prf_substtsc_nil zero W) _))

/-- Predicado inductivo (con testigo `W` externo, liftado bajo el `∀`). -/
def substtcTcPred (W : Term) : Formula :=
  Formula.eq (substtc zero (liftTerm 0 W) (tcFn (.var 0))) (tcFn (.var 0))

/-- **`substtc` deja invariante el código de un numeral** (∀ object, por inducción interna). -/
theorem prf_substtc_tcFn_all (W : Term) : Prf (Formula.forall (substtcTcPred W)) := by
  refine prf_nat_induction (substtcTcPred W) ?base ?step
  · simpa only [substtcTcPred, substFormula, substTerm, substTerms, substtc, tcFn, zero,
      reduceIte, if_true, FOL.substTerm_liftTerm] using prf_substtc_tcFn_zero W
  · refine Prf.gen _ ?_
    simpa only [substtcTcPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm,
      substTerms, substtc, tcFn, zero, succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
      Nat.reduceGT, reduceIte, if_true, norm11] using prf_substtc_tcFn_succ_imp (liftTerm 0 W) (.var 0)

/-- **`substtc zero W (tcFn a) =eq tcFn a`** para todo `a` (instancia del ∀). -/
theorem prf_substtc_tcFn (W a : Term) : Prf (substtc zero W (tcFn a) =eq tcFn a) := by
  have h := prf_spec (prf_substtc_tcFn_all W) a
  simpa only [substtcTcPred, substFormula, substTerm, substTerms, substtc, tcFn, zero,
    reduceIte, if_true, FOL.substTerm_liftTerm] using h

end ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

export ROBINSON_PlusPlus.Meta.NumCodeClosedPrf (
  prf_congr_liftc PrfH_congr_liftc PrfH_congr_substtc3 prf_congr_substtc3
  prf_congr_funcc2 PrfH_congr_funcc2
  prf_liftc_tcFn_zero prf_liftc_tcFn_succ_imp liftcTcPred prf_liftc_tcFn_all prf_liftc_tcFn
  prf_substtc_tcFn_zero prf_substtc_tcFn_succ_imp substtcTcPred prf_substtc_tcFn_all
  prf_substtc_tcFn
)

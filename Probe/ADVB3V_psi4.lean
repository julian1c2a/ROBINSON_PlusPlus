import ROBINSON_PlusPlus.Meta.StrongInductionPrf
/-! # HALLAZGO del verificador: el anexo ADR-019 se queda CORTO — falta el nivel 4.

`sondeos/EvalSubstfcPrf.lean:6611` y `sondeos/HasWitFReal.lean:6618` declaran ademas
`psi_l4` (CUATRO `liftFormula 0`), que el anexo del agente (`psi_lift_form2`/`psi_lift_form3`
/`PSI_inst3`) NO cubre. Son justo los dos sondeos que esta promocion dice abaratar.

Este fichero importa **solo `ROBINSON_PlusPlus.Meta.StrongInductionPrf`**, igual que el anexo
del agente, y prueba que el nivel 4 tambien cabe al final de ese modulo. -/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open FOL

set_option linter.unusedSimpArgs false

namespace ADVB3V_PSI4

theorem psi_lift_form2 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (PSI Φ))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) Φ) := by
  rw [psi_lift_form Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

theorem psi_lift_form3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) Φ) := by
  rw [psi_lift_form2 Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

/-- **EL QUE FALTA**: nivel 4, el que usan `EvalSubstfcPrf` y `HasWitFReal`. -/
theorem psi_lift_form4 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 5)) Φ) := by
  rw [psi_lift_form3 Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

/-- Y su extractor, espejo de `PSI_inst` / `PSI_inst3`. -/
theorem PSI_inst4 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))))
    (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 4)) (substFormula 0 z Φ)) := by
  rw [psi_lift_form4 Φ hΦ] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 5)) Φ)
      = Formula.impl (lt z (.var 4)) (substFormula 0 z Φ) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

end ADVB3V_PSI4

#print axioms ADVB3V_PSI4.psi_lift_form4
#print axioms ADVB3V_PSI4.PSI_inst4

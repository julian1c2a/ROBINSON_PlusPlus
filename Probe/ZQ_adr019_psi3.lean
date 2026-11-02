-- ADR-019: ¿puede BAJAR (= subir aguas arriba) la escalera nivel-2/3 de PSI?
-- Este Probe importa SOLO el destino propuesto (StrongInductionPrf).
-- NO importa el barrel, ni EvalLiftcPrf, ni LiftcCodePrf, ni nada aguas abajo.
import ROBINSON_PlusPlus.Meta.StrongInductionPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open FOL

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ZQ_ADR019

/-- Nivel 2, GENERICO en `Φ`. Copia de `psi_l2` del sondeo con `PHI := Φ`, `hPHI1 := hΦ`. -/
theorem psi_lift_form2 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (PSI Φ))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) Φ) := by
  rw [psi_lift_form Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hΦ]

/-- Nivel 3, GENERICO en `Φ`. Copia de `psi_l3`. -/
theorem psi_lift_form3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) Φ) := by
  rw [psi_lift_form2 Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hΦ]

/-- `PSI_inst` a NIVEL 3, GENERICO en `Φ`. Copia de `PSI_inst` del sondeo. -/
theorem PSI_inst3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z Φ)) := by
  rw [psi_lift_form3 Φ hΦ] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) Φ)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z Φ) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

end ZQ_ADR019

#print axioms ZQ_ADR019.psi_lift_form2
#print axioms ZQ_ADR019.psi_lift_form3
#print axioms ZQ_ADR019.PSI_inst3

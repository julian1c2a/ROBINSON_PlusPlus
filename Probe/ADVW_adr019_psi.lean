/- ADR-019 §D: ¿pueden psi_lift_form2/3 y PSI_inst3 vivir al final de
   `Meta/StrongInductionPrf.lean`? Importa SOLO ese modulo. -/
import ROBINSON_PlusPlus.Meta.StrongInductionPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open FOL

namespace ROBINSON_PlusPlus.Meta.StrongInductionPrf

theorem ADVW_psi_lift_form2 (F : Formula) (hF : liftFormula 1 F = F) :
    liftFormula 0 (liftFormula 0 (PSI F))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) F) := by
  rw [psi_lift_form F hF]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hF]

theorem ADVW_psi_lift_form3 (F : Formula) (hF : liftFormula 1 F = F) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI F)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) F) := by
  rw [ADVW_psi_lift_form2 F hF]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hF]

theorem ADVW_PSI_inst3 (F : Formula) (hF : liftFormula 1 F = F) {G : List Formula}
    (hpsi : PrfH G (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI F))))) (z : Term) :
    PrfH G (Formula.impl (lt z (.var 3)) (substFormula 0 z F)) := by
  rw [ADVW_psi_lift_form3 F hF] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) F)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z F) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

end ROBINSON_PlusPlus.Meta.StrongInductionPrf
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.ADVW_PSI_inst3

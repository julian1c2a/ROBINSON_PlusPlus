/- # DOC_sig2 — comprobaciones COMPILADAS de afirmaciones de SIGNIFICADO (auditoria)
       lake env lean Probe/DOC_sig2.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-! ## A · el FOOTPRINT que declara `Meta/EvalLiftcPrf.lean:679-690` -/
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons_all
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_isTermCodeE1_of_In
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_isTermCodeE1_of_boundedIn
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.liftF_targetLift
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.substF_targetLift
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PrfH_congr_targetLiftsc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_hasWit_descenso

/-! ## B · el «CONTROL DE FOOTPRINT — todo debe salir NET-0 (solo los `axiom` de Lean
       sancionados)» de `Meta/LiftcCodePrf.lean:1015` -/
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_func_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil

/-! ## C · ENUNCIADOS: el DESCENSO real contra el «enunciado exacto» de
       `Meta/LiftcCodePrf.lean:967-985` -/
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista
#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#check @ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst

/-! ## D · ¿el `PSI_inst` generico de produccion cubre la variante `PSI3` de los sondeos?
       `PSI3 := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))`,
       conclusion `lt z #3` (sondeos/EvalSubstfcPrf.lean:5683-5694). -/
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Minimal.Axioms in
example (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))) (z : Term) :
    True := by
  -- el `PSI_inst` de produccion NO se aplica a la hipotesis con TRIPLE lift
  fail_if_success
    have _h := PSI_inst Φ hΦ hpsi z
  trivial

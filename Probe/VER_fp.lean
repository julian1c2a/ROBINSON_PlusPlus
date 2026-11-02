/- VER_fp — verificacion independiente de footprints (auditor adversarial)
     lake env lean Probe/VER_fp.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-! ## A · EvalLiftcPrf: ¿quien sale con TRES y quien con CUATRO? -/
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.liftF_targetLift
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.liftF_targetLiftsc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PrfH_congr_targetLiftsc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons_at
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons_all
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_hasWit_descenso

/-! ## B · los PUENTES de §0 -/
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLift_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLiftsc_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.iz_inv_es_prf_substtc_termCode_nil

/-! ## C · LiftcCodePrf: substF_targetLift, refl_* -/
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil

/-! ## D · ENUNCIADOS -/
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp

/- VER_fp2 — «cero axiomas de Lean» y anclas de EvalPredPrf / CodeNatInjPrf / MpCodePrf
     lake env lean Probe/VER_fp2.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-! ## A · EvalPredPrf:27 «Cero axiomas de Lean, cero sorry» -/
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred_zero
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred_succ
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_varc_pred
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_congr_predcT_code
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_eval_pred_all

/-! ## B · CodeNatInjPrf -/
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_inj
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_ne

/-! ## C · MpCodePrf.pcc_axiom_inst4 -/
#print axioms ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4

/-! ## D · ENUNCIADOS -/
#check @ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp

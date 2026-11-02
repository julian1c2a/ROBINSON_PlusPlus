/- # DOC_sig3 — footprints de EvalPredPrf / CodeNatInjPrf, y el papel de `pcc_eval_pred`
       lake env lean Probe/DOC_sig3.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-! ## A · «Cero axiomas de Lean» (EvalPredPrf:27, CodeNatInjPrf:35) -/
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_varc_pred
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_congr_predcT_code
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_ne
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_inj
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.num_bridge

/-! ## B · `pcc_eval_pred` (SIN guarda) da la `PredHyp` GUARDADA en una linea:
       o sea, la forma que el frente pide es ESTRICTAMENTE mas debil. -/
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert in
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.HilbertDeduction in
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.EvalPredPrf in
theorem predhyp_de_pcc_eval_pred : ∀ v n : Term,
    Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n))))) :=
  fun v n => prf_deduction (prf_to_prfH (pcc_eval_pred n) _)

#print axioms predhyp_de_pcc_eval_pred

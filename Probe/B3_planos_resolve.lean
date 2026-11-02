import Lean
/- # `Probe/B3_planos_mecanica_IMPORTS.lean` — VALIDACION DE LA LISTA DE IMPORTS.

   Fichero AUXILIAR: mismo cuerpo que `Probe/B3_planos_mecanica.lean`, pero **sin el
   barrel**: con la lista de `import` concreta propuesta para el modulo real de `Meta/`.
   Si esto compila (exit 0), la lista es suficiente. -/
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.LiftcCodePrf


open Lean in
run_cmd do
  let mut rows : Array String := #[]
  for nm in [`Prf, `PrfH, `PrfH_leibniz_apply, `andc, `ax_substfc_and, `ax_substfc_bottom, `ax_substfc_impl, `ax_substfc_or, `binT, `botc, `cons, `consT, `eqCodeFn, `eqc, `forall_2, `forall_4, `formCode, `funcc, `implc, `liftTerm, `liftTerm_numeral, `liftTerm_numeralM, `liftTerm_strCode, `liftTerms, `liftc, `nil, `nulT, `numeral, `numeralM, `orc, `pcc_axiom_inst2, `pcc_axiom_inst4, `pcc_congr_binT_1_code, `pcc_congr_binT_2_code, `pcc_dot_bin, `pcc_dot_bin_symm, `pcc_dot_nul, `pcc_dot_nul_symm, `pcc_eq_trans_code, `pcc_thm_inst4, `prfH_hyp_self, `prf_congr_consT, `prf_congr_cons_head, `prf_congr_cons_tail, `prf_congr_eqCodeFn, `prf_congr_funcc2, `prf_congr_liftc, `prf_congr_substfc_arg3, `prf_congr_tcFn, `prf_deduction, `prf_eq_symm, `prf_eq_trans, `prf_gnum_lt, `prf_liftc_tcFn, `prf_mp, `prf_provCode_congr, `prf_provFromCode_eqCodeFn_refl, `prf_refl, `prf_substfc_and, `prf_substfc_arith_open, `prf_substfc_bottom, `prf_substfc_eq, `prf_substfc_impl, `prf_substfc_or, `prf_substtc_func, `prf_substtc_funcc2, `prf_substtc_nulT, `prf_substtc_tcFn, `prf_substtc_tcFn_at, `prf_substtc_termCode_closed, `prf_substtc_termCode_zero, `prf_substtc_var_eq, `prf_substtc_var_lt, `prf_substtc_varc0, `prf_substtsc_cons, `prf_substtsc_nil, `prf_to_prfH, `provFromCode, `strCode, `substCodeT, `substCodeT_closed, `substTerm, `substTerm_numeral, `substTerm_strCode, `substTerms, `substfc, `substtc, `substtc_inv_binT, `substtc_inv_nulT, `substtc_inv_tcFn, `succ, `tcFn, `termCode, `varc, `zero] do
    let env ← getEnv
    let cands ← Lean.Elab.Command.liftCoreM (Lean.realizeGlobalConst (Lean.mkIdent nm))
    for c in cands do
      match env.getModuleIdxFor? c with
      | some idx => rows := rows.push s!"{nm} -> {env.header.moduleNames[idx.toNat]!} ({c})"
      | none => rows := rows.push s!"{nm} -> LOCAL ({c})"
  logInfo (String.intercalate "
" rows.toList)

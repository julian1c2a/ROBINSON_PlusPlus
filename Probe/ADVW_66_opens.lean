/- ADVW: ¿bastan los CUATRO `open` que propone el informe para que los 66 resuelvan a secas? -/
import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.PropCodePrf
open ROBINSON_PlusPlus.Meta.NatMulPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Meta.EvalPredPrf

#check @argsIn
#check @argsInBody
#check @AX26_BODY
#check @AX26_BODY_ok
#check @consOk
#check @funccT
#check @funccT_termCode
#check @hasWit
#check @impT
#check @isTC1
#check @isTermCodeE1
#check @liftF_argsIn
#check @liftF_isTC1
#check @liftF_isTermCodeE1
#check @liftF_wfAll1
#check @nilOrCons
#check @nilOrCons_at
#check @pcc_axiom_inst4
#check @pcc_congr_consT_arg1_code
#check @pcc_congr_consT_arg2_code
#check @pcc_thm_inst4
#check @predcT
#check @predcT_termCode
#check @prf_argsIn_tail
#check @prf_cdrc_cons
#check @prf_congr_funccT
#check @prf_congr_predcT
#check @prf_congr_varcT
#check @prf_consOk_cons
#check @prf_isTermCodeE1_of_boundedIn
#check @prf_isTermCodeE1_of_In
#check @prf_nil_or_cons
#check @prf_nil_or_cons_all
#check @prf_or_elim_imp
#check @prf_orL
#check @prf_orR
#check @prf_substfc_atom2CodeFn
#check @prf_substfc_ltCodeFn'
#check @prf_substtc_binT_at
#check @prf_substtc_funccT_at
#check @prf_substtc_predcT
#check @prf_substtc_termCode_closed
#check @prf_substtc_termCode_numeralM
#check @prf_substtc_termCode_zero
#check @prf_substtc_unT_at
#check @prf_substtc_varcT_at
#check @PrfH_congr_argsIn
#check @PrfH_congr_In_left
#check @PrfH_congr_isTermCodeE1
#check @PrfH_congr_lenc
#check @PrfH_congr_nthc_lst
#check @PrfH_inst_argsIn
#check @PrfH_inst_wfAll1
#check @shapeBin
#check @shapeBin1_es_funcc
#check @shapeUn
#check @shapeUn0_es_varc
#check @substF_argsIn
#check @substF_isTC1
#check @substF_isTermCodeE1
#check @substF_wfAll1
#check @substtc_inv_predcT
#check @varcT
#check @varcT_termCode
#check @wfAll1
#check @wfAll1Body

import ROBINSON_PlusPlus.Meta

-- ============ AUDITORIA DE CIFRAS: footprint declarado en los docstrings ============

-- EvalLiftcPrf dice: los resultados sustantivos salen con CUATRO axiomas
-- [propext, Classical.choice, Quot.sound, Representability2Prf.prf_axiomsCodeT_eq]
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real

-- EvalLiftcPrf dice: los PUENTES de §0 salen "con los tres -- o con menos"
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLift_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLiftsc_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.hasWit_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.isTC1_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.iz_inv_es_prf_substtc_termCode_nil
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.eqc_eq_eqCodeFn_es_symm

-- EvalLiftcPrf dice: LiftcCodePrf arrastra prf_axiomsCodeT_eq en refl_termCode y refl_shapeUn_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp

-- CodeNatInjPrf dice: cero axiomas de Lean
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_ne
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_inj

-- EvalPredPrf dice: cero axiomas de Lean
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred
#print axioms ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form

-- ¿es rfl el "puente" eqc_eq_eqCodeFn_es_symm? (el docstring de §0 dice "todos rfl")
example (a b : ROBINSON_PlusPlus.Minimal.Axioms.Term) :
    ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqc a b
      = ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn a b := rfl

import ROBINSON_PlusPlus

/-!
# AUDITORIA CATEGORIA «AXIOMAS Y FOOTPRINT» — solo lectura
-/

-- (1) LOS DOS RESULTADOS DE CABECERA DE `CodeNatInjPrf`
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_ne
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNatTerm_ne

-- (2) DE DONDE ENTRA: la cadena que las alimenta
#print axioms ROBINSON_PlusPlus.Full.numeral_ne
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_inj
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.num_bridge

-- (3) CONTROL: `ax_induction` es una declaracion `axiom` de Lean
#check @ROBINSON_PlusPlus.Full.ax_induction
#print axioms ROBINSON_PlusPlus.Full.ax_induction

-- (4) `EvalPredPrf`: «cero axiomas de Lean»
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred'

-- (5) `StrongInductionPrf`: «sin axiomas nuevos»
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.prf_strong_induction
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form

-- (6) `MpCodePrf`: la familia inst4
#print axioms ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4
#print axioms ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4

-- (7) Los PUENTES de §0 de `EvalLiftcPrf` — ¿todos `rfl`?
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.hasWit_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.isTC1_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.eqc_eq_eqCodeFn_es_symm

-- (8) ¿Existe una imagen dotada de `ax_liftc_var_lt`? (el quinto axioma)
open Lean Elab Command in
elab "#existe " id:ident : command => do
  let env ← getEnv
  logInfo s!"EXISTE {id.getId} :: {(env.find? id.getId).isSome}"

#existe ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_lt_code
#existe ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_varlt_code
#existe ROBINSON_PlusPlus.Minimal.Axioms.ax_liftc_var_lt
#existe ROBINSON_PlusPlus.Minimal.Axioms.ax_liftc_var_ge
#existe ROBINSON_PlusPlus.Minimal.Axioms.ax_liftc_func
#existe ROBINSON_PlusPlus.Minimal.Axioms.ax_liftsc_nil
#existe ROBINSON_PlusPlus.Minimal.Axioms.ax_liftsc_cons

/-
VERIFICACION ADVERSARIAL de las citas `fichero.lean:NNN` — evidencia COMPILADA e
INDEPENDIENTE del grep. Pregunta al entorno de Lean por el rango de cada constante.

    lake env lean Probe\ADVQ_citas.lean
-/
import ROBINSON_PlusPlus.Meta

open Lean Elab Command

def dumpLine (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mod : String :=
    match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none   => "<NO EXISTE>"
  match ← findDeclarationRanges? n with
  | none   => logInfo s!"SIN RANGO   {n}   ({mod})"
  | some r => logInfo s!"{mod} : {r.range.pos.line}-{r.range.endPos.line}   [decl {r.selectionRange.pos.line}]   {n}"

def dumpAll (ns : List Name) : CommandElabM Unit := ns.forM dumpLine

run_cmd do
  logInfo "=== 1 · LiftcCodePrf: el vecindario disputado (hallazgos 1-4, 6) ==="
  dumpAll [`ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_termCode,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_termsCode,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLiftsc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeUn0_es_varc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.LIFTC_FUNC_BODY]

run_cmd do
  logInfo "=== 2 · CodeWitnessPrf: hallazgo 7 y las 9 citas 'limpias' ==="
  dumpAll [`ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.crit_junk_var0_witness1,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.okE1_Ts,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_head,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1]

run_cmd do
  logInfo "=== 3 · EvalLiftcPrf: lo que la cita :254/:368/:378 deberia senalar ==="
  dumpAll [`ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PrfH_congr_targetLiftsc,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_lift,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons]

run_cmd do
  logInfo "=== 4 · modulos ESTABLES declarados limpios (muestra) ==="
  dumpAll [`ROBINSON_PlusPlus.Full.numeral,
           `ROBINSON_PlusPlus.Meta.Godel.numeral,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substtc_var_gt,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_atom,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_eq,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_impl,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_and,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_or,
           `ROBINSON_PlusPlus.Minimal.Axioms.nil,
           `ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code,
           `ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form,
           `ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst,
           `ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq,
           `ROBINSON_PlusPlus.Meta.Representability.termsCodeM_eq,
           `ROBINSON_PlusPlus.Meta.Representability2Prf.prf_axiomsCodeT_eq,
           `ROBINSON_PlusPlus.Meta.CodeCtorKit.unT,
           `ROBINSON_PlusPlus.Meta.CodeCtorKit.binT,
           `ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_2_code,
           `ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked,
           `ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc,
           `ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code,
           `ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil]

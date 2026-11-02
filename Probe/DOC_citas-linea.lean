/-
AUDITORIA DE CITAS `fichero.lean:NNN` — evidencia COMPILADA.

No usa grep: pregunta al ENTORNO de Lean por el rango de declaracion de cada constante
citada en los docstrings del frente, y lo imprime como `modulo : linea`.

    lake env lean Probe\DOC_citas-linea.lean
-/
import ROBINSON_PlusPlus.Meta

open Lean Elab Command

/-- Imprime `modulo : LINEA` de la declaracion `n`, segun el propio entorno. -/
def dumpLine (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mod : String :=
    match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none   => "<este fichero>"
  match ← findDeclarationRanges? n with
  | none   => logInfo s!"{mod} : SIN RANGO   {n}"
  | some r => logInfo s!"{mod} : linea {r.range.pos.line}   {n}"

def dumpAll (ns : List Name) : CommandElabM Unit := ns.forM dumpLine

run_cmd do
  logInfo "=== A · LiftcCodePrf: el vecindario de substF_targetLift ==="
  dumpAll [`ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLiftsc,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp,
           `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp]

run_cmd do
  logInfo "=== B · CodeWitnessPrf: lo citado desde el frente ==="
  dumpAll [`ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_head,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail,
           `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.crit_junk_var0_witness1]

run_cmd do
  logInfo "=== C · el resto de los ficheros citados ==="
  dumpAll [`ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code,
           `ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc,
           `ROBINSON_PlusPlus.Meta.CodeCtorKit.unT,
           `ROBINSON_PlusPlus.Meta.CodeCtorKit.binT,
           `ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_2_code,
           `ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked,
           `ROBINSON_PlusPlus.Minimal.Axioms.nil,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substtc_var_gt,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_atom,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_eq,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_impl,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_and,
           `ROBINSON_PlusPlus.Minimal.Axioms.ax_substfc_or,
           `ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil,
           `ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code,
           `ROBINSON_PlusPlus.Meta.Representability2Prf.prf_axiomsCodeT_eq,
           `ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq,
           `ROBINSON_PlusPlus.Meta.Representability.termsCodeM_eq,
           `ROBINSON_PlusPlus.Full.numeral,
           `ROBINSON_PlusPlus.Meta.Godel.numeral,
           `ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form,
           `ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PrfH_congr_targetLiftsc,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons,
           `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc]

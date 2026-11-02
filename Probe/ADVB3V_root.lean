import ROBINSON_PlusPlus.Meta
/-! Verificador: ¿alguno de los 34 nombres del `export` propuesto YA resuelve en la RAIZ?
    Y ademas: ¿los 16 «colisionantes» resuelven hoy en la raiz? -/

open Lean Lean.Elab Lean.Elab.Command in
run_cmd do
  let env ← Lean.getEnv
  let propuestos : List String := [
    "substtcT","substtscT","substtcT_termCode","substtscT_termCode",
    "prf_congr_funcc3","prf_substtc_funcc3",
    "prf_congr_substtcT","prf_congr_substtscT",
    "prf_substtc_substtcT","prf_substtc_substtscT",
    "substtc_inv_substtcT","substtc_inv_substtscT",
    "SUBSTTSC_NIL_BODY","SUBSTTSC_NIL_BODY_ok","pcc_substtsc_nil_code",
    "SUBSTTC_FUNC_BODY","SUBSTTC_FUNC_BODY_ok","pcc_substtc_func_code",
    "SUBSTTSC_CONS_BODY","SUBSTTSC_CONS_BODY_ok","pcc_substtsc_cons_code",
    "SUBSTTC_VAR_EQ_BODY","SUBSTTC_VAR_GT_BODY","SUBSTTC_VAR_LT_BODY",
    "pcc_substtc_var_eq_code","pcc_substtc_var_gt_code","pcc_substtc_var_lt_code",
    "targetSubsttc","targetSubsttsc",
    "pcc_congr_substtcT_arg3_code","pcc_congr_substtscT_arg3_code",
    "pcc_eval_substtc","pcc_eval_substtsc","pcc_eval_substtc_hasWit" ]
  let colisionantes : List String := [
    "refl_caso_varc","refl_caso_funcc","refl_lista_nil","refl_lista_cons",
    "refl_shapeUn_imp","refl_caso_funcc_imp","refl_shapeBin_imp","refl_lista_cons_imp",
    "PSI_inst","PHIbody","PHI","PHI_at","PHI_use","PHI_step","PHI_all",
    "DESCENSO_imp","DESCENSO_lista_imp" ]
  let mut nProp : Nat := 0
  Lean.logInfo "--- PROPUESTOS AL EXPORT (34): ¿ya en la RAIZ? ---"
  for s in propuestos do
    let n := Name.mkSimple s
    let rs : List Name := (Lean.getAliases env n (skipProtected := false)) ++ (if env.contains n then [n] else [])
    if !rs.isEmpty then
      nProp := nProp + 1
      Lean.logInfo m!"  ⛔ YA-EN-RAIZ  {s}  ->  {rs}"
  Lean.logInfo m!"PROPUESTOS_YA_EN_RAIZ = {nProp} de {propuestos.length}"
  Lean.logInfo "--- COLISIONANTES (17 nombres): ¿en la RAIZ hoy? ---"
  let mut nCol : Nat := 0
  for s in colisionantes do
    let n := Name.mkSimple s
    let rs : List Name := (Lean.getAliases env n (skipProtected := false)) ++ (if env.contains n then [n] else [])
    if !rs.isEmpty then
      nCol := nCol + 1
      Lean.logInfo m!"  ⚠️ EN-RAIZ  {s}  ->  {rs}"
    else
      Lean.logInfo m!"  ok(no-raiz)  {s}"
  Lean.logInfo m!"COLISIONANTES_EN_RAIZ = {nCol} de {colisionantes.length}"

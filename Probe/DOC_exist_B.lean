/-
Probe/DOC_exist_B.lean — CENSO DE ENTORNO (auditoria de EXISTENCIA, agente B).
Para cada nombre citado en un docstring: existe? en que MODULO? en que LINEA?
Ademas: recuento de miembros por namespace, y USO REAL de un simbolo dentro de un modulo.
-/
import ROBINSON_PlusPlus
import Lean

open Lean Elab Command

def needlesB : Array String := #[
  -- === EvalLiftcPrf: tabla de imports "simbolo que lo exige" ===
  "prf_eq_symm", "prf_eq_trans", "prf_refl",
  "boundedIn", "prf_boundedIn_of_In", "PrfH_lt_subst2",
  "prf_cantor_mono_left", "prf_cantor_mono_right",
  "prf_list_induction", "PrfH_leibniz_subst", "PrfH_or_elim", "PrfH_spec",
  "PrfH_and_intro", "PrfH_and_elim_left", "PrfH_and_elim_right",
  "liftTerm_termCode", "liftTerm_strCode", "substTerm_strCode",
  "prf_substtc_termCode_nil",
  "prf_deduction", "deduction_aux", "prf_to_prfH", "prfH_nil_to_prf", "prf_ex_elim_imp",
  "prf_zero_lt_succ", "prf_succ_lt_succ_of_lt", "prf_lt_trans",
  "prf_lenc_cons", "prf_nthc_zero", "prf_nthc_succ",
  "termCode", "prf_mp", "prf_spec", "prf_and_intro", "prf_and_elim_left", "prf_carc_cons",
  "eqCodeFn", "eqCodeFn_eq_eqc", "objList", "provFromCode",
  "PSI", "prf_strong_induction", "psi_lift_form", "PSI_inst",
  "liftFormula_provFromCode_open", "substFormula_provFromCode_open",
  "qconf",
  -- === CodeWitnessPrf: SinWTs / ENS ===
  "isTC1", "wfAll1", "argsIn", "argsInBody", "isTermCodeE1", "tcodes1", "consOk",
  "impT", "prf_or_elim_imp", "prf_congr_liftc",
  "crit_junk_var0_witness1", "prf_isTC1_tcodes", "prf_argsIn_of_closed",
  "prf_argsIn_head", "prf_argsIn_tail", "PrfH_inst_argsIn", "PrfH_inst_wfAll1",
  "hasWit", "liftF_isTC1", "substF_isTC1", "substF_wfAll1", "CRIT_hasWit_real",
  "liftF_hasWit", "substF_hasWit",
  "liftF_argsIn", "substF_argsIn", "liftF_isTermCodeE1", "substF_isTermCodeE1",
  "liftF_wfAll1", "prf_isFormCodeE2_of_In",
  "shapeUn", "shapeBin",
  "PrfH_congr_isTermCodeE1", "PrfH_congr_argsIn", "PrfH_congr_In_left",
  "PrfH_congr_lenc", "PrfH_congr_nthc_lst",
  "closed_mem_tcodes1", "liftTerm_objList", "liftTerm_termsCodeM",
  "substTerm_objList", "substTerm_termsCodeM", "prf_lenc_termsCodeM",
  "prf_nthc_termsCodeM", "prf_congr_In_left", "prf_In_objList", "mem_tcodes1s_of_mem",
  -- === LiftcCodePrf: tabla "ya vive en" + citas internas ===
  "PrfH_eq_trans_code", "unT", "binT",
  "prf_substtc_unT", "prf_substtc_binT", "substtc_inv_termCode_numeralM",
  "prf_substfc_ltCodeFn_snd", "prf_substfc_ltCodeFn_varc0",
  "pcc_lt_tracked", "pcc_congr_binT_2_code",
  "pcc_nthc_zero_code", "pcc_dot_cons", "pcc_substfc_forall_dot", "pcc_nthc_zero_code",
  "ax_liftc_var_lt", "ax_liftc_var_ge", "ax_liftc_func", "ax_liftsc_nil", "ax_liftsc_cons",
  "targetLift", "targetLiftsc", "refl_termCode", "refl_termsCode",
  "PrfH_congr_targetLift", "refl_isTermCodeE1_imp", "prf_provFromCode_eqCodeFn_refl",
  "termCodeM_eq", "termsCodeM_eq", "prf_axiomsCodeT_eq",
  -- === StrongInductionPrf ===
  "substFormula_liftFormula", "strong_induction", "subst_lift_cancel_formula",
  "substTerm_liftLift", "prf_nat_induction", "psi_at", "prf_psi_elim", "psi_lift_eq_subst",
  "prf_lt_succ_self_cm", "prf_cantor_mono", "pcc_eval_substfc", "prf_le_self_add",
  -- === CodeNatInjPrf ===
  "triN", "consN", "codeNatChars", "codeNatTerm", "codeNat", "codeNatStr", "codeNatTerms",
  "numeral_ne", "canon_ne", "codeNat_ne", "codeNatTerm_ne", "num_bridge",
  -- === EvalPredPrf ===
  "ax_substtc_var_gt", "pcc_eval_add", "pcc_congr_succ_code", "addcT_termCode", "succcT",
  "pred_sym", "evalSubstfcCode", "pcc_eval_substtc", "prf_zero_or_eq_succ_pred",
  "substCodeF", "pcc_leibniz_apply", "pcc_congr_unT_code", "pcc_dot_un", "pcc_eq_trans_code",
  "ax25_pred_zero", "ax26_pred_succ", "prf_pred_succ", "prf_tc_succ'", "prf_tc_zero",
  "substtc_inv_unT", "substtc_inv_tcFn", "prf_substfc_arith_open", "predcT",
  "repr_pos'_prf",
  -- === MpCodePrf ===
  "d2_prf", "pcc_forallElim_code'", "pcc_exIntro_code'", "pcc_forallElim_code_open",
  "prf_substfc_forall", "prf_congr_substfc_arg3", "forall_4", "forall_3", "forall_2",
  "ax4_add_zero", "ax5_add_succ", "ax_substfc_impl", "ax_substfc_and", "ax_substfc_or",
  "ax_substfc_atom", "ax_substfc_eq", "prf_lineWF_mp", "prf_premsOf_mp", "pcc_axiom_inst4",
  -- === sospechosos ===
  "DescMutua", "DESCENSO_hasWitF", "prf_hasWitF_real", "iz_inv", "eqc_eq_eqCodeFn",
  "prf_isTermCodeE1_of_In", "prf_isTermCodeE1_of_boundedIn"
]

def nsToCountB : Array Name := #[
  `ROBINSON_PlusPlus.Meta.EvalLiftcPrf,
  `ROBINSON_PlusPlus.Meta.LiftcCodePrf,
  `ROBINSON_PlusPlus.Meta.CodeNatInjPrf,
  `ROBINSON_PlusPlus.Meta.EvalPredPrf,
  `ROBINSON_PlusPlus.Meta.MpCodePrf,
  `ROBINSON_PlusPlus.Meta.StrongInductionPrf,
  `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs,
  `ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS,
  `ROBINSON_PlusPlus.Meta.CodeWitnessPrf
]

/-- modulos cuyos USOS reales queremos medir -/
def modsToScan : Array Name := #[
  `ROBINSON_PlusPlus.Meta.EvalLiftcPrf,
  `ROBINSON_PlusPlus.Meta.LiftcCodePrf
]

def modOfB (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let mods := env.allImportedModuleNames
      if h : idx.toNat < mods.size then mods[idx.toNat] else `UNKNOWN
  | none => `CURRENT_FILE

def matchesNeedleB (n : Name) (needle : String) : Bool :=
  let s := n.toString
  s == needle || s.endsWith ("." ++ needle)

run_cmd do
  let env ← getEnv
  let mut cs : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let m := modOfB env n
    if m.getRoot == `ROBINSON_PlusPlus || m.getRoot == `FOL then
      cs := cs.push (n, m)
  logInfo s!"### constantes de proyecto censadas: {cs.size}"
  let mut out : Array String := #[]
  for needle in needlesB do
    let hits := cs.filter (fun (n, _) => matchesNeedleB n needle)
    if hits.isEmpty then
      out := out.push s!"MISSING :: {needle}"
    else
      for (n, m) in hits do
        let rng ← liftCoreM (findDeclarationRanges? n)
        let line := match rng with
          | some r => toString r.range.pos.line
          | none => "?"
        out := out.push s!"OK :: {needle} :: {n} :: {m} :: L{line}"
  logInfo (String.intercalate "\n" out.toList)

run_cmd do
  let env ← getEnv
  let mut cs : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let m := modOfB env n
    if m.getRoot == `ROBINSON_PlusPlus || m.getRoot == `FOL then
      cs := cs.push (n, m)
  let mut out2 : Array String := #[]
  for ns in nsToCountB do
    let mems := cs.filter (fun (n, _) => ns.isPrefixOf n && n != ns)
    let direct := mems.filter (fun (n, _) => n.getPrefix == ns)
    out2 := out2.push s!"NS :: {ns} :: total={mems.size} directos={direct.size}"
    let names := (direct.map (fun (n, _) => n.getString!)).qsort (· < ·)
    out2 := out2.push ("    " ++ String.intercalate " " names.toList)
  logInfo (String.intercalate "\n" out2.toList)

/-- Cuenta declaraciones POR MODULO (no por namespace): lo que el modulo APORTA al entorno. -/
run_cmd do
  let env ← getEnv
  for m in modsToScan do
    let mut k := 0
    let mut names : Array String := #[]
    for (n, _) in env.constants.toList do
      if n.isInternal then continue
      if modOfB env n == m then
        k := k + 1
        names := names.push n.toString
    logInfo s!"MOD :: {m} :: declaraciones={k}"

/-- USO REAL: para cada modulo escaneado, dice si un simbolo aparece en el cuerpo
    de ALGUNA de sus declaraciones (constantes usadas del termino de prueba). -/
run_cmd do
  let env ← getEnv
  for m in modsToScan do
    -- recoge todas las constantes usadas por las declaraciones del modulo m
    let mut used : Std.HashSet Name := {}
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      if modOfB env n != m then continue
      match ci.value? with
      | some v => for u in v.getUsedConstants do used := used.insert u
      | none => pure ()
      for u in ci.type.getUsedConstants do used := used.insert u
    let probe : Array String := #[
      "prf_eq_symm", "prf_eq_trans", "prf_refl", "boundedIn", "prf_boundedIn_of_In",
      "PrfH_lt_subst2", "prf_cantor_mono_left", "prf_cantor_mono_right",
      "prf_list_induction", "PrfH_leibniz_subst", "PrfH_or_elim", "PrfH_spec",
      "liftTerm_termCode", "liftTerm_strCode", "substTerm_strCode",
      "prf_substtc_termCode_nil", "prf_deduction", "deduction_aux", "prf_to_prfH",
      "prfH_nil_to_prf", "prf_ex_elim_imp", "prf_zero_lt_succ", "prf_succ_lt_succ_of_lt",
      "prf_lt_trans", "prf_lenc_cons", "prf_nthc_zero", "prf_nthc_succ",
      "prf_mp", "prf_spec", "prf_and_intro", "prf_and_elim_left", "prf_carc_cons",
      "eqCodeFn", "eqCodeFn_eq_eqc", "objList", "PSI", "prf_strong_induction",
      "psi_lift_form", "PSI_inst", "liftFormula_provFromCode_open",
      "substFormula_provFromCode_open", "qconf", "j1", "j2", "p1", "gen",
      "prf_substtc_termCode_zero", "substTerm_termCode", "refl_lista_nil",
      "refl_lista_cons_imp", "refl_shapeUn_imp", "refl_shapeBin_imp",
      "liftF_hasWit", "substF_hasWit", "substF_isTC1", "liftF_isTC1", "substF_wfAll1",
      "liftF_argsIn", "substF_argsIn", "liftF_isTermCodeE1", "substF_isTermCodeE1",
      "liftF_wfAll1", "prf_argsIn_head", "prf_argsIn_tail", "consOk", "prf_consOk_cons"
    ]
    let mut out : Array String := #[]
    for p in probe do
      let hits := used.toList.filter (fun n => matchesNeedleB n p)
      if hits.isEmpty then
        out := out.push s!"  NO-USADO :: {p}"
      else
        out := out.push s!"  usado :: {p} :: {hits.map (·.toString)}"
    logInfo s!"USOS EN {m}:\n{String.intercalate "\n" out.toList}"

import ROBINSON_PlusPlus
import Lean
open Lean Elab Command

/-! Censo de entorno para la auditoria de EXISTENCIA. NO edita nada de produccion. -/

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => toString (env.header.moduleNames[idx.toNat]!)
  | none => "<current>"

def esInterno (n : Name) : Bool :=
  n.isInternal || (n.components.any fun c =>
    let s := c.toString
    s.startsWith "_" || s == "proof_1" || s == "eq_def" || s == "eq_1" || s == "match_1")

/-- Nombres declarados en sondeos/DescensoLiftc.lean (198, extraidos del fuente). -/
def sondeoNames : List String := [
  "argsIn",
  "argsInBody",
  "closed_mem_tcodes1",
  "closed_mem_tcodes1s",
  "closed_termCodeM",
  "CodeClosed",
  "cOk",
  "consOk",
  "CRIT_antecedente_discrimina",
  "crit_closed_implc",
  "crit_cOk2_absurd",
  "crit_cOk3_absurd",
  "CRIT_hasWit_descenso",
  "CRIT_hasWit_real",
  "crit_isTC1_junk_refuted_open",
  "crit_isTermCodeB1_rejects",
  "crit_isTermCodeB1_rejects_andc",
  "crit_isTermCodeB1_rejects_atomc",
  "crit_isTermCodeB1_rejects_botc",
  "crit_isTermCodeB1_rejects_eqc",
  "crit_isTermCodeB1_rejects_exc",
  "crit_isTermCodeB1_rejects_forallc",
  "crit_isTermCodeB1_rejects_implc",
  "crit_isTermCodeB1_rejects_orc",
  "crit_isTermCodeE1_rejects",
  "crit_isTermCodeE1_rejects_implc",
  "crit_junk_SubCodesCritica_open1",
  "crit_junk_var0_witness1",
  "crit_num_ne",
  "CRIT_real_A",
  "CRIT_real_B",
  "CRIT_real_lista",
  "crit_tag_absurd",
  "CRIT_targetLift_real",
  "CRIT_targetLiftsc_real",
  "DESCENSO",
  "DESCENSO_hasWit",
  "DESCENSO_imp",
  "DESCENSO_lista",
  "DESCENSO_lista_imp",
  "eqc_eq_eqCodeFn",
  "funccT",
  "funccT_termCode",
  "funcOkT1",
  "hasWit",
  "hPHI",
  "impT",
  "isTC1",
  "isTermCodeB1",
  "isTermCodeE1",
  "iz_inv",
  "LIFTC_FUNC_BODY",
  "LIFTC_FUNC_BODY_ok",
  "LIFTC_VARGE_BODY",
  "LIFTC_VARGE_BODY_ok",
  "liftcT",
  "liftcT_termCode",
  "liftF_argsIn",
  "liftF_isTC1",
  "liftF_isTermCodeE1",
  "liftF_targetLift",
  "liftF_targetLiftsc",
  "liftF_wfAll1",
  "LIFTSC_CONS_BODY",
  "LIFTSC_CONS_BODY_ok",
  "LIFTSC_NIL_BODY",
  "LIFTSC_NIL_BODY_ok",
  "liftscT",
  "liftscT_termCode",
  "liftTerm_objList",
  "mem_of_getElem?",
  "mem_self_tcodes1",
  "mem_tcodes1s_of_mem",
  "nilOrCons",
  "nilOrCons_at",
  "okE1_T",
  "okE1_Ts",
  "pcc_congr_consT_arg1_code",
  "pcc_congr_consT_arg2_code",
  "pcc_congr_liftcT_arg2_code",
  "pcc_congr_liftscT_arg2_code",
  "pcc_eval_liftc",
  "pcc_liftc_func_code",
  "pcc_liftc_var_ge_code",
  "pcc_liftc0_func_code",
  "pcc_liftc0_var_code",
  "pcc_liftsc_cons_code",
  "pcc_liftsc_nil_code",
  "pcc_liftsc0_cons_code",
  "pcc_liftsc0_nil_code",
  "pcc_zero_lt_succ_code",
  "PHI",
  "PHI_all",
  "PHI_at",
  "PHI_step",
  "PHI_use",
  "PHIbody",
  "prf_argsIn_head",
  "prf_argsIn_of_closed",
  "prf_argsIn_tail",
  "prf_bdAll_numeral",
  "prf_bdAll_of_bound",
  "prf_cdrc_cons",
  "prf_congr_argsIn",
  "prf_congr_funccT",
  "prf_congr_In_left",
  "prf_congr_liftcT",
  "prf_congr_liftscT",
  "prf_congr_varcT",
  "prf_consOk_cons",
  "prf_crit_In_rejects_open1",
  "prf_In_objList",
  "prf_isTC1_tcodes",
  "prf_isTermCodeE1_func",
  "prf_isTermCodeE1_of_boundedIn",
  "prf_isTermCodeE1_of_In",
  "prf_isTermCodeE1_str",
  "prf_isTermCodeE1_var",
  "prf_lenc_c1",
  "prf_lenc_c2",
  "prf_lenc_c3",
  "prf_lenc_objList",
  "prf_lenc_termsCodeM",
  "prf_lorL",
  "prf_lorR",
  "prf_nil_or_cons",
  "prf_nil_or_cons_all",
  "prf_nthc_c1",
  "prf_nthc_c2",
  "prf_nthc_objList",
  "prf_nthc_termsCodeM",
  "prf_or_elim_imp",
  "prf_orL",
  "prf_orR",
  "prf_shape_strengthens",
  "prf_shapeBin_str",
  "prf_shapeUn_str",
  "prf_str_and",
  "prf_substfc_atom2CodeFn",
  "prf_substfc_ltCodeFn'",
  "prf_substtc_binT_at",
  "prf_substtc_funccT_at",
  "prf_substtc_liftcT",
  "prf_substtc_liftscT",
  "prf_substtc_termCode_closed",
  "prf_substtc_termCode_numeralM",
  "prf_substtc_termCode_zero",
  "prf_substtc_unT_at",
  "prf_substtc_varcT_at",
  "PrfH_congr_argsIn",
  "PrfH_congr_In_left",
  "PrfH_congr_isTermCodeE1",
  "PrfH_congr_lenc",
  "PrfH_congr_liftc",
  "PrfH_congr_nthc_idx",
  "PrfH_congr_nthc_lst",
  "PrfH_congr_targetLift",
  "PrfH_congr_targetLiftsc",
  "PrfH_eq_trans_code",
  "PrfH_inst_argsIn",
  "PrfH_inst_wfAll1",
  "PSI_inst",
  "psi_lift_form",
  "refl_caso_funcc",
  "refl_caso_funcc_imp",
  "refl_caso_varc",
  "refl_lista_cons",
  "refl_lista_cons_imp",
  "refl_lista_nil",
  "refl_shapeBin_imp",
  "refl_shapeUn_imp",
  "shapeBin",
  "shapeBin1_es_funcc",
  "shapeUn",
  "shapeUn0_es_varc",
  "substF_argsIn",
  "substF_isTC1",
  "substF_isTermCodeE1",
  "substF_targetLift",
  "substF_targetLift_hole",
  "substF_targetLiftsc",
  "substF_wfAll1",
  "substtc_inv_liftcT",
  "substtc_inv_liftscT",
  "substTerm_objList",
  "substTerm_termCode",
  "substTerm_termsCode",
  "targetLift",
  "targetLiftsc",
  "tcodes1",
  "tcodes1s",
  "tEjA",
  "tEjB",
  "varcT",
  "varcT_termCode",
  "varOkT",
  "wfAll1",
  "wfAll1Body",
  "ZZZ_centinela_inexistente"
]

/-- Simbolos citados en docstrings de los modulos auditados. -/
def citados : List String := [
  "shapeUn", "shapeBin", "argsInBody", "argsIn", "isTermCodeE1", "impT", "prf_or_elim_imp",
  "PrfH_eq_trans_code", "eqCodeFn_eq_eqc", "prf_congr_liftc",
  "prf_substtc_unT", "prf_substtc_binT", "substtc_inv_termCode_numeralM",
  "prf_substfc_ltCodeFn_snd", "prf_substfc_ltCodeFn_varc0",
  "pcc_lt_tracked", "pcc_congr_binT_2_code", "prf_substtc_termCode_nil",
  "prf_strong_induction", "prf_cantor_mono_left", "prf_cantor_mono_right",
  "psi_lift_form", "PSI_inst", "prf_argsIn_head", "prf_argsIn_tail",
  "prf_isTermCodeE1_of_boundedIn", "prf_isTermCodeE1_of_In",
  "prf_isFormCodeE2_of_boundedIn", "prf_isFormCodeE2_of_In",
  "PrfH_inst_argsIn", "PrfH_inst_wfAll1", "PrfH_lt_subst2", "boundedIn", "prf_boundedIn_of_In",
  "hasWit", "liftF_isTC1", "substF_isTC1", "substF_wfAll1", "liftF_hasWit", "substF_hasWit",
  "CRIT_hasWit_real", "isTC1", "wfAll1", "consOk", "tcodes1", "crit_junk_var0_witness1",
  "prf_isTC1_tcodes", "prf_argsIn_of_closed",
  "liftF_argsIn", "substF_argsIn", "liftF_isTermCodeE1", "substF_isTermCodeE1", "liftF_wfAll1",
  "termCodeM_eq", "termsCodeM_eq", "objList", "prf_axiomsCodeT_eq",
  "refl_termCode", "refl_termsCode", "DESCENSO", "DESCENSO_hasWit", "pcc_eval_liftc",
  "prf_list_induction", "prf_consOk_cons", "prf_lenc_cons", "prf_nthc_zero", "prf_nthc_succ",
  "prf_zero_lt_succ", "prf_succ_lt_succ_of_lt", "prf_lt_trans", "prf_spec", "prf_carc_cons",
  "prf_and_intro", "prf_and_elim_left", "liftTerm_termCode", "liftTerm_strCode",
  "substTerm_strCode", "termCode", "provFromCode", "eqCodeFn", "PSI",
  "liftFormula_provFromCode_open", "substFormula_provFromCode_open",
  "prf_ex_elim_imp", "prfH_nil_to_prf", "deduction_aux", "prf_to_prfH", "prf_deduction",
  "qconf", "p1", "j1", "j2",
  "triN", "consN", "codeNatChars", "codeNatTerm", "codeNat", "codeNatStr",
  "numeral_ne", "pcc_eval_add", "pcc_congr_succ_code",
  "ax_substtc_var_gt", "ax25_pred_zero", "ax26_pred_succ",
  "ax_substfc_impl", "ax_substfc_and", "ax_substfc_or", "ax_substfc_atom", "ax_substfc_eq",
  "pcc_forallElim_code_open", "pcc_forallElim_code'", "pcc_exIntro_code'",
  "pcc_nthc_zero_code", "pcc_dot_cons", "predcT", "pcc_eval_pred",
  "ZZZ_centinela_inexistente"
]

/-- Prefijos de namespace cuyo censo completo interesa. -/
def prefijos : List String := [
  "ROBINSON_PlusPlus.Meta.EvalLiftcPrf",
  "ROBINSON_PlusPlus.Meta.LiftcCodePrf",
  "ROBINSON_PlusPlus.Meta.CodeNatInjPrf",
  "ROBINSON_PlusPlus.Meta.EvalPredPrf",
  "ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs",
  "ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS"
]

def outPath : String :=
  "C:/msys64/tmp/claude/e--dropbox-github-lean4-ROBINSON-PlusPlus/85b0df6c-1e14-407d-a9ae-04b9e8841ed5/scratchpad/censo.txt"

run_cmd do
  let env ← getEnv
  let allTargets : List String := sondeoNames ++ citados
  let tset : Std.HashSet String := Std.HashSet.ofList allTargets
  let pset : List String := prefijos
  let (hits, nsHits) := env.constants.fold
      (init := ((∅ : Std.HashMap String (Array Name)), (∅ : Std.HashMap String (Array Name))))
      fun (acc, nacc) n _ =>
        if esInterno n then (acc, nacc) else
        let acc := match n with
          | .str _ s => if tset.contains s then acc.insert s ((acc.getD s #[]).push n) else acc
          | _ => acc
        let full := n.toString
        let nacc := pset.foldl (fun na p =>
          if full.startsWith (p ++ ".") then na.insert p ((na.getD p #[]).push n) else na) nacc
        (acc, nacc)
  let mut out : Array String := #[]
  -- (A) los 198 nombres del sondeo DescensoLiftc
  let mut nOk := 0
  let mut nMiss := 0
  out := out.push "########## (A) LOS 198 NOMBRES DE sondeos/DescensoLiftc.lean ##########"
  for s in sondeoNames do
    if s == "ZZZ_centinela_inexistente" then continue
    match hits.get? s with
    | none => nMiss := nMiss + 1; out := out.push s!"AUSENTE  {s}"
    | some arr =>
        nOk := nOk + 1
        let ds := arr.toList.map (fun n => s!"{n} @@ {modOf env n}")
        out := out.push s!"EXISTE   {s}  ->  {String.intercalate " | " ds}"
  out := out.push s!"##### (A) RESUMEN: total=198  EXISTE_EN_PRODUCCION={nOk}  AUSENTE={nMiss}"
  -- (B) simbolos citados en docstrings
  out := out.push ""
  out := out.push "########## (B) SIMBOLOS CITADOS EN DOCSTRINGS ##########"
  for s in citados do
    match hits.get? s with
    | none => out := out.push s!"AUSENTE  {s}"
    | some arr =>
        let ds := arr.toList.map (fun n => s!"{n} @@ {modOf env n}")
        out := out.push s!"EXISTE   {s}  ->  {String.intercalate " | " ds}"
  -- (C) censo por namespace
  out := out.push ""
  out := out.push "########## (C) CENSO POR NAMESPACE ##########"
  for p in prefijos do
    let arr := nsHits.getD p #[]
    out := out.push s!"----- {p} : {arr.size} constantes no-internas"
    for n in arr.qsort (fun a b => a.toString < b.toString) do
      out := out.push s!"    {n}"
  IO.FS.writeFile outPath (String.intercalate "\n" out.toList)
  logInfo s!"censo escrito: A_ok={nOk} A_miss={nMiss}"

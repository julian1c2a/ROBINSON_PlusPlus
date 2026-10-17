/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · el inventario de NegNum y PosNum: qué existe, dónde, y si es PURO (T08)

**Fecha:** 2026‑10‑16 · **Por qué:** ADR‑146, el ADR de diseño de NegNum y PosNum de T, la pieza grande de Rosser
(ADR‑145: por la ruta SINTÁCTICA, porque T08 tiene que aceptar la instancia de `rosser_ext`).

**Qué hace.** Para cada pieza que el plan de Rosser (`doc/registro/2026-10-05-adr122-d7-rosser/resultado.json`, Etapas
0–7) y los tres inventarios del 2026‑10‑16 nombran como reutilizable, busca la constante por su ÚLTIMO componente
(así no hay que adivinar el espacio de nombres: `SinWTs`, `ENS`…) y la clasifica con el recorrido de T08
(`Meta/PurezaTitulares.lean`, `recorrer`; ✏️ 2026‑10‑18, ADR‑157: hoy en `Meta/PurezaComando.lean`): PURO, o IMPURO
con el camino hasta la semántica. Si un nombre casa con
varias constantes, salen todas; si con ninguna del build, sale «FUERA»: las de los sondeos (`RosserBasura`,
`RosserReflexion`, `ExtensionPorReduccion`) no se pueden importar, y su pureza se lee en su fuente o la mide su propio
`#pureza`. También dice el MÓDULO.

**Escribe** `doc/registro/2026-10-16-negnum-posnum/pureza.txt` (efecto lateral). Se lanza con
`lake lean sondeos/InventarioRosser.lean` desde la raíz de RPP.

**Resultado de la ejecución del 2026‑10‑16:** en ADR‑146 §2.
-/

open Lean Elab Command ROBINSON_PlusPlus.Meta.PurezaComando

namespace InventarioRosser

/-- Índice: último componente (del nombre de usuario) ↦ las constantes que lo tienen. Se construye una vez. -/
def indicePorUltimo (env : Environment) : Std.HashMap String (Array Name) := Id.run do
  let mut idx : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.map₁.toList do
    match nombreUsuario n with
    | .str _ t => idx := idx.insert t ((idx.getD t #[]).push n)
    | _ => pure ()
  return idx

def moduloDe' (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString env.header.moduleNames[i.toNat]!
  | none => "este fichero"

/-- Las piezas, por etapa del plan. -/
def piezas : List (String × List String) := [
  ("Etapa 6 · PosNum (D1 y la evaluación a numeral)",
    ["repr_pos'_prf", "provCodeC'_intro_prf", "prf_chainOk_track", "prf_runFn_track", "prf_In_runFn_of_mem",
     "prf_cons_eval", "prf_cons_eval_of", "prf_formCode_numeral", "prf_termCode_numeral", "prf_strCode_numeral",
     "prf_cons_evalM", "prf_chainOk_subst2", "prf_congr_runFn_2", "prf_eq_subst_in", "stdChain_proofCode'",
     "prf_iff_derivation"]),
  ("W1 · el verificador es sólido (hoy con V₀)",
    ["verificador_solido", "cadena_buena", "linea_buena", "linea_thy", "linea_q1", "linea_mp", "linea_gen",
     "memN_codeNatList", "dec_codeNat", "dec_substfc", "dec_liftfc"]),
  ("Etapa 1 · la capa de listas sobre numerales",
    ["prf_in_cons_iff", "prf_not_in_nil", "prf_in_concat_singleton_iff", "crit_num_ne", "prf_lt_numeralM",
     "prf_objList_numeral", "prf_lenc_objList", "prf_nthc_objList", "prf_carc_numeral", "prf_zero_ne_cons",
     "prf_cons_def", "prf_succ_ne_zero", "prf_numeral_lt"]),
  ("Etapa 2 · la evaluación de la sustitución (hoy sólo sobre códigos canónicos)",
    ["prf_substTerm_arith", "prf_liftTerm_arith", "prf_substFormula_arith", "prf_liftFormula_arith",
     "prf_eval_substfc_num", "prf_eval_liftfc_num"]),
  ("Etapa 3 · GuardNeg (las guardas hasWit/hasWitF)",
    ["prf_crit_In_rejects_open1", "crit_isTC1_junk_refuted_open", "CRIT_isFC1_rejects_varc", "CRIT_E2_rejects_varc",
     "crit_isFormCodeB2_rejects", "crit_isTermCodeE1_rejects", "prf_isTermCodeE1_of_In", "prf_isFormCodeE2_of_In",
     "PrfH_inst_argsIn", "prf_ex_elim_imp", "prf_neg_hasWit_zero", "prf_neg_hasWit_tag", "prf_neg_hasWit_num",
     "prf_neg_hasWit_prof2", "control_codigo_no_refutable"]),
  ("Etapa 4 · NegLineWF (por etiqueta, thy y las proyecciones a las guardas)",
    ["prf_lineWF_inv", "prf_of_tagDisj", "pcc_tag_vacuous", "prf_lineWF_cons", "prf_lineWF_neg_of_tag",
     "prf_lineWF_tag_imp", "prf_lenc_of_tag", "prf_lineWF_thy", "prf_ancla", "prf_inAxC",
     "prf_lineWF_q1_hasWit", "prf_lineWF_q2_hasWit", "prf_lineWF_leibniz_hasWitF", "prf_lenc_q1", "prf_lenc_thy"]),
  ("Etapa 5 · NegChain y NegNum",
    ["prf_chainOk_cons", "prf_allIn_cons", "prf_chainOk_iff_chainOkB", "prf_lineWF_of_chainOk",
     "prf_boundedPremsIn_of_chainOk", "prf_In_runFn_iff", "prf_runFn_nil_objList"]),
  ("Etapa 7 · Rosser (y la reducción a T de ADR‑144)",
    ["prf_diagonal", "prf_bdAll_numeral", "prf_bdAll_of_bound", "prf_lt_trichotomy", "prf_lt_succ_split",
     "prf_not_lt_zero", "liar_isSentence", "prfH_iff_prf_impChain", "formCode_impChain"])]

elab "#inventario_rosser" : command => do
  let env ← getEnv
  let mut res := "INVENTARIO de NegNum y PosNum — 2026-10-16, sondeos/InventarioRosser.lean\n"
  res := res ++ "(PURO / IMPURO por el recorrido de T08; «FUERA» si ningún nombre del build casa (vive en un sondeo, o no existe); el módulo entre corchetes)\n"
  let idx := indicePorUltimo env
  let mut (np, ni, nn) := (0, 0, 0)
  for (etapa, nombres) in piezas do
    res := res ++ s!"\n## {etapa}\n"
    for s in nombres do
      let cs := idx.getD s #[]
      if cs.isEmpty then
        res := res ++ s!"  FUERA      {s}  (no está en el build: vive en un sondeo, o no existe)\n"; nn := nn + 1
      for c in cs do
        let r := recorrer env c
        let m := moduloDe' env c
        match r.camino with
        | none => res := res ++ s!"  PURO       {nombreUsuario c}  [{m}]\n"; np := np + 1
        | some ruta =>
          res := res ++ s!"  IMPURO     {nombreUsuario c}  [{m}]  ⟶  {mostrarCamino (ruta.drop 1 |>.take 3)}\n"
          ni := ni + 1
  res := res ++ s!"\nPUROS {np} · IMPUROS {ni} · FUERA DEL BUILD {nn}\n"
  let dir : System.FilePath := "doc/registro/2026-10-16-negnum-posnum"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "pureza.txt") res
  logInfo m!"{res}"

end InventarioRosser

#inventario_rosser

import ROBINSON_PlusPlus
open Lean Elab Command

/-- ¿Existe en el entorno una constante con este nombre EXACTO? -/
elab "#existe " s:str : command => do
  let env ← getEnv
  let n := s.getString.toName
  logInfo <| if env.contains n then s!"SI existe: {n}" else s!"NO EXISTE ninguna constante llamada: {n}"

-- Los cuatro nombres que `doc/book/fragmentos.json` lista en `base_sancionada`:
#existe "ROBINSON_PlusPlus.Full.Induction.ax_induction"
#existe "ROBINSON_PlusPlus.Full.Lists.ax_list_induction"
#existe "ROBINSON_PlusPlus.Full.Mod2.ax_mod2_alternation"
#existe "ROBINSON_PlusPlus.Minimal.Axioms.prf_axiomsCodeT_eq"

-- Los nombres REALES que `#print axioms` imprime y que el script compara:
#existe "ROBINSON_PlusPlus.Full.ax_induction"
#existe "ROBINSON_PlusPlus.Full.ax_list_induction"
#existe "ROBINSON_PlusPlus.Full.ax_mod2_alternation"
#existe "ROBINSON_PlusPlus.Meta.Representability2Prf.prf_axiomsCodeT_eq"

-- La salida literal que parsea `extraer.py` (regex "'X' depends on axioms: [...]"):
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_ne
#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred

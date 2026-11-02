import ROBINSON_PlusPlus

open Lean Elab Command
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

def fmt (axs : Array Name) : String :=
  let ss := (axs.map (·.toString)).qsort (· < ·)
  s!"{axs.size} :: [" ++ String.intercalate ", " ss.toList ++ "]"

elab "#fp " ids:ident+ : command => do
  let mut out : Array String := #[]
  for id in ids do
    let n := id.getId
    let axs ← liftCoreM (Lean.collectAxioms n)
    out := out.push s!"FP {n} :: {fmt axs}"
  logInfo (String.intercalate "\n" out.toList)

/-- ¿ALGUNA constante del entorno depende de un axioma NO inventariado? -/
elab "#barrido" : command => do
  let env ← getEnv
  let sospechosos : List Name :=
    [`sorryAx, `FOL.Theorems.Neg.dne, `FOL.Theorems.Quantifiers.forall_not_impl_exists_not,
     `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]
  let mut total := 0
  let mut hits : Array String := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    if !((`ROBINSON_PlusPlus).isPrefixOf n) then continue
    total := total + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      if sospechosos.contains a then
        hits := hits.push s!"!!! {n} depende de {a}"
  logInfo <| s!"BARRIDO: {total} constantes de ROBINSON_PlusPlus revisadas\n"
    ++ (if hits.isEmpty then "  ✔ NINGUNA depende de sorryAx ni de axiomas FOL fuera de MetaRules"
        else String.intercalate "\n" hits.toList)

/-! ## ¿Es `eqc a b = eqCodeFn a b` demostrable por `rfl` puro? -/
example (a b : FOL.Term) : eqc a b = eqCodeFn a b := rfl

#fp ROBINSON_PlusPlus.Full.numeral_ne
#fp ROBINSON_PlusPlus.Meta.CodeNatInjPrf.codeNat_ne
#fp ROBINSON_PlusPlus.Meta.EvalLiftcPrf.eqc_eq_eqCodeFn_es_symm
#fp ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc

/-! ## Los controles de LiftcCodePrf que el docstring :1015 promete NET-0 -/
#fp ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn
#fp ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole
#fp ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift
#fp ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_termCode
#fp ROBINSON_PlusPlus.Meta.EvalNthcPrf.pcc_nthc_zero_code
#fp ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons
#fp ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked

#barrido

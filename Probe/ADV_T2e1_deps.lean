import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-!
# VERIFICACION ADVERSARIAL de `Probe/T2_e1.lean`

Cierra el hueco metodologico del original: alli `#deps` midio COPIAS `def` (`MED_*`) en el
namespace `MEDIDA`, no los `theorem` reales dentro de `SinWTs`. Aqui se apaga
`Elab.async`, con lo que los `theorem` SI exponen su cuerpo, y se miden LOS DE VERDAD,
con los NOMBRES DEFINITIVOS y en el NAMESPACE definitivo.
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.MpCodePrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace ROBINSON_PlusPlus.Meta.CodeWitnessPrf

namespace SinWTs

/-! ## BLOQUE A, TAL CUAL, con los NOMBRES REALES (sin prima).
    Que estas declaraciones se acepten prueba ademas que NO hay colision de nombres
    dentro de `SinWTs`. -/

theorem prf_isTermCodeE1_of_boundedIn (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAll1, liftF_isTermCodeE1]
  refine deduction_aux ?_ (wfAll1 (liftTerm 0 w)) _ rfl
  have hwf : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (liftTerm 0 w))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) hwf) hlt
  exact PrfH_congr_isTermCodeE1 heq hitc

theorem prf_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (prf_isTermCodeE1_of_boundedIn w c)

end SinWTs

end ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! ## MEDIDA SOBRE LOS TEOREMAS REALES -/

open Lean Elab Command in
elab "#deps " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let pref : Name := `ROBINSON_PlusPlus.Meta.CodeWitnessPrf
  -- ⚠️ `env.find?` (BLOQUEANTE), no `env.findAsync?`: este ultimo devuelve la CABECERA y
  --    por eso el original creyo que los `theorem` «no exponen su cuerpo».
  let some ci := env.find? n | throwError "no existe {n}"
  let some v := ci.value? | throwError "{n}: SIN CUERPO en el entorno"
  let mut mx : Nat := 0
  let mut out : Array String := #[]
  -- constantes del VALOR *y* del TIPO (el original solo miro el valor)
  let used := v.getUsedConstants ++ ci.type.getUsedConstants
  for c in used do
    if pref.isPrefixOf c then
      let r ← liftCoreM <| findDeclarationRanges? c
      let ln : Nat := match r with | some rr => rr.range.pos.line | none => 0
      if ln > mx then mx := ln
      out := out.push s!"    {c}  @ {ln}"
  logInfo s!"{n} — MAXIMO = {mx}\n{String.intercalate "\n" out.toList}"

#deps ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn
#deps ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In

#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In

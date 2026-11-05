/- # `sondeos/CongruenciaHueco.lean` — las 19 congruencias internas `pcc_congr_*_code`, corolarios de UN genérico

   ✏️ 2026‑11‑05 (ADR‑261): el genérico `pcc_congr_hole_code` está en el BUILD (`Meta/EvalArithPrf.lean`), y las 19
   copias del build son sus corolarios. Este sondeo lo probó (T48, ADR‑247: el genérico de
   `Probe/B3_planos_dedup_kit.lean` —archivado en la etiqueta `archivo/probe-2026-11-02`—, adaptado a la guarda de
   testigo, daba las 19 con su enunciado literal, `rfl` contra cada copia); esa versión, en la historia de git
   (`f67a8f7:sondeos/CongruenciaHueco.lean`). Aquí queda la MEDIDA de que la sustitución está hecha y sigue hecha:

     §1 — por cada una de las 19, qué constantes nombra su prueba: TIENE que nombrar el genérico (o otra de las 19, que
          lo nombra) y NINGUNA pieza de Leibniz (`pcc_leibniz_apply`, `pcc_leibniz_apply_imp`, `PrfH_leibniz_apply`,
          `pcc_leibniz_code`): si alguna volviera a copiar la prueba, sale rojo.
     §2 — controles: el genérico SÍ nombra Leibniz, y `pcc_eq_trans_code_imp` (una prueba de Leibniz que no es una
          congruencia de un hueco) sale con Leibniz propio y sin el genérico: el detector ve las dos cosas.

   Lo mide sobre las constantes del build; no declara ningún teorema. -/
import ROBINSON_PlusPlus.Meta
import Lean

open Lean Elab Command

namespace CongruenciaHueco

/-- El genérico. -/
def generico : Name := ``ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_hole_code

/-- Las 19, en el orden de `git grep -n "^theorem pcc_congr_"` sobre `ROBINSON_PlusPlus/`. El doble acento grave las
    resuelve al compilar: si una desaparece o cambia de nombre, esto no compila. -/
def diecinueve : List Name := [
  ``ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_2_code,
  ``ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_1_code,
  ``ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_unT_code,
  ``ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code,
  ``ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code_imp,
  ``ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.pcc_congr_carcT_code_imp,
  ``ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_congr_liftfcT_arg2_code,
  ``ROBINSON_PlusPlus.Meta.EvalMulPrf.pcc_congr_addcT1_code_imp,
  ``ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_congr_predcT_code,
  ``ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_congr_substfcT_arg2_code,
  ``ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_congr_substtcT_arg3_code,
  ``ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_congr_substtscT_arg3_code,
  ``ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_liftcT_arg2_code,
  ``ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_liftscT_arg2_code,
  ``ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg2_code,
  ``ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code,
  ``ROBINSON_PlusPlus.Meta.LineWFTrackedPrf.pcc_congr_eqcT_diag_code_imp,
  ``ROBINSON_PlusPlus.Meta.SubstfcCodePrf.pcc_congr_substfcT_arg3_code,
  ``ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_congr_nthcT_arg1_code]

/-- Las piezas de Leibniz con las que cada copia hacía su prueba. -/
def leibniz : List Name := [
  ``ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_leibniz_apply,
  ``ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_leibniz_apply_imp,
  ``ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_leibniz_apply,
  ``ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.pcc_leibniz_code]

/-- Lo que nombra la prueba de `n`: (¿el genérico, o otra de las 19?, las piezas de Leibniz que nombra). -/
def mira (env : Environment) (n : Name) : Except String (Bool × List Name) := do
  let some ci := env.find? n | throw s!"{n}: no está en el entorno"
  let some v := ci.value? (allowOpaque := true) | throw s!"{n}: no tiene valor"
  let usa := v.getUsedConstants
  let gen := usa.contains generico || diecinueve.any (fun m => m != n && usa.contains m)
  return (gen, leibniz.filter usa.contains)

/-! ## §1 · LAS 19: cada una, por el genérico y sin Leibniz propio -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut malas : Nat := 0
  for n in diecinueve do
    match mira env n with
    | .error e => logError e; malas := malas + 1
    | .ok (gen, lb) =>
      let bien := gen && lb.isEmpty
      unless bien do malas := malas + 1
      logInfo m!"{if bien then "✓" else "✗"} {n.componentsRev.head!} · genérico: {gen} · Leibniz propio: {lb}"
  if malas = 0 then
    logInfo m!"✅ las {diecinueve.length} congruencias internas son corolarios del genérico; ninguna copia Leibniz"
  else
    logError m!"❌ {malas} de las {diecinueve.length} no van por el genérico o copian Leibniz"

/-! ## §2 · CONTROLES: el detector ve el genérico y ve Leibniz -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  -- el genérico: Leibniz SÍ (es donde vive la prueba)
  match mira env generico with
  | .ok (_, lb) =>
    if lb.isEmpty then logError m!"❌ control: el genérico no nombra Leibniz; el detector está ciego"
    else logInfo m!"✓ control: el genérico nombra {lb}"
  | .error e => logError e
  -- una prueba de Leibniz que no es una congruencia de un hueco: Leibniz propio y sin el genérico
  let t := ``ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_eq_trans_code_imp
  match mira env t with
  | .ok (gen, lb) =>
    if gen || lb.isEmpty then logError m!"❌ control: {t} debería salir sin genérico y con Leibniz ({gen}, {lb})"
    else logInfo m!"✓ control: {t} sale sin el genérico y con Leibniz propio {lb}"
  | .error e => logError e

end CongruenciaHueco

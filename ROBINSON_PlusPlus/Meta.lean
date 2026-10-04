/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Barrel file for `Meta/` — Gödelización del sistema `Minimal`.
Public API:
  · Godel          (Nivel B): G, ⌜·⌝, Teo G1 (encode_injective)
  · Provability    (Nivel C): formCode, IsFormula (núcleo real de codificación)
  · Nivel D, sobre el cálculo finitario `Prf`: verificador estructural
    (provCodeC'/chainOk/runFn); D1 `repr_pos'_prf`, D2 `d2_prf`, D3 `d3_prf_real`;
    punto fijo `prf_godelCN_fixedpoint`; Gödel I y II `goedel_first_prf` /
    `goedel_second_prf (hcon : ConsistentH)` (Meta/GodelTwoPrf.lean).
    🏁 Desde ADR‑117, con `ConsistentH` como ÚNICA hipótesis: el ancla de `axiomsCodeT` es un teorema
    (`prf_ancla`, instancia `instAnclaEq`). Hasta ese día eran VACUOS: `[AnclaEq]` daba `Prf ⊥` (F1,
    ADR‑114). ⚠️ La consistencia de los 142 axiomas no está probada (no hay modelo).

  🗑️ 2026‑10‑02 (ADR‑115): la capa `⊢` quedó retirada, y con ella lo que este barril anunciaba
  sobre ella — `Provable`, `godelCN_fixedpoint`, `goedel_first_numeral`, `d3` (D3 sobre `⊢`),
  `NegVerifier` y la mitad `⊬¬G`. (`goedel_second'` se retiró el 2026‑09‑11; `godelC'_fixedpoint`
  y `goedel_first_real'`, con la reparación de ADR‑012.)

  Nota (F7a, 2026‑07‑09): retirada la capa Gödel LEGACY postulada — el módulo
  `Meta/Incompleteness.lean` (Gödel I/II vía D2/D3 postulados) y los 7 postulados
  que consumía (`Dem`/`dem_iff_provable`/`provFormula`/`provFormula_repr`/
  `diagonal_lemma` en Provability + `D2`/`D3` en Incompleteness). La cadena real no
  los citaba (auditado con `#print axioms`).
-/
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.HasWitTcFnPrf
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.HilbertSeq
import ROBINSON_PlusPlus.Meta.CodeArith
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.Diagonal
import ROBINSON_PlusPlus.Meta.CodeDistinct
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.Representability2
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.Representability2Prf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.ReflectionPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NatOrderPrf
import ROBINSON_PlusPlus.Meta.NatMulPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.Div2ParityPrf
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.DiagonalNumeral
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalMulPrf
import ROBINSON_PlusPlus.Meta.ExIntroCodePrf
import ROBINSON_PlusPlus.Meta.ForallElimCodePrf
import ROBINSON_PlusPlus.Meta.LineWFCases
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.OmegaReflect
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1TrackedPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
import ROBINSON_PlusPlus.Meta.Sigma1BoundedPrf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
import ROBINSON_PlusPlus.Meta.ListEtaPrf
import ROBINSON_PlusPlus.Meta.PremsOfTagPrf
import ROBINSON_PlusPlus.Meta.PremsOfDotPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.EvalBoundedPrf
import ROBINSON_PlusPlus.Meta.EvalNthcPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.D3DottedPrf
import ROBINSON_PlusPlus.Meta.PropCodePrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.D3InDotPrf
import ROBINSON_PlusPlus.Meta.BdAllIntroPrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.LineWFMpPrf
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.EvalPredPrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.CodeNatInjPrf
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.SubstfcCodePrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
import ROBINSON_PlusPlus.Meta.LineWFEfqPrf
import ROBINSON_PlusPlus.Meta.CodeTreeReflect
import ROBINSON_PlusPlus.Meta.LineWFPropPrf
import ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
import ROBINSON_PlusPlus.Meta.LineWFThyPrf
import ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
import ROBINSON_PlusPlus.Meta.LineWFConsPrf
import ROBINSON_PlusPlus.Meta.CodeDecode
import ROBINSON_PlusPlus.Meta.ChainDecode
import ROBINSON_PlusPlus.Meta.DiagonalTwo
import ROBINSON_PlusPlus.Meta.GodelTwo
import ROBINSON_PlusPlus.Meta.EvalSubsttcPrf
import ROBINSON_PlusPlus.Meta.LineWFGuardPrf
import ROBINSON_PlusPlus.Meta.EvalSubstfcPrf
import ROBINSON_PlusPlus.Meta.D3ChainDotPrf
import ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
import ROBINSON_PlusPlus.Meta.HasWitTrackedPrf
import ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf
import ROBINSON_PlusPlus.Meta.SubstTreeReflect
import ROBINSON_PlusPlus.Meta.EvalLiftfcPrf
import ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf
import ROBINSON_PlusPlus.Meta.D3BodyPrf
import ROBINSON_PlusPlus.Meta.PremsBdAllPrf
import ROBINSON_PlusPlus.Meta.VerifierSound
import ROBINSON_PlusPlus.Meta.ChainNegPrf
import ROBINSON_PlusPlus.Meta.GodelTwoPrf
import FOL.Deduction
import FOL.FOL
import FOL.Theorems.Derived
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Quantifiers
import ROBINSON_PlusPlus.Full.Induction

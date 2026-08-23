/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Barrel file for `Meta/` — Gödelización del sistema `Minimal`.
Public API:
  · Godel          (Nivel B): G, ⌜·⌝, Teo G1 (encode_injective)
  · Provability    (Nivel C): formCode, IsFormula, Provable (núcleo real de codificación)
  · Nivel D REAL: verificador estructural (provCodeC'/chainOk/runFn) + D1/D2 reales +
    punto fijo real (godelC'_fixedpoint) + Gödel I real (goedel_first_real') +
    Gödel II (goedel_second', módulo el axioma d3).

  Nota (F7a, 2026‑07‑09): retirada la capa Gödel LEGACY postulada — el módulo
  `Meta/Incompleteness.lean` (Gödel I/II vía D2/D3 postulados) y los 7 postulados
  que consumía (`Dem`/`dem_iff_provable`/`provFormula`/`provFormula_repr`/
  `diagonal_lemma` en Provability + `D2`/`D3` en Incompleteness). La cadena real no
  los citaba (auditado con `#print axioms`).
-/
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.HilbertSeq
import ROBINSON_PlusPlus.Meta.CodeArith
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.StepArith
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.Necessitation
import ROBINSON_PlusPlus.Meta.Diagonal
import ROBINSON_PlusPlus.Meta.CodeDistinct
import ROBINSON_PlusPlus.Meta.Induction
import ROBINSON_PlusPlus.Meta.ListInductionArith
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.DerivCond
import ROBINSON_PlusPlus.Meta.Representability2
import ROBINSON_PlusPlus.Meta.Reflection
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.LineWFDerives
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
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.EvalBoundedPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.D3DottedPrf
import ROBINSON_PlusPlus.Meta.PropCodePrf
import ROBINSON_PlusPlus.Meta.LineWFConsPrf
import ROBINSON_PlusPlus.Meta.AxiomListCode
import ROBINSON_PlusPlus.Meta.CodeDecode
import ROBINSON_PlusPlus.Meta.ChainDecode
import ROBINSON_PlusPlus.Meta.DiagonalTwo
import ROBINSON_PlusPlus.Meta.GodelTwo

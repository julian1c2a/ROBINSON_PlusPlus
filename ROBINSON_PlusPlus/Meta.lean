/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Barrel file for `Meta/` — Gödelización del sistema `Minimal`. (✏️ 2026‑10‑12, ADR‑134: de `T_Prf`, el cálculo
`Prf` —con `ind`, `listInd`, `p3` y `qconf`— sobre los 142 axiomas de `Minimal`: `AXIOMS.md` §0.)
Public API:
  · Godel          (Nivel B): G, ⌜·⌝, Teo G1 (encode_injective)
  · Provability    (Nivel C): formCode, IsFormula (núcleo real de codificación)
  · Nivel D, sobre el cálculo finitario `Prf`: verificador estructural
    (provCodeC'/chainOk/runFn); D1 `repr_pos'_prf`, D2 `d2_prf`, D3 `d3_prf_real`;
    punto fijo `prf_godelCN_fixedpoint`; Gödel I y II `goedel_first_prf` /
    `goedel_second_prf (hcon : ConsistentH)` (Meta/GodelTwoPrf.lean).
    🏁 Desde ADR‑117, con `ConsistentH` como ÚNICA hipótesis: el ancla de `axiomsCodeT` es un teorema
    (`prf_ancla`; la clase `AnclaEq`, retirada con ADR‑118). Hasta ese día eran VACUOS: `[AnclaEq]` daba `Prf ⊥` (F1,
    ADR‑114). 🏁 La consistencia de `T_Prf` —los 142 con los esquemas de `Prf`— está probada desde ADR‑120
    (`consistencia : ConsistentH`: `MNV V₀`, un modelo estándar de los 142, y `prf_sound`; ✏️ 2026‑10‑14: decía
    «La consistencia de los 142»).
  · ✏️ 2026‑10‑14 (ADR‑134), sin hipótesis: `consistencia`, `goedel_I`, `goedel_II` (Meta/Consistencia.lean,
    ADR‑120); `goedel_I_neg` y `godelCN_indecidible` (Meta/SolidezVerificador.lean, ADR‑121: Gödel I entero);
    `tarski`, `tarski_semantico` (Meta/TarskiPrf.lean, ADR‑121).
  · ✏️ 2026‑10‑16 (ADR‑143, T08): `Meta/PurezaTitulares.lean`, el CONTROL de pureza: el build FALLA si el cierre de un
    titular de la clase (i) nombra la semántica (`FOL.Metamath.Semantics`, `Meta.SolidezPrf`), o si `goedel_I` y `tarski`
    dejan de nombrarla.
  · ✏️ 2026‑10‑17 (ADR‑148): `Meta/RosserW1.lean`, la primera etapa de Rosser (ADR‑146/147): `w1Ax`, W1 con el código
    de los 142 en lugar de `V₀`, sin el modelo, con su `#pureza`.
  · ✏️ 2026‑10‑17 (ADR‑149): `Meta/RosserPosNum.lean`, la etapa 6 de Rosser: `posNum`, D1 con el testigo en forma de
    NUMERAL (`prf_proofCode'_numeral`), con su `#pureza`.
  · ✏️ 2026‑10‑17 (ADR‑150): `Meta/RosserNumerales.lean`, la etapa 1 de Rosser: la capa de listas sobre numerales
    (descomponer, `carc`/`cdrc`/`lenc`/`nthc`, los constructores de código, `In` y `runFn` decididos), con su `#pureza`.
  · ✏️ 2026‑10‑17 (ADR‑152): `Meta/RosserNumEval.lean`, la etapa 2 de Rosser: `substtc`/`liftc`/`substfc`/`liftfc`
    evaluados sobre numerales con las guardas verdaderas (`prf_substfc_guarda`), con su `#pureza`.
  · ✏️ 2026‑10‑17 (ADR‑153): `Meta/RosserGuardNeg.lean`, la etapa 3 de Rosser: la guarda FALSA se refuta
    (`prf_neg_hasWit`, `prf_neg_hasWitF`), y decidida (`hasWit_decide`), con su `#pureza`.
  · ✏️ 2026‑10‑17 (ADR‑154): `Meta/RosserNegLinea.lean`, la etapa 4 de Rosser: la línea mala se refuta
    (`prf_neg_lineWF`), y la buena formación de una línea queda decidida (`lineWF_decide`), con su `#pureza`.
  · ✏️ 2026‑10‑17 (ADR‑156): `Meta/RosserNegNum.lean`, la etapa 5 de Rosser: el predicado de prueba de T, decidido
    sobre numerales (`proofN_decide`, `negNum`), y NegNum′ con W1(ax) (`negNum'`, `negNum_formCode`), con su `#pureza`.
  · ✏️ 2026‑10‑18 (ADR‑157): 🏁 `Meta/Rosser.lean`, ROSSER por la reducción: `rosser_ext` (si T+E es consistente, su
    sentencia de Rosser es indecidible en T+E), `rosser_red` (toda lista E) y `rosser` (T, sin hipótesis), con su
    `#pureza`. `rosser_ext` entra en `PUROS` y `rosser` en `IMPUROS`; para eso, el recorrido y `#pureza` pasan a
    `Meta/PurezaComando.lean`, y `Meta/PurezaTitulares.lean`, la lista, importa Rosser.
  · ✏️ 2026‑10‑18 (ADR‑159): 🏁 `Meta/Lob.lean`, LÖB: `lob : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ` y `lob_iff`, por el punto
    fijo de `Prov(#0) ⇒ φ` y D1–D3; Gödel II, de corolario (`goedel_second_de_lob`). `lob` entra en `PUROS`.
  · ✏️ 2026‑10‑18 (ADR‑160, T66): fuera del build el subárbol sin consumidor —`ChainNegPrf`, `VerifierSound`,
    `OmegaReflect`, `ChainDecode` y `CodeDecode`—, sin ninguna declaración en el cono de los 21 titulares; se recupera
    de la etiqueta `archivo/t66-2026-10-18`.
  · ✏️ 2026‑10‑18 (ADR‑161): y, aprobado el paso 3 de ADR‑139, `CodeDistinct`, `ReflectionPrf`, `Sigma1TrackedPrf` y
    `Sigma1BoundedPrf` (con los dos teoremas vacuos de T05), sin nada en el cono; etiqueta
    `archivo/fuera-del-cono-2026-10-18`.
  · ✏️ 2026‑10‑18 (ADR‑162, T78): `Meta/GodelCorolarios.lean`, los corolarios de libro de Gödel II:
    `prf_godel_iff_con : Prf (G ⇔ Con')`, `goedel_second_formalizado : Prf (Con' ⇒ ¬Prov⌜Con'⌝)` y `con_indecidible`.
  · ✏️ 2026‑10‑20 (ADR‑173, T75e): `Meta/RigidezEstandar.lean`, W1 y E10 en TODO modelo estándar:
    `prf_of_prov_de`, `modelo_prov_iff_de`, `godelCN_verdadera_de` y `con_verdadera_de`.
  · ✏️ 2026‑10‑20 (ADR‑175, T75): `tarski_semantico_de` (Tarski en todo modelo estándar, `Meta/TarskiPrf.lean`);
    `control_ancla` (sin el ancla, `Prov` puede mentir: `MNV V⊥` cree demostrable `⊥`, `Meta/RigidezEstandar.lean`);
    y `Meta/SegundoModelo.lean`, un segundo modelo estándar, distinto de `MNV V₀` (`segundo_modelo`).

  🗑️ 2026‑10‑02 (ADR‑115): la capa `⊢` quedó retirada, y con ella lo que este barril anunciaba
  sobre ella — `Provable`, `godelCN_fixedpoint`, `goedel_first_numeral`, `d3` (D3 sobre `⊢`),
  `NegVerifier` y la mitad `⊬¬G`. (`goedel_second'` se retiró el 2026‑09‑11; `godelC'_fixedpoint`
  y `goedel_first_real'`, con la reparación de ADR‑012.) (✏️ 2026‑10‑14, ADR‑134: la mitad `⊬¬G` volvió,
  sobre `Prf`, con ADR‑121: `goedel_I_neg`, por la solidez del verificador en `MNV V₀`.)

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
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.Diagonal
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.Representability2
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.Representability2Prf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
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
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
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
import ROBINSON_PlusPlus.Meta.GodelTwoPrf
import ROBINSON_PlusPlus.Meta.ModeloCodigo
import ROBINSON_PlusPlus.Meta.ModeloEstandar
import ROBINSON_PlusPlus.Meta.ModeloCodificacion
import ROBINSON_PlusPlus.Meta.SolidezPrf
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.SolidezVerificador
import ROBINSON_PlusPlus.Meta.PurezaComando
import ROBINSON_PlusPlus.Meta.RosserW1
import ROBINSON_PlusPlus.Meta.RosserPosNum
import ROBINSON_PlusPlus.Meta.RosserNumerales
import ROBINSON_PlusPlus.Meta.RosserNumEval
import ROBINSON_PlusPlus.Meta.RosserGuardNeg
import ROBINSON_PlusPlus.Meta.RosserNegLinea
import ROBINSON_PlusPlus.Meta.RosserNegNum
import ROBINSON_PlusPlus.Meta.Rosser
import ROBINSON_PlusPlus.Meta.Lob
import ROBINSON_PlusPlus.Meta.GodelCorolarios
import ROBINSON_PlusPlus.Meta.RigidezEstandar
import ROBINSON_PlusPlus.Meta.SegundoModelo
import ROBINSON_PlusPlus.Meta.PurezaTitulares
-- (✏️ 2026‑10‑19, ADR‑170, T74: `FOL.Deduction`, `FOL.Theorems.Derived`, `Impl` y `Neg`, sin nada en el cono, fuera.)
import FOL.FOL
import FOL.Theorems.Eq
import FOL.Theorems.Quantifiers
import ROBINSON_PlusPlus.Full.Induction

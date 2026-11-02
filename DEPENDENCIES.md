# Diagrama de Dependencias — ROBINSON_PlusPlus

**Last updated:** 2026-11-02 — GENERADO por `python3 gen-dependencies.py` desde las líneas `import`; no se edita a mano.
**Autor**: Julián Calderón Almendros

> ⚠️ Este fichero se **calcula** (T30, ADR‑238). Para actualizarlo: `python3 gen-dependencies.py`; para comprobar
> que está al día: `python3 gen-dependencies.py --check`, que corre en la CI de RPP. El DEPENDENCIES.md escrito a mano
> se sustituyó el 2026‑11‑02: desde ADR‑115 describía un árbol de 131 módulos que ya no existía. Está, tal cual, en la
> historia de git (`git show 6cdd2dd:DEPENDENCIES.md`).

## Cifras

* **119 módulos activos** (Minimal 2 + Meta 116 + Full 1), **389 aristas** `import` entre ellos, profundidad máxima **59**. Sin ciclos.
* 1 `lean_lib`, `ROBINSON_PlusPlus`, con `globs := #[.andSubmodules …]`: el build compila el barril
  y TODO su directorio (T15, ADR‑163). Que todo módulo esté además en el cierre de imports del barril lo comprueba [L]
  de `check-doc-sync.bash`, y la cifra de módulos activos de arriba la compara [A] con la suya.
* Imports externos de FOL, el único `require`: `FOL.Canonical0` (1), `FOL.Derives1` (1), `FOL.FOL` (18), `FOL.Lift0` (1), `FOL.Semantics` (2), `FOL.Sentence` (1), `FOL.SymLit` (1), `FOL.Theorems.Eq` (15), `FOL.Theorems.Quantifiers` (8) —entre paréntesis, cuántos módulos lo importan directamente; los barriles, aparte—. De fuera de FOL: ninguno.

## Por niveles (camino de imports más largo hasta una raíz)

* **0** — `Meta.ContratoTabla`, `Minimal.SymLit`
* **1** — `Minimal.Axioms`
* **2** — `Full.Induction`, `Meta.Godel`
* **3** — `Meta.Hilbert`, `Meta.Provability`
* **4** — `Meta.HilbertDeduction`, `Meta.HilbertSeq`, `Meta.SubstArith`
* **5** — `Meta.CheckArith`
* **6** — `Meta.ProofChain`
* **7** — `Meta.Representability`
* **8** — `Meta.Diagonal`, `Meta.ReprPrf`
* **9** — `Meta.ArithPrf`, `Meta.ChainPrf`, `Meta.NumListPrf`
* **10** — `Meta.NatArithPrf`, `Meta.SubstCodeOpenPrf`, `Meta.TcArithPrf`
* **11** — `Meta.BoundedInPrf`, `Meta.NatOrderPrf`, `Meta.NumCodeClosedPrf`
* **12** — `Meta.CodeWitnessPrf`, `Meta.NatMulPrf`, `Meta.RunFnBoundedPrf`
* **13** — `Meta.CantorMonoPrf`, `Meta.ChainOkBoundedPrf`, `Meta.Representability2`
* **14** — `Meta.DiagonalTwo`, `Meta.LineWFConsPrf`, `Meta.StrongInductionPrf`
* **15** — `Meta.Div2ParityPrf`
* **16** — `Meta.CodeNumeralPrf`
* **17** — `Meta.CodeNatInjPrf`, `Meta.DiagonalNumeral`, `Meta.Representability2Prf`, `Meta.SolidezPrf`
* **18** — `Meta.DerivCondPrf`, `Meta.ModeloCodigo`
* **19** — `Meta.ModeloEstandar`, `Meta.Sigma1Prf`, `Meta.SolidezDobleNegacion`
* **20** — `Meta.HasWitTcFnPrf`, `Meta.ModeloCodificacion`, `Meta.Sigma1CorePrf`
* **21** — `Meta.ExIntroCodePrf`, `Meta.LineWFCases`, `Meta.SubstfcWitnessPrf`
* **22** — `Meta.ListEtaPrf`, `Meta.TrackedCorePrf`
* **23** — `Meta.ForallElimCodePrf`, `Meta.Sigma1AtomPrf`
* **24** — `Meta.MpCodePrf`
* **25** — `Meta.EvalArithPrf`
* **26** — `Meta.EvalMulPrf`
* **27** — `Meta.DotConsPrf`
* **28** — `Meta.EvalListPrf`
* **29** — `Meta.EvalLtPrf`, `Meta.EvalRunFnPrf`
* **30** — `Meta.EvalBoundedPrf`, `Meta.EvalNthcPrf`
* **31** — `Meta.Delta0ReflectPrf`, `Meta.EvalCarcNthcPrf`, `Meta.PropCodePrf`
* **32** — `Meta.D3DottedPrf`
* **33** — `Meta.D3InDotPrf`
* **34** — `Meta.BdAllIntroPrf`, `Meta.InAxiomsCodePrf`
* **35** — `Meta.LineWFTrackedPrf`
* **36** — `Meta.LineWFMpPrf`, `Meta.LineWFSchemaPrf`, `Meta.LineWFThyPrf`
* **37** — `Meta.CodeCtorKit`, `Meta.LineWFGuardPrf`
* **38** — `Meta.CodeTreeReflect`, `Meta.EvalPredPrf`, `Meta.LiftcCodePrf`, `Meta.LineWFEfqPrf`
* **39** — `Meta.EvalLiftcPrf`, `Meta.LineWFPropPrf`, `Meta.SubstfcCodePrf`, `Meta.TrackedAtomsPrf`
* **40** — `Meta.D3ChainDotPrf`, `Meta.EvalSubsttcPrf`, `Meta.HasWitTrackedPrf`, `Meta.LineWFAssemblePrf`
* **41** — `Meta.EvalSubstfcPrf`, `Meta.HasWitFTrackedPrf`, `Meta.PremsOfTagPrf`
* **42** — `Meta.EvalLiftfcPrf`
* **43** — `Meta.LiftfcWitnessPrf`
* **44** — `Meta.SubstTreeReflect`
* **45** — `Meta.PremsOfDotPrf`
* **46** — `Meta.D3BodyPrf`
* **47** — `Meta.PremsBdAllPrf`
* **48** — `Meta.GodelTwo`
* **49** — `Meta.GodelTwoPrf`
* **50** — `Meta.Consistencia`
* **51** — `Meta.PurezaComando`, `Meta.SolidezVerificador`, `Meta.TarskiPrf`
* **52** — `Meta.GodelCorolarios`, `Meta.Lob`, `Meta.RosserNumerales`, `Meta.RosserPosNum`, `Meta.RosserW1`
* **53** — `Meta.RosserNumEval`
* **54** — `Meta.RigidezEstandar`, `Meta.RosserGuardNeg`
* **55** — `Meta.PuenteFOL`, `Meta.RosserNegLinea`
* **56** — `Meta.RosserNegNum`
* **57** — `Meta.ProvFiel`, `Meta.Rosser`
* **58** — `Meta.ContratoTitulares`, `Meta.SegundoModelo`
* **59** — `Meta.PurezaTitulares`

## Grafo

`A --> B` se lee «`A` importa `B`» (de abajo arriba: las raíces, arriba). Sólo las aristas entre módulos de RPP.

```mermaid
graph BT
    Full_Induction["Full.Induction"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_ArithPrf["Meta.ArithPrf"] --> Full_Induction["Full.Induction"]
    Meta_ArithPrf["Meta.ArithPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_ArithPrf["Meta.ArithPrf"] --> Meta_SubstArith["Meta.SubstArith"]
    Meta_BdAllIntroPrf["Meta.BdAllIntroPrf"] --> Meta_D3InDotPrf["Meta.D3InDotPrf"]
    Meta_BdAllIntroPrf["Meta.BdAllIntroPrf"] --> Meta_PropCodePrf["Meta.PropCodePrf"]
    Meta_BoundedInPrf["Meta.BoundedInPrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_BoundedInPrf["Meta.BoundedInPrf"] --> Meta_NumListPrf["Meta.NumListPrf"]
    Meta_CantorMonoPrf["Meta.CantorMonoPrf"] --> Meta_NatMulPrf["Meta.NatMulPrf"]
    Meta_ChainOkBoundedPrf["Meta.ChainOkBoundedPrf"] --> Meta_RunFnBoundedPrf["Meta.RunFnBoundedPrf"]
    Meta_ChainPrf["Meta.ChainPrf"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_ChainPrf["Meta.ChainPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_CheckArith["Meta.CheckArith"] --> Meta_SubstArith["Meta.SubstArith"]
    Meta_CodeCtorKit["Meta.CodeCtorKit"] --> Meta_LineWFSchemaPrf["Meta.LineWFSchemaPrf"]
    Meta_CodeCtorKit["Meta.CodeCtorKit"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_CodeNatInjPrf["Meta.CodeNatInjPrf"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"] --> Meta_Div2ParityPrf["Meta.Div2ParityPrf"]
    Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_CodeTreeReflect["Meta.CodeTreeReflect"] --> Meta_CodeCtorKit["Meta.CodeCtorKit"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_ChainPrf["Meta.ChainPrf"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_Godel["Meta.Godel"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_NatOrderPrf["Meta.NatOrderPrf"]
    Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_Consistencia["Meta.Consistencia"] --> Meta_GodelTwoPrf["Meta.GodelTwoPrf"]
    Meta_Consistencia["Meta.Consistencia"] --> Meta_ModeloCodificacion["Meta.ModeloCodificacion"]
    Meta_Consistencia["Meta.Consistencia"] --> Meta_SolidezDobleNegacion["Meta.SolidezDobleNegacion"]
    Meta_Consistencia["Meta.Consistencia"] --> Meta_SolidezPrf["Meta.SolidezPrf"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_Consistencia["Meta.Consistencia"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_GodelCorolarios["Meta.GodelCorolarios"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_Lob["Meta.Lob"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_ProvFiel["Meta.ProvFiel"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_PuenteFOL["Meta.PuenteFOL"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_RigidezEstandar["Meta.RigidezEstandar"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_Rosser["Meta.Rosser"]
    Meta_ContratoTitulares["Meta.ContratoTitulares"] --> Meta_TarskiPrf["Meta.TarskiPrf"]
    Meta_D3BodyPrf["Meta.D3BodyPrf"] --> Meta_D3ChainDotPrf["Meta.D3ChainDotPrf"]
    Meta_D3BodyPrf["Meta.D3BodyPrf"] --> Meta_PremsOfDotPrf["Meta.PremsOfDotPrf"]
    Meta_D3BodyPrf["Meta.D3BodyPrf"] --> Meta_SubstTreeReflect["Meta.SubstTreeReflect"]
    Meta_D3ChainDotPrf["Meta.D3ChainDotPrf"] --> Meta_BdAllIntroPrf["Meta.BdAllIntroPrf"]
    Meta_D3ChainDotPrf["Meta.D3ChainDotPrf"] --> Meta_ChainOkBoundedPrf["Meta.ChainOkBoundedPrf"]
    Meta_D3ChainDotPrf["Meta.D3ChainDotPrf"] --> Meta_D3DottedPrf["Meta.D3DottedPrf"]
    Meta_D3ChainDotPrf["Meta.D3ChainDotPrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_D3ChainDotPrf["Meta.D3ChainDotPrf"] --> Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"]
    Meta_D3DottedPrf["Meta.D3DottedPrf"] --> Meta_Delta0ReflectPrf["Meta.Delta0ReflectPrf"]
    Meta_D3InDotPrf["Meta.D3InDotPrf"] --> Meta_D3DottedPrf["Meta.D3DottedPrf"]
    Meta_D3InDotPrf["Meta.D3InDotPrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_Delta0ReflectPrf["Meta.Delta0ReflectPrf"] --> Meta_EvalBoundedPrf["Meta.EvalBoundedPrf"]
    Meta_DerivCondPrf["Meta.DerivCondPrf"] --> Meta_ChainPrf["Meta.ChainPrf"]
    Meta_DerivCondPrf["Meta.DerivCondPrf"] --> Meta_Representability2Prf["Meta.Representability2Prf"]
    Meta_Diagonal["Meta.Diagonal"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_Diagonal["Meta.Diagonal"] --> Meta_Representability["Meta.Representability"]
    Meta_DiagonalNumeral["Meta.DiagonalNumeral"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_DiagonalNumeral["Meta.DiagonalNumeral"] --> Meta_DiagonalTwo["Meta.DiagonalTwo"]
    Meta_DiagonalTwo["Meta.DiagonalTwo"] --> Meta_Diagonal["Meta.Diagonal"]
    Meta_DiagonalTwo["Meta.DiagonalTwo"] --> Meta_Representability2["Meta.Representability2"]
    Meta_Div2ParityPrf["Meta.Div2ParityPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_Div2ParityPrf["Meta.Div2ParityPrf"] --> Meta_NatMulPrf["Meta.NatMulPrf"]
    Meta_Div2ParityPrf["Meta.Div2ParityPrf"] --> Meta_StrongInductionPrf["Meta.StrongInductionPrf"]
    Meta_DotConsPrf["Meta.DotConsPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_DotConsPrf["Meta.DotConsPrf"] --> Meta_Div2ParityPrf["Meta.Div2ParityPrf"]
    Meta_DotConsPrf["Meta.DotConsPrf"] --> Meta_EvalMulPrf["Meta.EvalMulPrf"]
    Meta_DotConsPrf["Meta.DotConsPrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_DotConsPrf["Meta.DotConsPrf"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_DotConsPrf["Meta.DotConsPrf"] --> Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"]
    Meta_EvalArithPrf["Meta.EvalArithPrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_EvalArithPrf["Meta.EvalArithPrf"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_EvalArithPrf["Meta.EvalArithPrf"] --> Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"]
    Meta_EvalArithPrf["Meta.EvalArithPrf"] --> Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"]
    Meta_EvalBoundedPrf["Meta.EvalBoundedPrf"] --> Meta_EvalLtPrf["Meta.EvalLtPrf"]
    Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"] --> Meta_EvalNthcPrf["Meta.EvalNthcPrf"]
    Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"] --> Meta_LineWFConsPrf["Meta.LineWFConsPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_ChainPrf["Meta.ChainPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_EvalRunFnPrf["Meta.EvalRunFnPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_LiftcCodePrf["Meta.LiftcCodePrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_NatOrderPrf["Meta.NatOrderPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_NumListPrf["Meta.NumListPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_Provability["Meta.Provability"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_Sigma1Prf["Meta.Sigma1Prf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_StrongInductionPrf["Meta.StrongInductionPrf"]
    Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"] --> Meta_TrackedCorePrf["Meta.TrackedCorePrf"]
    Meta_EvalLiftfcPrf["Meta.EvalLiftfcPrf"] --> Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"]
    Meta_EvalLiftfcPrf["Meta.EvalLiftfcPrf"] --> Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"]
    Meta_EvalListPrf["Meta.EvalListPrf"] --> Meta_DotConsPrf["Meta.DotConsPrf"]
    Meta_EvalListPrf["Meta.EvalListPrf"] --> Meta_EvalArithPrf["Meta.EvalArithPrf"]
    Meta_EvalListPrf["Meta.EvalListPrf"] --> Meta_NumListPrf["Meta.NumListPrf"]
    Meta_EvalLtPrf["Meta.EvalLtPrf"] --> Meta_EvalListPrf["Meta.EvalListPrf"]
    Meta_EvalLtPrf["Meta.EvalLtPrf"] --> Meta_ExIntroCodePrf["Meta.ExIntroCodePrf"]
    Meta_EvalMulPrf["Meta.EvalMulPrf"] --> Meta_EvalArithPrf["Meta.EvalArithPrf"]
    Meta_EvalMulPrf["Meta.EvalMulPrf"] --> Meta_NatMulPrf["Meta.NatMulPrf"]
    Meta_EvalNthcPrf["Meta.EvalNthcPrf"] --> Meta_DotConsPrf["Meta.DotConsPrf"]
    Meta_EvalNthcPrf["Meta.EvalNthcPrf"] --> Meta_EvalLtPrf["Meta.EvalLtPrf"]
    Meta_EvalNthcPrf["Meta.EvalNthcPrf"] --> Meta_EvalRunFnPrf["Meta.EvalRunFnPrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_CodeCtorKit["Meta.CodeCtorKit"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_EvalArithPrf["Meta.EvalArithPrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"]
    Meta_EvalPredPrf["Meta.EvalPredPrf"] --> Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"]
    Meta_EvalRunFnPrf["Meta.EvalRunFnPrf"] --> Meta_EvalListPrf["Meta.EvalListPrf"]
    Meta_EvalRunFnPrf["Meta.EvalRunFnPrf"] --> Meta_RunFnBoundedPrf["Meta.RunFnBoundedPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_D3InDotPrf["Meta.D3InDotPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_Delta0ReflectPrf["Meta.Delta0ReflectPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_ForallElimCodePrf["Meta.ForallElimCodePrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_LiftcCodePrf["Meta.LiftcCodePrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_PropCodePrf["Meta.PropCodePrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"]
    Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_D3InDotPrf["Meta.D3InDotPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_Delta0ReflectPrf["Meta.Delta0ReflectPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_EvalLiftcPrf["Meta.EvalLiftcPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_EvalPredPrf["Meta.EvalPredPrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_LiftcCodePrf["Meta.LiftcCodePrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_PropCodePrf["Meta.PropCodePrf"]
    Meta_EvalSubsttcPrf["Meta.EvalSubsttcPrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_ExIntroCodePrf["Meta.ExIntroCodePrf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_ExIntroCodePrf["Meta.ExIntroCodePrf"] --> Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"]
    Meta_ForallElimCodePrf["Meta.ForallElimCodePrf"] --> Meta_ExIntroCodePrf["Meta.ExIntroCodePrf"]
    Meta_ForallElimCodePrf["Meta.ForallElimCodePrf"] --> Meta_TrackedCorePrf["Meta.TrackedCorePrf"]
    Meta_Godel["Meta.Godel"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_GodelCorolarios["Meta.GodelCorolarios"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_GodelCorolarios["Meta.GodelCorolarios"] --> Meta_SolidezVerificador["Meta.SolidezVerificador"]
    Meta_GodelTwo["Meta.GodelTwo"] --> Meta_PremsBdAllPrf["Meta.PremsBdAllPrf"]
    Meta_GodelTwo["Meta.GodelTwo"] --> Meta_ProofChain["Meta.ProofChain"]
    Meta_GodelTwo["Meta.GodelTwo"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_GodelTwo["Meta.GodelTwo"] --> Meta_Representability2["Meta.Representability2"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_DiagonalNumeral["Meta.DiagonalNumeral"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_DiagonalTwo["Meta.DiagonalTwo"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_GodelTwo["Meta.GodelTwo"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_LineWFCases["Meta.LineWFCases"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_PremsBdAllPrf["Meta.PremsBdAllPrf"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_Representability2Prf["Meta.Representability2Prf"]
    Meta_GodelTwoPrf["Meta.GodelTwoPrf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_HasWitFTrackedPrf["Meta.HasWitFTrackedPrf"] --> Meta_HasWitTrackedPrf["Meta.HasWitTrackedPrf"]
    Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"] --> Meta_NumListPrf["Meta.NumListPrf"]
    Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"] --> Meta_Sigma1Prf["Meta.Sigma1Prf"]
    Meta_HasWitTrackedPrf["Meta.HasWitTrackedPrf"] --> Meta_LiftcCodePrf["Meta.LiftcCodePrf"]
    Meta_HasWitTrackedPrf["Meta.HasWitTrackedPrf"] --> Meta_LineWFGuardPrf["Meta.LineWFGuardPrf"]
    Meta_HasWitTrackedPrf["Meta.HasWitTrackedPrf"] --> Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"]
    Meta_Hilbert["Meta.Hilbert"] --> Full_Induction["Full.Induction"]
    Meta_Hilbert["Meta.Hilbert"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_HilbertDeduction["Meta.HilbertDeduction"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_HilbertSeq["Meta.HilbertSeq"] --> Meta_Godel["Meta.Godel"]
    Meta_HilbertSeq["Meta.HilbertSeq"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_HilbertSeq["Meta.HilbertSeq"] --> Meta_Provability["Meta.Provability"]
    Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"] --> Meta_D3InDotPrf["Meta.D3InDotPrf"]
    Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"] --> Meta_Representability2Prf["Meta.Representability2Prf"]
    Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"] --> Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_ChainPrf["Meta.ChainPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_CodeCtorKit["Meta.CodeCtorKit"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_Delta0ReflectPrf["Meta.Delta0ReflectPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_DotConsPrf["Meta.DotConsPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_EvalArithPrf["Meta.EvalArithPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_EvalLtPrf["Meta.EvalLtPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_EvalRunFnPrf["Meta.EvalRunFnPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_Godel["Meta.Godel"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_Provability["Meta.Provability"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_Sigma1Prf["Meta.Sigma1Prf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_LiftcCodePrf["Meta.LiftcCodePrf"] --> Meta_TrackedCorePrf["Meta.TrackedCorePrf"]
    Meta_LiftfcWitnessPrf["Meta.LiftfcWitnessPrf"] --> Meta_EvalLiftfcPrf["Meta.EvalLiftfcPrf"]
    Meta_LineWFAssemblePrf["Meta.LineWFAssemblePrf"] --> Meta_LineWFEfqPrf["Meta.LineWFEfqPrf"]
    Meta_LineWFAssemblePrf["Meta.LineWFAssemblePrf"] --> Meta_LineWFMpPrf["Meta.LineWFMpPrf"]
    Meta_LineWFAssemblePrf["Meta.LineWFAssemblePrf"] --> Meta_LineWFPropPrf["Meta.LineWFPropPrf"]
    Meta_LineWFAssemblePrf["Meta.LineWFAssemblePrf"] --> Meta_LineWFThyPrf["Meta.LineWFThyPrf"]
    Meta_LineWFCases["Meta.LineWFCases"] --> Meta_Provability["Meta.Provability"]
    Meta_LineWFCases["Meta.LineWFCases"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_LineWFCases["Meta.LineWFCases"] --> Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"]
    Meta_LineWFCases["Meta.LineWFCases"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_LineWFConsPrf["Meta.LineWFConsPrf"] --> Meta_ChainOkBoundedPrf["Meta.ChainOkBoundedPrf"]
    Meta_LineWFEfqPrf["Meta.LineWFEfqPrf"] --> Meta_CodeCtorKit["Meta.CodeCtorKit"]
    Meta_LineWFGuardPrf["Meta.LineWFGuardPrf"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_LineWFGuardPrf["Meta.LineWFGuardPrf"] --> Meta_Delta0ReflectPrf["Meta.Delta0ReflectPrf"]
    Meta_LineWFGuardPrf["Meta.LineWFGuardPrf"] --> Meta_LineWFSchemaPrf["Meta.LineWFSchemaPrf"]
    Meta_LineWFGuardPrf["Meta.LineWFGuardPrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_LineWFMpPrf["Meta.LineWFMpPrf"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_LineWFPropPrf["Meta.LineWFPropPrf"] --> Meta_CodeTreeReflect["Meta.CodeTreeReflect"]
    Meta_LineWFSchemaPrf["Meta.LineWFSchemaPrf"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_LineWFThyPrf["Meta.LineWFThyPrf"] --> Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"]
    Meta_LineWFThyPrf["Meta.LineWFThyPrf"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_BdAllIntroPrf["Meta.BdAllIntroPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_D3InDotPrf["Meta.D3InDotPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_EvalBoundedPrf["Meta.EvalBoundedPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_EvalListPrf["Meta.EvalListPrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"] --> Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"]
    Meta_ListEtaPrf["Meta.ListEtaPrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_Lob["Meta.Lob"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_Lob["Meta.Lob"] --> Meta_TarskiPrf["Meta.TarskiPrf"]
    Meta_ModeloCodificacion["Meta.ModeloCodificacion"] --> Meta_ModeloEstandar["Meta.ModeloEstandar"]
    Meta_ModeloCodigo["Meta.ModeloCodigo"] --> Meta_CodeNatInjPrf["Meta.CodeNatInjPrf"]
    Meta_ModeloCodigo["Meta.ModeloCodigo"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_ModeloEstandar["Meta.ModeloEstandar"] --> Meta_ModeloCodigo["Meta.ModeloCodigo"]
    Meta_MpCodePrf["Meta.MpCodePrf"] --> Meta_ForallElimCodePrf["Meta.ForallElimCodePrf"]
    Meta_MpCodePrf["Meta.MpCodePrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_NatArithPrf["Meta.NatArithPrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_NatArithPrf["Meta.NatArithPrf"] --> Meta_ChainPrf["Meta.ChainPrf"]
    Meta_NatMulPrf["Meta.NatMulPrf"] --> Meta_NatOrderPrf["Meta.NatOrderPrf"]
    Meta_NatOrderPrf["Meta.NatOrderPrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"] --> Meta_NatArithPrf["Meta.NatArithPrf"]
    Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"] --> Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"]
    Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_NumListPrf["Meta.NumListPrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_PremsBdAllPrf["Meta.PremsBdAllPrf"] --> Meta_D3BodyPrf["Meta.D3BodyPrf"]
    Meta_PremsOfDotPrf["Meta.PremsOfDotPrf"] --> Meta_PremsOfTagPrf["Meta.PremsOfTagPrf"]
    Meta_PremsOfDotPrf["Meta.PremsOfDotPrf"] --> Meta_SubstTreeReflect["Meta.SubstTreeReflect"]
    Meta_PremsOfTagPrf["Meta.PremsOfTagPrf"] --> Meta_LineWFAssemblePrf["Meta.LineWFAssemblePrf"]
    Meta_PremsOfTagPrf["Meta.PremsOfTagPrf"] --> Meta_LineWFSchemaPrf["Meta.LineWFSchemaPrf"]
    Meta_PremsOfTagPrf["Meta.PremsOfTagPrf"] --> Meta_ListEtaPrf["Meta.ListEtaPrf"]
    Meta_ProofChain["Meta.ProofChain"] --> Full_Induction["Full.Induction"]
    Meta_ProofChain["Meta.ProofChain"] --> Meta_CheckArith["Meta.CheckArith"]
    Meta_ProofChain["Meta.ProofChain"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_PropCodePrf["Meta.PropCodePrf"] --> Meta_EvalBoundedPrf["Meta.EvalBoundedPrf"]
    Meta_ProvFiel["Meta.ProvFiel"] --> Meta_RigidezEstandar["Meta.RigidezEstandar"]
    Meta_ProvFiel["Meta.ProvFiel"] --> Meta_RosserNegNum["Meta.RosserNegNum"]
    Meta_Provability["Meta.Provability"] --> Meta_Godel["Meta.Godel"]
    Meta_Provability["Meta.Provability"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_PuenteFOL["Meta.PuenteFOL"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_PuenteFOL["Meta.PuenteFOL"] --> Meta_RigidezEstandar["Meta.RigidezEstandar"]
    Meta_PuenteFOL["Meta.PuenteFOL"] --> Meta_TarskiPrf["Meta.TarskiPrf"]
    Meta_PurezaComando["Meta.PurezaComando"] --> Meta_Consistencia["Meta.Consistencia"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_Consistencia["Meta.Consistencia"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_ContratoTabla["Meta.ContratoTabla"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_ContratoTitulares["Meta.ContratoTitulares"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_GodelCorolarios["Meta.GodelCorolarios"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_Lob["Meta.Lob"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_Rosser["Meta.Rosser"]
    Meta_PurezaTitulares["Meta.PurezaTitulares"] --> Meta_TarskiPrf["Meta.TarskiPrf"]
    Meta_ReprPrf["Meta.ReprPrf"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_ReprPrf["Meta.ReprPrf"] --> Meta_ProofChain["Meta.ProofChain"]
    Meta_ReprPrf["Meta.ReprPrf"] --> Meta_Representability["Meta.Representability"]
    Meta_Representability["Meta.Representability"] --> Full_Induction["Full.Induction"]
    Meta_Representability["Meta.Representability"] --> Meta_CheckArith["Meta.CheckArith"]
    Meta_Representability["Meta.Representability"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_Representability["Meta.Representability"] --> Meta_HilbertSeq["Meta.HilbertSeq"]
    Meta_Representability["Meta.Representability"] --> Meta_ProofChain["Meta.ProofChain"]
    Meta_Representability["Meta.Representability"] --> Meta_SubstArith["Meta.SubstArith"]
    Meta_Representability["Meta.Representability"] --> Minimal_Axioms["Minimal.Axioms"]
    Meta_Representability2["Meta.Representability2"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_Representability2["Meta.Representability2"] --> Meta_ProofChain["Meta.ProofChain"]
    Meta_Representability2["Meta.Representability2"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_Representability2["Meta.Representability2"] --> Meta_Representability["Meta.Representability"]
    Meta_Representability2Prf["Meta.Representability2Prf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_Representability2Prf["Meta.Representability2Prf"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_Representability2Prf["Meta.Representability2Prf"] --> Meta_Representability2["Meta.Representability2"]
    Meta_Representability2Prf["Meta.Representability2Prf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_RigidezEstandar["Meta.RigidezEstandar"] --> Meta_RosserNumEval["Meta.RosserNumEval"]
    Meta_RigidezEstandar["Meta.RigidezEstandar"] --> Meta_SolidezVerificador["Meta.SolidezVerificador"]
    Meta_Rosser["Meta.Rosser"] --> Meta_RosserNegNum["Meta.RosserNegNum"]
    Meta_Rosser["Meta.Rosser"] --> Meta_TarskiPrf["Meta.TarskiPrf"]
    Meta_RosserGuardNeg["Meta.RosserGuardNeg"] --> Meta_Consistencia["Meta.Consistencia"]
    Meta_RosserGuardNeg["Meta.RosserGuardNeg"] --> Meta_RosserNumEval["Meta.RosserNumEval"]
    Meta_RosserNegLinea["Meta.RosserNegLinea"] --> Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"]
    Meta_RosserNegLinea["Meta.RosserNegLinea"] --> Meta_Representability2Prf["Meta.Representability2Prf"]
    Meta_RosserNegLinea["Meta.RosserNegLinea"] --> Meta_RosserGuardNeg["Meta.RosserGuardNeg"]
    Meta_RosserNegLinea["Meta.RosserNegLinea"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_RosserNegNum["Meta.RosserNegNum"] --> Meta_PremsOfTagPrf["Meta.PremsOfTagPrf"]
    Meta_RosserNegNum["Meta.RosserNegNum"] --> Meta_RosserNegLinea["Meta.RosserNegLinea"]
    Meta_RosserNegNum["Meta.RosserNegNum"] --> Meta_RosserPosNum["Meta.RosserPosNum"]
    Meta_RosserNegNum["Meta.RosserNegNum"] --> Meta_RosserW1["Meta.RosserW1"]
    Meta_RosserNumEval["Meta.RosserNumEval"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_RosserNumEval["Meta.RosserNumEval"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_RosserNumEval["Meta.RosserNumEval"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_RosserNumEval["Meta.RosserNumEval"] --> Meta_RosserNumerales["Meta.RosserNumerales"]
    Meta_RosserNumerales["Meta.RosserNumerales"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_RosserNumerales["Meta.RosserNumerales"] --> Meta_CodeWitnessPrf["Meta.CodeWitnessPrf"]
    Meta_RosserNumerales["Meta.RosserNumerales"] --> Meta_ModeloEstandar["Meta.ModeloEstandar"]
    Meta_RosserNumerales["Meta.RosserNumerales"] --> Meta_NumListPrf["Meta.NumListPrf"]
    Meta_RosserNumerales["Meta.RosserNumerales"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_RosserPosNum["Meta.RosserPosNum"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_RosserPosNum["Meta.RosserPosNum"] --> Meta_Representability2Prf["Meta.Representability2Prf"]
    Meta_RosserPosNum["Meta.RosserPosNum"] --> Meta_SolidezVerificador["Meta.SolidezVerificador"]
    Meta_RosserW1["Meta.RosserW1"] --> Meta_PurezaComando["Meta.PurezaComando"]
    Meta_RosserW1["Meta.RosserW1"] --> Meta_SolidezVerificador["Meta.SolidezVerificador"]
    Meta_RunFnBoundedPrf["Meta.RunFnBoundedPrf"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_SegundoModelo["Meta.SegundoModelo"] --> Meta_ProvFiel["Meta.ProvFiel"]
    Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"] --> Meta_TrackedCorePrf["Meta.TrackedCorePrf"]
    Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"] --> Meta_Sigma1Prf["Meta.Sigma1Prf"]
    Meta_Sigma1CorePrf["Meta.Sigma1CorePrf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_Sigma1Prf["Meta.Sigma1Prf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_SolidezDobleNegacion["Meta.SolidezDobleNegacion"] --> Meta_ModeloCodigo["Meta.ModeloCodigo"]
    Meta_SolidezDobleNegacion["Meta.SolidezDobleNegacion"] --> Meta_SolidezPrf["Meta.SolidezPrf"]
    Meta_SolidezPrf["Meta.SolidezPrf"] --> Meta_CodeNumeralPrf["Meta.CodeNumeralPrf"]
    Meta_SolidezPrf["Meta.SolidezPrf"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_SolidezPrf["Meta.SolidezPrf"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_SolidezVerificador["Meta.SolidezVerificador"] --> Meta_Consistencia["Meta.Consistencia"]
    Meta_SolidezVerificador["Meta.SolidezVerificador"] --> Meta_Representability["Meta.Representability"]
    Meta_StrongInductionPrf["Meta.StrongInductionPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_SubstArith["Meta.SubstArith"] --> Meta_Provability["Meta.Provability"]
    Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_SubstTreeReflect["Meta.SubstTreeReflect"] --> Meta_CodeTreeReflect["Meta.CodeTreeReflect"]
    Meta_SubstTreeReflect["Meta.SubstTreeReflect"] --> Meta_EvalLiftfcPrf["Meta.EvalLiftfcPrf"]
    Meta_SubstTreeReflect["Meta.SubstTreeReflect"] --> Meta_EvalSubstfcPrf["Meta.EvalSubstfcPrf"]
    Meta_SubstTreeReflect["Meta.SubstTreeReflect"] --> Meta_HasWitFTrackedPrf["Meta.HasWitFTrackedPrf"]
    Meta_SubstTreeReflect["Meta.SubstTreeReflect"] --> Meta_LiftfcWitnessPrf["Meta.LiftfcWitnessPrf"]
    Meta_SubstTreeReflect["Meta.SubstTreeReflect"] --> Meta_LineWFAssemblePrf["Meta.LineWFAssemblePrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_CodeCtorKit["Meta.CodeCtorKit"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_DerivCondPrf["Meta.DerivCondPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_DotConsPrf["Meta.DotConsPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_EvalArithPrf["Meta.EvalArithPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_EvalCarcNthcPrf["Meta.EvalCarcNthcPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_EvalLtPrf["Meta.EvalLtPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_Godel["Meta.Godel"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_Hilbert["Meta.Hilbert"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_HilbertDeduction["Meta.HilbertDeduction"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_LiftcCodePrf["Meta.LiftcCodePrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_MpCodePrf["Meta.MpCodePrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_Provability["Meta.Provability"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_ReprPrf["Meta.ReprPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_Sigma1AtomPrf["Meta.Sigma1AtomPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_Sigma1Prf["Meta.Sigma1Prf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_SubstCodeOpenPrf["Meta.SubstCodeOpenPrf"]
    Meta_SubstfcCodePrf["Meta.SubstfcCodePrf"] --> Meta_TcArithPrf["Meta.TcArithPrf"]
    Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"] --> Meta_BoundedInPrf["Meta.BoundedInPrf"]
    Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"] --> Meta_CantorMonoPrf["Meta.CantorMonoPrf"]
    Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"] --> Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"]
    Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"] --> Meta_NumCodeClosedPrf["Meta.NumCodeClosedPrf"]
    Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"] --> Meta_StrongInductionPrf["Meta.StrongInductionPrf"]
    Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"] --> Meta_SubstArith["Meta.SubstArith"]
    Meta_TarskiPrf["Meta.TarskiPrf"] --> Meta_Consistencia["Meta.Consistencia"]
    Meta_TarskiPrf["Meta.TarskiPrf"] --> Meta_GodelTwoPrf["Meta.GodelTwoPrf"]
    Meta_TcArithPrf["Meta.TcArithPrf"] --> Meta_ArithPrf["Meta.ArithPrf"]
    Meta_TcArithPrf["Meta.TcArithPrf"] --> Meta_Representability["Meta.Representability"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_BdAllIntroPrf["Meta.BdAllIntroPrf"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_CodeTreeReflect["Meta.CodeTreeReflect"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_D3InDotPrf["Meta.D3InDotPrf"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_InAxiomsCodePrf["Meta.InAxiomsCodePrf"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_LiftcCodePrf["Meta.LiftcCodePrf"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_LineWFTrackedPrf["Meta.LineWFTrackedPrf"]
    Meta_TrackedAtomsPrf["Meta.TrackedAtomsPrf"] --> Meta_SubstfcWitnessPrf["Meta.SubstfcWitnessPrf"]
    Meta_TrackedCorePrf["Meta.TrackedCorePrf"] --> Meta_ExIntroCodePrf["Meta.ExIntroCodePrf"]
    Meta_TrackedCorePrf["Meta.TrackedCorePrf"] --> Meta_HasWitTcFnPrf["Meta.HasWitTcFnPrf"]
    Minimal_Axioms["Minimal.Axioms"] --> Minimal_SymLit["Minimal.SymLit"]
```

## Tabla

| módulo | nivel | importa | lo importan |
|---|---|---|---|
| `Meta.ContratoTabla` | 0 | — | `Meta.PurezaTitulares` |
| `Minimal.SymLit` | 0 | — · externo: `FOL.SymLit` | `Minimal.Axioms` |
| `Minimal.Axioms` | 1 | `Minimal.SymLit` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Full.Induction`, `Meta.Godel`, `Meta.Hilbert`, `Meta.LineWFCases`, `Meta.ProofChain`, `Meta.Provability`, `Meta.Representability` |
| `Full.Induction` | 2 | `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Quantifiers` | `Meta.ArithPrf`, `Meta.Hilbert`, `Meta.ProofChain`, `Meta.Representability` |
| `Meta.Godel` | 2 | `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers` | `Meta.CodeWitnessPrf`, `Meta.HilbertSeq`, `Meta.LiftcCodePrf`, `Meta.Provability`, `Meta.SubstfcCodePrf` |
| `Meta.Hilbert` | 3 | `Full.Induction`, `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers` | `Meta.CodeWitnessPrf`, `Meta.Diagonal`, `Meta.EvalLiftcPrf`, `Meta.HilbertDeduction`, `Meta.HilbertSeq`, `Meta.LiftcCodePrf`, `Meta.ReprPrf`, `Meta.Representability`, `Meta.SolidezPrf`, `Meta.SubstfcCodePrf` |
| `Meta.Provability` | 3 | `Meta.Godel`, `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Quantifiers` | `Meta.EvalLiftcPrf`, `Meta.HilbertSeq`, `Meta.LiftcCodePrf`, `Meta.LineWFCases`, `Meta.SubstArith`, `Meta.SubstfcCodePrf` |
| `Meta.HilbertDeduction` | 4 | `Meta.Hilbert` | `Meta.ChainPrf`, `Meta.CodeWitnessPrf`, `Meta.EvalLiftcPrf`, `Meta.LiftcCodePrf`, `Meta.PuenteFOL`, `Meta.SolidezPrf`, `Meta.SubstfcCodePrf` |
| `Meta.HilbertSeq` | 4 | `Meta.Godel`, `Meta.Hilbert`, `Meta.Provability` · externo: `FOL.FOL` | `Meta.Representability` |
| `Meta.SubstArith` | 4 | `Meta.Provability` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.ArithPrf`, `Meta.CheckArith`, `Meta.Representability`, `Meta.SubstfcWitnessPrf` |
| `Meta.CheckArith` | 5 | `Meta.SubstArith` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.ProofChain`, `Meta.Representability` |
| `Meta.ProofChain` | 6 | `Full.Induction`, `Meta.CheckArith`, `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers` | `Meta.GodelTwo`, `Meta.ReprPrf`, `Meta.Representability`, `Meta.Representability2` |
| `Meta.Representability` | 7 | `Full.Induction`, `Meta.CheckArith`, `Meta.Hilbert`, `Meta.HilbertSeq`, `Meta.ProofChain`, `Meta.SubstArith`, `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers` | `Meta.Diagonal`, `Meta.ReprPrf`, `Meta.Representability2`, `Meta.SolidezVerificador`, `Meta.TcArithPrf` |
| `Meta.Diagonal` | 8 | `Meta.Hilbert`, `Meta.Representability` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.DiagonalTwo` |
| `Meta.ReprPrf` | 8 | `Meta.Hilbert`, `Meta.ProofChain`, `Meta.Representability` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.ArithPrf`, `Meta.ChainPrf`, `Meta.CodeNumeralPrf`, `Meta.CodeWitnessPrf`, `Meta.EvalLiftcPrf`, `Meta.GodelTwo`, `Meta.GodelTwoPrf`, `Meta.LiftcCodePrf`, `Meta.LineWFCases`, `Meta.NumListPrf`, `Meta.Representability2`, `Meta.SubstfcCodePrf` |
| `Meta.ArithPrf` | 9 | `Full.Induction`, `Meta.ReprPrf`, `Meta.SubstArith` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.CodeWitnessPrf`, `Meta.EvalLiftcPrf`, `Meta.GodelTwoPrf`, `Meta.LiftcCodePrf`, `Meta.NatArithPrf`, `Meta.Representability2Prf`, `Meta.SubstCodeOpenPrf`, `Meta.SubstfcCodePrf`, `Meta.TcArithPrf` |
| `Meta.ChainPrf` | 9 | `Meta.HilbertDeduction`, `Meta.ReprPrf` | `Meta.CodeWitnessPrf`, `Meta.DerivCondPrf`, `Meta.EvalLiftcPrf`, `Meta.LiftcCodePrf`, `Meta.NatArithPrf` |
| `Meta.NumListPrf` | 9 | `Meta.ReprPrf` | `Meta.BoundedInPrf`, `Meta.EvalLiftcPrf`, `Meta.EvalListPrf`, `Meta.HasWitTcFnPrf`, `Meta.RosserNumerales` |
| `Meta.NatArithPrf` | 10 | `Meta.ArithPrf`, `Meta.ChainPrf` | `Meta.BoundedInPrf`, `Meta.CodeWitnessPrf`, `Meta.EvalLiftcPrf`, `Meta.HasWitTcFnPrf`, `Meta.LiftcCodePrf`, `Meta.NatOrderPrf`, `Meta.NumCodeClosedPrf` |
| `Meta.SubstCodeOpenPrf` | 10 | `Meta.ArithPrf` | `Meta.DotConsPrf`, `Meta.EvalArithPrf`, `Meta.EvalPredPrf`, `Meta.LiftcCodePrf`, `Meta.NumCodeClosedPrf`, `Meta.SubstfcCodePrf` |
| `Meta.TcArithPrf` | 10 | `Meta.ArithPrf`, `Meta.Representability` | `Meta.GodelTwoPrf`, `Meta.LiftcCodePrf`, `Meta.NumCodeClosedPrf`, `Meta.Representability2Prf`, `Meta.Sigma1AtomPrf`, `Meta.Sigma1CorePrf`, `Meta.SubstfcCodePrf` |
| `Meta.BoundedInPrf` | 11 | `Meta.NatArithPrf`, `Meta.NumListPrf` | `Meta.CodeWitnessPrf`, `Meta.EvalLiftcPrf`, `Meta.EvalPredPrf`, `Meta.LineWFTrackedPrf`, `Meta.RosserNumEval`, `Meta.RunFnBoundedPrf`, `Meta.SubstfcWitnessPrf` |
| `Meta.NatOrderPrf` | 11 | `Meta.NatArithPrf` | `Meta.CodeWitnessPrf`, `Meta.EvalLiftcPrf`, `Meta.NatMulPrf` |
| `Meta.NumCodeClosedPrf` | 11 | `Meta.NatArithPrf`, `Meta.SubstCodeOpenPrf`, `Meta.TcArithPrf` | `Meta.DotConsPrf`, `Meta.EvalArithPrf`, `Meta.EvalPredPrf`, `Meta.LiftcCodePrf`, `Meta.RosserNumEval`, `Meta.SubstfcCodePrf`, `Meta.SubstfcWitnessPrf` |
| `Meta.CodeWitnessPrf` | 12 | `Meta.ArithPrf`, `Meta.BoundedInPrf`, `Meta.ChainPrf`, `Meta.Godel`, `Meta.Hilbert`, `Meta.HilbertDeduction`, `Meta.NatArithPrf`, `Meta.NatOrderPrf`, `Meta.ReprPrf` | `Meta.EvalLiftcPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.HasWitTcFnPrf`, `Meta.LiftcCodePrf`, `Meta.LineWFGuardPrf`, `Meta.Representability2`, `Meta.RosserNumerales` |
| `Meta.NatMulPrf` | 12 | `Meta.NatOrderPrf` | `Meta.CantorMonoPrf`, `Meta.Div2ParityPrf`, `Meta.EvalMulPrf` |
| `Meta.RunFnBoundedPrf` | 12 | `Meta.BoundedInPrf` | `Meta.ChainOkBoundedPrf`, `Meta.EvalRunFnPrf` |
| `Meta.CantorMonoPrf` | 13 | `Meta.NatMulPrf` | `Meta.Div2ParityPrf`, `Meta.DotConsPrf`, `Meta.EvalLiftcPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.StrongInductionPrf`, `Meta.SubstfcWitnessPrf` |
| `Meta.ChainOkBoundedPrf` | 13 | `Meta.RunFnBoundedPrf` | `Meta.D3ChainDotPrf`, `Meta.LineWFConsPrf` |
| `Meta.Representability2` | 13 | `Meta.CodeWitnessPrf`, `Meta.ProofChain`, `Meta.ReprPrf`, `Meta.Representability` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.DiagonalTwo`, `Meta.GodelTwo`, `Meta.Representability2Prf` |
| `Meta.DiagonalTwo` | 14 | `Meta.Diagonal`, `Meta.Representability2` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.DiagonalNumeral`, `Meta.GodelTwoPrf` |
| `Meta.LineWFConsPrf` | 14 | `Meta.ChainOkBoundedPrf` | `Meta.EvalCarcNthcPrf` |
| `Meta.StrongInductionPrf` | 14 | `Meta.CantorMonoPrf` | `Meta.Div2ParityPrf`, `Meta.EvalLiftcPrf`, `Meta.SubstfcWitnessPrf` |
| `Meta.Div2ParityPrf` | 15 | `Meta.CantorMonoPrf`, `Meta.NatMulPrf`, `Meta.StrongInductionPrf` | `Meta.CodeNumeralPrf`, `Meta.DotConsPrf` |
| `Meta.CodeNumeralPrf` | 16 | `Meta.Div2ParityPrf`, `Meta.ReprPrf` | `Meta.CodeNatInjPrf`, `Meta.DiagonalNumeral`, `Meta.GodelTwoPrf`, `Meta.ModeloCodigo`, `Meta.Representability2Prf`, `Meta.RosserNumerales`, `Meta.Sigma1CorePrf`, `Meta.SolidezPrf` |
| `Meta.CodeNatInjPrf` | 17 | `Meta.CodeNumeralPrf` | `Meta.ModeloCodigo` |
| `Meta.DiagonalNumeral` | 17 | `Meta.CodeNumeralPrf`, `Meta.DiagonalTwo` | `Meta.GodelTwoPrf` |
| `Meta.Representability2Prf` | 17 | `Meta.ArithPrf`, `Meta.CodeNumeralPrf`, `Meta.Representability2`, `Meta.TcArithPrf` · externo: `FOL.FOL`, `FOL.Theorems.Eq` | `Meta.DerivCondPrf`, `Meta.GodelTwoPrf`, `Meta.InAxiomsCodePrf`, `Meta.RosserNegLinea`, `Meta.RosserPosNum` |
| `Meta.SolidezPrf` | 17 | `Meta.CodeNumeralPrf`, `Meta.Hilbert`, `Meta.HilbertDeduction` · externo: `FOL.Semantics` | `Meta.Consistencia`, `Meta.SolidezDobleNegacion` |
| `Meta.DerivCondPrf` | 18 | `Meta.ChainPrf`, `Meta.Representability2Prf` | `Meta.EvalLiftcPrf`, `Meta.EvalPredPrf`, `Meta.ExIntroCodePrf`, `Meta.GodelTwoPrf`, `Meta.LiftcCodePrf`, `Meta.Sigma1Prf`, `Meta.SubstfcCodePrf` |
| `Meta.ModeloCodigo` | 18 | `Meta.CodeNatInjPrf`, `Meta.CodeNumeralPrf` | `Meta.ModeloEstandar`, `Meta.SolidezDobleNegacion` |
| `Meta.ModeloEstandar` | 19 | `Meta.ModeloCodigo` · externo: `FOL.Semantics` | `Meta.ModeloCodificacion`, `Meta.RosserNumerales` |
| `Meta.Sigma1Prf` | 19 | `Meta.DerivCondPrf` | `Meta.EvalLiftcPrf`, `Meta.HasWitTcFnPrf`, `Meta.LiftcCodePrf`, `Meta.Sigma1CorePrf`, `Meta.SubstfcCodePrf` |
| `Meta.SolidezDobleNegacion` | 19 | `Meta.ModeloCodigo`, `Meta.SolidezPrf` | `Meta.Consistencia` |
| `Meta.HasWitTcFnPrf` | 20 | `Meta.CodeWitnessPrf`, `Meta.NatArithPrf`, `Meta.NumListPrf`, `Meta.Sigma1Prf` | `Meta.RosserNegLinea`, `Meta.SubstfcWitnessPrf`, `Meta.TrackedCorePrf` |
| `Meta.ModeloCodificacion` | 20 | `Meta.ModeloEstandar` | `Meta.Consistencia` |
| `Meta.Sigma1CorePrf` | 20 | `Meta.CodeNumeralPrf`, `Meta.Sigma1Prf`, `Meta.TcArithPrf` | `Meta.EvalLiftcPrf`, `Meta.ExIntroCodePrf`, `Meta.InAxiomsCodePrf`, `Meta.LineWFCases` |
| `Meta.ExIntroCodePrf` | 21 | `Meta.DerivCondPrf`, `Meta.Sigma1CorePrf` | `Meta.EvalLtPrf`, `Meta.ForallElimCodePrf`, `Meta.TrackedCorePrf` |
| `Meta.LineWFCases` | 21 | `Meta.Provability`, `Meta.ReprPrf`, `Meta.Sigma1CorePrf`, `Minimal.Axioms` · externo: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers` | `Meta.GodelTwoPrf` |
| `Meta.SubstfcWitnessPrf` | 21 | `Meta.BoundedInPrf`, `Meta.CantorMonoPrf`, `Meta.HasWitTcFnPrf`, `Meta.NumCodeClosedPrf`, `Meta.StrongInductionPrf`, `Meta.SubstArith` | `Meta.D3ChainDotPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.LineWFGuardPrf`, `Meta.ListEtaPrf`, `Meta.MpCodePrf`, `Meta.RosserNegLinea`, `Meta.TrackedAtomsPrf` |
| `Meta.ListEtaPrf` | 22 | `Meta.SubstfcWitnessPrf` | `Meta.PremsOfTagPrf` |
| `Meta.TrackedCorePrf` | 22 | `Meta.ExIntroCodePrf`, `Meta.HasWitTcFnPrf` | `Meta.EvalLiftcPrf`, `Meta.ForallElimCodePrf`, `Meta.LiftcCodePrf`, `Meta.Sigma1AtomPrf` |
| `Meta.ForallElimCodePrf` | 23 | `Meta.ExIntroCodePrf`, `Meta.TrackedCorePrf` | `Meta.EvalSubstfcPrf`, `Meta.MpCodePrf` |
| `Meta.Sigma1AtomPrf` | 23 | `Meta.TcArithPrf`, `Meta.TrackedCorePrf` | `Meta.EvalArithPrf`, `Meta.EvalLiftcPrf`, `Meta.EvalPredPrf`, `Meta.LiftcCodePrf`, `Meta.LineWFTrackedPrf`, `Meta.SubstfcCodePrf` |
| `Meta.MpCodePrf` | 24 | `Meta.ForallElimCodePrf`, `Meta.SubstfcWitnessPrf` | `Meta.DotConsPrf`, `Meta.EvalArithPrf`, `Meta.EvalPredPrf`, `Meta.InAxiomsCodePrf`, `Meta.LiftcCodePrf`, `Meta.LineWFTrackedPrf`, `Meta.SubstfcCodePrf` |
| `Meta.EvalArithPrf` | 25 | `Meta.MpCodePrf`, `Meta.NumCodeClosedPrf`, `Meta.Sigma1AtomPrf`, `Meta.SubstCodeOpenPrf` | `Meta.EvalListPrf`, `Meta.EvalMulPrf`, `Meta.EvalPredPrf`, `Meta.LiftcCodePrf`, `Meta.SubstfcCodePrf` |
| `Meta.EvalMulPrf` | 26 | `Meta.EvalArithPrf`, `Meta.NatMulPrf` | `Meta.DotConsPrf` |
| `Meta.DotConsPrf` | 27 | `Meta.CantorMonoPrf`, `Meta.Div2ParityPrf`, `Meta.EvalMulPrf`, `Meta.MpCodePrf`, `Meta.NumCodeClosedPrf`, `Meta.SubstCodeOpenPrf` | `Meta.EvalListPrf`, `Meta.EvalNthcPrf`, `Meta.LiftcCodePrf`, `Meta.SubstfcCodePrf` |
| `Meta.EvalListPrf` | 28 | `Meta.DotConsPrf`, `Meta.EvalArithPrf`, `Meta.NumListPrf` | `Meta.EvalLtPrf`, `Meta.EvalRunFnPrf`, `Meta.LineWFTrackedPrf` |
| `Meta.EvalLtPrf` | 29 | `Meta.EvalListPrf`, `Meta.ExIntroCodePrf` | `Meta.EvalBoundedPrf`, `Meta.EvalNthcPrf`, `Meta.LiftcCodePrf`, `Meta.SubstfcCodePrf` |
| `Meta.EvalRunFnPrf` | 29 | `Meta.EvalListPrf`, `Meta.RunFnBoundedPrf` | `Meta.EvalLiftcPrf`, `Meta.EvalNthcPrf`, `Meta.LiftcCodePrf` |
| `Meta.EvalBoundedPrf` | 30 | `Meta.EvalLtPrf` | `Meta.Delta0ReflectPrf`, `Meta.LineWFTrackedPrf`, `Meta.PropCodePrf` |
| `Meta.EvalNthcPrf` | 30 | `Meta.DotConsPrf`, `Meta.EvalLtPrf`, `Meta.EvalRunFnPrf` | `Meta.EvalCarcNthcPrf` |
| `Meta.Delta0ReflectPrf` | 31 | `Meta.EvalBoundedPrf` | `Meta.D3DottedPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.LiftcCodePrf`, `Meta.LineWFGuardPrf` |
| `Meta.EvalCarcNthcPrf` | 31 | `Meta.EvalNthcPrf`, `Meta.LineWFConsPrf` | `Meta.D3InDotPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.InAxiomsCodePrf`, `Meta.LiftcCodePrf`, `Meta.LineWFTrackedPrf`, `Meta.SubstfcCodePrf` |
| `Meta.PropCodePrf` | 31 | `Meta.EvalBoundedPrf` | `Meta.BdAllIntroPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf` |
| `Meta.D3DottedPrf` | 32 | `Meta.Delta0ReflectPrf` | `Meta.D3ChainDotPrf`, `Meta.D3InDotPrf` |
| `Meta.D3InDotPrf` | 33 | `Meta.D3DottedPrf`, `Meta.EvalCarcNthcPrf` | `Meta.BdAllIntroPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.InAxiomsCodePrf`, `Meta.LineWFTrackedPrf`, `Meta.TrackedAtomsPrf` |
| `Meta.BdAllIntroPrf` | 34 | `Meta.D3InDotPrf`, `Meta.PropCodePrf` | `Meta.D3ChainDotPrf`, `Meta.LineWFTrackedPrf`, `Meta.TrackedAtomsPrf` |
| `Meta.InAxiomsCodePrf` | 34 | `Meta.D3InDotPrf`, `Meta.EvalCarcNthcPrf`, `Meta.MpCodePrf`, `Meta.Representability2Prf`, `Meta.Sigma1CorePrf` | `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.LineWFThyPrf`, `Meta.TrackedAtomsPrf` |
| `Meta.LineWFTrackedPrf` | 35 | `Meta.BdAllIntroPrf`, `Meta.BoundedInPrf`, `Meta.D3InDotPrf`, `Meta.EvalBoundedPrf`, `Meta.EvalCarcNthcPrf`, `Meta.EvalListPrf`, `Meta.MpCodePrf`, `Meta.Sigma1AtomPrf` | `Meta.CodeCtorKit`, `Meta.LiftcCodePrf`, `Meta.LineWFMpPrf`, `Meta.LineWFSchemaPrf`, `Meta.LineWFThyPrf`, `Meta.RosserNumEval`, `Meta.TrackedAtomsPrf` |
| `Meta.LineWFMpPrf` | 36 | `Meta.LineWFTrackedPrf` | `Meta.LineWFAssemblePrf` |
| `Meta.LineWFSchemaPrf` | 36 | `Meta.LineWFTrackedPrf` | `Meta.CodeCtorKit`, `Meta.LineWFGuardPrf`, `Meta.PremsOfTagPrf` |
| `Meta.LineWFThyPrf` | 36 | `Meta.InAxiomsCodePrf`, `Meta.LineWFTrackedPrf` | `Meta.LineWFAssemblePrf` |
| `Meta.CodeCtorKit` | 37 | `Meta.LineWFSchemaPrf`, `Meta.LineWFTrackedPrf` | `Meta.CodeTreeReflect`, `Meta.EvalPredPrf`, `Meta.LiftcCodePrf`, `Meta.LineWFEfqPrf`, `Meta.SubstfcCodePrf` |
| `Meta.LineWFGuardPrf` | 37 | `Meta.CodeWitnessPrf`, `Meta.Delta0ReflectPrf`, `Meta.LineWFSchemaPrf`, `Meta.SubstfcWitnessPrf` | `Meta.HasWitTrackedPrf` |
| `Meta.CodeTreeReflect` | 38 | `Meta.CodeCtorKit` | `Meta.LineWFPropPrf`, `Meta.SubstTreeReflect`, `Meta.TrackedAtomsPrf` |
| `Meta.EvalPredPrf` | 38 | `Meta.BoundedInPrf`, `Meta.CodeCtorKit`, `Meta.DerivCondPrf`, `Meta.EvalArithPrf`, `Meta.MpCodePrf`, `Meta.NumCodeClosedPrf`, `Meta.Sigma1AtomPrf`, `Meta.SubstCodeOpenPrf` | `Meta.EvalSubsttcPrf` |
| `Meta.LiftcCodePrf` | 38 | `Meta.ArithPrf`, `Meta.ChainPrf`, `Meta.CodeCtorKit`, `Meta.CodeWitnessPrf`, `Meta.Delta0ReflectPrf`, `Meta.DerivCondPrf`, `Meta.DotConsPrf`, `Meta.EvalArithPrf`, `Meta.EvalCarcNthcPrf`, `Meta.EvalLtPrf`, `Meta.EvalRunFnPrf`, `Meta.Godel`, `Meta.Hilbert`, `Meta.HilbertDeduction`, `Meta.LineWFTrackedPrf`, `Meta.MpCodePrf`, `Meta.NatArithPrf`, `Meta.NumCodeClosedPrf`, `Meta.Provability`, `Meta.ReprPrf`, `Meta.Sigma1AtomPrf`, `Meta.Sigma1Prf`, `Meta.SubstCodeOpenPrf`, `Meta.TcArithPrf`, `Meta.TrackedCorePrf` | `Meta.EvalLiftcPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf`, `Meta.HasWitTrackedPrf`, `Meta.SubstfcCodePrf`, `Meta.TrackedAtomsPrf` |
| `Meta.LineWFEfqPrf` | 38 | `Meta.CodeCtorKit` | `Meta.LineWFAssemblePrf` |
| `Meta.EvalLiftcPrf` | 39 | `Meta.ArithPrf`, `Meta.BoundedInPrf`, `Meta.CantorMonoPrf`, `Meta.ChainPrf`, `Meta.CodeWitnessPrf`, `Meta.DerivCondPrf`, `Meta.EvalRunFnPrf`, `Meta.Hilbert`, `Meta.HilbertDeduction`, `Meta.LiftcCodePrf`, `Meta.NatArithPrf`, `Meta.NatOrderPrf`, `Meta.NumListPrf`, `Meta.Provability`, `Meta.ReprPrf`, `Meta.Sigma1AtomPrf`, `Meta.Sigma1CorePrf`, `Meta.Sigma1Prf`, `Meta.StrongInductionPrf`, `Meta.TrackedCorePrf` | `Meta.EvalLiftfcPrf`, `Meta.EvalSubstfcPrf`, `Meta.EvalSubsttcPrf` |
| `Meta.LineWFPropPrf` | 39 | `Meta.CodeTreeReflect` | `Meta.LineWFAssemblePrf` |
| `Meta.SubstfcCodePrf` | 39 | `Meta.ArithPrf`, `Meta.CodeCtorKit`, `Meta.DerivCondPrf`, `Meta.DotConsPrf`, `Meta.EvalArithPrf`, `Meta.EvalCarcNthcPrf`, `Meta.EvalLtPrf`, `Meta.Godel`, `Meta.Hilbert`, `Meta.HilbertDeduction`, `Meta.LiftcCodePrf`, `Meta.MpCodePrf`, `Meta.NumCodeClosedPrf`, `Meta.Provability`, `Meta.ReprPrf`, `Meta.Sigma1AtomPrf`, `Meta.Sigma1Prf`, `Meta.SubstCodeOpenPrf`, `Meta.TcArithPrf` | `Meta.EvalSubstfcPrf` |
| `Meta.TrackedAtomsPrf` | 39 | `Meta.BdAllIntroPrf`, `Meta.CodeTreeReflect`, `Meta.D3InDotPrf`, `Meta.InAxiomsCodePrf`, `Meta.LiftcCodePrf`, `Meta.LineWFTrackedPrf`, `Meta.SubstfcWitnessPrf` | `Meta.D3ChainDotPrf`, `Meta.HasWitTrackedPrf` |
| `Meta.D3ChainDotPrf` | 40 | `Meta.BdAllIntroPrf`, `Meta.ChainOkBoundedPrf`, `Meta.D3DottedPrf`, `Meta.SubstfcWitnessPrf`, `Meta.TrackedAtomsPrf` | `Meta.D3BodyPrf` |
| `Meta.EvalSubsttcPrf` | 40 | `Meta.CantorMonoPrf`, `Meta.CodeWitnessPrf`, `Meta.D3InDotPrf`, `Meta.Delta0ReflectPrf`, `Meta.EvalCarcNthcPrf`, `Meta.EvalLiftcPrf`, `Meta.EvalPredPrf`, `Meta.InAxiomsCodePrf`, `Meta.LiftcCodePrf`, `Meta.PropCodePrf`, `Meta.SubstfcWitnessPrf` | `Meta.EvalSubstfcPrf` |
| `Meta.HasWitTrackedPrf` | 40 | `Meta.LiftcCodePrf`, `Meta.LineWFGuardPrf`, `Meta.TrackedAtomsPrf` | `Meta.HasWitFTrackedPrf` |
| `Meta.LineWFAssemblePrf` | 40 | `Meta.LineWFEfqPrf`, `Meta.LineWFMpPrf`, `Meta.LineWFPropPrf`, `Meta.LineWFThyPrf` | `Meta.PremsOfTagPrf`, `Meta.SubstTreeReflect` |
| `Meta.EvalSubstfcPrf` | 41 | `Meta.CantorMonoPrf`, `Meta.CodeWitnessPrf`, `Meta.D3InDotPrf`, `Meta.Delta0ReflectPrf`, `Meta.EvalCarcNthcPrf`, `Meta.EvalLiftcPrf`, `Meta.EvalSubsttcPrf`, `Meta.ForallElimCodePrf`, `Meta.InAxiomsCodePrf`, `Meta.LiftcCodePrf`, `Meta.PropCodePrf`, `Meta.SubstfcCodePrf`, `Meta.SubstfcWitnessPrf` | `Meta.EvalLiftfcPrf`, `Meta.SubstTreeReflect` |
| `Meta.HasWitFTrackedPrf` | 41 | `Meta.HasWitTrackedPrf` | `Meta.SubstTreeReflect` |
| `Meta.PremsOfTagPrf` | 41 | `Meta.LineWFAssemblePrf`, `Meta.LineWFSchemaPrf`, `Meta.ListEtaPrf` | `Meta.PremsOfDotPrf`, `Meta.RosserNegNum` |
| `Meta.EvalLiftfcPrf` | 42 | `Meta.EvalLiftcPrf`, `Meta.EvalSubstfcPrf` | `Meta.LiftfcWitnessPrf`, `Meta.SubstTreeReflect` |
| `Meta.LiftfcWitnessPrf` | 43 | `Meta.EvalLiftfcPrf` | `Meta.SubstTreeReflect` |
| `Meta.SubstTreeReflect` | 44 | `Meta.CodeTreeReflect`, `Meta.EvalLiftfcPrf`, `Meta.EvalSubstfcPrf`, `Meta.HasWitFTrackedPrf`, `Meta.LiftfcWitnessPrf`, `Meta.LineWFAssemblePrf` | `Meta.D3BodyPrf`, `Meta.PremsOfDotPrf` |
| `Meta.PremsOfDotPrf` | 45 | `Meta.PremsOfTagPrf`, `Meta.SubstTreeReflect` | `Meta.D3BodyPrf` |
| `Meta.D3BodyPrf` | 46 | `Meta.D3ChainDotPrf`, `Meta.PremsOfDotPrf`, `Meta.SubstTreeReflect` | `Meta.PremsBdAllPrf` |
| `Meta.PremsBdAllPrf` | 47 | `Meta.D3BodyPrf` | `Meta.GodelTwo`, `Meta.GodelTwoPrf` |
| `Meta.GodelTwo` | 48 | `Meta.PremsBdAllPrf`, `Meta.ProofChain`, `Meta.ReprPrf`, `Meta.Representability2` · externo: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers` | `Meta.GodelTwoPrf` |
| `Meta.GodelTwoPrf` | 49 | `Meta.ArithPrf`, `Meta.CodeNumeralPrf`, `Meta.DerivCondPrf`, `Meta.DiagonalNumeral`, `Meta.DiagonalTwo`, `Meta.GodelTwo`, `Meta.LineWFCases`, `Meta.PremsBdAllPrf`, `Meta.ReprPrf`, `Meta.Representability2Prf`, `Meta.TcArithPrf` | `Meta.Consistencia`, `Meta.TarskiPrf` |
| `Meta.Consistencia` | 50 | `Meta.GodelTwoPrf`, `Meta.ModeloCodificacion`, `Meta.SolidezDobleNegacion`, `Meta.SolidezPrf` | `Meta.ContratoTitulares`, `Meta.PurezaComando`, `Meta.PurezaTitulares`, `Meta.RosserGuardNeg`, `Meta.SolidezVerificador`, `Meta.TarskiPrf` |
| `Meta.PurezaComando` | 51 | `Meta.Consistencia` | `Meta.ContratoTitulares`, `Meta.GodelCorolarios`, `Meta.Lob`, `Meta.PurezaTitulares`, `Meta.RosserNumerales`, `Meta.RosserPosNum`, `Meta.RosserW1` |
| `Meta.SolidezVerificador` | 51 | `Meta.Consistencia`, `Meta.Representability` | `Meta.GodelCorolarios`, `Meta.RigidezEstandar`, `Meta.RosserPosNum`, `Meta.RosserW1` |
| `Meta.TarskiPrf` | 51 | `Meta.Consistencia`, `Meta.GodelTwoPrf` · externo: `FOL.Lift0` | `Meta.ContratoTitulares`, `Meta.Lob`, `Meta.PuenteFOL`, `Meta.PurezaTitulares`, `Meta.Rosser` |
| `Meta.GodelCorolarios` | 52 | `Meta.PurezaComando`, `Meta.SolidezVerificador` | `Meta.ContratoTitulares`, `Meta.PurezaTitulares` |
| `Meta.Lob` | 52 | `Meta.PurezaComando`, `Meta.TarskiPrf` | `Meta.ContratoTitulares`, `Meta.PurezaTitulares` |
| `Meta.RosserNumerales` | 52 | `Meta.CodeNumeralPrf`, `Meta.CodeWitnessPrf`, `Meta.ModeloEstandar`, `Meta.NumListPrf`, `Meta.PurezaComando` | `Meta.RosserNumEval` |
| `Meta.RosserPosNum` | 52 | `Meta.PurezaComando`, `Meta.Representability2Prf`, `Meta.SolidezVerificador` | `Meta.RosserNegNum` |
| `Meta.RosserW1` | 52 | `Meta.PurezaComando`, `Meta.SolidezVerificador` | `Meta.RosserNegNum` |
| `Meta.RosserNumEval` | 53 | `Meta.BoundedInPrf`, `Meta.LineWFTrackedPrf`, `Meta.NumCodeClosedPrf`, `Meta.RosserNumerales` | `Meta.RigidezEstandar`, `Meta.RosserGuardNeg` |
| `Meta.RigidezEstandar` | 54 | `Meta.RosserNumEval`, `Meta.SolidezVerificador` | `Meta.ContratoTitulares`, `Meta.ProvFiel`, `Meta.PuenteFOL` |
| `Meta.RosserGuardNeg` | 54 | `Meta.Consistencia`, `Meta.RosserNumEval` | `Meta.RosserNegLinea` |
| `Meta.PuenteFOL` | 55 | `Meta.HilbertDeduction`, `Meta.RigidezEstandar`, `Meta.TarskiPrf` · externo: `FOL.Canonical0`, `FOL.Derives1`, `FOL.Sentence` | `Meta.ContratoTitulares` |
| `Meta.RosserNegLinea` | 55 | `Meta.HasWitTcFnPrf`, `Meta.Representability2Prf`, `Meta.RosserGuardNeg`, `Meta.SubstfcWitnessPrf` | `Meta.RosserNegNum` |
| `Meta.RosserNegNum` | 56 | `Meta.PremsOfTagPrf`, `Meta.RosserNegLinea`, `Meta.RosserPosNum`, `Meta.RosserW1` | `Meta.ProvFiel`, `Meta.Rosser` |
| `Meta.ProvFiel` | 57 | `Meta.RigidezEstandar`, `Meta.RosserNegNum` | `Meta.ContratoTitulares`, `Meta.SegundoModelo` |
| `Meta.Rosser` | 57 | `Meta.RosserNegNum`, `Meta.TarskiPrf` | `Meta.ContratoTitulares`, `Meta.PurezaTitulares` |
| `Meta.ContratoTitulares` | 58 | `Meta.Consistencia`, `Meta.GodelCorolarios`, `Meta.Lob`, `Meta.ProvFiel`, `Meta.PuenteFOL`, `Meta.PurezaComando`, `Meta.RigidezEstandar`, `Meta.Rosser`, `Meta.TarskiPrf` | `Meta.PurezaTitulares` |
| `Meta.SegundoModelo` | 58 | `Meta.ProvFiel` | — |
| `Meta.PurezaTitulares` | 59 | `Meta.Consistencia`, `Meta.ContratoTabla`, `Meta.ContratoTitulares`, `Meta.GodelCorolarios`, `Meta.Lob`, `Meta.PurezaComando`, `Meta.Rosser`, `Meta.TarskiPrf` | — |

## Barriles

* `ROBINSON_PlusPlus.lean` importa 6: `Minimal.Axioms`, `Meta`, `Full.Induction`; externos: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers`.
* `ROBINSON_PlusPlus/Meta.lean` importa 118: `Meta.Godel`, `Meta.Provability`, `Meta.HasWitTcFnPrf`, `Meta.Hilbert`, `Meta.HilbertDeduction`, `Meta.HilbertSeq`, `Meta.SubstArith`, `Meta.CheckArith`, `Meta.Representability`, `Meta.Diagonal`, `Meta.ProofChain`, `Meta.Representability2`, `Meta.ReprPrf`, `Meta.ArithPrf`, `Meta.Representability2Prf`, `Meta.ChainPrf`, `Meta.DerivCondPrf`, `Meta.Sigma1Prf`, `Meta.TcArithPrf`, `Meta.NumListPrf`, `Meta.NatArithPrf`, `Meta.NatOrderPrf`, `Meta.NatMulPrf`, `Meta.CantorMonoPrf`, `Meta.Div2ParityPrf`, `Meta.CodeNumeralPrf`, `Meta.DiagonalNumeral`, `Meta.Sigma1CorePrf`, `Meta.EvalArithPrf`, `Meta.EvalMulPrf`, `Meta.ExIntroCodePrf`, `Meta.ForallElimCodePrf`, `Meta.LineWFCases`, `Meta.MpCodePrf`, `Meta.Sigma1AtomPrf`, `Meta.TrackedCorePrf`, `Meta.StrongInductionPrf`, `Meta.BoundedInPrf`, `Meta.RunFnBoundedPrf`, `Meta.ChainOkBoundedPrf`, `Meta.SubstCodeOpenPrf`, `Meta.NumCodeClosedPrf`, `Meta.SubstfcWitnessPrf`, `Meta.ListEtaPrf`, `Meta.PremsOfTagPrf`, `Meta.PremsOfDotPrf`, `Meta.DotConsPrf`, `Meta.EvalListPrf`, `Meta.EvalLtPrf`, `Meta.EvalRunFnPrf`, `Meta.EvalBoundedPrf`, `Meta.EvalNthcPrf`, `Meta.Delta0ReflectPrf`, `Meta.D3DottedPrf`, `Meta.PropCodePrf`, `Meta.EvalCarcNthcPrf`, `Meta.D3InDotPrf`, `Meta.BdAllIntroPrf`, `Meta.LineWFTrackedPrf`, `Meta.LineWFMpPrf`, `Meta.LineWFSchemaPrf`, `Meta.CodeCtorKit`, `Meta.EvalPredPrf`, `Meta.CodeWitnessPrf`, `Meta.CodeNatInjPrf`, `Meta.LiftcCodePrf`, `Meta.SubstfcCodePrf`, `Meta.EvalLiftcPrf`, `Meta.LineWFEfqPrf`, `Meta.CodeTreeReflect`, `Meta.LineWFPropPrf`, `Meta.InAxiomsCodePrf`, `Meta.LineWFThyPrf`, `Meta.LineWFAssemblePrf`, `Meta.LineWFConsPrf`, `Meta.DiagonalTwo`, `Meta.GodelTwo`, `Meta.EvalSubsttcPrf`, `Meta.LineWFGuardPrf`, `Meta.EvalSubstfcPrf`, `Meta.D3ChainDotPrf`, `Meta.TrackedAtomsPrf`, `Meta.HasWitTrackedPrf`, `Meta.HasWitFTrackedPrf`, `Meta.SubstTreeReflect`, `Meta.EvalLiftfcPrf`, `Meta.LiftfcWitnessPrf`, `Meta.D3BodyPrf`, `Meta.PremsBdAllPrf`, `Meta.GodelTwoPrf`, `Meta.ModeloCodigo`, `Meta.ModeloEstandar`, `Meta.ModeloCodificacion`, `Meta.SolidezPrf`, `Meta.SolidezDobleNegacion`, `Meta.Consistencia`, `Meta.TarskiPrf`, `Meta.SolidezVerificador`, `Meta.PurezaComando`, `Meta.RosserW1`, `Meta.RosserPosNum`, `Meta.RosserNumerales`, `Meta.RosserNumEval`, `Meta.RosserGuardNeg`, `Meta.RosserNegLinea`, `Meta.RosserNegNum`, `Meta.Rosser`, `Meta.Lob`, `Meta.GodelCorolarios`, `Meta.RigidezEstandar`, `Meta.ProvFiel`, `Meta.SegundoModelo`, `Meta.PuenteFOL`, `Meta.PurezaTitulares`, `Full.Induction`; externos: `FOL.FOL`, `FOL.Theorems.Eq`, `FOL.Theorems.Quantifiers`.


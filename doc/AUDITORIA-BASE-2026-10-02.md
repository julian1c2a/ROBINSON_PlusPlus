# Auditoría de la base · 2026‑10‑02 — las MEDICIONES, versionadas

**Last updated:** 2026-10-02 · Lean v4.31.0 — creado para que las cifras de ADR‑114/ADR‑115 no vivan sólo en
un scratchpad (lección: *una medición cuyo artefacto vive en un scratchpad se evapora*).

Este documento no razona: **guarda lo medido**. El razonamiento y las decisiones están en
[ADR‑114](../DECISIONS.md) (ronda 1: los cuatro defectos de la base) y [ADR‑115](../DECISIONS.md) (la retirada
de la capa `⊢`). Los sondeos citados viven en [`sondeos/`](../sondeos/README.md).

## 1 · P0 — ¿usa la cadena de Gödel algo de `⊢`? (medido ANTES de borrar, sobre `1dac85a`)

Cierre por constantes —tipo, **cuerpo** (`value? (allowOpaque := true)`) y constructores— de
`goedel_first_prf` y `goedel_second_prf`. Sin `allowOpaque` el sondeo era **vacuo** (en v4.31 `value?` no
devuelve el cuerpo de un `theorem`); lo cazó el control positivo.

Resultado (salida de la ejecución del 2026‑10‑02 sobre el árbol anterior a la retirada; no se puede volver a
ejecutar sobre el actual, porque los módulos que comprueba ya no existen):

* **6 710 constantes** en el cierre · **⊢ en el tipo: 0** · **en módulos a borrar: 1** —
  `ROBINSON_PlusPlus.Minimal.Axioms.le.eq_1`, el lema de ecuación autogenerado de `le` (una `def` que
  sobrevive), materializado en `Block2`; inocuo, no es ninguna de las 633 declaraciones borradas.
* **criterio robusto: 0 de 12 prohibidas** en el cierre.
* **controles positivos**: `d3_prf_real`, `repr_pos'_prf`, `prf_inAxC`, `AnclaEq` y
  `prf_godelCN_fixedpoint` están en el cierre (los cinco `true`).
* **control del detector**: el cierre de `negVerifier_proved` contiene **9 de las 12** prohibidas.

```lean
import Lean
import Std.Data.HashSet
import ROBINSON_PlusPlus
/-! Sonda R2-2 · ¿usa la cadena Gödel I/II sobre `Prf` algo de la capa `⊢`? Cierre por constantes
(tipo + valor + constructores). Predicción del grafo (sin compilar): «⊢ en el tipo: 0 · en módulos a borrar: 0». -/
open Lean Elab Command

namespace SondaR22

def usadas (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some ci =>
    let v : Array Name := match ci.value? (allowOpaque := true) with
      | some e => e.getUsedConstants
      | none => #[]
    let k : Array Name := match ci with
      | .inductInfo i => i.ctors.toArray
      | .ctorInfo i => #[i.induct]
      | _ => #[]
    ci.type.getUsedConstants ++ v ++ k

def cierre (env : Environment) (raices : List Name) : Std.HashSet Name := Id.run do
  let mut vis : Std.HashSet Name := {}
  let mut pila : Array Name := raices.toArray
  while pila.size > 0 do
    let c := pila.back!
    pila := pila.pop
    if vis.contains c then continue
    vis := vis.insert c
    for d in usadas env c do
      if !vis.contains d then pila := pila.push d
  return vis

def modulo (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => Name.anonymous

/-- Los 27 módulos que el plan borra enteros, más `FOL.MetaRules`. -/
def aBorrar : List Name :=
  [`FOL.MetaRules, `ROBINSON_PlusPlus.Full.Bounded, `ROBINSON_PlusPlus.Full.Divisibility,
   `ROBINSON_PlusPlus.Full.Division, `ROBINSON_PlusPlus.Full.Lists, `ROBINSON_PlusPlus.Full.Mod2,
   `ROBINSON_PlusPlus.Full.Primality, `ROBINSON_PlusPlus.Full.Factorization,
   `ROBINSON_PlusPlus.Full.StrongInduction, `ROBINSON_PlusPlus.Meta.AxiomListCode,
   `ROBINSON_PlusPlus.Meta.DerivCond, `ROBINSON_PlusPlus.Meta.Induction,
   `ROBINSON_PlusPlus.Meta.LineWFDerives, `ROBINSON_PlusPlus.Meta.ListInductionArith,
   `ROBINSON_PlusPlus.Meta.Necessitation, `ROBINSON_PlusPlus.Meta.OmegaStrength,
   `ROBINSON_PlusPlus.Meta.Reflection, `ROBINSON_PlusPlus.Meta.StepArith,
   `ROBINSON_PlusPlus.Minimal.Theorems.Block1, `ROBINSON_PlusPlus.Minimal.Theorems.Block2,
   `ROBINSON_PlusPlus.Minimal.Theorems.Block3, `ROBINSON_PlusPlus.Minimal.Theorems.Block4,
   `ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5, `ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7,
   `ROBINSON_PlusPlus.Minimal.Theorems.Block5, `ROBINSON_PlusPlus.Minimal.Theorems.Block6,
   `ROBINSON_PlusPlus.Minimal.Theorems.Block7, `ROBINSON_PlusPlus.Minimal.Theorems.Block8]

end SondaR22

open SondaR22 in
elab "#capaD_en_la_cadena" : command => do
  let env ← getEnv
  let S := cierre env [``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf,
                       ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf]
  let mut nD : Nat := 0
  let mut nB : Nat := 0
  for c in S.toList do
    if let some ci := env.find? c then
      if c != ``Derives && ci.type.getUsedConstants.contains ``Derives then
        nD := nD + 1
        logInfo m!"⊢ en el TIPO: {c}"
      if aBorrar.contains (modulo env c) then
        nB := nB + 1
        logInfo m!"en un módulo que el plan borra: {c} ∈ {modulo env c}"
  logInfo m!"cierre: {S.size} constantes · ⊢ en el tipo: {nD} · en módulos a borrar: {nB}"
  -- Criterio ROBUSTO (verificador de R22-1): el cierre es de tipo Y valor; ninguna de estas debe estar.
  let prohibidas : List Name := [``Derives, ``FOL.MetaRules.imp_intro, ``FOL.MetaRules.raa,
    ``FOL.MetaRules.or_elim, ``FOL.MetaRules.ex_elim, ``ROBINSON_PlusPlus.Full.ax_induction_prim,
    ``ROBINSON_PlusPlus.Full.ax_list_induction, ``ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq,
    ``ROBINSON_PlusPlus.Meta.Hilbert.ConsistentOmega, ``ROBINSON_PlusPlus.Meta.DiagonalTwo.Reflects,
    ``ROBINSON_PlusPlus.Meta.OmegaReflect.NegVerifier, ``ROBINSON_PlusPlus.Meta.OmegaReflect.OmegaConsistent]
  let mut malas : Nat := 0
  for p in prohibidas do
    if S.contains p then
      malas := malas + 1
      logInfo m!"⛔ PROHIBIDA en el cierre: {p}"
  logInfo m!"criterio robusto: {malas} de {prohibidas.length} prohibidas en el cierre"
  -- CONTROL POSITIVO: el cierre tiene que contener piezas que la cadena SÍ usa.
  for q in [``ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real, ``ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf,
            ``ROBINSON_PlusPlus.Meta.Representability2Prf.prf_inAxC, ``ROBINSON_PlusPlus.Meta.Representability2Prf.AnclaEq,
            ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint] do
    logInfo m!"control positivo · {q} ∈ cierre: {S.contains q}"
  -- CONTROL DE QUE EL DETECTOR VE: el cierre de un teorema de la capa ⊢ SÍ debe contener lo prohibido.
  let T := cierre env [``ROBINSON_PlusPlus.Meta.ChainNegPrf.negVerifier_proved]
  let mut vistas : Nat := 0
  for p in prohibidas do
    if T.contains p then vistas := vistas + 1
  logInfo m!"control del detector · cierre de negVerifier_proved: {T.size} constantes, {vistas} de {prohibidas.length} prohibidas (debe ser > 0)"

#capaD_en_la_cadena
```

## 2 · Los footprints de los siete sondeos de la auditoría (recompilados el 2026‑10‑02, 19:50, árbol final)

```
=================== MetaReglasRefutables · exit 0
'Sondeos.MetaReglasRefutables.derives_tval' depends on axioms: [propext, Quot.sound]
'Sondeos.MetaReglasRefutables.imp_intro_refutable' depends on axioms: [propext, Quot.sound]
'Sondeos.MetaReglasRefutables.raa_refutable' depends on axioms: [propext, Quot.sound]
'Sondeos.MetaReglasRefutables.ax_list_induction_refutable' depends on axioms: [propext, Quot.sound]
'Sondeos.MetaReglasRefutables.derives_to_derives0' depends on axioms: [propext, Quot.sound]
'Sondeos.MetaReglasRefutables.derives_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sondeos.MetaReglasRefutables.ex_elim_refutable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sondeos.MetaReglasRefutables.or_elim_refutable' depends on axioms: [propext, Classical.choice, Quot.sound]
=================== ListInductionAxiomRefutable · exit 0
'Sondeos.ListInductionAxiomRefutable.nil_bot_of' depends on axioms: [propext]
=================== OmegaConsistentRefutable · exit 0
'Sondeos.OmegaConsistentRefutable.prf_objList_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sondeos.OmegaConsistentRefutable.not_omegaConsistentPrf' depends on axioms: [propext, Classical.choice, Quot.sound]
=================== PrfBotCodificacionVieja · exit 0
'Sondeos.PrfBotCodificacionVieja.cons_cero_cero_en_Prf' depends on axioms: [propext, Classical.choice, Quot.sound]
=================== AnclaEqInconsistente · exit 0
'Sondeos.AnclaEqInconsistente.anclaEq_prf_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sondeos.AnclaEqInconsistente.hipotesis_goedel_insatisfacibles' depends on axioms: [propext,
'Sondeos.AnclaEqInconsistente.prf_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
'verif_g1_vacuo' depends on axioms: [propext, Classical.choice, Quot.sound]
'verif_g2_vacuo' depends on axioms: [propext, Classical.choice, Quot.sound]
=================== ModeloBasura · exit 0
'ModeloBasura.uno_no_es_cons' depends on axioms: [propext, Quot.sound]
'ModeloBasura.base' does not depend on any axioms
'ModeloBasura.paso' does not depend on any axioms
'ModeloBasura.falla' depends on axioms: [propext, Quot.sound]
=================== AnclaSoundness · exit 0
'Sondeos.AnclaSoundness.prfI_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sondeos.AnclaSoundness.prfI_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sondeos.AnclaSoundness.ancla_underivable_prfI' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3 · Cuáles de los 85 sondeos compilan (2026‑10‑02, tras la retirada)

`lake env lean sondeos/<f>.lean` sobre los 85, de uno en uno: **32 compilan, 53 no** (31 en la pasada completa
más `AnclaSoundness`, reparado después y recompilado aparte). Clasificación de los 53 en ADR‑115 §5 y en
`sondeos/README.md`. ⚠️ Esta tabla es de su fecha: al retirar `FOL/MetaRules.lean` cae además
`HenkinSaleDeRaa`.

| sondeo | compila | primer error |
|---|:---:|---|
| `A3ConsOkRefuta.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `nil_ne_cons` |
| `A3IsFCBTracked.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `AcotarEsLaMismaObligacion.lean` | ✅ |  |
| `AnclaEqInconsistente.lean` | ✅ |  |
| `AnclaSoundness.lean` | ✅ |  |
| `CanonNeRefuta.lean` | ❌ | error: Type mismatch: After simplification, term |
| `CantorSobreyectivo.lean` | ✅ |  |
| `CarcPayoff.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `ChainNegPuente.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `FOL.MetaRules.raa` |
| `ClassicalChoiceCenso.lean` | ✅ |  |
| `ClausuraFormaEcuacional.lean` | ✅ |  |
| `ClausuraLiftSinWTs.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `ClausuraNoHaceFalta.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `ClausuraSubsttc.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `CodeNatInj.lean` | ❌ | error: Type mismatch |
| `CraigEqVacuo.lean` | ✅ |  |
| `CtorDotados.lean` | ❌ | error: Ambiguous term |
| `DerivesSinMetaReglas.lean` | ✅ |  |
| `DescargaHFN.lean` | ❌ | error: unknown namespace `ROBINSON_PlusPlus.Meta.Induction` |
| `DescensoLiftc.lean` | ❌ | error: Ambiguous term |
| `DespachadorCoste.lean` | ✅ |  |
| `DiscriminaEcuacional.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `DiscriminaTestigoAbierto.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `Div2Gen.lean` | ✅ |  |
| `EnsamblajeMedida.lean` | ❌ | error: Ambiguous term |
| `EnsamblajeTriple.lean` | ❌ | error: Ambiguous term |
| `EnumFormulaPorInyeccion.lean` | ✅ |  |
| `EqTransCodeImp2.lean` | ❌ | error: Ambiguous term |
| `EvalPredDot.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `EvalSubstfcPrf.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `EvalSubsttc.lean` | ❌ | error: Ambiguous term |
| `GateGuardaEnriquecida.lean` | ❌ | error: Ambiguous term |
| `HasWitFCritica.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `HasWitFReal.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `HasWitFRealMin.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `HasWitTcFn.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `HenkinSaleDeRaa.lean` | ✅ |  |
| `InTracked.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `KitPayoff.lean` | ❌ | error: Application type mismatch: The argument |
| `ListInductionAxiomRefutable.lean` | ✅ |  |
| `MDiezEnLaFirma.lean` | ✅ |  |
| `Magnitud.lean` | ✅ |  |
| `MedirC_Carga.lean` | ❌ | error: Not a definitional equality: the left-hand side |
| `MedirC_Deriva.lean` | ❌ | error: Not a definitional equality: the left-hand side |
| `MedirC_Enmienda.lean` | ❌ | error: Not a definitional equality: the left-hand side |
| `MedirF_Censo.lean` | ❌ | error: unknown namespace `ROBINSON_PlusPlus.Meta.AxiomListCode` |
| `MedirF_Opaco.lean` | ❌ | error: unknown namespace `ROBINSON_PlusPlus.Meta.AxiomListCode` |
| `MedirF_Replan.lean` | ❌ | error: unknown namespace `ROBINSON_PlusPlus.Meta.AxiomListCode` |
| `MergeTestigos.lean` | ✅ |  |
| `MetaReglasRefutables.lean` | ✅ |  |
| `ModeloBasura.lean` | ✅ |  |
| `ModeloDiscriminador.lean` | ✅ |  |
| `ModeloNat.lean` | ✅ |  |
| `NegVerifierModE.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `derives_lineWF_neg_of_tag` |
| `NombresFrescosMedicion.lean` | ✅ |  |
| `OmegaConsistentRefutable.lean` | ✅ |  |
| `ParseWitness.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `ParticionDiscrimina.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `ParticionTresPredicados.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `Paso2CasoForall.lean` | ❌ | error: Ambiguous term |
| `Paso2Guardado.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `PilotoAislado.lean` | ✅ |  |
| `PilotoDiagonal.lean` | ❌ | error: unknown namespace `ROBINSON_PlusPlus.Meta.Induction` |
| `PilotoRastreada.lean` | ❌ | error: Type mismatch |
| `PrfBotCodificacionVieja.lean` | ✅ |  |
| `PrfHMono.lean` | ✅ |  |
| `RecodCoste.lean` | ✅ |  |
| `ReflectorAtomoAllIn.lean` | ❌ | error: Ambiguous term |
| `ReflectorDesdeConsumidor.lean` | ❌ | error: Ambiguous term |
| `ReflectorForallAnidado.lean` | ❌ | error: Ambiguous term |
| `S1Audit.lean` | ❌ | error(lean.unknownIdentifier): Unknown constant `ROBINSON_PlusPlus.Meta.DiagonalTwo.goedel_first_real'` |
| `S3S5.lean` | ❌ | error(lean.invalidField): Invalid field notation: Type of |
| `S4.lean` | ✅ |  |
| `SegundoMuro.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `SimbolosSinString.lean` | ✅ |  |
| `SubCodesCritica.lean` | ❌ | error: Ambiguous term |
| `SubCodesWitness.lean` | ❌ | error: Ambiguous term |
| `SubstfcEx.lean` | ❌ | error(lean.unknownIdentifier): Unknown identifier `ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2` |
| `SubstfcPlanos.lean` | ❌ | error: Ambiguous term |
| `SustituyendoOpaco.lean` | ✅ |  |
| `SymbolParam.lean` | ✅ |  |
| `SymbolParamCoste.lean` | ✅ |  |
| `TagConclCoste.lean` | ✅ |  |
| `TcFormPayoff.lean` | ❌ | error(lean.synthInstanceFailed): failed to synthesize instance of type class |
| `TestigoAbierto.lean` | ❌ | error: don't know how to synthesize implicit argument `α` |

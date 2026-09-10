/-
🔬 SONDEO OBLIGATORIO DEL MÓDULO E (2026-09-10h) — el que `PLAN-NEGVERIFIER.md` §8 exigía
   *antes* de codificar `VerifierSound`.

## LA PREGUNTA

> «Intentar construir una cadena canónica basura, **aceptada por los axiomas objeto**, cuya `runFn`
> contenga un `formCode φ` con `⊬ φ`. Si se encuentra ⇒ **PARAR**: el verificador objeto sería
> INSÓLIDO y habría que reforzar los esquemas primero.»

## EL VEREDICTO, en tres frases

1. ✅ **NO hay bug de solidez.** Ninguna de las cadenas basura que los axiomas objeto aceptan
   concluye un `formCode φ` con `⊬φ`.
2. ⭐⭐ **Y el módulo E sale CASI GRATIS**, por una razón estructural que el plan no vio: el decisor
   que E necesita **no tiene que ser el verificador objeto**. Basta el **decodificador META**
   (`Meta/ChainDecode.lean`), y entonces la solidez **ya está probada**: es `decodeChain_prf`.
3. ⛔ **PERO EL RIESGO NO ESTABA DONDE EL PLAN LO PONÍA.** El plan marcaba E como RIESGO ALTO y C/D
   como MEDIO. Es al revés: E es una línea, y el que hay que rediseñar es el par **(C, D)** — la
   completitud negativa —, porque los esquemas objeto **aceptan más que el decodificador**.

## EL MURO, medido

`IsCodeShaped` (la clase de testigos de `StdChain`) **NO SEPARA**: admite a la vez `numeralM n` y
`cons h t`, y `cons nil nil ≐ numeralM 2` es **PROVABLE**. Un `formCode φ` **es** un numeral, sólo
que astronómico. ⇒ Refutar `In ⌜φ⌝ (runFn nil t)` contra una conclusión basura exigiría **evaluar
el emparejamiento de Cantor** — inviable.

⇒ **La viabilidad de `NegVerifier` depende de ESTRECHAR la clase de testigos** hasta que todas las
comparaciones sean **paralelas por tipo** (`formCode` contra `formCode`, `termCode` contra
`termCode`), que es donde `formCode_ne` y compañía deciden. Eso es una decisión de diseño con
consecuencias sobre la fuerza de `OmegaConsistent`, y va a ADR.

## Las cinco mediciones de abajo

| # | qué mide | resultado |
|---|---|---|
| 1 | la vía POSITIVA sobre `formCode` | ✅ `refuta_eqrefl` |
| 2 | `IsCodeShaped` no separa | ⛔ `colision_iguales_en_la_teoria` |
| 3 | `StdChain` admite listas de numerales | ⛔ `StdChain_admite_numerales` |
| 4 | el módulo E | ⭐ `modulo_E`, una línea |
| 5 | la discrepancia objeto/meta | ⛔ `basura_p1_aceptada_objeto` |

Todas compilan. Footprint: el del árbol.
-/
import ROBINSON_PlusPlus.Meta
set_option maxRecDepth 20000

open FOL Formula Term
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.OmegaReflect
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open ROBINSON_PlusPlus.Meta.CodeDecode ROBINSON_PlusPlus.Meta.ChainDecode
open ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.HilbertSeq

namespace NegVerifierModE

/-! ## MEDICIÓN 1 · la vía POSITIVA — una línea `formCode`-shaped SÍ se refuta

`tagConcl 12 [termCode t] = eqc (termCode t) (termCode t) = formCode (t ≐ t)`, así que la
comparación es **`formCode` contra `formCode`** y `formCode_ne` decide. -/

theorem meas_tagConcl_eqrefl (t : Term) :
    tagConcl 12 [termCode t] = some (formCode (Formula.eq t t)) := rfl

/-- ⭐ Una línea `eqrefl` cuya conclusión **no es** `t ≐ t` queda REFUTADA. Comparación paralela
    por tipo: `formCode φ` contra `formCode (t ≐ t)`. -/
theorem refuta_eqrefl (φ : Formula) (t : Term) (h : φ ≠ Formula.eq t t) :
    axioms ⊢ neg (lineWF (cons (formCode φ)
      (cons (numeralM 12) (objList [termCode t])))) :=
  derives_lineWF_neg_of_tag 12 (formCode φ) [termCode t] (formCode (Formula.eq t t))
    (meas_tagConcl_eqrefl t) (formCode_ne h)

/-! ## MEDICIÓN 2 · ⛔ la vía que NO existe — una conclusión `numeralM` NO se puede refutar

`IsCodeShaped` admite `numeralM n` como línea y como conclusión. Para refutar haría falta

    axioms ⊢ neg (numeralM n =eq formCode (t ≐ t))

y **no hay ningún lema que lo dé**: `formCode_ne` compara `formCode` con `formCode`,
`termCode_ne` compara `termCode` con `termCode`, y `numeral_ne` compara `numeral` con `numeral`.
⚠️ Y **no puede haberlo genérico**, porque `cons nil nil ≐ numeralM 2` **es provable**
(`sondeos/CanonNeRefuta.lean`): un `formCode` **es** un numeral, sólo que astronómico. Decidir la
desigualdad exigiría **evaluar el emparejamiento de Cantor** — inviable.

La medición que lo certifica, re‑hecha aquí para que quede en un solo sitio: -/

theorem colision_IsCodeShaped_izq : IsCodeShaped (cons nil nil) :=
  IsCodeShaped.cons IsCodeShaped.nil IsCodeShaped.nil

theorem colision_IsCodeShaped_der : IsCodeShaped (numeralM 2) := IsCodeShaped.numeral 2

theorem colision_distintos_en_Lean : cons nil nil ≠ numeralM 2 := by decide

/-- ⛔ **Y PROVABLEMENTE IGUALES en la teoría.** ⇒ `IsCodeShaped` **no separa**. -/
theorem colision_iguales_en_la_teoria : Prf (cons nil nil =eq numeralM 2) := by
  have h := prf_cons_eval 0 0
  simpa only [numeral, numeralM, nil, ROBINSON_PlusPlus.Meta.CodeNumeralPrf.consN,
    ROBINSON_PlusPlus.Meta.CodeNumeralPrf.triN] using h

/-! ## MEDICIÓN 3 · el alcance del daño

Una lista `l` **code‑shaped** cuyos elementos son numerales es un testigo legítimo de
`StdChain`, y su `objList` es una cadena que la teoría **no puede analizar por accesores**:
`carc (numeralM n)` sólo se determina invirtiendo Cantor. -/

theorem StdChain_admite_numerales : StdChain [numeralM 7, numeralM 3] := by
  intro x hx
  rcases hx with _ | ⟨_, hx⟩
  · exact IsCodeShaped.numeral 7
  · rcases hx with _ | ⟨_, hx⟩
    · exact IsCodeShaped.numeral 3
    · cases hx


/-! ## MEDICIÓN 4 · ⭐⭐ EL MÓDULO E SALE **CASI GRATIS** — no hay bug de solidez

`PLAN-NEGVERIFIER.md` §8 marcaba el módulo E como **el corazón y el RIESGO ALTO**, y exigía un
sondeo antes de codificarlo: *«intentar construir una cadena canónica basura, aceptada por los
axiomas objeto, cuya `runFn` contenga un `formCode φ` con `⊬φ`»*.

⭐ **El sondeo sale limpio, y por una razón estructural: la solidez ya está probada.** El decisor
que el módulo E necesita **no** tiene que ser el verificador OBJETO — basta el **decodificador
META**, y entonces:

| pieza | dónde | estado |
|---|---|---|
| `decodeForm_inj : decodeForm c = some φ → c = formCodeM φ` | `Meta/CodeDecode.lean` | ✅ |
| `decodeChain_checkProof` | `Meta/ChainDecode.lean` | ✅ |
| `decodeChain_prf` — **el módulo E** | `Meta/ChainDecode.lean` | ✅ |

⇒ Con `chainOkDec l := (decodeChain (objList l)).isSome`, la solidez estructural es **inmediata**. -/

/-- El decisor META de cadenas. -/
def chainOkDec (l : List Term) : Bool := (decodeChain (objList l)).isSome

/-- 🏁 **EL MÓDULO E, en una línea.** Si el decodificador acepta y `φ` está entre las conclusiones,
    entonces `Prf φ`. No hay nada que probar: es `decodeChain_prf`. -/
theorem modulo_E {l : List Term} {rs : List Rule} {φ : Formula}
    (h : decodeChain (objList l) = some rs)
    (hmem : ∀ L, checkProof rs = some L → φ ∈ L) : Prf φ :=
  decodeChain_prf h hmem

/-! ## MEDICIÓN 5 · ⛔ DÓNDE ESTÁ EL RIESGO DE VERDAD: la COMPLETITUD NEGATIVA

El módulo E cubre la mitad **(a)**: *decisor acepta ⟹ `Prf φ`*. `NegVerifier` necesita también la
mitad **(b)**: *decisor rechaza ⟹ la teoría REFUTA `chainOk`*. Y ahí sí hay discrepancia, medida:

⚠️ **Los esquemas objeto valen para args ARBITRARIOS, el decodificador sólo para códigos reales.** -/

/-- Un término que **no** es el código de ninguna fórmula. -/
def basura : Term := numeralM 7

theorem basura_no_decodifica : decodeForm basura = none := by decide

/-- Y por tanto tampoco decodifica la conclusión que `p1` construye con él. -/
theorem basura_p1_no_decodifica :
    decodeForm (implc basura (implc basura basura)) = none := by decide

/-- ⛔ **PERO LA LÍNEA ES ACEPTADA POR LOS AXIOMAS OBJETO.** El esquema `p1` cuantifica sobre
    códigos **cualesquiera**, así que la reconstrucción casa por reflexividad. -/
theorem basura_p1_aceptada_objeto :
    axioms ⊢ lineWF (cons (implc basura (implc basura basura))
      (cons (numeralM 0) (cons basura (cons basura nil)))) :=
  FOL.MetaRules.mp
    (FOL.MetaRules.and_elim_right (lineWF_p1 (implc basura (implc basura basura)) basura basura))
    (ROBINSON_PlusPlus.Minimal.Axioms.eq_refl _)

/-! ### ⇒ El diagnóstico, en una frase

**El verificador objeto NO es insólido** —la línea de arriba concluye un código basura, no un
`formCode φ` con `⊬φ`—, pero **acepta más que el decodificador**. Y `NegVerifier` necesita refutar
`In ⌜φ⌝ (runFn nil t)` contra esas conclusiones basura, o sea distinguir `formCode φ` de
`implc basura …`.

⛔ **Y eso vuelve al mismo muro de la MEDICIÓN 2**: `formCode φ` y `implc basura …` son ambos
`cons`‑árboles, `cons` **es** un número, y decidir su desigualdad exige **evaluar Cantor**.
`formCode_ne` no aplica porque el lado derecho **no es un `formCode`**.

🔑 ⇒ **El riesgo del frente NO estaba donde el plan lo ponía.** El módulo E es gratis; el que hay
que rediseñar es el **par (C, D)** — la completitud negativa —, y su viabilidad depende de
**estrechar la clase de testigos** hasta que todas las comparaciones sean **paralelas por tipo**. -/

end NegVerifierModE

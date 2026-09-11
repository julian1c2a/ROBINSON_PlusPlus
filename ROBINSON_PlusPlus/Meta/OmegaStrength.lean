/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Hilbert

/-!
# LA FUERZA DE `axioms ⊢` — medida, no supuesta (2026‑09‑11)

La auditoría del 2026‑09‑11 dejó abierta **la pregunta más importante del proyecto**: *¿cuál es la
fuerza real del cálculo `axioms ⊢`?* De ella dependía si `goedel_second'` era «una pieza que falta»
o **un teorema vacuo**. Este módulo la contesta, y la respuesta es peor de lo que la pregunta
suponía.

## ⛔⛔ `axioms ⊢` es **sintácticamente COMPLETO**: decide toda sentencia

Y no hace falta ninguna hipótesis para demostrarlo. La razón está en la **forma** de los
meta‑axiomas de `FOL/MetaRules.lean`, no en su contenido aritmético:

    axiom raa {Γ A} (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A

La premisa es una **función de Lean**. Si `axioms ⊬ A`, esa función existe **vacuamente** —el
dominio está vacío— ⇒ **el cálculo refuta A**. Con excluido medio en Lean, para toda `A`:
`(axioms ⊢ A) ∨ (axioms ⊢ ¬A)`.

⇒ **`axioms ⊢` no es una relación de derivabilidad de primer orden.** Es una noción metateórica de
verdad: **todo lo que no prueba, lo refuta**.

## ⚠️ Lo que esto obliga a corregir, y no es poco

1. ⛔ **`goedel_second'` NO es el Segundo Teorema de Gödel.** La incompletitud habla de teorías que
   **no deciden** alguna sentencia; éste decide **todas**. Su hipótesis `hgi : ¬(axioms ⊢ G)`
   equivale, por `refuta_lo_que_no_prueba`, a **`axioms ⊢ ¬G`**: no dice «`G` es indemostrable»,
   dice «el cálculo refuta `G`». ⇒ el enunciado es **correcto como implicación** y **no es
   incompletitud**. El Gödel II de verdad está en `Meta/GodelTwoPrf.lean`, sobre `Prf`.
2. ⚠️ **El docstring de `gen` en `FOL/MetaRules.lean` llama «ω‑regla» a algo que no lo es.** La
   ω‑regla toma como premisa `A[n̄]` para cada **numeral**; `gen` la toma para **todo `Term`** —
   variables libres y aplicaciones de función incluidas—. Su premisa es **estrictamente mayor**, así
   que como **regla** es **más débil** que la ω‑regla: está más cerca de la generalización ordinaria
   con variable propia. **La fuerza del cálculo no viene de `gen`: viene de `raa` e `imp_intro`**,
   que toman funciones de Lean.
3. ✅ **Gödel I NO está afectado.** `goedel_first_numeral` concluye sobre **`Prf`**, que **sí** es
   finitario y **no** es completo. Su hipótesis `ConsistentOmega : ¬(axioms ⊢ ⊥)` sigue siendo una
   suposición legítima y no trivial — completitud no da consistencia.

## ⭐ «Pero eso ES la definición de completitud, y es justo lo que Gödel I dice que NO pasa»

Exacto, y conviene fijarlo porque es lo que da sentido a todo lo demás.

`derives_completo` **es** la completitud sintáctica: *para toda `A`, la teoría prueba `A` o prueba
`¬A`*. Y el Primer Teorema dice que **ninguna teoría consistente, suficientemente fuerte y
EFECTIVAMENTE AXIOMATIZADA es completa**.

⇒ No hay contradicción: lo que se ha demostrado es que **`axioms ⊢` incumple la tercera hipótesis**.

    Gödel I  =  consistente  +  suficientemente fuerte  +  r.e.  ⟹  INCOMPLETA
    medido   =  `axioms ⊢` es COMPLETA
    ⇒           `axioms ⊢` NO es r.e.

Y se ve **dónde** deja de serlo: `raa` e `imp_intro` toman como premisa una **función de Lean**, es
decir, cuantifican sobre **todas las demostraciones de la metateoría**. Eso no es una regla de
inferencia efectiva: no hay procedimiento que enumere las derivaciones. El conjunto
`{A | axioms ⊢ A}` es una **compleción consistente** de `axioms` —del tipo Lindenbaum—, no un
sistema formal.

🔑 **Por eso el teorema de Gödel de este proyecto vive sobre `Prf` y no sobre `⊢`, y no es una
preferencia de estilo**: `Prf` **sí** es r.e. —está definido por derivaciones **finitas** que
`checkProof` verifica, y eso es exactamente lo que el verificador aritmetizado internaliza—. `⊢` no
lo es, y por eso **no puede** ser el sujeto de un teorema de incompletitud: no cumple la hipótesis.

⇒ Lejos de romper nada, este módulo **explica por qué la arquitectura del proyecto es la correcta**:
`⊢` como herramienta cómoda de trabajo, `Prf` como sujeto de los enunciados.

## Qué hay que decidir (y no lo decide este módulo)

`axioms ⊢` se usa como **cálculo de trabajo** en toda la capa `Minimal`/`Full` y en buena parte de
`Meta`, y ahí su comodidad es real: `imp_intro` y `raa` ahorran el teorema de deducción. Lo que **no**
puede hacer es aparecer en el **enunciado** de un resultado de incompletitud. La frontera —qué
teorema puede hablar de `⊢` y cuál tiene que hablar de `Prf`— es una decisión de diseño, y está
planteada en `doc/AUDITORIA-2026-09-11.md` §F‑1.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms

namespace ROBINSON_PlusPlus.Meta.OmegaStrength

/-- **(1) Todo lo que el cálculo no prueba, lo refuta.** Una línea, desde `raa`: si `axioms ⊬ A`,
    la función `axioms ⊢ A → axioms ⊢ ⊥` existe **vacuamente**. -/
theorem refuta_lo_que_no_prueba (A : Formula) (h : ¬ (axioms ⊢ A)) : axioms ⊢ neg A :=
  FOL.MetaRules.raa (fun hA => absurd hA h)

/-- 🏁 **(2) `axioms ⊢` es SINTÁCTICAMENTE COMPLETO**: decide toda sentencia, sin hipótesis. -/
theorem derives_completo (A : Formula) : Or (axioms ⊢ A) (axioms ⊢ neg A) := by
  by_cases h : axioms ⊢ A
  · exact Or.inl h
  · exact Or.inr (refuta_lo_que_no_prueba A h)

/-- **(3) Lo mismo por `imp_intro`**: de `axioms ⊬ A` sale `axioms ⊢ (A ⇒ B)` para **cualquier** `B`. -/
theorem implica_lo_que_sea (A B : Formula) (h : ¬ (axioms ⊢ A)) : axioms ⊢ (A ⇒ B) :=
  FOL.MetaRules.imp_intro (fun hA => absurd hA h)

/-- ⛔ **(4) La consecuencia sobre `goedel_second'`**: su hipótesis `hgi` **no dice «`G` es
    indemostrable»** — dice **«el cálculo refuta `G`»**. -/
theorem hgi_es_refutar (G : Formula) (h : ¬ (axioms ⊢ G)) : axioms ⊢ neg G :=
  refuta_lo_que_no_prueba G h

/-- **(5) Y la contrapositiva**: si el cálculo **no refuta** `G`, entonces lo **prueba**, y la
    hipótesis de `goedel_second'` es **falsa** — el teorema no dice nada de esa `G`. -/
theorem no_refuta_implica_prueba (G : Formula) (h : ¬ (axioms ⊢ neg G)) : axioms ⊢ G := by
  by_cases hG : axioms ⊢ G
  · exact hG
  · exact absurd (refuta_lo_que_no_prueba G hG) h

/-! ## §2 · La otra mitad: la disyunción es **EXCLUSIVA**, y eso ES la consistencia

⭐ **Observación del propietario (2026‑09‑11), y es exacta**: `derives_completo` da un `∨`
**inclusivo**, y la completitud que uno quiere decir es *«prueba exactamente una de las dos»*. La
mitad que falta —`¬(L ∧ R)`— **no es otra propiedad: ES la consistencia**, porque de `⊢ A` y
`⊢ ¬A` sale `⊢ ⊥` por un `mp`.

⇒ Con `ConsistentOmega`, `axioms ⊢` **decide exactamente una** de cada par ⟨A, ¬A⟩. Es decir, se
comporta **como un predicado de verdad**: es una teoría **completa y consistente**, y por tanto —por
Gödel I— **no puede ser r.e.**

⚠️ **Y sobre el intuicionismo, la duda también es pertinente.** `derives_completo` se demuestra con
`by_cases`, es decir con **excluido medio EN LA METATEORÍA** (Lean con `Classical.choice`). Es un
**metateorema clásico**: intuicionísticamente **no** se obtendría, porque el paso es exactamente
«o hay demostración de `A`, o no la hay», que es EM sobre un enunciado no decidible.

🔑 Conviene separar los dos planos, que aquí se tocan y no son lo mismo:

| plano | ¿clásico? | por qué |
|---|---|---|
| **lógica OBJETO** (`Derives`) | **sí** | el meta‑axioma `dne` la hace clásica, explícitamente |
| **METATEORÍA** (Lean) | **sí**, y aquí se usa | `by_cases` sobre `axioms ⊢ A` |

⇒ La completitud medida es **un hecho clásico sobre un cálculo clásico**. Si la metateoría fuese
intuicionista, `derives_completo` **no sería demostrable** — pero `refuta_lo_que_no_prueba` **sí**
(no usa EM: sólo `raa` y una función vacua), y ésa ya basta para lo que importa: **de `⊬ A` sale
`⊢ ¬A`**, que es lo que hace que `⊢` no sea r.e. -/

/-- **La exclusividad ES la consistencia**: dos demostraciones opuestas dan `⊥` por un `mp`. -/
theorem derives_exclusivo (hcon : ConsistentOmega) (A : Formula) :
    ¬ (And (axioms ⊢ A) (axioms ⊢ neg A)) :=
  fun h => hcon (FOL.MetaRules.mp h.2 h.1)

/-- 🏁 **COMPLETITUD EN SU FORMA FUERTE**: con consistencia, el cálculo decide **exactamente una**
    de cada par ⟨`A`, `¬A`⟩ — `(L ∧ ¬R) ∨ (¬L ∧ R)`, que es lo que el propietario pedía. -/
theorem derives_decide_exactamente_una (hcon : ConsistentOmega) (A : Formula) :
    Or (And (axioms ⊢ A) (¬ (axioms ⊢ neg A)))
       (And (¬ (axioms ⊢ A)) (axioms ⊢ neg A)) := by
  rcases derives_completo A with h | h
  · exact Or.inl ⟨h, fun hn => hcon (FOL.MetaRules.mp hn h)⟩
  · exact Or.inr ⟨fun hp => hcon (FOL.MetaRules.mp h hp), h⟩

end ROBINSON_PlusPlus.Meta.OmegaStrength

/-! ## `export` — por CONSUMO

Consumidor previsto: la documentación y quien vaya a **enunciar** un resultado sobre `⊢`. -/
export ROBINSON_PlusPlus.Meta.OmegaStrength (
  refuta_lo_que_no_prueba derives_completo implica_lo_que_sea
  hgi_es_refutar no_refuta_implica_prueba
  derives_exclusivo derives_decide_exactamente_una
)

/-! ## FOOTPRINT — lo único que usa son las meta‑reglas ω y el excluido medio -/
#print axioms ROBINSON_PlusPlus.Meta.OmegaStrength.derives_completo

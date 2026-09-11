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

end ROBINSON_PlusPlus.Meta.OmegaStrength

/-! ## `export` — por CONSUMO

Consumidor previsto: la documentación y quien vaya a **enunciar** un resultado sobre `⊢`. -/
export ROBINSON_PlusPlus.Meta.OmegaStrength (
  refuta_lo_que_no_prueba derives_completo implica_lo_que_sea
  hgi_es_refutar no_refuta_implica_prueba
)

/-! ## FOOTPRINT — lo único que usa son las meta‑reglas ω y el excluido medio -/
#print axioms ROBINSON_PlusPlus.Meta.OmegaStrength.derives_completo

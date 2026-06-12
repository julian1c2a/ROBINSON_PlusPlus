/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Provability

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Incompleteness

/-!
## META — NIVEL D: Primer Teorema de Incompletitud de Gödel

Deriva la **mitad esencial del Primer Teorema de Incompletitud** a partir de
las condiciones de demostrabilidad del Nivel C (`Meta/Provability.lean`):

* **Diagonalización** → `goedelSentence_fixedpoint` : `⊢ G ⇔ ¬Prov(⌜G⌝)`.
* **Condición D1** (representabilidad de la demostrabilidad) → `provFormula_repr`
  : `(⊢ Prov(⌜φ⌝)) ↔ (⊢ φ)`.

**Resultado** (`goedel_first_unprovable`): si `axioms` es consistente, la
sentencia de Gödel `G` **no es demostrable**. Como `G` afirma su propia
indemostrabilidad, `G` es entonces **verdadera pero indemostrable**
(`goedel_first_true`).

**Alcance** (honesto):

* La **otra mitad** (`⊬ ¬G`) requiere ω-consistencia (Gödel) o la eliminación
  de doble negación object-level (FOL aquí es **intuicionista**: la DNE sólo
  está disponible asumiendo `doubleNegAxiom` en el contexto). No se deriva aquí.
* **Gödel II** (`⊬ Con`) requiere las condiciones D2 y D3 (no postuladas en el
  Nivel C). Queda fuera.
* La justificación de las propias condiciones D1/diagonalización, y la sutileza
  ω-lógica del sistema de RPP (la `gen` ω-regla hace `axioms ⊢` no
  finitariamente r.e.), se discuten en `GODEL-STATUS.md`. Aquí derivamos la
  **lógica** de Gödel I *dados* esos postulados — el ejercicio estándar de
  libro a partir de las condiciones de demostrabilidad.
-/

/-- `Prov(⌜φ⌝)` — la fórmula que afirma "⌜φ⌝ es demostrable" (sustituyendo el
    código de `φ` en `provFormula`). -/
noncomputable def provCode (φ : Formula) : Formula := substFormula 0 (formCode φ) provFormula

/-- **Consistencia** de `axioms`: no deriva `⊥`. -/
def Consistent : Prop := ¬ (axioms ⊢ Formula.bottom)

/-- **Primer Teorema de Incompletitud (mitad esencial)**: si `axioms` es
    consistente, la sentencia de Gödel **no es demostrable**.

    Prueba: si `⊢ G`, entonces (D1) `⊢ Prov(⌜G⌝)`; y por el punto fijo
    `⊢ G ⇔ ¬Prov(⌜G⌝)`, `⊢ ¬Prov(⌜G⌝)`. Modus ponens da `⊢ ⊥`, contra
    la consistencia. -/
theorem goedel_first_unprovable (hcon : Consistent) :
    ¬ (axioms ⊢ goedelSentence) := by
  intro hG
  -- D1: ⊢ G → ⊢ Prov(⌜G⌝)
  have hProv : axioms ⊢ provCode goedelSentence :=
    (provFormula_repr goedelSentence).mpr hG
  -- punto fijo: ⊢ G ⇔ ¬Prov(⌜G⌝); con ⊢ G obtenemos ⊢ ¬Prov(⌜G⌝)
  have hNotProv : axioms ⊢ neg (provCode goedelSentence) :=
    iff_mp goedelSentence_fixedpoint hG
  -- ¬Prov(⌜G⌝) = Prov(⌜G⌝) ⇒ ⊥; modus ponens con ⊢ Prov(⌜G⌝) da ⊥
  exact hcon (mp hNotProv hProv)

/-- **Corolario — `G` es verdadera pero indemostrable**: bajo consistencia, el
    código de `G` **no es `Provable`**. Como `G` afirma exactamente eso
    (`G ⇔ ¬Prov(⌜G⌝)`), `G` es verdadera y, a la vez, indemostrable. -/
theorem goedel_first_true (hcon : Consistent) :
    ¬ Provable (formCode goedelSentence) := by
  rw [provable_formCode_iff]
  exact goedel_first_unprovable hcon

/-- **Incompletitud**: bajo consistencia, existe una sentencia indemostrable —
    a saber, la sentencia de Gödel. (`axioms` no es negación-completa por la
    vía de `G`; la sentencia es indecidible salvo refinamiento con
    ω-consistencia para la otra mitad.) -/
theorem incompleteness (hcon : Consistent) :
    ∃ φ : Formula, ¬ (axioms ⊢ φ) :=
  ⟨goedelSentence, goedel_first_unprovable hcon⟩

end ROBINSON_PlusPlus.Meta.Incompleteness

-- Exports: Nivel D
export ROBINSON_PlusPlus.Meta.Incompleteness (
  provCode
  Consistent
  goedel_first_unprovable
  goedel_first_true
  incompleteness
)

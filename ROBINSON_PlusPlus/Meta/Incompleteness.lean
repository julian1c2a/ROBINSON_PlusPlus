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

/-!
### Segundo Teorema de Incompletitud (postulando D2, D3)

Con las condiciones de Hilbert-Bernays-Löb completas (D1 ya disponible vía
`provFormula_repr`; **D2** y **D3** postuladas aquí), se deriva Gödel II.

La fórmula de **consistencia** es `Con := ¬Prov(⌜⊥⌝)`. Gödel II: si `axioms` es
consistente, **no demuestra su propia consistencia**.

Crucial: toda la cadena de implicaciones (incluida la contrapositiva) se
construye con `imp_intro`/`mp` — **no se necesita DNE object-level**, así que
funciona en el FOL intuicionista de aquí.
-/

/-- **D2** (condición de demostrabilidad): la demostrabilidad distribuye sobre
    la implicación. `⊢ Prov(⌜A⇒B⌝) ⇒ (Prov(⌜A⌝) ⇒ Prov(⌜B⌝))`. Meta-axioma. -/
axiom D2 (A B : Formula) :
    axioms ⊢ (provCode (Formula.impl A B) ⇒ (provCode A ⇒ provCode B))

/-- **D3** (condición de demostrabilidad): la demostrabilidad es provablemente
    provable. `⊢ Prov(⌜A⌝) ⇒ Prov(⌜Prov(⌜A⌝)⌝)`. Meta-axioma. -/
axiom D3 (A : Formula) :
    axioms ⊢ (provCode A ⇒ provCode (provCode A))

/-- **Fórmula de consistencia** `Con := ¬Prov(⌜⊥⌝)`. -/
noncomputable def consistencyFormula : Formula := neg (provCode Formula.bottom)

/-- **Gödel I formalizado**: `⊢ Con ⇒ G`. El sistema demuestra "si soy
    consistente entonces `G`". Derivado de D1 (necesitación), D2, D3 y el punto
    fijo. Es el corazón del Segundo Teorema. -/
theorem con_imp_goedelSentence :
    axioms ⊢ (consistencyFormula ⇒ goedelSentence) := by
  -- abreviaturas: PG = Prov(⌜G⌝), PBot = Prov(⌜⊥⌝)
  -- punto fijo: ⊢ G ⇔ ¬PG  (defeq con la forma sustituida)
  have hfp : axioms ⊢ (goedelSentence ⇔ neg (provCode goedelSentence)) :=
    goedelSentence_fixedpoint
  have fp_fwd : axioms ⊢ (goedelSentence ⇒ neg (provCode goedelSentence)) :=
    Minimal.Axioms.and_elim_left hfp
  have fp_bwd : axioms ⊢ (neg (provCode goedelSentence) ⇒ goedelSentence) :=
    Minimal.Axioms.and_elim_right hfp
  -- D1 (necesitación): ⊢ (G ⇒ ¬PG) → ⊢ Prov(⌜G ⇒ ¬PG⌝)
  have nec1 : axioms ⊢ provCode (Formula.impl goedelSentence (neg (provCode goedelSentence))) :=
    (provFormula_repr _).mpr fp_fwd
  -- D2(G, ¬PG): ⊢ Prov(⌜G⇒¬PG⌝) ⇒ (PG ⇒ Prov(⌜¬PG⌝))
  have step_a : axioms ⊢ (provCode goedelSentence ⇒ provCode (neg (provCode goedelSentence))) :=
    mp (D2 goedelSentence (neg (provCode goedelSentence))) nec1
  -- D2(PG, ⊥): ⊢ Prov(⌜¬PG⌝) ⇒ (Prov(⌜PG⌝) ⇒ Prov(⌜⊥⌝))
  have step_b : axioms ⊢ (provCode goedelSentence ⇒
      (provCode (provCode goedelSentence) ⇒ provCode Formula.bottom)) :=
    imp_intro (fun hpg =>
      mp (D2 (provCode goedelSentence) Formula.bottom) (mp step_a hpg))
  -- D3(G): ⊢ PG ⇒ Prov(⌜PG⌝)
  have d3 : axioms ⊢ (provCode goedelSentence ⇒ provCode (provCode goedelSentence)) :=
    D3 goedelSentence
  -- combinando: ⊢ PG ⇒ PBot
  have pg_imp_pbot : axioms ⊢ (provCode goedelSentence ⇒ provCode Formula.bottom) :=
    imp_intro (fun hpg => mp (mp step_b hpg) (mp d3 hpg))
  -- contrapositiva + punto fijo: ⊢ Con ⇒ G   (Con = ¬PBot)
  exact imp_intro (fun hcon =>
    mp fp_bwd (imp_intro (fun hpg => mp hcon (mp pg_imp_pbot hpg))))

/-- **Segundo Teorema de Incompletitud de Gödel**: si `axioms` es consistente,
    **no demuestra su propia consistencia** (`⊬ Con`).

    Prueba: si `⊢ Con`, entonces (por `con_imp_goedelSentence` + mp) `⊢ G`; pero
    por el Primer Teorema (`goedel_first_unprovable`) `⊬ G` bajo consistencia —
    contradicción. -/
theorem goedel_second (hcon : Consistent) :
    ¬ (axioms ⊢ consistencyFormula) := by
  intro hConProvable
  exact goedel_first_unprovable hcon (mp con_imp_goedelSentence hConProvable)

end ROBINSON_PlusPlus.Meta.Incompleteness

-- Exports: Nivel D
export ROBINSON_PlusPlus.Meta.Incompleteness (
  provCode
  Consistent
  goedel_first_unprovable
  goedel_first_true
  incompleteness
  D2
  D3
  consistencyFormula
  con_imp_goedelSentence
  goedel_second
)

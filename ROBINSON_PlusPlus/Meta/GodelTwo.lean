/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DerivCond
import ROBINSON_PlusPlus.Meta.Reflection

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.DerivCond
open ROBINSON_PlusPlus.Meta.Reflection

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.GodelTwo

/-!
## META — NIVEL D real: Segundo Teorema de Gödel sobre `provCodeC'` (D3 postulado)

Cierre del **núcleo lógico** de Gödel II para el predicado de demostrabilidad
estructural `provCodeC'`, con la cadena de Hilbert-Bernays-Löb:

* **D1** (`repr_pos'`) — real (`Meta/Representability2.lean`).
* **D2** (`d2`) — **real** (`Meta/DerivCond.lean`), usado explícitamente aquí.
* **D3** — **postulado** (`d3` abajo). Su prueba real (Σ₁-completitud provable por
  inducción object internalizando `repr_pos'`) es la pieza pendiente más grande, y
  además requiere unificar `Prf.thy → axioms` (el verificador como teoría). Ver
  `project_godel_nivel_d_real` / análisis de D3.

⚠️ **ACTUALIZADO 2026‑08‑19:** el punto fijo disponible es ahora `godelCN_fixedpoint`
(`Meta/DiagonalNumeral.lean`), sobre la sentencia **numeral** `godelCN`; el de `godelC'` se retiró
con `ax_tc_cons`. `goedel_second'` **no se ve afectado**: es modular, toma `fp_bwd` como hipótesis.
Para instanciarlo hay que usar `godelCN` y su `and_elim_right godelCN_fixedpoint`.

Las dos condiciones restantes —el **punto fijo** (`godelCN ⇔ ¬provCodeC' godelCN`)
y la **necesitación** del condicional del punto fijo, junto con la
**indemostrabilidad ω** de `G` (mitad de Gödel I a nivel ω)— se exponen como
**hipótesis explícitas** (no se postulan a la ligera): su realización honesta
necesita la adaptación del lema diagonal a `provFormulaC'` y el refactor
`Prf.thy → axioms` (para que la necesitación del punto fijo sea Prf-demostrable).
Así el teorema es **verde y honesto**: la *lógica* de Gödel II es real, con **D2
real** en la cadena, y las piezas no-cerradas quedan **visibles** como hipótesis.

(Mejora sobre el `goedel_second` legacy, que postulaba **D2 y D3**; aquí D2 es real.)
-/

/-- **D3 (postulado)** para `provCodeC'`: la demostrabilidad es provablemente
    provable. Único axioma gödeliano restante de la cadena (D1/D2 son teoremas).
    Su prueba real es la Σ₁-completitud provable del verificador. -/
axiom d3 (φ : Formula) :
    axioms ⊢ (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))

/-- **Fórmula de consistencia** `Con' := ¬ Prov'(⌜⊥⌝)`. -/
noncomputable def consistencyFormula' : Formula := neg (provCodeC' Formula.bottom)

/-- **Gödel I formalizado internamente** (`⊢ Con' ⇒ G`): el sistema demuestra "si
    soy consistente entonces `G`". Núcleo del Segundo Teorema, vía D1 (necesitación,
    `nec1`), **D2 real** (`d2`), D3 (`d3`) y el punto fijo (`fp_bwd`).

    Parametrizado por `G` y las dos condiciones aún no cerradas:
    * `fp_bwd` : dirección `¬Prov'(⌜G⌝) ⇒ G` del punto fijo.
    * `nec1`   : necesitación del condicional del punto fijo `G ⇒ ¬Prov'(⌜G⌝)`. -/
theorem con_imp_godel' (G : Formula)
    (fp_bwd : axioms ⊢ (neg (provCodeC' G) ⇒ G))
    (nec1 : axioms ⊢ provCodeC' (G ⇒ neg (provCodeC' G))) :
    axioms ⊢ (consistencyFormula' ⇒ G) := by
  -- D2(G, ¬PG): Prov'(⌜G⇒¬PG⌝) ⇒ (PG ⇒ Prov'(⌜¬PG⌝))
  have step_a : axioms ⊢ (provCodeC' G ⇒ provCodeC' (neg (provCodeC' G))) :=
    mp (d2 G (neg (provCodeC' G))) nec1
  -- D2(PG, ⊥): Prov'(⌜¬PG⌝)=Prov'(⌜PG⇒⊥⌝) ⇒ (Prov'(⌜PG⌝) ⇒ Prov'(⌜⊥⌝))
  have step_b : axioms ⊢
      (provCodeC' G ⇒ (provCodeC' (provCodeC' G) ⇒ provCodeC' Formula.bottom)) :=
    imp_intro (fun hpg => mp (d2 (provCodeC' G) Formula.bottom) (mp step_a hpg))
  -- D3(G): PG ⇒ Prov'(⌜PG⌝); combinando ⟹ PG ⇒ PBot
  have pg_imp_pbot : axioms ⊢ (provCodeC' G ⇒ provCodeC' Formula.bottom) :=
    imp_intro (fun hpg => mp (mp step_b hpg) (mp (d3 G) hpg))
  -- contrapositiva + punto fijo: Con' ⇒ G  (Con' = ¬PBot)
  exact imp_intro (fun hcon =>
    mp fp_bwd (imp_intro (fun hpg => mp hcon (mp pg_imp_pbot hpg))))

/-- **Segundo Teorema de Incompletitud de Gödel** (sobre `provCodeC'`): si el sistema
    es consistente, **no demuestra su propia consistencia** (`⊬ Con'`).

    Prueba (la de libro): si `⊢ Con'`, por `con_imp_godel'` + mp se tiene `⊢ G`,
    contra la indemostrabilidad de `G` (`hgi`, mitad de Gödel I). Parametrizado por
    el punto fijo (`fp_bwd`), la necesitación (`nec1`) y `hgi : ⊬ G`. **D2 real**,
    **D3 postulado** (`d3`). -/
theorem goedel_second' (G : Formula)
    (fp_bwd : axioms ⊢ (neg (provCodeC' G) ⇒ G))
    (nec1 : axioms ⊢ provCodeC' (G ⇒ neg (provCodeC' G)))
    (hgi : ¬ (axioms ⊢ G)) :
    ¬ (axioms ⊢ consistencyFormula') := by
  intro hcon
  exact hgi (mp (con_imp_godel' G fp_bwd nec1) hcon)

end ROBINSON_PlusPlus.Meta.GodelTwo

export ROBINSON_PlusPlus.Meta.GodelTwo (
  d3
  consistencyFormula'
  con_imp_godel'
  goedel_second'
)

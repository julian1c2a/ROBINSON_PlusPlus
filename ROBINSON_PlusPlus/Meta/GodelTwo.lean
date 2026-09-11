/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DerivCond
import ROBINSON_PlusPlus.Meta.Reflection
-- ⚠️ 2026‑09‑10g: entra la cadena entera de D3 para **retirar el `axiom d3`**.
-- `GodelTwo` no lo importa nadie salvo el barril, así que no hay ciclo.
import ROBINSON_PlusPlus.Meta.PremsBdAllPrf

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
* **D3** (`d3` abajo) — 🏁 **TEOREMA desde el 2026‑09‑10g**, ya no postulado.
  `d3_prf_real` (`Meta/PremsBdAllPrf.lean` §10) la demuestra: Σ₁‑completitud provable
  por inducción objeto, con `pcc_eval_premsOf` (B1), el puente de la cota (B2) y el
  chasis interior (B3). ⇒ **la cadena D1/D2/D3 no postula ninguna de las tres**, y los
  `axiom` de Lean pasaron de **7 a 6**. Detalle: `doc/REFERENCE-Incompleteness.md` §3.67.
  ⚠️ Este párrafo decía hasta hoy «postulado… la pieza pendiente más grande»: lo cazó la
  auditoría de `doc/book/AUDITORIA-2026-09-10.md` R3 — un docstring que contradecía a un
  teorema **33 líneas más abajo, en su propio fichero**.

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

/-- 🏁🏁🏁 **D3 — TEOREMA desde el 2026‑09‑10g.**

    Era el **último axioma gödeliano** de la cadena: `axiom d3`, postulado desde el principio
    porque su prueba real es la Σ₁‑completitud provable del verificador. Ahora es exactamente eso,
    probado: `d3_prf_real` (`Meta/PremsBdAllPrf.lean` §10), y la cadena D1/D2/D3 **no postula
    ninguna de las tres**.

    ⚠️ Retirar un axioma sólo puede **fortalecer** el resultado: lo que antes se suponía ahora se
    deriva, y todo lo que dependía de `d3` conserva su enunciado con un footprint más pequeño.

    La ruta, entera, está en `doc/REFERENCE-Incompleteness.md` §3.55–§3.67. -/
theorem d3 (φ : Formula) :
    axioms ⊢ (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  ROBINSON_PlusPlus.Meta.Hilbert.prf_to_derives
    (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real φ)

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
    contra la indemostrabilidad de `G` (`hgi`). Parametrizado por el punto fijo (`fp_bwd`),
    la necesitación (`nec1`) y `hgi`.

    🏁 **D1, D2 y D3 son las TRES teoremas** desde el 2026‑09‑10g (`d3` dejó de ser `axiom`).

    ⛔⛔ **PERO ESTE TEOREMA NO ESTÁ ENSAMBLADO, Y LA RAZÓN ES DE FONDO** (auditoría 2026‑09‑11,
    hallazgo **F‑1** de `doc/AUDITORIA-2026-09-11.md`). El día 2026‑09‑10h este docstring llegó a
    afirmar que *«`hgi` es la mitad demostrada de Gödel I»*. **Es FALSO**, y la medición es simple:

        hgi                     : ¬ (axioms ⊢ G)     -- el cálculo ω
        goedel_first_numeral    : ¬ Prf godelCN      -- el cálculo FINITARIO
        prf_to_derives          : Prf φ → axioms ⊢ φ

    De la tercera sale `¬(axioms ⊢ G) → ¬ Prf G`, **no al revés**: `hgi` es **estrictamente más
    fuerte** que lo que Gödel I entrega. Y **no existe** la vuelta `⊢ → Prf` en el árbol
    (comprobado), ni ninguna versión ω de Gödel I.

    ⚠️ **Y hay algo peor que una hipótesis no descargada**: `FOL/MetaRules.lean` documenta `gen`
    como la **ω‑regla** y `dne` con la lectura *«demostrabilidad = verdad en ℕ»*. Bajo esa lectura
    `G` es **verdadera**, luego `hgi` sería **falsa** y este teorema **vacuo**. ⬜ **No está medido**
    —requiere decidir la fuerza real de `axioms ⊢`— y es la pregunta abierta más importante del
    proyecto.

    ⭐ **La salida está identificada y es construible**: Gödel II **sobre `Prf`**
    (`goedel_second_prf : ConsistentH → ¬ Prf Con'`, el nombre que el proyecto lleva planeando
    desde junio). Las tres condiciones **ya existen sobre `Prf`** —`repr_pos'_prf` (D1),
    `d2_prf` (D2), `d3_prf_real` (D3)—; faltan las versiones `Prf` del **punto fijo**
    (`godelCN_fixedpoint`) y de **`con_imp_godel'`**. -/
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

/-! ## FOOTPRINT — 🏁 **sin `d3`** desde el 2026‑09‑10g -/

#print axioms ROBINSON_PlusPlus.Meta.GodelTwo.d3
#print axioms ROBINSON_PlusPlus.Meta.GodelTwo.goedel_second'

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
theorem d3 [AnclaEq] (φ : Formula) :
    axioms ⊢ (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  ROBINSON_PlusPlus.Meta.Hilbert.prf_to_derives
    (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real φ)

/-- **Fórmula de consistencia** `Con' := ¬ Prov'(⌜⊥⌝)`. -/
noncomputable def consistencyFormula' : Formula := neg (provCodeC' Formula.bottom)

/-! ## ⛔⛔ RETIRADOS el 2026‑09‑11: `con_imp_godel'` y `goedel_second'`

Aquí vivían `con_imp_godel' : axioms ⊢ (Con' ⇒ G)` y `goedel_second'`, la versión del Segundo
Teorema **sobre el cálculo `⊢`**. **Se retiran**, y no por deuda técnica: porque **decían algo que
no es**.

`Meta/OmegaStrength.lean` mide que **`axioms ⊢` es sintácticamente COMPLETO** —decide toda
sentencia—, porque `raa`/`imp_intro` toman como premisa una **función de Lean** y lo que el cálculo
no prueba, lo **refuta**. Un cálculo que decide todo **no puede** ser el sujeto de un teorema de
incompletitud: **no es r.e.**, que es justo la hipótesis que Gödel I exige.

⇒ La hipótesis `hgi : ¬(axioms ⊢ G)` de aquel teorema no significaba «`G` es indemostrable»: por
`hgi_es_refutar`, significa **«el cálculo REFUTA `G`»**. El enunciado era una implicación correcta y
**no era incompletitud**.

🏁 **El Segundo Teorema de verdad está en `Meta/GodelTwoPrf.lean`**, sobre el cálculo finitario
`Prf` —que **sí** es r.e.—:

    goedel_second_prf (hcon : ConsistentOmega) : ¬ Prf consistencyFormula'

con **una sola hipótesis** y **ninguna suelta**. Su `prf_con_imp_godel` sustituye a
`con_imp_godel'`, que sólo existía para alimentar a `goedel_second'`.

⚠️ **Qué NO se retira**: `d3` (la tercera condición de derivabilidad sobre `⊢`, que fue `axiom`
hasta el 2026‑09‑10g y hoy es teorema) y `consistencyFormula'`, que `GodelTwoPrf` consume.
Decisión del propietario, 2026‑09‑11, opción (b). Ver `doc/AUDITORIA-2026-09-11.md` F‑1 y
[ADR‑024](../../DECISIONS.md). -/

end ROBINSON_PlusPlus.Meta.GodelTwo

export ROBINSON_PlusPlus.Meta.GodelTwo (
  d3
  consistencyFormula'
)

/-! ## FOOTPRINT — 🏁 **sin `d3`** desde el 2026‑09‑10g.
El de `goedel_second'` se retiró con el teorema; el que importa ahora es el de
`goedel_second_prf` (`Meta/GodelTwoPrf.lean`). -/

#print axioms ROBINSON_PlusPlus.Meta.GodelTwo.d3


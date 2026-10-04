/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
-- ⚠️ 2026‑09‑10g: entró la cadena entera de D3 para que `d3` dejara de ser `axiom` y pasara a
-- teorema. Ese teorema (D3 sobre `⊢`) era el consumidor de este import y se retiró con ADR‑115.
import ROBINSON_PlusPlus.Meta.PremsBdAllPrf

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Deduction
import FOL.Theorems.Derived
import FOL.Theorems.Eq
import FOL.Theorems.Quantifiers
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Representability2

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`repr_pos'`, `d2`, `d3`, `godelCN_fixedpoint`, `hgi_es_refutar`, y los módulos `Meta/DerivCond.lean` y
> `Meta/OmegaStrength.lean`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.GodelTwo

/-!
## META — NIVEL D real: Segundo Teorema de Gödel sobre `provCodeC'` (registro)

🗑️ **2026‑10‑02 (ADR‑115) — registro.** Este docstring describe el módulo cuando tenía la cadena
de Gödel II sobre `⊢`: `goedel_second'` (retirado el 2026‑09‑11, ver abajo) y el teorema `d3`
(retirado con ADR‑115). **Hoy el módulo sólo define `consistencyFormula'`.** Gödel II está en
`Meta/GodelTwoPrf.lean`, sobre `Prf`: era ⛔ **vacuo** por `[AnclaEq]` (F1, ADR‑114) hasta ADR‑117, que
hizo del ancla un teorema; hoy su única hipótesis es `ConsistentH`.

Cierre del **núcleo lógico** de Gödel II para el predicado de demostrabilidad
estructural `provCodeC'`, con la cadena de Hilbert-Bernays-Löb:

* **D1** — sobre `⊢` era `repr_pos'` (`Meta/Representability2.lean`), retirado (ADR‑115). Sobre
  `Prf`: `repr_pos'_prf` (`Meta/Representability2Prf.lean`), con `[AnclaEq]` hasta ADR‑118.
* **D2** — sobre `⊢` era `d2` (`Meta/DerivCond.lean`, módulo retirado, ADR‑115). Sobre `Prf`:
  `d2_prf` (`Meta/DerivCondPrf.lean`).
* **D3** — sobre `⊢` era el teorema `d3` de este módulo, retirado (ADR‑115). 🏁 **TEOREMA desde el
  2026‑09‑10g**, ya no postulado: `d3_prf_real` (`Meta/PremsBdAllPrf.lean` §10; `[AnclaEq]`, hasta ADR‑118) la
  demuestra sobre `Prf`: Σ₁‑completitud provable por inducción objeto, con `pcc_eval_premsOf` (B1),
  el puente de la cota (B2) y el chasis interior (B3). ⇒ **ninguna de las tres es `axiom`**, y los
  `axiom` de Lean pasaron de **7 a 6** (cifra del 2026‑09‑10g; hoy 0 en RPP, ADR‑115). ⛔ Pero D1 y
  D3 llevaban `[AnclaEq]` en la firma, que daba `Prf ⊥` (F1, ADR‑114) hasta ADR‑117; desde ADR‑118 no hay
  ligadura: el ancla es el teorema `prf_ancla`. Detalle:
  `doc/REFERENCE-Incompleteness.md` §3.67.
  ⚠️ Este párrafo decía hasta el 2026‑09‑10 «postulado… la pieza pendiente más grande»: lo cazó la
  auditoría de `doc/book/AUDITORIA-2026-09-10.md` R3 — un docstring que contradecía a un
  teorema que estaba **33 líneas más abajo, en su propio fichero**.

⚠️ **ACTUALIZADO 2026‑08‑19:** el punto fijo pasó a ser `godelCN_fixedpoint`
(`Meta/DiagonalNumeral.lean`, sobre `⊢`; retirado con ADR‑115), sobre la sentencia **numeral**
`godelCN`; el de `godelC'` se retiró con `ax_tc_cons`. **Hoy** el punto fijo es
`prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`), sobre `Prf`. (`goedel_second'` no se vio
afectado: era modular y tomaba `fp_bwd` como hipótesis.)

Las dos condiciones restantes —el **punto fijo** (`godelCN ⇔ ¬provCodeC' godelCN`)
y la **necesitación** del condicional del punto fijo, junto con la
**indemostrabilidad ω** de `G` (mitad de Gödel I a nivel ω)— se exponían como
**hipótesis explícitas** (no se postulaban a la ligera): su realización honesta
necesitaba la adaptación del lema diagonal a `provFormulaC'` y el refactor
`Prf.thy → axioms` (para que la necesitación del punto fijo fuera Prf-demostrable).
Así el teorema era **verde**: la *lógica* de Gödel II era real, con **D2 real** en la
cadena, y las piezas no-cerradas quedaban **visibles** como hipótesis. ⛔ Pero su prueba (vía
`con_imp_godel'`) usaba la meta‑regla `imp_intro`, cuyo enunciado es falso: Lean más ella demuestra
`False` (ADR‑115 §1).

(Mejora sobre el `goedel_second` legacy, que postulaba **D2 y D3**; aquí D2 era real.)
-/


/-- **Fórmula de consistencia** `Con' := ¬ Prov'(⌜⊥⌝)`. -/
noncomputable def consistencyFormula' : Formula := neg (provCodeC' Formula.bottom)

/-! ## ⛔⛔ RETIRADOS el 2026‑09‑11: `con_imp_godel'` y `goedel_second'`

Aquí vivían `con_imp_godel' : axioms ⊢ (Con' ⇒ G)` y `goedel_second'`, la versión del Segundo
Teorema **sobre el cálculo `⊢`**. **Se retiran**, y no por deuda técnica: porque **decían algo que
no es**.

`Meta/OmegaStrength.lean` (módulo retirado con ADR‑115) midió que **`axioms ⊢` era sintácticamente
COMPLETO** —decidía toda sentencia—, porque `raa`/`imp_intro` toman como premisa una **función de
Lean** y lo que el cálculo no probaba, lo **refutaba**. Un cálculo que decide todo **no puede** ser el
sujeto de un teorema de incompletitud: **no es r.e.**, que es justo la hipótesis que Gödel I exige.
(ADR‑114 y ADR‑115 midieron después algo peor: Lean más cualquiera de las meta‑reglas demuestra
`False`; por eso la capa `⊢` entera se retiró, ADR‑115.)

⇒ La hipótesis `hgi : ¬(axioms ⊢ G)` de aquel teorema no significaba «`G` es indemostrable»: por
`hgi_es_refutar` (de `OmegaStrength`, retirado), significaba **«el cálculo REFUTA `G`»**. El
enunciado era una implicación correcta y **no era incompletitud**.

🏁 **El Segundo Teorema sobre el cálculo finitario `Prf`** —que **sí** es r.e.— está en
`Meta/GodelTwoPrf.lean`:

    goedel_second_prf (hcon : ConsistentH) : ¬ Prf consistencyFormula'

Hasta ADR‑117 llevaba también `[AnclaEq]`, que daba `Prf ⊥` (F1, ADR‑114): era vacuo. ⚠️ Hoy no lo es por
F1, pero la consistencia de los 142 axiomas sigue sin probar.
Su `prf_con_imp_godel` sustituye a `con_imp_godel'`, que sólo existía para alimentar a
`goedel_second'`.

⚠️ **Qué se conservó el 2026‑09‑11** (decisión del propietario, opción (b); ver
`doc/AUDITORIA-2026-09-11.md` F‑1 y [ADR‑024](../../DECISIONS.md)): el teorema `d3` y
`consistencyFormula'`. **Hoy sólo queda `consistencyFormula'`**, que `GodelTwoPrf` consume: `d3`
(D3 sobre `⊢`) se retiró con ADR‑115. D3 vive como `d3_prf_real` (`Meta/PremsBdAllPrf.lean`) y D2
como `d2_prf` (`Meta/DerivCondPrf.lean`), los dos sobre `Prf`. -/

end ROBINSON_PlusPlus.Meta.GodelTwo

export ROBINSON_PlusPlus.Meta.GodelTwo (
  consistencyFormula'
)

/-! (Aquí vivía el FOOTPRINT del teorema `d3`, sobre `⊢`; retirado con ADR‑115. El que importa es el
de `goedel_second_prf`, en `Meta/GodelTwoPrf.lean`.) -/


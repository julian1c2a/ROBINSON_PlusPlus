/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus

/-!
# SONDEO · ¿se puede sustituir `String` por algo más primitivo? — la medición que faltaba

**Fecha:** 2026‑09‑14 · **Origen:** análisis de **btw**, recogido en
`doc/PLAN-COMPLETITUD-FINITISTA.md` §7.2.

## Por qué existe este fichero

El análisis de btw declaraba **una medición pendiente**, y era la que decidía su propia
recomendación:

> *«`Char` no está verificado del todo. Está medido que `Char.ofNat`, `Char.ofNat_toNat` y
> `charsCode` son limpios, pero no `DecidableEq Char` ni la aritmética de `UInt32` por debajo. Si
> eso arrastrara choice, `List Char` pierde la gracia y habría que ir a `Nat` o `List Bool`. Es una
> medición de tres líneas, pero no está hecha.»*

Hecha. **Sale limpia.**

## El resultado

| constante | footprint |
|---|---|
| `Char` | **sin axiomas** |
| `Char.val` · `Char.ofNat` · `Char.toNat` | **sin axiomas** |
| `Char.ofNat_toNat` | **sin axiomas** |
| `Char.isValidCharNat` | **sin axiomas** |
| `instDecidableEqChar` | **sin axiomas** |
| `DecidableEq (List Char)` | **sin axiomas** |
| `ROBINSON_PlusPlus.Meta.Provability.charsCode` | **sin axiomas** (ya medido el 09‑13) |

⇒ ⭐ **La recomendación de btw queda confirmada por medición**: `List Char` cumple los cuatro
requisitos —`DecidableEq` limpio, infinito numerable, codificación limpia a `Term`, literales
legibles— y **`strCode` se convierte literalmente en `charsCode`**, que ya está limpio.

⚠️ **Y `String` es lo único sucio de la cadena.** Medido el 09‑13
(`sondeos/ClassicalChoiceCenso.lean`): `strCode s := charsCode s.toList`, y `String.toList` trae
`Classical.choice`. **La cadena de Gödel entera está a una composición de estar limpia.**

## ⚠️ Lo que esto NO dice

* **No mide la propagación.** El proyecto tiene el escarmiento escrito: el cierre por nombres
  sobreestimó por **dos órdenes de magnitud**, y sólo el compilador vale
  (`feedback_medicion_propagacion`). ⬜ **No medido.**
* **No decide nada.** Cambiar la firma **cambia `G`**: cambia `strCode`, y con él `formCode`,
  `axiomsCodeT`, `provCodeC'` y la sentencia de Gödel. Los teoremas son paramétricos y *deberían*
  sobrevivir, pero hay muchos puentes por `rfl` que habría que re‑verificar uno a uno.
  🔑 *Eso es una estimación, y va etiquetada como tal.*
-/

namespace SimbolosSinString

-- ── La medición que faltaba ────────────────────────────────────────────────
#print axioms Char
#print axioms Char.val
#print axioms Char.ofNat
#print axioms Char.toNat
#print axioms Char.ofNat_toNat
#print axioms Char.isValidCharNat
#print axioms instDecidableEqChar

/-- La igualdad decidible que usaría el `filter` de Henkin con símbolos `List Char`. -/
def decEqListChar : DecidableEq (List Char) := inferInstance

#print axioms decEqListChar

-- ── El contraste, para que se vea dónde está la suciedad ───────────────────
#print axioms ROBINSON_PlusPlus.Meta.Provability.charsCode   -- ✅ sin axiomas
#print axioms ROBINSON_PlusPlus.Meta.Provability.strCode     -- ⛔ = charsCode s.toList
#print axioms String.toList                                  -- ⛔ la causa

end SimbolosSinString

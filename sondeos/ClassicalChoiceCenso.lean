/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus

/-!
# SONDEO · de dónde sale `Classical.choice` en los dos repos

**Fecha:** 2026‑09‑14 · **Encargo:** *«¿hay usos de `Classical.choice` en FOL que puedan
eliminarse de forma totalmente constructiva? Y el mismo análisis en RPP.»*

## 0 · El censo, medido

Barrido con `collectAxioms` sobre **todas** las declaraciones de los dos paquetes
(`.thmInfo`/`.defnInfo`/`.axiomInfo`, sin internas):

| | declaraciones | con `Classical.choice` |
|---|---:|---:|
| `FOL` (antes del arreglo de hoy) | 411 | **26** |
| `FOL` (después) | 411 | **16** |
| `FOL` + `ROBINSON_PlusPlus` | 5 045 | **3 143** (62 %) |

⚠️ El grafo de dependencias **no** se puede recorrer con `ConstantInfo.value?`: en Lean v4.31 los
cuerpos de los teoremas importados llegan **perezosos** y `value?` da `none`. Medido. El análisis
de abajo se hizo bisecando con pruebas, no con el grafo.

## 1 · ⭐ CAUSA A — `omega` cerrando una rama imposible (MECÁNICA, se quita)

Es la causa en `FOL/Theorems/Eq.lean`, y el arreglo está aplicado: **26 → 16** en FOL.

⚠️⚠️ **Y aquí hay que tener cuidado con el enunciado de la regla, porque mi primera versión era
demasiado general y este mismo fichero la habría desmentido.** Lo medido es esto:

| fichero de prueba | `theorem (h : n < c) (hEq : n = c) : s = t := by omega` |
|---|---|
| `import FOL.FOL` | ⛔ `[propext, Classical.choice, Quot.sound]` |
| `import ROBINSON_PlusPlus` | ✅ `[propext, Quot.sound]` |
| sin imports, con `s t : Nat` | ✅ `[propext, Quot.sound]` |

**El mismo enunciado y la misma táctica dan footprints distintos según el CONTEXTO DE IMPORTS.**
⇒ 🔑 **El footprint de una táctica automática no es propiedad ni del enunciado ni de la táctica:
depende del entorno.** Por eso §A de abajo —que importa `ROBINSON_PlusPlus`— sale limpio: para
reproducir la variante sucia hay que compilar el mismo teorema con **sólo** `import FOL.FOL`.

✅ **Lo que SÍ es robusto, medido en los dos contextos**: `exfalso; omega` y `absurd h (by omega)`
salen limpios **siempre**. Y el estilo `by_cases` + `simp` (el que ya usaba el hermano
`substTerm_lift_comm`, que nunca estuvo sucio) también.

⇒ 🔑 **La regla operativa**: *no dejes que una táctica automática cierre una rama imposible sobre
un objetivo que no es de su dominio; mándala a `False` tú primero.* Es barato y no depende del
entorno.

⚠️ **Descartados por medición** (todos limpios): `split`, `by_cases`, `unfold`, `simp` sobre las
ecuaciones de una definición mutua, `Nat.lt_trichotomy`, `Nat.le_of_not_lt`, `Nat.lt_of_le_of_ne`.

## 2 · ⛔ CAUSA B — `String`, y es IRREDUCIBLE

En Lean v4.31 `String` es **UTF‑8 opaco** (`toByteArray` + `IsValidUTF8`), y **toda operación que
DESCOMPONE una cadena** trae `Classical.choice`. Medido, §B de abajo: `toList`, `data`, `foldr`,
`foldl`, `length`, `get` sucias; `ofList`, `iter`, `toSubstring`, `toByteArray`, `decEq` limpias.

⇒ En RPP la raíz son **dos líneas**:

    Meta/Provability.lean:39   def strCode  (s : String) : Term := charsCode  s.toList
    Minimal/Axioms.lean:568    def strCodeM (s : String) : Term := charsCodeM s.toList

`charsCode`/`charsCodeM` (sobre `List Char`) **no dependen de ningún axioma**; `strCode`/`strCodeM`
y, tras ellos, `termCode`/`formCode`/`termCodeM`/`formCodeM` sí. Y como toda la cadena de Gödel
pasa por ahí, **la mayor parte de las 3 143 es esto**.

## 3 · 🔑 La regla que sale de aquí

> **El footprint NO distingue la no‑constructividad MATEMÁTICA de la deuda de IMPLEMENTACIÓN del
> núcleo.**

`strCode` es una función **computable y perfectamente constructiva**: recorre los caracteres y
construye un `Term`. Su `Classical.choice` no dice nada sobre la matemática del proyecto; dice
cómo implementa `String` la v4.31 de Lean. ⚠️ En un proyecto que **lee footprints como evidencia**,
esto es una trampa de interpretación, y conviene tenerla escrita.

⬜ **Y el corolario para el plan finitista**: si alguna vez se quiere un FOL⁼ realmente
constructivo, lo que hay que quitar **no es un axioma, es `String` de la firma** —
`Term.func : String → List Term → Term` con `Nat` (o un tipo de símbolos abstracto con
`DecidableEq`) en su lugar. Eso limpiaría también las 6 de `FOL/Enumeration.lean`, que hoy vienen
de `String.ofList_toList`.

⚠️ Este fichero **no entra en el build**. Reejecutar con
`lake env lean sondeos/ClassicalChoiceCenso.lean` desde la raíz de RPP.
-/

namespace ChoiceCenso

open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Minimal.Axioms

-- ════════════════════════════════════════════════════════════════
-- §A · CAUSA A · las variantes ROBUSTAS
-- ════════════════════════════════════════════════════════════════
--
-- ⚠️ Este fichero importa `ROBINSON_PlusPlus`, y en ESE contexto `a_omega` sale LIMPIO.
-- La variante sucia se reproduce con **sólo** `import FOL.FOL` (ver §1: es la misma prueba
-- con otro entorno). Lo que aquí se certifica es que `exfalso; omega` y `absurd _ (by omega)`
-- son limpios **también** aquí ⇒ son la forma que no depende del contexto.

theorem a_omega    (n c : Nat) (s t : Term) (h : n < c) (hEq : n = c) : s = t := by omega
theorem a_exfalso  (n c : Nat) (s t : Term) (h : n < c) (hEq : n = c) : s = t := by exfalso; omega
theorem a_absurd   (n c : Nat) (s t : Term) (h : n < c) (hEq : n = c) : s = t := absurd hEq (by omega)
theorem a_arit     (n c : Nat) (h : n < c) : n + 1 ≤ c := by omega

#print axioms a_omega     -- ⚠️ LIMPIO AQUÍ, sucio con sólo `import FOL.FOL`
#print axioms a_exfalso   -- ✅ limpio en los dos contextos
#print axioms a_absurd    -- ✅ limpio en los dos contextos
#print axioms a_arit      -- ✅ objetivo aritmético

-- Lo que NO era la causa, descartado midiendo:
#print axioms Nat.lt_trichotomy      -- limpio
#print axioms Nat.le_of_not_lt       -- limpio
#print axioms Nat.lt_of_le_of_ne     -- limpio

-- ════════════════════════════════════════════════════════════════
-- §B · CAUSA B · el `String` del núcleo de Lean v4.31
-- ════════════════════════════════════════════════════════════════

-- DESCOMPONER una cadena ensucia:
#print axioms String.toList
#print axioms String.data
#print axioms String.foldr
#print axioms String.foldl
#print axioms String.length
#print axioms String.get

-- CONSTRUIRLA o compararla, no:
#print axioms String.ofList
#print axioms String.iter
#print axioms String.toSubstring
#print axioms String.toByteArray
#print axioms String.decEq        -- ⭐ un `DecidableEq Formula` REAL es construible sin choice

-- ════════════════════════════════════════════════════════════════
-- §C · la raíz en RPP: una sola llamada, `s.toList`
-- ════════════════════════════════════════════════════════════════

#print axioms charsCode       -- ✅ sin axiomas   (sobre `List Char`)
#print axioms strCode         -- ⛔ = charsCode s.toList
#print axioms termCode        -- ⛔ (vía strCode)
#print axioms formCode        -- ⛔

#print axioms charsCodeM      -- ✅ sin axiomas
#print axioms strCodeM        -- ⛔
#print axioms termCodeM       -- ⛔
#print axioms formCodeM       -- ⛔

#print axioms numeralM        -- ✅ sin axiomas
#print axioms axiomsCodeT     -- ✅ sin axiomas  ⭐ no toca `String`

end ChoiceCenso

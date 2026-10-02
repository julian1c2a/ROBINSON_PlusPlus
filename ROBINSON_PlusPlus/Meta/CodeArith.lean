/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Full.Numerals

import FOL.FOL
import FOL.Theorems.Eq

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`gnum_ne`, `gnum_add`, `gnum_mul`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeArith

/-!
## META — NIVEL D (real): aritmética de códigos  (Fase 2, sub-paso 2.1)

Cimiento universal de la **representabilidad** (Fase 2, aritmetización total).
Los códigos de Gödel (`formCode`, `ruleCode`, …) se construyen con
`Meta.Godel.numeral`, mientras que los hechos aritméticos object-level sobre
`Full.numeral` (misma definición, distinto namespace) vivían en `Full.Numerals`,
sobre `⊢`. Aquí se tendía el **puente** y se re-exponía esa aritmética para los
códigos de Gödel:

* `numeral_bridge` : `Meta.Godel.numeral = Full.numeral`.
* `gnum_ne` : `a ≠ b → ⊢ ¬(⌜a⌝ = ⌜b⌝)` (separación: la teoría distingue numerales
  distintos — clave para decidir igualdades de tags/índices en el verificador).
* `gnum_add` / `gnum_mul` : homomorfismos `+`/`·`.

🗑️ Los `gnum_*` y esa aritmética de `Full.Numerals` eran de `⊢`: retirados con esa capa (ADR‑115).
Aquí queda sólo `numeral_bridge`, que usan sus gemelos en `Prf`: `prf_gnum_add`
(`Meta/CodeNumeralPrf.lean`), `prf_gnum_lt` (`Meta/ArithPrf.lean`) y `prf_gnum_mul`
(`Meta/Div2ParityPrf.lean`).

Patrón general (el de `Full.Numerals`, que siguen hoy esos gemelos): la **inducción meta** (en
Lean) demuestra hechos de **cómputo object-level**; el cálculo no necesita inducción, solo las
ecuaciones recursivas de cada función. Este es el motor de toda la Fase 2.
-/

/-- Las dos definiciones de `numeral` (Meta.Godel y Full) coinciden punto a punto. -/
theorem numeral_bridge (n : Nat) :
    ROBINSON_PlusPlus.Meta.Godel.numeral n = ROBINSON_PlusPlus.Full.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [ROBINSON_PlusPlus.Meta.Godel.numeral, ROBINSON_PlusPlus.Full.numeral, ih]


end ROBINSON_PlusPlus.Meta.CodeArith

export ROBINSON_PlusPlus.Meta.CodeArith (
  numeral_bridge
)

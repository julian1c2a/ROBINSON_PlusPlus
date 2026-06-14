/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Full.Numerals

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeArith

/-!
## META — NIVEL D (real): aritmética de códigos  (Fase 2, sub-paso 2.1)

Cimiento universal de la **representabilidad** (Fase 2, aritmetización total).
Los códigos de Gödel (`formCode`, `ruleCode`, …) se construyen con
`Meta.Godel.numeral`, mientras que los hechos aritméticos object-level ya
demostrados viven en `Full.Numerals` sobre `Full.numeral` (misma definición,
distinto namespace). Aquí tendemos el **puente** y re-exponemos la aritmética de
numerales para los códigos de Gödel:

* `numeral_bridge` : `Meta.Godel.numeral = Full.numeral`.
* `gnum_ne` : `a ≠ b → ⊢ ¬(⌜a⌝ = ⌜b⌝)` (separación: la teoría distingue numerales
  distintos — clave para decidir igualdades de tags/índices en el verificador).
* `gnum_add` / `gnum_mul` : homomorfismos `+`/`·`.

Patrón general (de `Full.Numerals`): la **inducción meta** (en Lean) demuestra
hechos de **cómputo object-level**; la teoría `⊢` no necesita inducción, solo las
ecuaciones recursivas de cada función. Este es el motor de toda la Fase 2.
-/

/-- Las dos definiciones de `numeral` (Meta.Godel y Full) coinciden punto a punto. -/
theorem numeral_bridge (n : Nat) :
    ROBINSON_PlusPlus.Meta.Godel.numeral n = ROBINSON_PlusPlus.Full.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [ROBINSON_PlusPlus.Meta.Godel.numeral, ROBINSON_PlusPlus.Full.numeral, ih]

/-- **Separación de códigos numéricos**: numerales meta distintos tienen códigos
    que la teoría **refuta** como iguales. (Re-expuesto de `Full.numeral_ne`.) -/
theorem gnum_ne {a b : Nat} (h : a ≠ b) :
    axioms ⊢ neg (ROBINSON_PlusPlus.Meta.Godel.numeral a =eq ROBINSON_PlusPlus.Meta.Godel.numeral b) := by
  rw [numeral_bridge, numeral_bridge]
  exact ROBINSON_PlusPlus.Full.numeral_ne h

/-- Reflexividad de igualdad de códigos (igual ⟹ provablemente igual). Trivial
    pero es la mitad "positiva" que usa la representabilidad-completitud. -/
theorem gnum_refl (n : Nat) :
    axioms ⊢ (ROBINSON_PlusPlus.Meta.Godel.numeral n =eq ROBINSON_PlusPlus.Meta.Godel.numeral n) :=
  eq_refl _

/-- Homomorfismo aditivo para códigos numéricos. (Re-expuesto de `Full.numeral_add`.) -/
theorem gnum_add (a b : Nat) :
    axioms ⊢ (add (ROBINSON_PlusPlus.Meta.Godel.numeral a) (ROBINSON_PlusPlus.Meta.Godel.numeral b)
      =eq ROBINSON_PlusPlus.Meta.Godel.numeral (a + b)) := by
  rw [numeral_bridge, numeral_bridge, numeral_bridge]
  exact ROBINSON_PlusPlus.Full.numeral_add a b

/-- Orden estricto para códigos numéricos. (Re-expuesto de `Full.numeral_lt`.) -/
theorem gnum_lt {a b : Nat} (h : a < b) :
    axioms ⊢ lt (ROBINSON_PlusPlus.Meta.Godel.numeral a) (ROBINSON_PlusPlus.Meta.Godel.numeral b) := by
  rw [numeral_bridge, numeral_bridge]
  exact ROBINSON_PlusPlus.Full.numeral_lt h

/-- Homomorfismo multiplicativo para códigos numéricos. (De `Full.numeral_mul`.) -/
theorem gnum_mul (a b : Nat) :
    axioms ⊢ (mul (ROBINSON_PlusPlus.Meta.Godel.numeral a) (ROBINSON_PlusPlus.Meta.Godel.numeral b)
      =eq ROBINSON_PlusPlus.Meta.Godel.numeral (a * b)) := by
  rw [numeral_bridge, numeral_bridge, numeral_bridge]
  exact ROBINSON_PlusPlus.Full.numeral_mul a b

end ROBINSON_PlusPlus.Meta.CodeArith

export ROBINSON_PlusPlus.Meta.CodeArith (
  numeral_bridge
  gnum_ne
  gnum_refl
  gnum_add
  gnum_mul
)

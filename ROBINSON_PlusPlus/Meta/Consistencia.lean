/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ModeloCodificacion
import ROBINSON_PlusPlus.Meta.SolidezPrf
import ROBINSON_PlusPlus.Meta.GodelTwoPrf

/-!
# `Meta/Consistencia.lean` — 🏁🏁 `ConsistentH` es un TEOREMA, y Gödel I y II van SIN HIPÓTESIS (ADR‑120)

* `estandar_MN : Estandar (MNV V₀)` — cada campo INSTANCIA un lema probado para `V` arbitrario.
* `consistencia : ConsistentH` — `¬ Prf ⊥`: `MNV V₀` es un modelo de los 142 (`MN_axioms`) y `Prf` es sólido
  en todo modelo estándar (`prf_sound`).
* `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'` — `goedel_first_prf` y
  `goedel_second_prf` (`Meta/GodelTwoPrf.lean`), aplicados a `consistencia`.

Footprint de los tres: `[propext, Classical.choice, Quot.sound]` (`check-footprints`).

⚠️ Lo que NO dice: que `G` y `Con` sean VERDADERAS en `MNV V₀` —no hace falta para lo de arriba—; que
`V₀ = codeNatList axioms`, es decir, que en el modelo la regla `thy` acepte exactamente los 142 (E10 lo pediría;
un cálculo a mano dice que sí, sin medir); ni nada de `⊬¬G` (Rosser).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## §7 · `ConsistentH`, TEOREMA; y Gödel I/II sin hipótesis -/

namespace ROBINSON_PlusPlus.Meta.Consistencia

section Final
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.ModeloEstandar
open ROBINSON_PlusPlus.Meta.ModeloCodificacion

/-- `MNV V₀` es estándar. `hzero`, `hsucc` y `hcons` INSTANCIAN lemas `rfl` demostrados para `V` arbitrario —⛔
    ningún `rfl` compara nada con `V₀`: el núcleo desplegaría `V₀` antes que `MNV`, por altura de definición, y no
    acabaría—; `haxs` es `MN_axioms`, propio de `V₀` porque el ancla fija `V`: junta `MN_coreAxioms` y
    `MN_codingAxioms` (genéricos en `V`) con `v_ancla`. -/
theorem estandar_MN : ROBINSON_PlusPlus.Meta.SolidezPrf.Estandar (MNV V₀) where
  hzero := MN_zero
  hsucc := MN_succ
  hcons := MN_cons
  haxs := MN_axioms

/-- 🏁 **Los 142 son CONSISTENTES**: `Prf ⊥` no tiene prueba, porque `MNV V₀` satisface los 142 (`MN_axioms`). -/
theorem consistencia : ConsistentH := ROBINSON_PlusPlus.Meta.SolidezPrf.consistentH_de estandar_MN

/-- 🏁 **GÖDEL I, sin hipótesis.** -/
theorem goedel_I : ¬ Prf ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf consistencia

/-- 🏁 **GÖDEL II, sin hipótesis.** -/
theorem goedel_II : ¬ Prf ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf consistencia

end Final

end ROBINSON_PlusPlus.Meta.Consistencia

#print axioms ROBINSON_PlusPlus.Meta.Consistencia.consistencia
#print axioms ROBINSON_PlusPlus.Meta.Consistencia.goedel_I
#print axioms ROBINSON_PlusPlus.Meta.Consistencia.goedel_II

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ModeloCodificacion
import ROBINSON_PlusPlus.Meta.SolidezPrf
import ROBINSON_PlusPlus.Meta.SolidezDobleNegacion
import ROBINSON_PlusPlus.Meta.Representability2Prf

/-!
# `Meta/Consistencia.lean` — 🏁🏁 `ConsistentH` es un TEOREMA (ADR‑120)

* `estandar_MN : Estandar (MNV V₀)` — cada campo INSTANCIA un lema probado para `V` arbitrario.
* `consistencia : ConsistentH` — `¬ Prf ⊥`: `MNV V₀` es un modelo de los 120 (`MN_axioms`) y `Prf` es sólido
  en todo modelo estándar leído por la traducción doble‑negada (`prf_sound_dn`, `Meta/SolidezDobleNegacion.lean`,
  ADR‑191), sin lógica clásica.
* ✏️ 2026‑11‑17 (ADR‑269): `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'` —Gödel I y II sin
  hipótesis: `goedel_first_prf` y `goedel_second_prf` (`Meta/GodelTwoPrf.lean`) aplicados a `consistencia`— están en
  `Meta/TitularesII.lean`, con los titulares de la clase (ii) (las capas de ADR‑266): este módulo es de C5 y no
  importa los de la clase (i).

Footprint de `consistencia` (y de los dos de Gödel): `[propext, Quot.sound]` desde ADR‑191 (`check-footprints`; hasta entonces llevaban
`Classical.choice`, de la regla `p3` en `prf_sound`).

Y `V₀_eq_codigo : V₀ = codeNatList axioms` (ADR‑121): en el modelo, la regla `thy` acepta exactamente los 120.
La otra mitad de Gödel I (`⊬ ¬G`), y que `G` y `Con` son VERDADERAS en `MNV V₀`, están en
`Meta/TitularesIII.lean` (ADR‑121; ✏️ ADR‑268: estaban en `Meta/SolidezVerificador.lean`). ⚠️ Lo que NO dice: nada de Rosser.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## §7 · `ConsistentH`, TEOREMA (Gödel I/II sin hipótesis, en `Meta/TitularesII.lean`: ADR‑269) -/

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

/-- …y lo es de la lectura doble‑negada (`estandarDN_de`, ADR‑191): con él se lee en el modelo lo que `Prf` demuestra,
    sin lógica clásica. -/
theorem estandarDN_MN : ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.EstandarDN (MNV V₀) :=
  ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.estandarDN_de estandar_MN

/-- 🏁 **`T_Prf` es CONSISTENTE** (los 120 con los esquemas de `Prf`): `Prf ⊥` no tiene prueba, porque `MNV V₀` es
    estándar y satisface los 120 (`estandar_MN`), y `Prf` es sólido en todo modelo estándar, leído por la traducción
    doble‑negada (`consistentH_de`, ADR‑191): sin lógica clásica, `[propext, Quot.sound]`.
    ⚠️ **La consistencia es RELATIVA a Lean** (ADR‑138; ✏️ 2026‑10‑17, ADR‑155): es un teorema de Lean, y fuera de Lean
    da PRA ⊢ Con(Lean) → Con(T_Prf), si el núcleo implementa bien su teoría de tipos. Absoluta no puede ser: `T_Prf`
    contiene a PA, y por Gödel II la metateoría que la demuestra es por fuerza más fuerte que ella. El detalle, en
    `TEOREMAS-E-HIPOTESIS.md` §4.
    (✏️ 2026‑10‑14: decía «Los 142 son CONSISTENTES… porque `MNV V₀` satisface los 142 (`MN_axioms`)».) -/
theorem consistencia : ConsistentH := ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.consistentH_de estandar_MN

/-- 🏁 En `MNV V₀`, `axiomsCodeT` vale EXACTAMENTE el código de los 120 (ADR‑121): `prf_ancla` —el ancla es teorema—
    por la solidez. Es lo que dice que, en el modelo, la regla `thy` acepta exactamente los 120. Desde ADR‑191, por la
    solidez doble‑negada: el ancla es una igualdad, y en `Nat` la igualdad es decidible (`eq_de_prf`). -/
theorem V₀_eq_codigo : V₀ = codeNatList axioms := by
  have h' : evalTerm (MNV V₀) (fun _ => 0) axiomsCodeT =
      evalTerm (MNV V₀) (fun _ => 0) (listFormCodeM axioms) :=
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.eq_de_prf estandarDN_MN
      ROBINSON_PlusPlus.Meta.Representability2Prf.prf_ancla (fun _ => 0)
  rw [ev_axiomsCodeT, ev_listFormCodeM] at h'
  exact h'

end Final

end ROBINSON_PlusPlus.Meta.Consistencia

#print axioms ROBINSON_PlusPlus.Meta.Consistencia.consistencia
#print axioms ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.Rosser
import ROBINSON_PlusPlus.Meta.Consistencia

/-!
# `Meta/TitularesII.lean` — los titulares de la clase (ii): usan el modelo SÓLO a través de `consistencia` (C7.ii; ADR‑268)

Las capas de ADR‑266: todos los titulares en C7, separados por clase. Aquí, por ahora, `tarski` (de
`Meta/TarskiPrf.lean`) y `rosser` (de `Meta/Rosser.lean`), los dos sin hipótesis porque `consistencia` descarga la de
su versión sintáctica (`prf_tarski`, `rosser_ext`, de la clase (i)). Vendrán en el paso 4 de ADR‑266 `goedel_I` y
`goedel_II` (de `Meta/Consistencia.lean`) y los dos de Gödel en FOL (de `Meta/PuenteFOL.lean`). Mismos enunciados y
pruebas; el espacio de nombres es el de este fichero (NAMING‑CONVENTIONS §6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ROBINSON_PlusPlus.Meta.TitularesII

section Tarski
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.Sentencia
open ROBINSON_PlusPlus.Meta.TarskiPrf

/-- 🏁 **TARSKI**, sin hipótesis (`consistencia`, ADR‑120): ninguna `Tr` define la verdad en la teoría —`Tr(⌜L⌝) ⇔ L`
    no es teorema en su propio mentiroso `L`—. -/
theorem tarski (Tr : Formula) :
    ¬ Prf (substFormula 0 (numeral (codeNat (liar Tr))) Tr ⇔ liar Tr) :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prf_mp (prf_tarski Tr) h)

end Tarski

section Rosser
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.TarskiPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.RosserNegNum ROBINSON_PlusPlus.Meta.Sentencia
open ROBINSON_PlusPlus.Meta.Rosser

/-- 🏁 **ROSSER para T, sin hipótesis** (con `consistencia`): ni `R []` ni `¬R []` son teoremas. -/
theorem rosser : And (¬ Prf (R [])) (¬ Prf (neg (R []))) := by
  have h := rosser_ext [] (fun _ hm => nomatch hm)
    (fun hb => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prfH_nil_to_prf hb rfl))
  exact ⟨fun hp => h.1 (prf_to_prfH hp []), fun hp => h.2 (prf_to_prfH hp [])⟩

end Rosser

end ROBINSON_PlusPlus.Meta.TitularesII

#print axioms ROBINSON_PlusPlus.Meta.TitularesII.tarski
#print axioms ROBINSON_PlusPlus.Meta.TitularesII.rosser

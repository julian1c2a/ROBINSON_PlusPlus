/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.Rosser
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.PuenteFOL

/-!
# `Meta/TitularesII.lean` — los titulares de la clase (ii): usan el modelo SÓLO a través de `consistencia` (C7.ii; ADR‑268)

Las capas de ADR‑266: todos los titulares en C7, separados por clase. Aquí, los SEIS de la clase (ii): `tarski` (de
`Meta/TarskiPrf.lean`) y `rosser` (de `Meta/Rosser.lean`), desde ADR‑268; y `goedel_I` y `goedel_II` (de
`Meta/Consistencia.lean`) y `goedel_I_fol` y `goedel_II_fol` (de `Meta/PuenteFOL.lean`), desde ADR‑269. Los cuatro
primeros, sin hipótesis, porque `consistencia` descarga la de su versión sintáctica, de la clase (i) (`prf_tarski`,
`rosser_ext`, `goedel_first_prf`, `goedel_second_prf`); los dos de FOL, con la del conjunto de teoremas (`hS`). Mismos
enunciados y pruebas; el espacio de nombres es el de este fichero (NAMING‑CONVENTIONS §6).
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

section Consistencia
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.ModeloEstandar
open ROBINSON_PlusPlus.Meta.ModeloCodificacion
open ROBINSON_PlusPlus.Meta.Consistencia

/-- 🏁 **GÖDEL I, la mitad `⊬ G`, sin hipótesis** (la otra, `goedel_I_neg`, en `Meta/TitularesIII.lean`). -/
theorem goedel_I : ¬ Prf ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf consistencia

/-- 🏁 **GÖDEL II, sin hipótesis.** -/
theorem goedel_II : ¬ Prf ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf consistencia

end Consistencia

section PuenteFOL
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open FOL.Metamath.Semantics FOL.Henkin0
open ROBINSON_PlusPlus.Meta.PuenteFOL

/-- 🏁 **Gödel I en FOL** (titular, ADR‑210): ningún conjunto `S` de teoremas de `Prf` deriva `G` en la lógica de
    primer orden de FOL. `S` puede ser `AxiomasT` (los 120 y las instancias de los dos esquemas: `prf_of_axiomasT`),
    sus clausuras universales (teoremas de `Prf` por `gen`) o todos los teoremas a la vez; el enunciado de libro, «las
    clausuras de T no derivan G», es una instancia, y no pide que los 120 sean sentencias. -/
theorem goedel_I_fol {S : Formula → Prop} (hS : ∀ φ, S φ → Prf φ) :
    ¬ DerivesSet₀ S ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  fun h => ROBINSON_PlusPlus.Meta.TitularesII.goedel_I (prf_of_derivesSet hS h)

/-- 🏁 **Gödel II en FOL** (titular, ADR‑210): ningún conjunto de teoremas de `Prf` deriva en FOL la consistencia
    de `T_Prf`. -/
theorem goedel_II_fol {S : Formula → Prop} (hS : ∀ φ, S φ → Prf φ) :
    ¬ DerivesSet₀ S ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun h => ROBINSON_PlusPlus.Meta.TitularesII.goedel_II (prf_of_derivesSet hS h)

-- La hipótesis no es vacía: la cumplen `AxiomasT` y el conjunto de TODOS los teoremas de `Prf` (que contiene las
-- clausuras universales de los axiomas, por `gen`).
example : ¬ DerivesSet₀ AxiomasT ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  goedel_I_fol (fun _ => prf_of_axiomasT)
example (A : Formula) (h : AxiomasT A) : Prf (Formula.forall A) := Prf.gen A (prf_of_axiomasT h)
example : ¬ DerivesSet₀ (fun g => Prf g) ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  goedel_II_fol (fun _ h => h)

-- Las clausuras de `AxiomasT` no derivan `G` en FOL: el enunciado de libro, una instancia más de `goedel_I_fol`.
example : ¬ DerivesSet₀ ClausurasT ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  goedel_I_fol (fun _ => prf_of_clausurasT)

end PuenteFOL

end ROBINSON_PlusPlus.Meta.TitularesII

#print axioms ROBINSON_PlusPlus.Meta.TitularesII.tarski
#print axioms ROBINSON_PlusPlus.Meta.TitularesII.rosser
#print axioms ROBINSON_PlusPlus.Meta.TitularesII.goedel_I
#print axioms ROBINSON_PlusPlus.Meta.TitularesII.goedel_II
#print axioms ROBINSON_PlusPlus.Meta.TitularesII.goedel_I_fol
#print axioms ROBINSON_PlusPlus.Meta.TitularesII.goedel_II_fol

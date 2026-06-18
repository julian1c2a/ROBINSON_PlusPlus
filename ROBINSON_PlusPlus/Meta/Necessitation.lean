/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.Hilbert

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Representability

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Necessitation

/-!
## META — NIVEL D (real): condición D1 (necesitación)  (Fase 3)

`repr_pos` (Fase 2.5) ES la condición de demostrabilidad **D1** honesta para el
sistema finitario de Hilbert `Prf` y su predicado de demostrabilidad object
`provCodeC` (= `provFormulaC[⌜·⌝]`, una `Formula` Σ₁ **concreta**, no postulada):

> **D1 (necesitación):** `Prf φ ⟹ axioms ⊢ Prov(⌜φ⌝)`.

Es decir, *si `φ` es demostrable en el sistema finitario, la teoría verificadora
demuestra el enunciado aritmetizado «`⌜φ⌝` es demostrable»*. Esto **reemplaza la
dirección `.mpr` del postulado `provFormula_repr`** (`Meta/Incompleteness.lean`,
legacy) por un teorema.

**Asimetría honesta (Tarski).** Sólo se obtiene esta dirección. La recíproca
(*reflexión*: `axioms ⊢ Prov(⌜φ⌝) ⟹ …`) muere por la indefinibilidad de la
verdad y, además, `provCodeC` rastrea la demostrabilidad **finitaria** `Prf`, no
la ω-demostrabilidad `axioms ⊢` (que prueba estrictamente más); se difiere a 2.6.

**Sistemas en juego.** La teoría *object* (cuya demostrabilidad se aritmetiza) es
`Prf` (finitaria, r.e.). La teoría *verificadora* es la base `axioms ⊢` (incluye
las ω-reglas), que contiene a `Prf` vía `prf_to_derives`. D1 va de la primera a la
segunda — el encuadre estándar.
-/

/-- **D1 (necesitación) real**: si `φ` es demostrable en el cálculo finitario de
    Hilbert `Prf`, la teoría demuestra el enunciado aritmetizado de su
    demostrabilidad `provCodeC φ`. Es `repr_pos` (Fase 2.5) leído como condición
    de demostrabilidad de Hilbert–Bernays–Löb. -/
theorem d1 {φ : Formula} (h : Prf φ) : axioms ⊢ provCodeC φ := repr_pos h

/-- Alias con el nombre clásico de la condición. -/
theorem necessitation {φ : Formula} (h : Prf φ) : axioms ⊢ provCodeC φ := repr_pos h

/-!
### Primer Teorema de Incompletitud (mitad de indemostrabilidad) — versión real

Forma **modular**: dada una sentencia de punto fijo `G ⇔ ¬Prov(⌜G⌝)` para el
predicado **concreto** `provCodeC`, D1 (real, sin postular) basta para la mitad de
indemostrabilidad de Gödel I. La construcción del punto fijo (lema diagonal para
`provCodeC`) es representabilidad de la sustitución y se difiere; aquí se toma como
hipótesis explícita en vez de postularse globalmente.
-/

/-- **Gödel I real (indemostrabilidad), modular.** Si la teoría verificadora es
    consistente y existe un punto fijo `G ⇔ ¬Prov(⌜G⌝)` para `provCodeC`, entonces
    `G` **no** es demostrable en el sistema finitario `Prf`.

    Prueba: si `Prf G`, por **D1** `axioms ⊢ Prov(⌜G⌝)`; por `prf_to_derives`
    `axioms ⊢ G`, y con el punto fijo `axioms ⊢ ¬Prov(⌜G⌝)`; modus ponens da
    `axioms ⊢ ⊥`, contra la consistencia. **Usa D1 honesto (no postulado).** -/
theorem goedel_first_unprovable_real {G : Formula}
    (hcon : ConsistentOmega)
    (hfp : axioms ⊢ (G ⇔ neg (provCodeC G))) :
    ¬ Prf G := by
  intro hG
  have hProv : axioms ⊢ provCodeC G := d1 hG
  have hGder : axioms ⊢ G := prf_to_derives hG
  have fp_fwd : axioms ⊢ (G ⇒ neg (provCodeC G)) := Minimal.Axioms.and_elim_left hfp
  have hNotProv : axioms ⊢ neg (provCodeC G) := mp fp_fwd hGder
  exact hcon (mp hNotProv hProv)

end ROBINSON_PlusPlus.Meta.Necessitation

export ROBINSON_PlusPlus.Meta.Necessitation (
  d1
  necessitation
  goedel_first_unprovable_real
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Full.Induction

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Theorems.Eq
import FOL.Deduction
import FOL.Tactics

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Hilbert

/-!
## META — NIVEL D (real): cálculo de Hilbert finitario `⊢ᴴ`  (Fase 0)

Para demostrar las condiciones de demostrabilidad **D1–D3** como teoremas (no
postulados) hace falta un sistema de demostrabilidad **finitario y r.e.** que
aritmetizar. El `axioms ⊢ φ` que el proyecto usaba entonces no lo era: sus meta‑reglas
(`raa`, `imp_intro`…) toman una función de Lean como premisa. Quedó retirado (ADR‑115).
✏️ Aquí se achacaba a la «ω‑regla `gen`», y `gen` no es la ω‑regla. Ver
`GODEL-D-ARITHMETIZATION.md`.

Aquí definimos un **cálculo de Hilbert clásico fresco** sobre `Minimal.axioms`,
**en dos capas** para que se vea exactamente dónde entra la lógica clásica:

* **`Prfᵢ`** (intuicionista): todos los esquemas salvo DNE.
* **`Prf`** (clásico): añade el esquema DNE (P3), la inducción (`ind`, `listInd`) y el
  confinamiento (`qconf`), y se cierra bajo MP/GEN.

🗑️ **2026‑10‑02 · ADR‑115 — los puentes a `⊢`, RETIRADOS, y lo que decían de ellos era FALSO.**
Aquí vivían `prfI_to_derives` y `prf_to_derives` (`Prf → axioms ⊢`). La doctrina decía que el
primero usaba «solo los constructores nativos de `Derives` … cero meta‑axiomas, cero `dne`» y que el
segundo lo reusaba y empleaba «`dne` en un único punto … Esa es toda la dependencia clásica». No era
cierto para el segundo: el footprint de `prf_to_derives` llevaba además los `axiom`
`ax_induction_prim`, `ax_list_induction` y `MetaRules.imp_intro` (medido: es el de
`not_omegaConsistent` en el registro de `sondeos/OmegaConsistentRefutable.lean`, que a `prf_to_derives`
sólo le añade lemas limpios; el del primero no se midió). Y las meta‑reglas de `⊢` son refutables
(`sondeos/MetaReglasRefutables.lean`). Con la capa `⊢` retirada, `Prf` **ya no tiene puente a `⊢`**; sí
a sus auxiliares de RPP —`PrfH` (`prf_to_prfH`, deducción finitaria) y las secuencias del verificador
(`prf_to_derivation`)—, que la cadena de Gödel usa. Su solidez es inducción sobre `Prf`: `prf_sound` (`Meta/SolidezPrf.lean`, ADR‑120).
-/

/-! ### Identidad De Bruijn auxiliar (cancelación a mismo nivel) -/

/-- **Cancelación lift/subst a mismo nivel**: sustituir en el nivel `c` deshace
    el desplazamiento en el nivel `c`. Complementa `subst_lift_cancel_formula`
    (la variante off-by-one).

    📌 **BAJADO A FOL el 2026‑09‑12 (R‑4)**: es lógica pura de FOL⁼, y este repo lo tenía
    probado **TRES veces** —aquí bajo este nombre, y como `substFormula_liftFormula` en
    `Full/StrongInduction.lean` **y** `Meta/StrongInductionPrf.lean`— con **ninguno de los
    tres docstrings mencionando a los otros dos**. El general vive ahora en
    `FOL/Theorems/Eq.lean`, junto a su versión de término. Esto es un **alias local**. -/
theorem subst_lift_same (f : Formula) : ∀ (c : Nat) (s : Term),
    substFormula c s (liftFormula c f) = f :=
  fun c s => FOL.substFormula_liftFormula f c s

set_option maxRecDepth 20000 in
/-- La lista BASE (los 141 de antes de ADR‑117) es de **sentencias cerradas**: su lift se cierra por
    cómputo (`rfl`). `maxRecDepth` cubre los numerales de símbolos (`σ` = codepoint 963). -/
theorem axiomsBase_lift_eq : axiomsBase.map (liftFormula 0) = axiomsBase := by
  simp only [axiomsBase, coreAxioms, codingAxioms, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- Los axiomas de `Minimal` son **sentencias cerradas**: desplazarlos es la identidad. La base, por
    cómputo (`axiomsBase_lift_eq`); el ancla, por ESTRUCTURA (`ax_axiomsCodeT_def_lift`), porque su
    `rfl` tendría que recorrer el numeral `numeralM (codeNat ψ)`, que es astronómico (ADR‑117). -/
theorem axioms_lift_eq : axioms.map (liftFormula 0) = axioms := by
  rw [axioms_split, List.map_append, axiomsBase_lift_eq, List.map_cons, List.map_nil,
    ax_axiomsCodeT_def_lift]

/-! ### Capa intuicionista `Prfᵢ`

Se llamó `Prf₀` hasta el 2026-09-26. Se renombró por la regla de subíndices de cálculo (ADR-102;
`../FOL/NAMING-CONVENTIONS.md` §9): el subíndice nombra un CÁLCULO, `₀` es el clásico `Derives₀`
de FOL y `ᵢ` el intuicionista. Con `Prf₀`, la misma marca decía lo contrario en los dos repos. -/

/-- **Cálculo de Hilbert intuicionista** sobre `Minimal.axioms`: esquemas
    proposicionales (P1/P2), conjunción (C), disyunción (J, en la forma de
    `Derived.or_elim`), ex falso (efq), cuantificadores (Q), igualdad
    (refl/leibniz), axiomas de la teoría (thy), y reglas **MP** y **GEN**
    (generalización de una premisa, modo-teorema). **Sin** DNE. -/
inductive Prfᵢ : Formula → Prop where
  | p1 (A B : Formula) : Prfᵢ (A ⇒ (B ⇒ A))
  | p2 (A B C : Formula) : Prfᵢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  | c1 (A B : Formula) : Prfᵢ (A ⇒ (B ⇒ (A ∧ B)))
  | c2 (A B : Formula) : Prfᵢ ((A ∧ B) ⇒ A)
  | c3 (A B : Formula) : Prfᵢ ((A ∧ B) ⇒ B)
  | j1 (A B : Formula) : Prfᵢ (A ⇒ (A ∨ B))
  | j2 (A B : Formula) : Prfᵢ (B ⇒ (A ∨ B))
  | j3 (A B C : Formula) : Prfᵢ ((A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C)))
  | efq (A : Formula) : Prfᵢ (⊥ ⇒ A)
  | q1 (A : Formula) (t : Term) : Prfᵢ ((Formula.forall A) ⇒ substFormula 0 t A)
  | q2 (A : Formula) (t : Term) : Prfᵢ (substFormula 0 t A ⇒ Formula.ex A)
  | q3 (A B : Formula) : Prfᵢ ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ ((Formula.ex A) ⇒ B))
  | eqrefl (t : Term) : Prfᵢ (t ≐ t)
  | leibniz (A : Formula) (t₁ t₂ : Term) :
      Prfᵢ ((t₁ ≐ t₂) ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A))
  | thy (a : Formula) : List.Mem a axioms → Prfᵢ a
  | mp (A B : Formula) : Prfᵢ (A ⇒ B) → Prfᵢ A → Prfᵢ B
  | gen (A : Formula) : Prfᵢ A → Prfᵢ (Formula.forall A)


/-! ### Esquema de confinamiento ∀ (para el teorema de deducción de `Prf`) -/

/-- **Fórmula de confinamiento ∀** (la variable ligada no ocurre en el antecedente
    `P`, codificada como `liftFormula 0 P`): `(∀(↑P ⇒ C)) ⇒ (P ⇒ ∀C)`. Es el
    esquema lógico que cierra el caso `gen` del teorema de deducción de un cálculo
    de Hilbert. Lógicamente válido; es el constructor `Prf.qconf` y una regla del verificador.
    (Su prueba sobre `⊢`, `confinement_derives`, se retiró con esa capa: ADR‑115.) -/
def confinementFormula (P C : Formula) : Formula :=
  (Formula.forall (liftFormula 0 P ⇒ C)) ⇒ (P ⇒ Formula.forall C)


/-! ### Esquema de inducción de listas (para los lemas de cadena en `Prf`) -/

/-- **Fórmula de inducción estructural sobre listas** (esquema objeto, análogo binario
    de `Full.inductionFormula`): `Φ[nil] ⇒ ((∀h ∀t (Φ[t] ⇒ Φ[cons h t])) ⇒ ∀L Φ[L])`.
    El consecuente del paso usa `C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`
    (slot ← `cons h t` bajo los dos binders; identidad De Bruijn vía Barendregt). -/
def listInductionFormula (Φ : Formula) : Formula :=
  Formula.impl (substFormula 0 nil Φ)
    (Formula.impl
      (Formula.forall (Formula.forall
        (Formula.impl
          (liftFormula 1 Φ)
          (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 Φ))))))
      (Formula.forall Φ))


/-! ### Capa clásica `Prf` -/

/-- **Cálculo de Hilbert clásico**: la capa intuicionista (`incl`), el esquema **DNE** (`p3`), la
    **inducción** (`ind`, el esquema `Full.inductionFormula` para toda fórmula), el
    **confinamiento** ∀ (`qconf`) y la **inducción de listas** (`listInd`), cerrado bajo MP y GEN.
    Es r.e. (Fase 1). 🏁 Su **solidez para ℕ está demostrada** desde ADR‑120 (`prf_sound`, `Meta/SolidezPrf.lean`), con el modelo
    de los 142 axiomas de `axioms` (141 y el ancla, ADR‑117) de `Meta/ModeloCodificacion.lean`; hasta ese día, pendiente. (Hasta el 2026‑10‑02
    decía «coherente con el `dne` y la inducción del proyecto» —los de la capa `⊢`, retirada con ADR‑115— y daba
    «sólido para ℕ» por hecho.) -/
inductive Prf : Formula → Prop where
  | incl {φ : Formula} : Prfᵢ φ → Prf φ
  | p3 (A : Formula) : Prf (((A ⇒ ⊥) ⇒ ⊥) ⇒ A)
  | ind (A : Formula) : Prf (Full.inductionFormula A)
  | qconf (P C : Formula) : Prf (confinementFormula P C)
  | listInd (A : Formula) : Prf (listInductionFormula A)
  | mp (A B : Formula) : Prf (A ⇒ B) → Prf A → Prf B
  | gen (A : Formula) : Prf A → Prf (Formula.forall A)

/-- Notación local para la demostrabilidad de Hilbert (clásica). -/
scoped notation "⊢ᴴ " φ => Prf φ


/-! ### Consistencia

(Hasta el 2026‑10‑02 esta sección se llamaba «Consistencia transferida»: transfería la de `⊢` a `Prf`
por `prf_to_derives`. Retirado con la capa `⊢`, ADR‑115; queda la definición.) -/


/-- Consistencia del **cálculo de Hilbert** `⊢ᴴ`: no demuestra `⊥`. -/
def ConsistentH : Prop := ¬ Prf Formula.bottom


end ROBINSON_PlusPlus.Meta.Hilbert

-- Exports: Nivel D real, Fase 0
export ROBINSON_PlusPlus.Meta.Hilbert (
  subst_lift_same
  Prfᵢ
  Prf
  ConsistentH
)

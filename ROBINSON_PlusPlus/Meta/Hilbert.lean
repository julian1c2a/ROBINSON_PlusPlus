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

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Hilbert

/-!
## META — NIVEL D (real): cálculo de Hilbert finitario `⊢ᴴ`  (Fase 0)

Para demostrar las condiciones de demostrabilidad **D1–D3** como teoremas (no
postulados) hace falta un sistema de demostrabilidad **finitario y r.e.** que
aritmetizar. El `axioms ⊢ φ` del proyecto incluye la ω-regla `gen` (premisas
infinitas), luego no es r.e. y `provFormula` no puede ser Σ₁ (Tarski). Ver
`GODEL-D-ARITHMETIZATION.md`.

Aquí definimos un **cálculo de Hilbert clásico fresco** sobre `Minimal.axioms`,
**en dos capas** para que se vea exactamente dónde entra la lógica clásica:

* **`Prf₀`** (intuicionista): todos los esquemas salvo DNE. Su puente
  `prf0_to_derives` se construye usando **solo los constructores nativos de
  `Derives`** (deducción natural) — **cero meta-axiomas, cero `dne`**.
* **`Prf`** (clásico): añade el esquema DNE (P3) y se cierra bajo MP/GEN. Su
  puente `prf_to_derives` reusa `prf0_to_derives` y emplea **`dne` en un único
  punto**: el caso `p3`. Esa es **toda** la dependencia clásica.

Esto materializa la observación: *nuestro FOL (los constructores de `Derives`)
deriva todo el cálculo de Hilbert; el único ingrediente no constructivo es una
aplicación de DNE clásica, y la ω-regla no se invoca jamás* (GEN de Hilbert es
`Derives.intro_forall`, finitaria de una premisa).
-/

/-! ### Identidad De Bruijn auxiliar (cancelación a mismo nivel) -/

/-- **Cancelación lift/subst a mismo nivel**: sustituir en el nivel `c` deshace
    el desplazamiento en el nivel `c`. Complementa `subst_lift_cancel_formula`
    (la variante off-by-one). Inducción estructural; átomos/igualdades vía las
    versiones de término `FOL.substTerm(s)_liftTerm(s)`. -/
theorem subst_lift_same (f : Formula) : ∀ (c : Nat) (s : Term),
    substFormula c s (liftFormula c f) = f := by
  induction f with
  | bottom => intro c s; rfl
  | atom p ts => intro c s; simp only [liftFormula, substFormula, FOL.substTerms_liftTerms]
  | eq t u => intro c s; simp only [liftFormula, substFormula, FOL.substTerm_liftTerm]
  | impl a b iha ihb => intro c s; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | «forall» a iha => intro c s; simp only [liftFormula, substFormula]; rw [iha]
  | and a b iha ihb => intro c s; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | or a b iha ihb => intro c s; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | ex a iha => intro c s; simp only [liftFormula, substFormula]; rw [iha]

set_option maxRecDepth 20000 in
/-- Los axiomas de `Minimal` son **sentencias cerradas**: desplazarlos es la
    identidad. Los axiomas matemáticos y la mayoría de las ecuaciones de coding se
    cierran por cómputo (`rfl`); el axioma `ax_axiomsCodeT` (que contiene el código
    gigante `listFormCodeM coreAxioms`) se aísla y se cierra por `ax_axiomsCodeT_lift`
    (clausura estructural, sin `rfl`). -/
theorem axioms_lift_eq : axioms.map (liftFormula 0) = axioms := by
  -- Expone el `map` y reescribe el término gigante `liftFormula 0 ax_axiomsCodeT`
  -- a `ax_axiomsCodeT` (idéntico en ambos lados); el `rfl` final solo computa el
  -- lift sobre los axiomas pequeños. `maxRecDepth` cubre los numerales de símbolos
  -- (`σ` = codepoint 963) en `ax_tc_succ`; el código realmente gigante
  -- (`listFormCodeM coreAxioms`) nunca se computa (lo cubre `ax_axiomsCodeT_lift`).
  simp only [axioms, List.map_cons, List.map_nil, ax_axiomsCodeT_lift]
  rfl

/-! ### Capa intuicionista `Prf₀` -/

/-- **Cálculo de Hilbert intuicionista** sobre `Minimal.axioms`: esquemas
    proposicionales (P1/P2), conjunción (C), disyunción (J, en la forma de
    `Derived.or_elim`), ex falso (efq), cuantificadores (Q), igualdad
    (refl/leibniz), axiomas de la teoría (thy), y reglas **MP** y **GEN**
    (generalización de una premisa, modo-teorema). **Sin** DNE. -/
inductive Prf₀ : Formula → Prop where
  | p1 (A B : Formula) : Prf₀ (A ⇒ (B ⇒ A))
  | p2 (A B C : Formula) : Prf₀ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  | c1 (A B : Formula) : Prf₀ (A ⇒ (B ⇒ (A ∧ B)))
  | c2 (A B : Formula) : Prf₀ ((A ∧ B) ⇒ A)
  | c3 (A B : Formula) : Prf₀ ((A ∧ B) ⇒ B)
  | j1 (A B : Formula) : Prf₀ (A ⇒ (A ∨ B))
  | j2 (A B : Formula) : Prf₀ (B ⇒ (A ∨ B))
  | j3 (A B C : Formula) : Prf₀ ((A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C)))
  | efq (A : Formula) : Prf₀ (⊥ ⇒ A)
  | q1 (A : Formula) (t : Term) : Prf₀ ((Formula.forall A) ⇒ substFormula 0 t A)
  | q2 (A : Formula) (t : Term) : Prf₀ (substFormula 0 t A ⇒ Formula.ex A)
  | q3 (A B : Formula) : Prf₀ ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ ((Formula.ex A) ⇒ B))
  | eqrefl (t : Term) : Prf₀ (t ≐ t)
  | leibniz (A : Formula) (t₁ t₂ : Term) :
      Prf₀ ((t₁ ≐ t₂) ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A))
  | thy (a : Formula) : List.Mem a coreAxioms → Prf₀ a
  | mp (A B : Formula) : Prf₀ (A ⇒ B) → Prf₀ A → Prf₀ B
  | gen (A : Formula) : Prf₀ A → Prf₀ (Formula.forall A)

/-- **Puente intuicionista**: todo teorema de `Prf₀` es teorema de `Derives`
    sobre `axioms`, usando **únicamente los constructores de `Derives`** (más los
    teoremas lógicos constructor-puros de `FOL.Theorems`). **No usa `dne` ni
    ninguna meta-regla ω.** Verificable con `#print axioms prf0_to_derives`. -/
theorem prf0_to_derives {φ : Formula} (h : Prf₀ φ) : axioms ⊢ φ := by
  induction h with
  | p1 A B => exact FOL.Theorems.Impl.k_impl
  | p2 A B C => exact FOL.Theorems.Impl.s_impl
  | c1 A B => exact FOL.Theorems.Derived.and_intro
  | c2 A B => exact FOL.Theorems.Derived.and_elim_left
  | c3 A B => exact FOL.Theorems.Derived.and_elim_right
  | j1 A B => exact FOL.Theorems.Derived.or_intro_left
  | j2 A B => exact FOL.Theorems.Derived.or_intro_right
  | j3 A B C => exact FOL.Theorems.Derived.or_elim
  | efq A => exact FOL.Theorems.Neg.explosion_impl
  | q1 A t =>
      apply Derives.intro_impl
      exact Derives.elim_forall _ A t (Derives.hyp _ _ (List.Mem.head _))
  | q2 A t =>
      apply Derives.intro_impl
      exact Derives.intro_ex _ A t (Derives.hyp _ _ (List.Mem.head _))
  | q3 A B =>
      apply Derives.intro_impl
      apply Derives.intro_impl
      apply Derives.elim_ex _ A B
      · exact Derives.hyp _ _ (List.Mem.head _)
      · -- contexto: A :: ((∃A)::(∀(A⇒↑B))::axioms).map (liftFormula 0)
        have hall := Derives.hyp
          (A :: (((Formula.ex A) :: (Formula.forall (A ⇒ liftFormula 0 B)) :: axioms).map
            (liftFormula 0)))
          (liftFormula 0 (Formula.forall (A ⇒ liftFormula 0 B)))
          (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.Mem.tail _ (List.Mem.head _))))
        simp only [liftFormula] at hall
        have hinst := Derives.elim_forall _ _ (#0) hall
        simp only [substFormula] at hinst
        rw [subst_lift_cancel_formula, subst_lift_cancel_formula] at hinst
        exact Derives.elim_impl _ A (liftFormula 0 B) hinst (Derives.hyp _ _ (List.Mem.head _))
  | eqrefl t => exact Derives.refl _ t
  | leibniz A t₁ t₂ =>
      apply Derives.intro_impl
      apply Derives.intro_impl
      exact Derives.subst _ t₁ t₂ A
        (Derives.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (Derives.hyp _ _ (List.Mem.head _))
  | thy a ha => exact Derives.hyp _ a (mem_axioms_of_mem_core ha)
  | mp A B _ _ ihAB ihA => exact Derives.elim_impl _ A B ihAB ihA
  | gen A _ ihA =>
      apply Derives.intro_forall
      rw [axioms_lift_eq]
      exact ihA

/-! ### Capa clásica `Prf` -/

/-- **Cálculo de Hilbert clásico**: la capa intuicionista (`incl`), el esquema
    **DNE** (`p3`) y el **esquema de inducción** (`ind`, IΣ₁), cerrado bajo MP y
    GEN. Clásico, coherente con el `dne` y la inducción del proyecto, sólido para
    ℕ. Es r.e. (Fase 1). -/
inductive Prf : Formula → Prop where
  | incl {φ : Formula} : Prf₀ φ → Prf φ
  | p3 (A : Formula) : Prf (((A ⇒ ⊥) ⇒ ⊥) ⇒ A)
  | ind (A : Formula) : Prf (Full.inductionFormula A)
  | mp (A B : Formula) : Prf (A ⇒ B) → Prf A → Prf B
  | gen (A : Formula) : Prf A → Prf (Formula.forall A)

/-- Notación local para la demostrabilidad de Hilbert (clásica). -/
scoped notation "⊢ᴴ " φ => Prf φ

/-- **Puente clásico**: todo teorema de `Prf` es teorema de `Derives` sobre
    `axioms`. Reusa `prf0_to_derives` para la capa intuicionista; **`dne`
    aparece exactamente una vez**, en el caso `p3`. Verificable con
    `#print axioms` (compárese con `prf0_to_derives`, que no depende de `dne`). -/
theorem prf_to_derives {φ : Formula} (h : Prf φ) : axioms ⊢ φ := by
  induction h with
  | incl h0 => exact prf0_to_derives h0
  | p3 A =>
      -- ⭐ EL ÚNICO USO DE `dne` (lógica clásica) en todo el puente.
      apply Derives.intro_impl
      exact Minimal.Axioms.dne (Derives.hyp _ _ (List.Mem.head _))
  | ind A =>
      -- Esquema de inducción: axioma legítimo de la aritmética (IΣ₁), sólido vía
      -- `Full.ax_induction` (misma `Minimal.axioms`; `Meta` importa `Full`).
      exact Full.ax_induction A
  | mp A B _ _ ihAB ihA => exact Derives.elim_impl _ A B ihAB ihA
  | gen A _ ihA =>
      apply Derives.intro_forall
      rw [axioms_lift_eq]
      exact ihA

/-! ### Consistencia transferida -/

/-- Consistencia del sistema **fuerte** del proyecto (`Derives` + meta-reglas):
    no deriva `⊥`. -/
def ConsistentOmega : Prop := ¬ (axioms ⊢ Formula.bottom)

/-- Consistencia del **cálculo de Hilbert** `⊢ᴴ`: no demuestra `⊥`. -/
def ConsistentH : Prop := ¬ Prf Formula.bottom

/-- **Transferencia de consistencia**: si el sistema fuerte es consistente,
    también lo es el cálculo de Hilbert (por el puente). Así la hipótesis de
    Gödel sobre `⊢ᴴ` se hereda. -/
theorem consistentH_of_omega (h : ConsistentOmega) : ConsistentH :=
  fun hp => h (prf_to_derives hp)

end ROBINSON_PlusPlus.Meta.Hilbert

-- Exports: Nivel D real, Fase 0
export ROBINSON_PlusPlus.Meta.Hilbert (
  subst_lift_same
  Prf₀
  prf0_to_derives
  Prf
  prf_to_derives
  ConsistentOmega
  ConsistentH
  consistentH_of_omega
)

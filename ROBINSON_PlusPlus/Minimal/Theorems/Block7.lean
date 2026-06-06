/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block4
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7
import ROBINSON_PlusPlus.Minimal.Theorems.Block5

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block4
open ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7
open ROBINSON_PlusPlus.Minimal.Theorems.Block5

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block7

/-!
## BLOQUE VII — FUNCIONES DISCRETAS

Implementa Def 21 (`IsFunction`), Def 24 (`Functional`) y Teos F1–F3 de
`TuplasFuncionesYListas.md §BLOQUE VII`.

**Estilo de formalización**: `IsFunction` y `Functional` se definen como
**meta-predicados Lean** (`Term → Prop`) parametrizados por cuantificación
universal sobre `Term`. Esto evita el manejo manual de índices De Bruijn
(`liftTerm`/`substTerm`) que aparecería si los expresáramos como `Formula`
con `forall_2`/`forall_3`. La traducción es directa: una prueba de
`IsFunction F` en Lean equivale a una prueba uniforme en FOL para cada
par de términos `p₁, p₂` (esquema, no axioma).

Sobre Def 23 (`Map`): se inlinea como `In (pair x y) F` dentro de
`Functional`, evitando un wrapper redundante.
-/

def Γ := axioms

/-!
### Fase 15: IsFunction y Evaluación Única
-/

/-- **Def 21**: `IsFunction(F)` — para cualesquiera `p₁, p₂ ∈ F` con la
    misma primera componente, son iguales. Esquema en `Term`. -/
def IsFunction (F : Term) : Prop :=
  ∀ p1 p2 : Term,
    (axioms ⊢ In p1 F) → (axioms ⊢ In p2 F) →
    (axioms ⊢ (proj1 p1 =eq proj1 p2)) →
    (axioms ⊢ (p1 =eq p2))

/-- **Teo F1**: `IsFunction(nil)`.

    Vacuamente verdad: por `ax_L1`, `¬In(p, nil)` para todo `p`, así que la
    hipótesis nunca se satisface. -/
theorem teo_F1 : IsFunction nil := by
  intros p1 _ h_in_p1 _ _
  have h_axL1 := ax (by simp [axioms] : ax_L1_in_nil ∈ axioms)
  have h_neg_in_p1 : axioms ⊢ neg (In p1 nil) := by
    have hh := spec h_axL1 p1
    simp [In, nil, zero] at hh
    exact hh
  exact false_elim (mp h_neg_in_p1 h_in_p1)

/-- **Teo F2** (Evaluación única): si `F` es función y contiene `⟨x,y⟩` y
    `⟨x,y'⟩`, entonces `y = y'`.

    Prueba: aplicamos `IsFunction(F)` a `p₁ := pair x y`, `p₂ := pair x y'`;
    `proj1` de ambos es `x` (`proj1_pair_eq_x`), así que la hipótesis se
    satisface y se concluye `pair x y = pair x y'`. `pair_inj` da `y = y'`. -/
theorem teo_F2 {F x y y' : Term}
    (h_isF : IsFunction F)
    (h_xy  : Γ ⊢ In (pair x y) F)
    (h_xy' : Γ ⊢ In (pair x y') F) :
      Γ ⊢ (y =eq y') := by
  have h_proj1_xy  : axioms ⊢ (proj1 (pair x y)  =eq x) := proj1_pair_eq_x x y
  have h_proj1_xy' : axioms ⊢ (proj1 (pair x y') =eq x) := proj1_pair_eq_x x y'
  have h_proj1_eq : axioms ⊢ (proj1 (pair x y) =eq proj1 (pair x y')) :=
    FOL.derive_eq_trans h_proj1_xy (eq_symm h_proj1_xy')
  have h_pair_eq : axioms ⊢ (pair x y =eq pair x y') :=
    h_isF (pair x y) (pair x y') h_xy h_xy' h_proj1_eq
  have h_eqs : axioms ⊢ Axioms.land (x =eq x) (y =eq y') := mp pair_inj h_pair_eq
  exact Axioms.and_elim_right h_eqs

/-!
### Fase 16: Isomorfismo con Relaciones
-/

/-- **Def 24** (con `Map` inlineado como `In (pair x y) F`):
    `Functional(F)` — para cualesquiera `x, y, y'`, si `⟨x,y⟩` y `⟨x,y'⟩`
    están ambos en `F`, entonces `y = y'`. -/
def Functional (F : Term) : Prop :=
  ∀ x y y' : Term,
    (axioms ⊢ In (pair x y) F) → (axioms ⊢ In (pair x y') F) →
    (axioms ⊢ (y =eq y'))

/-- **Teo F3**: `IsFunction(F) ⟺ Functional(F)`.

    Direcciones:
    * `(⇒)`: aplicación directa de `teo_F2`.
    * `(⇐)`: dados `p₁, p₂` con `proj1 p₁ = proj1 p₂ =: x`, reescribimos
      `pᵢ = pair (proj1 pᵢ) (proj2 pᵢ)` vía `pair_proj_eq_c`; ambos son
      `pair x (proj2 pᵢ)` (tras transportar la igualdad de proyecciones), y
      `Functional` da `proj2 p₁ = proj2 p₂`, de donde `p₁ = p₂` por
      congruencia. -/
theorem teo_F3 (F : Term) : IsFunction F ↔ Functional F := by
  constructor
  · -- IsFunction F → Functional F: aplicación directa de F2
    intro h_isF x y y' h_xy h_xy'
    exact teo_F2 h_isF h_xy h_xy'
  · -- Functional F → IsFunction F
    intro h_func p1 p2 h_in_p1 h_in_p2 h_proj1_eq
    -- p_i = pair (proj1 p_i) (proj2 p_i)   vía pair_proj_eq_c
    have h_p1_eq : axioms ⊢ (pair (proj1 p1) (proj2 p1) =eq p1) := pair_proj_eq_c p1
    have h_p2_eq : axioms ⊢ (pair (proj1 p2) (proj2 p2) =eq p2) := pair_proj_eq_c p2
    -- Reformular In(p1, F) como In(pair (proj1 p1)(proj2 p1), F)  vía eq_symm h_p1_eq
    -- y luego como In(pair (proj1 p2)(proj2 p1), F)  vía h_proj1_eq (al primer arg de pair)
    let x := proj1 p2
    have h_x_eq_proj1_p1 : axioms ⊢ (proj1 p2 =eq proj1 p1) := eq_symm h_proj1_eq
    -- pair (proj1 p1)(proj2 p1) =eq pair x (proj2 p1)   [eq_congr_pair_left con h_x_eq_proj1_p1]
    have h_pair_p1_x : axioms ⊢ (pair (proj1 p1) (proj2 p1) =eq pair x (proj2 p1)) := by
      -- pair es div2(cantor_poly ...), así que necesitamos congruencia en x → proj1 p1
      -- Usamos eq_congr_pair (probablemente vía cantor_func congruencia)
      have h_eq_first : axioms ⊢ (proj1 p1 =eq x) := eq_symm h_x_eq_proj1_p1
      -- pair x' y =eq pair x y' si x' = x e y = y'... aquí solo cambia primer arg
      -- Estrategia genérica: usar Derives.subst con fórmula "pair (.var 0) (proj2 p1) =eq ..."
      let f_pair : Formula := Formula.eq
        (pair (liftTerm 0 (proj1 p1)) (liftTerm 0 (proj2 p1)))
        (pair (.var 0) (liftTerm 0 (proj2 p1)))
      have hS_p1_first : substFormula 0 (proj1 p1) f_pair
          = (pair (proj1 p1) (proj2 p1) =eq pair (proj1 p1) (proj2 p1)) := by
        simp only [f_pair, substFormula, substTerm, substTerms, pair, cantor_func, div2,
                   cantor_poly, mul, add, succ, two, one, zero,
                   FOL.substTerm_liftTerm, if_true]
      have hS_p1_x : substFormula 0 x f_pair
          = (pair (proj1 p1) (proj2 p1) =eq pair x (proj2 p1)) := by
        simp only [f_pair, substFormula, substTerm, substTerms, pair, cantor_func, div2,
                   cantor_poly, mul, add, succ, two, one, zero,
                   FOL.substTerm_liftTerm, if_true]
      have h_refl : axioms ⊢ (pair (proj1 p1) (proj2 p1) =eq pair (proj1 p1) (proj2 p1)) :=
        eq_refl _
      exact hS_p1_x ▸ Derives.subst axioms (proj1 p1) x f_pair h_eq_first
        (hS_p1_first ▸ h_refl)
    -- Combinado: pair x (proj2 p1) =eq p1
    have h_pair_x_eq_p1 : axioms ⊢ (pair x (proj2 p1) =eq p1) :=
      FOL.derive_eq_trans (eq_symm h_pair_p1_x) h_p1_eq
    -- In (pair x (proj2 p1)) F   sustituyendo p1 → pair x (proj2 p1) en h_in_p1
    have h_in_x_p1 : axioms ⊢ In (pair x (proj2 p1)) F := by
      let f_in : Formula := Formula.atom in_sym [.var 0, liftTerm 0 F]
      have hS_p1 : substFormula 0 p1 f_in = In p1 F := by
        simp only [f_in, substFormula, substTerm, substTerms, In,
                   FOL.substTerm_liftTerm, if_true]
      have hS_x_p1 : substFormula 0 (pair x (proj2 p1)) f_in
          = In (pair x (proj2 p1)) F := by
        simp only [f_in, substFormula, substTerm, substTerms, In,
                   FOL.substTerm_liftTerm, if_true]
      exact hS_x_p1 ▸ Derives.subst axioms p1 (pair x (proj2 p1)) f_in
        (eq_symm h_pair_x_eq_p1) (hS_p1 ▸ h_in_p1)
    -- Análogamente: In (pair x (proj2 p2)) F   desde h_in_p2 (con x = proj1 p2)
    have h_in_x_p2 : axioms ⊢ In (pair x (proj2 p2)) F := by
      have h_pair_p2_self : axioms ⊢ (pair (proj1 p2) (proj2 p2) =eq pair x (proj2 p2)) :=
        eq_refl _  -- x = proj1 p2 definicionalmente
      have h_pair_x_eq_p2 : axioms ⊢ (pair x (proj2 p2) =eq p2) :=
        FOL.derive_eq_trans (eq_symm h_pair_p2_self) h_p2_eq
      let f_in : Formula := Formula.atom in_sym [.var 0, liftTerm 0 F]
      have hS_p2 : substFormula 0 p2 f_in = In p2 F := by
        simp only [f_in, substFormula, substTerm, substTerms, In,
                   FOL.substTerm_liftTerm, if_true]
      have hS_x_p2 : substFormula 0 (pair x (proj2 p2)) f_in
          = In (pair x (proj2 p2)) F := by
        simp only [f_in, substFormula, substTerm, substTerms, In,
                   FOL.substTerm_liftTerm, if_true]
      exact hS_x_p2 ▸ Derives.subst axioms p2 (pair x (proj2 p2)) f_in
        (eq_symm h_pair_x_eq_p2) (hS_p2 ▸ h_in_p2)
    -- Functional aplicado a x, proj2 p1, proj2 p2 → proj2 p1 = proj2 p2
    have h_proj2_eq : axioms ⊢ (proj2 p1 =eq proj2 p2) :=
      h_func x (proj2 p1) (proj2 p2) h_in_x_p1 h_in_x_p2
    -- Concluir p1 = p2: p1 = pair x (proj2 p1) = pair x (proj2 p2) = p2
    have h_pair_x_eq : axioms ⊢ (pair x (proj2 p1) =eq pair x (proj2 p2)) := by
      -- congruencia en segundo arg de pair
      let f_pair : Formula := Formula.eq
        (pair (liftTerm 0 x) (liftTerm 0 (proj2 p1)))
        (pair (liftTerm 0 x) (.var 0))
      have hS_p1 : substFormula 0 (proj2 p1) f_pair
          = (pair x (proj2 p1) =eq pair x (proj2 p1)) := by
        simp only [f_pair, substFormula, substTerm, substTerms, pair, cantor_func, div2,
                   cantor_poly, mul, add, succ, two, one, zero,
                   FOL.substTerm_liftTerm, if_true]
      have hS_p2 : substFormula 0 (proj2 p2) f_pair
          = (pair x (proj2 p1) =eq pair x (proj2 p2)) := by
        simp only [f_pair, substFormula, substTerm, substTerms, pair, cantor_func, div2,
                   cantor_poly, mul, add, succ, two, one, zero,
                   FOL.substTerm_liftTerm, if_true]
      have h_refl : axioms ⊢ (pair x (proj2 p1) =eq pair x (proj2 p1)) := eq_refl _
      exact hS_p2 ▸ Derives.subst axioms (proj2 p1) (proj2 p2) f_pair h_proj2_eq
        (hS_p1 ▸ h_refl)
    -- p1 =eq pair x (proj2 p1) =eq pair x (proj2 p2) =eq p2
    have h_p1_eq_sym : axioms ⊢ (p1 =eq pair x (proj2 p1)) := eq_symm h_pair_x_eq_p1
    have h_pair_x_p2_eq_p2 : axioms ⊢ (pair x (proj2 p2) =eq p2) := by
      have h_pair_p2_self : axioms ⊢ (pair (proj1 p2) (proj2 p2) =eq pair x (proj2 p2)) :=
        eq_refl _
      exact FOL.derive_eq_trans (eq_symm h_pair_p2_self) h_p2_eq
    exact FOL.derive_eq_trans h_p1_eq_sym
      (FOL.derive_eq_trans h_pair_x_eq h_pair_x_p2_eq_p2)

end ROBINSON_PlusPlus.Minimal.Theorems.Block7

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block7 (
  IsFunction
  Functional
  teo_F1
  teo_F2
  teo_F3
)

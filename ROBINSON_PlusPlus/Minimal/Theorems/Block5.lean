/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block3
import ROBINSON_PlusPlus.Minimal.Theorems.Block4

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block3
open ROBINSON_PlusPlus.Minimal.Theorems.Block4

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block5

/-!
## BLOQUE V — TUPLAS Y PROYECCIONES
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 11: Isomorfismo de Tuplas
-/

-- Lema Auxiliar: n = 2*k ⇒ mod2(n) = 0
private theorem mod2_of_even {n k : Term} (h : Γ ⊢ (n =eq mul two k)) : Γ ⊢ (mod2 n =eq zero) := by sorry

-- Teo C8: [⟨x,y⟩].1 = x
theorem proj1_pair_eq_x (x y : Term) : Γ ⊢ (proj1 (pair x y) =eq x) := by sorry

-- Teo C9: [⟨x,y⟩].2 = y
theorem proj2_pair_eq_y (x y : Term) : Γ ⊢ (proj2 (pair x y) =eq y) := by sorry

-- Teo C10: ⟨[c].1, [c].2⟩ = c
theorem pair_proj_eq_c (c : Term) : Γ ⊢ (pair (proj1 c) (proj2 c) =eq c) := by sorry

-- Teo C11: ⟨x,y⟩ = ⟨x',y'⟩ ⇒ x = x' ∧ y = y'
theorem pair_inj {x y x' y' : Term} : Γ ⊢ (pair x y =eq pair x' y') ⇒ land (x =eq x') (y =eq y') := by sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block5 (
  proj1_pair_eq_x
  proj2_pair_eq_y
  pair_proj_eq_c
  pair_inj
)

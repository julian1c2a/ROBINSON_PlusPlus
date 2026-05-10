/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
-- Block2 is not strictly needed for the first theorems, but will be for later ones.
-- open ROBINSON_PlusPlus.Minimal.Theorems.Block2

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block3

/-!
## BLOQUE III — div2 Y mod2
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 5: Valores de div2 y mod2 como Teoremas
-/

-- Teo 5.1: mod2(0) = 0
theorem mod2_zero : Γ ⊢ (mod2 zero =eq zero) := by sorry

-- Teo 5.2: div2(0) = 0
theorem div2_zero : Γ ⊢ (div2 zero =eq zero) := by sorry

-- Teo 5.3: mod2(1) = 1
theorem mod2_one : Γ ⊢ (mod2 one =eq one) := by sorry

-- Teo 5.4: div2(1) = 0
theorem div2_one : Γ ⊢ (div2 one =eq zero) := by sorry

-- Teo 5.5: mod2(2) = 0
theorem mod2_two : Γ ⊢ (mod2 two =eq zero) := by sorry

-- Teo 5.6: div2(2) = 1
theorem div2_two : Γ ⊢ (div2 two =eq one) := by sorry

-- Teo 5.7: mod2(3) = 1
theorem mod2_three : Γ ⊢ (mod2 three =eq one) := by sorry

-- Teo 5.8: div2(3) = 1
theorem div2_three : Γ ⊢ (div2 three =eq one) := by sorry

-- Teo 5.9: mod2(4) = 0
theorem mod2_four : Γ ⊢ (mod2 four =eq zero) := by sorry

-- Teo 5.9: div2(4) = 2
theorem div2_four : Γ ⊢ (div2 four =eq two) := by sorry

-- Teo 5.10: ∀ n, mod2(n) = 0 ∨ mod2(n) = 1
theorem mod2_range : Γ ⊢ ax21_mod2_range := by sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block3

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block3 (
  mod2_zero
  div2_zero
  mod2_one
  div2_one
  mod2_two
  div2_two
  mod2_three
  div2_three
  mod2_four
  div2_four
  mod2_range
)

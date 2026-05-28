/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
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
open ROBINSON_PlusPlus.Minimal.Theorems.Block5

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block6

/-!
## BLOQUE VI — LISTAS
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 12: Nil y Cons
-/

-- Teo L1: ∀ h,t, Cons(h,t) ≠ Nil
theorem cons_neq_nil (h t : Term) : Γ ⊢ neg (cons h t =eq nil) := by sorry

-- Teo L2: Cons(h,t) = Cons(h',t') ⇒ h = h' ∧ t = t'
theorem cons_inj {h t h' t' : Term} : Γ ⊢ (cons h t =eq cons h' t') ⇒ land (h =eq h') (t =eq t') := by sorry

/-!
### Fase 13: Pertenencia
-/

-- Teo L4: In(x, Cons(x, Nil))
theorem in_cons_self_nil (x : Term) : Γ ⊢ In x (cons x Nil) := by sorry

-- Teo L5: In(x, Cons(h, Nil)) ⇒ x = h
theorem in_cons_nil_imp_eq {x h : Term} : Γ ⊢ In x (cons h Nil) ⇒ (x =eq h) := by sorry

/-!
### Fase 14: Concatenación
-/

-- Teo L6: [x] ⊕ [y] = [x,y]
theorem concat_singletons (x y : Term) : Γ ⊢ (concat (cons x Nil) (cons y Nil) =eq cons x (cons y Nil)) := by sorry

-- Teo L7: (L ⊕ M) ⊕ N = L ⊕ (M ⊕ N)
theorem concat_assoc (L M N : Term) : Γ ⊢ (concat (concat L M) N =eq concat L (concat M N)) := by sorry

-- Teo L8: In(x, L ⊕ M) ⇔ In(x,L) ∨ In(x,M)
theorem in_concat_iff (x L M : Term) : Γ ⊢ In x (concat L M) ⇔ lor (In x L) (In x M) := by
  -- Proof requires induction on L.
  sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block6

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block6 (
  cons_neq_nil
  cons_inj
  in_cons_self_nil
  in_cons_nil_imp_eq
  concat_singletons
  concat_assoc
  in_concat_iff
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Full.StrongInduction
import ROBINSON_PlusPlus.Full.Numerals

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — Cuantificación acotada: `le d (numeral n)` ⇒ casos finitos

`le_numeral_split` es el **eliminador de cuantificación acotada**: si
`d ≤ numeral n` (object), entonces para probar cualquier conclusión object `C`
basta probarla en cada caso `d = numeral i` con `i ≤ n` (meta).

Es la herramienta que convierte un `∀d ≤ numeral n` formal en un análisis de
**casos finitos** a nivel meta. Pilar de la representabilidad de la primalidad
y del algoritmo de división sobre numerales.

La conclusión `C` es object (`axioms ⊢ C`), por lo que `or_elim`/`false_elim`
funcionan dentro de la prueba (no hay extracción meta de testigos).
-/

/-- **Eliminador de cuantificación acotada**. De `d ≤ numeral n` y una prueba
    de `C` para cada caso `d = numeral i` (`i ≤ n`), concluye `C`.

    Por inducción meta en `n`, usando `lt_succ_split` (de `StrongInduction`). -/
theorem le_numeral_split (d : Term) (C : Formula) :
    ∀ n : Nat, axioms ⊢ le d (numeral n) →
      (∀ i : Nat, Nat.le i n → axioms ⊢ (d =eq numeral i) → axioms ⊢ C) →
      axioms ⊢ C := by
  intro n
  induction n with
  | zero =>
    intro h cases
    -- h : le d (numeral 0) = le d zero = (lt d zero ∨ d = zero)
    apply Minimal.Axioms.or_elim h
    · intro hlt
      exact false_elim (mp (not_lt_zero d) hlt)
    · intro heq
      exact cases 0 (Nat.le_refl 0) heq
  | succ k ih =>
    intro h cases
    -- h : le d (numeral (k+1)) = le d (succ (numeral k)) = (lt d (σ νk) ∨ d = σ νk)
    apply Minimal.Axioms.or_elim h
    · intro hlt
      -- lt d (succ (numeral k)) → lt d (numeral k) ∨ d = numeral k
      apply Minimal.Axioms.or_elim (lt_succ_split d (numeral k) hlt)
      · intro hlt'
        -- lt d (numeral k) → le d (numeral k); aplicar IH
        refine ih (Minimal.Axioms.or_intro_left hlt') ?_
        intro i hi heqi
        exact cases i (Nat.le_succ_of_le hi) heqi
      · intro heq'
        exact cases k (Nat.le_succ k) heq'
    · intro heq
      -- d = succ (numeral k) = numeral (k+1)
      exact cases (k + 1) (Nat.le_refl _) heq

end ROBINSON_PlusPlus.Full

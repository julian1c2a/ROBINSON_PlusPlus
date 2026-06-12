/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
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
## FULL — División con resto (sobre numerales)

`division_numeral` : para `d > 0`, `numeral n = numeral(n/d)·numeral d +
numeral(n%d)` y `numeral(n%d) < numeral d`.

Con el puente de numerales el algoritmo de la división es **trivial**: el
cociente y el resto se computan en `ℕ` (`n/d`, `n%d`) y se transfieren por el
homomorfismo (`numeral_mul`, `numeral_add`, `numeral_lt`). No requiere
inducción fuerte object ni manejo De Bruijn — los Muros 1/2 quedan disueltos.
-/

/-- **División con resto** sobre numerales. Cociente `n/d`, resto `n%d`
    computados en `ℕ` y transferidos. -/
theorem division_numeral (n d : Nat) (hd : 0 < d) :
    (axioms ⊢ (numeral n =eq
        add (mul (numeral (n / d)) (numeral d)) (numeral (n % d)))) ∧
    (axioms ⊢ lt (numeral (n % d)) (numeral d)) := by
  refine ⟨?_, numeral_lt (Nat.mod_lt n hd)⟩
  -- n = (n/d)·d + n%d  en ℕ
  have hqr : (n / d) * d + n % d = n := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod n d
  -- transferencia: add (mul ν(n/d) νd) ν(n%d) =eq numeral ((n/d)*d + n%d) = numeral n
  have step1 : axioms ⊢ (add (mul (numeral (n / d)) (numeral d)) (numeral (n % d)) =eq
                         add (numeral (n / d * d)) (numeral (n % d))) :=
    eq_congr_add_right (u := numeral (n % d)) (numeral_mul (n / d) d)
  have step2 : axioms ⊢ (add (numeral (n / d * d)) (numeral (n % d)) =eq
                         numeral (n / d * d + n % d)) :=
    numeral_add (n / d * d) (n % d)
  have H : axioms ⊢ (add (mul (numeral (n / d)) (numeral d)) (numeral (n % d)) =eq
                     numeral (n / d * d + n % d)) :=
    FOL.derive_eq_trans step1 step2
  rw [hqr] at H
  exact eq_symm H

end ROBINSON_PlusPlus.Full

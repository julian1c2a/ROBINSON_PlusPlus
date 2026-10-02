/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Full.Induction

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`: los homomorfismos, el orden y la separación (`numeral_add`,
> `numeral_mul`, `numeral_pow`, `numeral_lt`, `numeral_ne`) **ya no existen**; lo que se lea sobre
> ellos es REGISTRO, no estado. Lo que queda en el módulo —`numeral` y sus lemas `rfl`— no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — Numerales: el puente meta↔object

`numeral : ℕ → Term` envía el natural meta `n` al término object `σⁿ(0)`. Es lo que
queda del módulo, con sus lemas `rfl` (`numeral_zero`, `numeral_succ`, `numeral_one`,
`numeral_two`).

🗑️ **2026‑10‑02 (ADR‑115) — registro.** El módulo demostraba además, sobre `⊢`, que la
aritmética object sobre numerales **refleja** la de `ℕ`: los homomorfismos de `+`, `·` y `^`,
el orden (`a < b ⇒ lt (numeral a) (numeral b)`) y la separación
(`a ≠ b ⇒ neg (numeral a =eq numeral b)`), por inducción meta. Todo eso quedó retirado con la
capa `⊢`, y con ello su papel de base para `Division` y el TFA objeto (`Full/Division.lean` y
`Full/Factorization.lean`, retirados también). Lo que hay hoy sobre `Prf`, y sobre este mismo
`numeral`: `prf_numeral_add` y `prf_numeral_lt` (`Meta/ArithPrf.lean`) y `prf_numeral_mul`
(`Meta/Div2ParityPrf.lean`). La separación está sobre `numeralM` (`crit_num_ne`,
`Meta/CodeWitnessPrf.lean`); `^` no tiene versión `Prf`.
-/

/-! ### Definición de `numeral` -/

/-- `numeral n = σⁿ(0)`: el término object que representa al natural meta `n`. -/
def numeral : Nat → Term
  | 0     => zero
  | n + 1 => succ (numeral n)

@[simp] theorem numeral_zero : numeral 0 = zero := rfl
@[simp] theorem numeral_succ (n : Nat) : numeral (n + 1) = succ (numeral n) := rfl

-- (Aquí vivían, sobre `⊢`, los homomorfismos de `+`, `·` y `^`, el orden y la separación, con sus
-- helpers; retirados con ADR‑115.)

/-! ### Numerales de constantes pequeñas (puente con la notación de Minimal) -/

@[simp] theorem numeral_one : numeral 1 = one := rfl
@[simp] theorem numeral_two : numeral 2 = two := rfl

end ROBINSON_PlusPlus.Full

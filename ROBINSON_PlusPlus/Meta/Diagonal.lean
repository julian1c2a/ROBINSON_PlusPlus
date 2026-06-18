/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Representability

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Diagonal

/-!
## META — NIVEL D (real): lema diagonal  (Fase 4) — cimientos

Para el **lema diagonal** (punto fijo `⊢ G ⇔ φ(⌜G⌝)`) hace falta representar la
diagonalización: substituir el código de una fórmula en sí misma, lo que requiere
el **código del código** `termCode (formCode ψ)`. La función object `tcFn`
(`Minimal/Axioms.lean`) computa `termCode` sobre códigos; aquí se re-derivan sus
ecuaciones como teoremas `axioms ⊢ …` (vía `ax`+`spec`, puentes `numeralM_eq`/
`strCodeM_eq`) y se prueba `tc_numeral` (cómputo sobre numerales) por inducción
meta. Lo que sigue (cadena `tc_arith` para `formCode`, `diagTerm`, punto fijo) se
construye encima.
-/

/-! ### Ecuaciones de `tcFn` re-derivadas (espejo de la cláusula `.func` de `termCode`) -/

/-- `tcFn 0 = ⌜0⌝` (= `termCode zero`). -/
theorem tc_zero : axioms ⊢ (tcFn zero =eq termCode zero) := by
  have h := ax (show ax_tc_zero ∈ axioms by simp [axioms])
  simp only [ax_tc_zero, numeralM_eq, strCodeM_eq] at h
  simpa only [termCode, termsCode, zero, nil] using h

/-- `tcFn (σ x) = ⌜σ·⌝[tcFn x]` (espejo de `termCode (succ x)`). -/
theorem tc_succ (x : Term) :
    axioms ⊢ (tcFn (succ x) =eq
      cons (numeral 1) (cons (strCode succ_sym) (cons (cons (tcFn x) nil) nil))) := by
  have h := spec (ax (show ax_tc_succ ∈ axioms by simp [axioms])) x
  simp [ax_tc_succ, substFormula, substTerm, substTerms, tcFn, succ, cons, nil, zero,
    substTerm_numeralM, substTerm_strCodeM, substTerm_nil, FOL.substTerm_liftTerm] at h
  simp only [numeralM_eq, strCodeM_eq] at h
  exact h

/-- `tcFn (a :: b) = ⌜::·⌝[tcFn a, tcFn b]` (espejo de `termCode (cons a b)`). -/
theorem tc_cons (a b : Term) :
    axioms ⊢ (tcFn (cons a b) =eq
      cons (numeral 1) (cons (strCode cons_sym)
        (cons (cons (tcFn a) (cons (tcFn b) nil)) nil))) := by
  have h := spec (spec (ax (show ax_tc_cons ∈ axioms by simp [axioms])) a) b
  simp [ax_tc_cons, substFormula, substTerm, substTerms, tcFn, cons, nil, zero,
    substTerm_numeralM, substTerm_strCodeM, substTerm_nil, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift] at h
  simp only [numeralM_eq, strCodeM_eq] at h
  exact h

/-! ### `tcFn` computa `termCode` sobre numerales -/

/-- **Cómputo de `tcFn` sobre numerales**: `tcFn (numeral n) = ⌜numeral n⌝`. Por
    inducción meta en `n` (caso `σ` vía `tc_succ` + congruencia + IH). -/
theorem tc_numeral : ∀ n : Nat, axioms ⊢ (tcFn (numeral n) =eq termCode (numeral n))
  | 0 => by simpa only [numeral] using tc_zero
  | n + 1 => by
      -- `numeral (n+1) = succ (numeral n)`; `termCode (succ ·)` es la cláusula `.func`.
      have hstep := tc_succ (numeral n)
      have hcongr :
          axioms ⊢ (cons (numeral 1) (cons (strCode succ_sym)
              (cons (cons (tcFn (numeral n)) nil) nil)) =eq
            cons (numeral 1) (cons (strCode succ_sym)
              (cons (cons (termCode (numeral n)) nil) nil))) :=
        congr_cons_tail (congr_cons_tail (congr_cons_head (congr_cons_head (tc_numeral n))))
      have : axioms ⊢ (tcFn (numeral (n + 1)) =eq
          cons (numeral 1) (cons (strCode succ_sym)
            (cons (cons (termCode (numeral n)) nil) nil))) :=
        FOL.derive_eq_trans hstep hcongr
      simpa only [numeral, termCode, termsCode] using this

end ROBINSON_PlusPlus.Meta.Diagonal

export ROBINSON_PlusPlus.Meta.Diagonal (
  tc_zero
  tc_succ
  tc_cons
  tc_numeral
)

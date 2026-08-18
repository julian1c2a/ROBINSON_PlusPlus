/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.Representability

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.TcArithPrf

/-!
## META — NIVEL D real: `tcFn` (código del código) a nivel `Prf` (cimiento de la Σ₁-completitud object)

Porte finitario de la cadena `tc_arith` de `Meta/Diagonal.lean` (ω) al cálculo `Prf`.
`tcFn` es la **función object** que computa `termCode`; sus ecuaciones se re-derivan de
`Minimal.axioms` (vía `prf_ax`+`prf_spec`), y `prf_tc_numeral`/`prf_tc_form` prueban por
inducción meta que `tcFn` computa `termCode` sobre **todo código**. Es la herramienta base
para reformular la Σ₁-completitud del verificador (`hC`/`hI`) al nivel del código object
(donde `tcFn` **tiene congruencia Leibniz**, a diferencia de la `termCode` meta).
-/

/-- `tcFn 0 = ⌜0⌝`. -/
theorem prf_tc_zero : Prf (tcFn zero =eq termCode zero) := by
  have h := prf_ax (show ax_tc_zero ∈ axioms by simp [axioms])
  simp only [ax_tc_zero, numeralM_eq, strCodeM_eq] at h
  simpa only [termCode, termsCode, zero, nil] using h

/-- `tcFn (σ x) = ⌜σ·⌝[tcFn x]`. -/
theorem prf_tc_succ (x : Term) :
    Prf (tcFn (succ x) =eq
      cons (numeral 1) (cons (strCode succ_sym) (cons (cons (tcFn x) nil) nil))) := by
  have h := prf_spec (prf_ax (show ax_tc_succ ∈ axioms by simp [axioms])) x
  simp [ax_tc_succ, substFormula, substTerm, substTerms, tcFn, succ, cons, nil, zero,
    substTerm_numeralM, substTerm_strCodeM, substTerm_nil, FOL.substTerm_liftTerm] at h
  simp only [numeralM_eq, strCodeM_eq] at h
  exact h

-- [REPARACION] Familia SINTACTICA de `tc` RETIRADA con `ax_tc_cons`.
-- Sustituida por la via NUMERAL: ver `Meta/CodeNumeralPrf.lean` y `Meta/DiagonalNumeral.lean`.

/-- **Cómputo de `tcFn` sobre numerales**: `tcFn (numeral n) = ⌜numeral n⌝` (inducción meta). -/
theorem prf_tc_numeral : ∀ n : Nat, Prf (tcFn (numeral n) =eq termCode (numeral n))
  | 0 => by simpa only [numeral] using prf_tc_zero
  | n + 1 => by
      have hstep := prf_tc_succ (numeral n)
      have hcongr :
          Prf (cons (numeral 1) (cons (strCode succ_sym)
              (cons (cons (tcFn (numeral n)) nil) nil)) =eq
            cons (numeral 1) (cons (strCode succ_sym)
              (cons (cons (termCode (numeral n)) nil) nil))) :=
        prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
          (prf_congr_cons_head (prf_tc_numeral n))))
      have : Prf (tcFn (numeral (n + 1)) =eq
          cons (numeral 1) (cons (strCode succ_sym)
            (cons (cons (termCode (numeral n)) nil) nil))) :=
        prf_eq_trans hstep hcongr
      simpa only [numeral, succ, termCode, termsCode] using this

/-- Congruencia en los dos hijos de un nodo `func`-2 codificado. -/
theorem prf_congr_tc2 {S A A' B B' : Term} (hA : Prf (A =eq A')) (hB : Prf (B =eq B')) :
    Prf (cons (numeral 1) (cons S (cons (cons A (cons B nil)) nil)) =eq
         cons (numeral 1) (cons S (cons (cons A' (cons B' nil)) nil))) :=
  prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head hA) (prf_congr_cons_tail (prf_congr_cons_head hB)))))

-- [REPARACION] Familia SINTACTICA de `tc` RETIRADA con `ax_tc_cons`.
-- Sustituida por la via NUMERAL: ver `Meta/CodeNumeralPrf.lean` y `Meta/DiagonalNumeral.lean`.

/-- **Congruencia de `tcFn`** en `Prf` (Leibniz object): `x =eq y → tcFn x =eq tcFn y`.
    A diferencia de `termCode` (meta), `tcFn` es una **función object** y respeta la igualdad
    demostrable. Es la pieza que habilita rastrear el testigo por código object. -/
theorem prf_congr_tcFn {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (tcFn t₁ =eq tcFn t₂) := by
  let f : Formula := Formula.eq (tcFn (liftTerm 0 t₁)) (tcFn (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (tcFn t₁) (tcFn s) := by
    intro s; simp only [f, substFormula, tcFn, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (tcFn t₁))

end ROBINSON_PlusPlus.Meta.TcArithPrf

export ROBINSON_PlusPlus.Meta.TcArithPrf (
  prf_tc_zero prf_tc_succ prf_tc_numeral prf_congr_tc2 prf_congr_tcFn
)

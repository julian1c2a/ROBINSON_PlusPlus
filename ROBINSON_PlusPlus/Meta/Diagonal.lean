/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.Necessitation

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Necessitation

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
      simpa only [numeral, succ, termCode, termsCode] using this

/-! ### `tc_arith`: `tcFn` computa `termCode` sobre TODO código

Lema clave de recursión `tc_of_cons`: si `tcFn` computa `termCode` en `a` y `b`,
lo hace en `cons a b`. Con él, la familia `tc_chars`/`tc_str`/`tc_term`/`tc_form`
sale por composición directa siguiendo la estructura de cada codificador. -/

/-- Congruencia en los dos hijos de un nodo `func`-2 codificado
    (`⟨1, S, [A, B]⟩`). -/
theorem congr_tc2 {S A A' B B' : Term} (hA : axioms ⊢ (A =eq A')) (hB : axioms ⊢ (B =eq B')) :
    axioms ⊢ (cons (numeral 1) (cons S (cons (cons A (cons B nil)) nil)) =eq
              cons (numeral 1) (cons S (cons (cons A' (cons B' nil)) nil))) :=
  congr_cons_tail (congr_cons_tail (congr_cons_head
    (FOL.derive_eq_trans (congr_cons_head hA) (congr_cons_tail (congr_cons_head hB)))))

/-- **Recursión de `tc_arith`**: `tcFn` respeta `cons`. -/
theorem tc_of_cons {a b : Term} (ha : axioms ⊢ (tcFn a =eq termCode a))
    (hb : axioms ⊢ (tcFn b =eq termCode b)) :
    axioms ⊢ (tcFn (cons a b) =eq termCode (cons a b)) :=
  FOL.derive_eq_trans (tc_cons a b) (congr_tc2 ha hb)

/-- `tcFn (charsCode cs) = ⌜charsCode cs⌝`. -/
theorem tc_chars : ∀ cs : List Char, axioms ⊢ (tcFn (charsCode cs) =eq termCode (charsCode cs))
  | []      => tc_zero
  | c :: cs => tc_of_cons (tc_numeral c.toNat) (tc_chars cs)

/-- `tcFn (strCode s) = ⌜strCode s⌝`. -/
theorem tc_str (s : String) : axioms ⊢ (tcFn (strCode s) =eq termCode (strCode s)) :=
  tc_chars s.toList

mutual
/-- `tcFn (termCode t) = ⌜termCode t⌝`. -/
theorem tc_term : ∀ t : Term, axioms ⊢ (tcFn (termCode t) =eq termCode (termCode t))
  | .var n     => tc_of_cons (tc_numeral 0) (tc_of_cons (tc_numeral n) tc_zero)
  | .func s ts => tc_of_cons (tc_numeral 1) (tc_of_cons (tc_str s) (tc_of_cons (tc_terms ts) tc_zero))
/-- `tcFn (termsCode ts) = ⌜termsCode ts⌝`. -/
theorem tc_terms : ∀ ts : List Term, axioms ⊢ (tcFn (termsCode ts) =eq termCode (termsCode ts))
  | []      => tc_zero
  | t :: ts => tc_of_cons (tc_term t) (tc_terms ts)
end

/-- **`tc_arith`**: `tcFn (formCode φ) = ⌜formCode φ⌝` (el «código del código»). -/
theorem tc_form : ∀ φ : Formula, axioms ⊢ (tcFn (formCode φ) =eq termCode (formCode φ))
  | .bottom    => tc_of_cons (tc_numeral 2) tc_zero
  | .atom p ts => tc_of_cons (tc_numeral 3) (tc_of_cons (tc_str p) (tc_of_cons (tc_terms ts) tc_zero))
  | .eq t u    => tc_of_cons (tc_numeral 4) (tc_of_cons (tc_term t) (tc_of_cons (tc_term u) tc_zero))
  | .impl a b  => tc_of_cons (tc_numeral 5) (tc_of_cons (tc_form a) (tc_of_cons (tc_form b) tc_zero))
  | .forall a  => tc_of_cons (tc_numeral 6) (tc_of_cons (tc_form a) tc_zero)
  | .and a b   => tc_of_cons (tc_numeral 7) (tc_of_cons (tc_form a) (tc_of_cons (tc_form b) tc_zero))
  | .or a b    => tc_of_cons (tc_numeral 8) (tc_of_cons (tc_form a) (tc_of_cons (tc_form b) tc_zero))
  | .ex a      => tc_of_cons (tc_numeral 9) (tc_of_cons (tc_form a) tc_zero)

/-! ### Función de diagonalización representada (`diagTerm` / `diag_arith`) -/

/-- **Auto-aplicación**: `ψ` con su propio código sustituido en su variable libre 0. -/
def selfApp (ψ : Formula) : Formula := substFormula 0 (formCode ψ) ψ

/-- **Término de diagonalización** (variable libre 0): aplicado a `⌜ψ⌝` produce
    (provablemente) `⌜selfApp ψ⌝`. Usa `tcFn` (código del código) y `substfc`. -/
def diagTerm : Term := substfc (numeral 0) (tcFn (Term.var 0)) (Term.var 0)

/-- **Representabilidad de la diagonalización**: `diagTerm[⌜ψ⌝] = ⌜selfApp ψ⌝`.
    Es `tc_form` (código del código) + `substFormula_arith` (sustitución). -/
theorem diag_arith (ψ : Formula) :
    axioms ⊢ (substTerm 0 (formCode ψ) diagTerm =eq formCode (selfApp ψ)) := by
  have key : axioms ⊢
      (substfc (numeral 0) (tcFn (formCode ψ)) (formCode ψ) =eq formCode (selfApp ψ)) :=
    FOL.derive_eq_trans (congr_substfc_arg2 (tc_form ψ)) (substFormula_arith 0 (formCode ψ) ψ)
  exact key

/-! ### Punto fijo (lema diagonal) y Primer Teorema de Gödel real

Para el predicado concreto de Gödel `godelPred = ¬provFormulaC` (una variable
libre, sin variables libres ≥ 1) la composición de sustituciones se reduce con un
único `substTerm_lift_comm` (no hace falta el lema general De Bruijn). -/

/-- **Leibniz para fórmulas**: de `t₁ = t₂` se obtiene `φ[t₁] ⇔ φ[t₂]`. -/
theorem subst_eq_iff {t₁ t₂ : Term} (φ : Formula) (h : axioms ⊢ (t₁ =eq t₂)) :
    axioms ⊢ (substFormula 0 t₁ φ ⇔ substFormula 0 t₂ φ) :=
  FOL.MetaRules.and_intro
    (imp_intro (fun hp => Derives.subst axioms t₁ t₂ φ h hp))
    (imp_intro (fun hp => Derives.subst axioms t₂ t₁ φ (FOL.derive_eq_symm h) hp))

/-- Predicado de Gödel `¬Prov(·)` (variable libre 0). -/
def godelPred : Formula := neg provFormulaC

/-- Predicado diagonalizado `β` (variable libre 0). -/
def godelBeta : Formula := substFormula 0 diagTerm godelPred

/-- **Sentencia de Gödel real** `G = β(⌜β⌝)`. -/
noncomputable def godelC : Formula := selfApp godelBeta

/-- Composición de sustituciones para `godelPred` (sin var libre ≥ 1): se reduce
    con `substTerm_lift_comm`. -/
theorem godel_comp (s : Term) :
    substFormula 0 s godelBeta = substFormula 0 (substTerm 0 s diagTerm) godelPred := by
  simp [godelBeta, godelPred, neg, provFormulaC, substFormula, substTerm, substTerms,
    In, validProofFn, nil, zero, FOL.substTerm_liftTerm, FOL.substTerm_lift_comm]

/-- **Lema diagonal (punto fijo) real**: `⊢ G ⇔ ¬Prov(⌜G⌝)`. Reemplaza el postulado
    `diagonal_lemma`/`goedelSentence_fixedpoint` para el predicado **concreto**
    `provCodeC`. -/
theorem godelC_fixedpoint : axioms ⊢ (godelC ⇔ neg (provCodeC godelC)) := by
  have hiff := subst_eq_iff godelPred (diag_arith godelBeta)
  rw [← godel_comp (formCode godelBeta)] at hiff
  -- `substFormula 0 ⌜β⌝ β = selfApp β = G`; `substFormula 0 ⌜G⌝ godelPred = ¬provCodeC G`
  simpa only [godelC, selfApp, godelPred, provCodeC, neg, substFormula] using hiff

/-- **Primer Teorema de Incompletitud de Gödel — REAL** (mitad de
    indemostrabilidad): si la teoría es consistente, la sentencia de Gödel `G`
    (construida con el predicado de demostrabilidad **concreto** `provCodeC`) **no**
    es demostrable en el cálculo finitario `Prf`. Sin postular el lema diagonal ni
    las condiciones de demostrabilidad. -/
theorem goedel_first_real (hcon : ConsistentOmega) : ¬ Prf godelC :=
  goedel_first_unprovable_real hcon godelC_fixedpoint

end ROBINSON_PlusPlus.Meta.Diagonal

export ROBINSON_PlusPlus.Meta.Diagonal (
  tc_zero
  tc_succ
  tc_cons
  tc_numeral
  tc_of_cons
  tc_chars
  tc_str
  tc_term
  tc_terms
  tc_form
  selfApp
  diagTerm
  diag_arith
  subst_eq_iff
  godelPred
  godelBeta
  godelC
  godelC_fixedpoint
  goedel_first_real
)

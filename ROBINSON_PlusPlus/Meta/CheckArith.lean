/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.StepArith

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CheckArith

/-!
## META — NIVEL D (real): verificador object de demostraciones  (Fase 2.4)

`demFormula` (la fórmula Σ₁ de demostrabilidad) reposa sobre un verificador
object-level de demostraciones-secuencia **anotadas hacia adelante**: cada línea
lleva su etiqueta de regla (`numeralM 0..17`) y sus parámetros; el verificador
`validProofFn` recorre la secuencia recomputando la conclusión de cada línea (los
esquemas Q usan `substfc`/`liftfc`, ya hechos) y, para MP/Gen, comprueba la
pertenencia de las premisas vía `In`.

Este archivo arranca con los **extractores** `carc`/`cdrc` (cabeza/cola de
`cons`) computados, y el puente `numeralM = Godel.numeral`. El ensamblaje de
`validProofFn` + `demFormula` sigue (las ecuaciones van en `Minimal.axioms`).
-/

/-- `numeralM` (Minimal) coincide con `Godel.numeral` (misma definición). -/
theorem numeralM_eq (n : Nat) : numeralM n = ROBINSON_PlusPlus.Meta.Godel.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [numeralM, ROBINSON_PlusPlus.Meta.Godel.numeral, ih]

/-- Cómputo de `carc (cons h t) = h`. -/
theorem carc_cons (h t : Term) : axioms ⊢ (carc (cons h t) =eq h) := by
  have hh := spec (spec (ax (show ax_carc ∈ axioms by simp [axioms])) h) t
  simp [ax_carc, substFormula, substTerm, substTerms, carc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Cómputo de `cdrc (cons h t) = t`. -/
theorem cdrc_cons (h t : Term) : axioms ⊢ (cdrc (cons h t) =eq t) := by
  have hh := spec (spec (ax (show ax_cdrc ∈ axioms by simp [axioms])) h) t
  simp [ax_cdrc, substFormula, substTerm, substTerms, cdrc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Pasos de `validProofFn` (re-derivados de `Minimal.axioms`) -/

theorem vpf_p1 (checked a b rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 0) (cons a (cons b nil))) rest) =eq
      validProofFn (concat checked (cons (implc a (implc b a)) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_p1 ∈ axioms by simp [axioms])) checked) a) b) rest
  simp [ax_vpf_p1, substFormula, substTerm, substTerms, validProofFn, concat, implc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_p2 (checked a b c rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 1) (cons a (cons b (cons c nil)))) rest) =eq
      validProofFn (concat checked (cons (implc (implc a (implc b c)) (implc (implc a b) (implc a c))) nil)) rest) := by
  have hh := spec (spec (spec (spec (spec (ax (show ax_vpf_p2 ∈ axioms by simp [axioms])) checked) a) b) c) rest
  simp [ax_vpf_p2, substFormula, substTerm, substTerms, validProofFn, concat, implc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh

theorem vpf_nil (checked : Term) :
    axioms ⊢ (validProofFn checked nil =eq checked) := by
  have hh := spec (ax (show ax_vpf_nil ∈ axioms by simp [axioms])) checked
  simp [ax_vpf_nil, substFormula, substTerm, substTerms, validProofFn, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

theorem vpf_c1 (checked a b rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 2) (cons a (cons b nil))) rest) =eq
      validProofFn (concat checked (cons (implc a (implc b (andc a b))) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_c1 ∈ axioms by simp [axioms])) checked) a) b) rest
  simp [ax_vpf_c1, substFormula, substTerm, substTerms, validProofFn, concat, implc, andc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_c2 (checked a b rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 3) (cons a (cons b nil))) rest) =eq
      validProofFn (concat checked (cons (implc (andc a b) a) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_c2 ∈ axioms by simp [axioms])) checked) a) b) rest
  simp [ax_vpf_c2, substFormula, substTerm, substTerms, validProofFn, concat, implc, andc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_c3 (checked a b rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 4) (cons a (cons b nil))) rest) =eq
      validProofFn (concat checked (cons (implc (andc a b) b) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_c3 ∈ axioms by simp [axioms])) checked) a) b) rest
  simp [ax_vpf_c3, substFormula, substTerm, substTerms, validProofFn, concat, implc, andc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_j1 (checked a b rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 5) (cons a (cons b nil))) rest) =eq
      validProofFn (concat checked (cons (implc a (orc a b)) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_j1 ∈ axioms by simp [axioms])) checked) a) b) rest
  simp [ax_vpf_j1, substFormula, substTerm, substTerms, validProofFn, concat, implc, orc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_j2 (checked a b rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 6) (cons a (cons b nil))) rest) =eq
      validProofFn (concat checked (cons (implc b (orc a b)) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_j2 ∈ axioms by simp [axioms])) checked) a) b) rest
  simp [ax_vpf_j2, substFormula, substTerm, substTerms, validProofFn, concat, implc, orc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_j3 (checked a b c rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 7) (cons a (cons b (cons c nil)))) rest) =eq
      validProofFn (concat checked (cons (implc (orc a b) (implc (implc a c) (implc (implc b c) c))) nil)) rest) := by
  have hh := spec (spec (spec (spec (spec (ax (show ax_vpf_j3 ∈ axioms by simp [axioms])) checked) a) b) c) rest
  simp [ax_vpf_j3, substFormula, substTerm, substTerms, validProofFn, concat, implc, orc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh

theorem vpf_efq (checked a rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 8) (cons a nil)) rest) =eq
      validProofFn (concat checked (cons (implc botc a) nil)) rest) := by
  have hh := spec (spec (spec (ax (show ax_vpf_efq ∈ axioms by simp [axioms])) checked) a) rest
  simp [ax_vpf_efq, substFormula, substTerm, substTerms, validProofFn, concat, implc, botc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem vpf_q1 (checked A t rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 9) (cons A (cons t nil))) rest) =eq
      validProofFn (concat checked (cons (implc (forallc A) (substfc zero t A)) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_q1 ∈ axioms by simp [axioms])) checked) A) t) rest
  simp [ax_vpf_q1, substFormula, substTerm, substTerms, validProofFn, concat, implc, forallc, substfc, numeralM,
    cons, nil, zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_q2 (checked A t rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 10) (cons A (cons t nil))) rest) =eq
      validProofFn (concat checked (cons (implc (substfc zero t A) (exc A)) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_q2 ∈ axioms by simp [axioms])) checked) A) t) rest
  simp [ax_vpf_q2, substFormula, substTerm, substTerms, validProofFn, concat, implc, exc, substfc, numeralM,
    cons, nil, zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_q3 (checked A B rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 11) (cons A (cons B nil))) rest) =eq
      validProofFn (concat checked (cons (implc (forallc (implc A (liftfc zero B))) (implc (exc A) B)) nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_q3 ∈ axioms by simp [axioms])) checked) A) B) rest
  simp [ax_vpf_q3, substFormula, substTerm, substTerms, validProofFn, concat, implc, forallc, exc, liftfc, numeralM,
    cons, nil, zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

theorem vpf_eqrefl (checked t rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 12) (cons t nil)) rest) =eq
      validProofFn (concat checked (cons (eqc t t) nil)) rest) := by
  have hh := spec (spec (spec (ax (show ax_vpf_eqrefl ∈ axioms by simp [axioms])) checked) t) rest
  simp [ax_vpf_eqrefl, substFormula, substTerm, substTerms, validProofFn, concat, eqc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem vpf_leibniz (checked A t₁ t₂ rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil)))) rest) =eq
      validProofFn (concat checked (cons (implc (eqc t₁ t₂) (implc (substfc zero t₁ A) (substfc zero t₂ A))) nil)) rest) := by
  have hh := spec (spec (spec (spec (spec (ax (show ax_vpf_leibniz ∈ axioms by simp [axioms])) checked) A) t₁) t₂) rest
  simp [ax_vpf_leibniz, substFormula, substTerm, substTerms, validProofFn, concat, implc, eqc, substfc, numeralM,
    cons, nil, zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh

theorem vpf_p3 (checked a rest : Term) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 14) (cons a nil)) rest) =eq
      validProofFn (concat checked (cons (implc (implc (implc a botc) botc) a) nil)) rest) := by
  have hh := spec (spec (spec (ax (show ax_vpf_p3 ∈ axioms by simp [axioms])) checked) a) rest
  simp [ax_vpf_p3, substFormula, substTerm, substTerms, validProofFn, concat, implc, botc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem vpf_mp (checked conclB premiseA rest : Term)
    (h1 : axioms ⊢ In (implc premiseA conclB) checked) (h2 : axioms ⊢ In premiseA checked) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 16) (cons conclB (cons premiseA nil))) rest) =eq
      validProofFn (concat checked (cons conclB nil)) rest) := by
  have hh := spec (spec (spec (spec (ax (show ax_vpf_mp ∈ axioms by simp [axioms])) checked) conclB) premiseA) rest
  simp [ax_vpf_mp, substFormula, substTerm, substTerms, validProofFn, concat, implc, In, in_sym, numeralM, cons,
    nil, zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact mp (mp hh h1) h2

theorem vpf_gen (checked body rest : Term)
    (h1 : axioms ⊢ In body checked) :
    axioms ⊢ (validProofFn checked (cons (cons (numeralM 17) (cons body nil)) rest) =eq
      validProofFn (concat checked (cons (forallc body) nil)) rest) := by
  have hh := spec (spec (spec (ax (show ax_vpf_gen ∈ axioms by simp [axioms])) checked) body) rest
  simp [ax_vpf_gen, substFormula, substTerm, substTerms, validProofFn, concat, forallc, In, in_sym, numeralM, cons,
    nil, zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact mp hh h1

/-! ### Fórmula de demostrabilidad object Σ₁ -/

/-- **Predicado de demostrabilidad object** (Σ₁): `∃ p, In x (validProofFn nil p)`
    — "existe una demostración-secuencia `p` cuyas conclusiones contienen `x`".
    `x` ocupa la variable libre 0 (convención de `substFormula 0 ⌜φ⌝ ·`). Versión
    **concreta** del `provFormula` postulado en `Meta/Provability.lean`. -/
def provFormulaC : Formula := Formula.ex (In (Term.var 1) (validProofFn nil (Term.var 0)))

/-- `Prov(⌜φ⌝)` concreto. -/
noncomputable def provCodeC (φ : Formula) : Formula := substFormula 0 (formCode φ) provFormulaC

end ROBINSON_PlusPlus.Meta.CheckArith

export ROBINSON_PlusPlus.Meta.CheckArith (
  provFormulaC
  provCodeC
  numeralM_eq
  carc_cons
  cdrc_cons
  vpf_nil
  vpf_p1
  vpf_p2
  vpf_c1
  vpf_c2
  vpf_c3
  vpf_j1
  vpf_j2
  vpf_j3
  vpf_efq
  vpf_q1
  vpf_q2
  vpf_q3
  vpf_eqrefl
  vpf_leibniz
  vpf_p3
  vpf_mp
  vpf_gen
)

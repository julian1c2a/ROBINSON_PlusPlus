/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.Representability

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ProofChain

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Representability2

/-!
## META — NIVEL D real: representabilidad positiva con `runFn` (R4-parte 2)

Re-construye `repr_pos` para el verificador estructural `runFn`/`chainOk` y el
predicado `provCodeC'`. Encoder **a medida** del nuevo formato: cada línea es
`cons ⌜concl⌝ (lineJustif …)` — la conclusión va incorporada como cabeza, de modo
que `carc` la extrae **uniformemente** (sin partir por reglas).

Este archivo arranca con el **runFn-tracking** (la mitad `In ⌜φ⌝`): `runFn` sobre
`proofCode' rs acc` calcula el código de la lista de conclusiones de `checkAux rs
acc`. Es RULE-AGNÓSTICO (solo usa `carc`), mucho más simple que el viejo `vpf_run`.
La validez `chainOk` (la otra mitad) sigue con los `lineWF`/`premsOf` por regla.
-/

/-! ### Encoder object del nuevo formato -/

/-- Justificación de una línea (etiqueta + parámetros), **sin** la conclusión
    (que va como cabeza en `lineCode'`). `mp`/`gen` transportan el código de la
    premisa resuelta; `thy` solo la etiqueta. -/
def lineJustif (acc : List Formula) : Rule → Term
  | .p1 A B => cons (numeralM 0) (cons (formCode A) (cons (formCode B) nil))
  | .p2 A B C => cons (numeralM 1) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .c1 A B => cons (numeralM 2) (cons (formCode A) (cons (formCode B) nil))
  | .c2 A B => cons (numeralM 3) (cons (formCode A) (cons (formCode B) nil))
  | .c3 A B => cons (numeralM 4) (cons (formCode A) (cons (formCode B) nil))
  | .j1 A B => cons (numeralM 5) (cons (formCode A) (cons (formCode B) nil))
  | .j2 A B => cons (numeralM 6) (cons (formCode A) (cons (formCode B) nil))
  | .j3 A B C => cons (numeralM 7) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .efq A => cons (numeralM 8) (cons (formCode A) nil)
  | .q1 A t => cons (numeralM 9) (cons (formCode A) (cons (termCode t) nil))
  | .q2 A t => cons (numeralM 10) (cons (formCode A) (cons (termCode t) nil))
  | .q3 A B => cons (numeralM 11) (cons (formCode A) (cons (formCode B) nil))
  | .eqrefl t => cons (numeralM 12) (cons (termCode t) nil)
  | .leibniz A t₁ t₂ =>
      cons (numeralM 13) (cons (formCode A) (cons (termCode t₁) (cons (termCode t₂) nil)))
  | .p3 A => cons (numeralM 14) (cons (formCode A) nil)
  | .ind A => cons (numeralM 18) (cons (formCode A) nil)
  | .thy _ => cons (numeralM 15) nil
  | .mp _ j => cons (numeralM 16) (cons (formCode ((acc[j]?).getD Formula.bottom)) nil)
  | .gen i => cons (numeralM 17) (cons (formCode ((acc[i]?).getD Formula.bottom)) nil)

/-- Línea completa: `cons ⌜concl⌝ justif`. La conclusión `f` (= `stepConcl acc r`)
    va como cabeza ⟹ `carc (lineCode' acc f r) =eq ⌜f⌝` para CUALQUIER regla. -/
def lineCode' (acc : List Formula) (f : Formula) (r : Rule) : Term :=
  cons (formCode f) (lineJustif acc r)

/-- Código object de una demostración-secuencia (nuevo formato). -/
def proofCode' : List Rule → List Formula → Term
  | [], _ => nil
  | r :: rs, acc =>
      match stepConcl acc r with
      | some f => cons (lineCode' acc f r) (proofCode' rs (acc ++ [f]))
      | none => nil

/-! ### runFn-tracking (mitad `In ⌜φ⌝`) -/

/-- `concat ⌜acc⌝ [⌜f⌝] =eq ⌜acc ++ [f]⌝`. -/
theorem concat_listFormCode_singleton (acc : List Formula) (f : Formula) :
    axioms ⊢ (concat (listFormCode acc) (cons (formCode f) nil) =eq listFormCode (acc ++ [f])) := by
  simpa [listFormCode] using concat_listFormCode acc [f]

/-- **runFn-tracking**: sobre `proofCode' rs acc`, `runFn` calcula el código de la
    lista de conclusiones que `checkAux rs acc` produce. RULE-AGNÓSTICO (solo `carc`). -/
theorem runFn_track (rs : List Rule) : ∀ (acc L : List Formula), checkAux rs acc = some L →
    axioms ⊢ (runFn (listFormCode acc) (proofCode' rs acc) =eq listFormCode L) := by
  induction rs with
  | nil =>
      intro acc L h
      simp only [checkAux, Option.some.injEq] at h
      subst h
      simpa [proofCode'] using runFn_nil (listFormCode acc)
  | cons r rs ih =>
      intro acc L h
      cases hsc : stepConcl acc r with
      | none => simp [checkAux, hsc] at h
      | some f =>
          have hcheck : checkAux rs (acc ++ [f]) = some L := by
            have h2 := h; simp only [checkAux, hsc] at h2; exact h2
          have ihf := ih (acc ++ [f]) L hcheck
          rw [show proofCode' (r :: rs) acc = cons (lineCode' acc f r) (proofCode' rs (acc ++ [f]))
                from by simp [proofCode', hsc]]
          -- runFn (⌜acc⌝) (cons (lineCode') rest) =eq runFn (⌜acc⌝ ++ [carc lineCode']) rest
          refine FOL.derive_eq_trans
            (runFn_cons (listFormCode acc) (lineCode' acc f r) (proofCode' rs (acc ++ [f]))) ?_
          -- carc (lineCode' acc f r) =eq ⌜f⌝
          have hcarc : axioms ⊢ (carc (lineCode' acc f r) =eq formCode f) :=
            carc_cons (formCode f) (lineJustif acc r)
          -- runFn (⌜acc⌝ ++ [carc]) rest =eq runFn ⌜acc++[f]⌝ rest
          refine FOL.derive_eq_trans
            (congr_runFn_1 (FOL.derive_eq_trans (Full.eq_congr_concat_left (congr_cons_head hcarc))
              (concat_listFormCode_singleton acc f))) ?_
          exact ihf

/-! ### Pertenencia object de `φ` en las conclusiones -/

/-- Si `checkAux rs [] = some L` y `φ ∈ L`, entonces `⊢ In ⌜φ⌝ (runFn nil (proofCode' rs []))`. -/
theorem In_runFn_of_mem {rs : List Rule} {L : List Formula} {φ : Formula}
    (hchk : checkAux rs [] = some L) (hmem : φ ∈ L) :
    axioms ⊢ In (formCode φ) (runFn nil (proofCode' rs [])) := by
  have htrack : axioms ⊢ (runFn nil (proofCode' rs []) =eq listFormCode L) := by
    simpa [listFormCode] using runFn_track rs [] L hchk
  exact Full.eq_subst_in (FOL.derive_eq_symm htrack) (In_listFormCode hmem)

end ROBINSON_PlusPlus.Meta.Representability2

export ROBINSON_PlusPlus.Meta.Representability2 (
  lineJustif
  lineCode'
  proofCode'
  runFn_track
  In_runFn_of_mem
)

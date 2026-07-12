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
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.StepArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.Induction
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
  | .qconf P C => cons (numeralM 19) (cons (formCode P) (cons (formCode C) nil))
  | .listInd A => cons (numeralM 20) (cons (formCode A) nil)
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

/-! ### chainOk-tracking (validez de la cadena) -/

/-- Pertenencia del código de un axioma a `axiomsCodeT` (vía meta-axioma `ax_inAxC`
    + puente `formCodeM_eq`). Reusado en el caso `thy`. -/
private theorem inAxiomsCodeT {f : Formula} (hmem : f ∈ axioms) :
    axioms ⊢ In (formCode f) axiomsCodeT := by
  have h0 : axioms ⊢ In (formCodeM f) axiomsCodeT := ax_inAxC f hmem
  rwa [formCodeM_eq] at h0

/-- **chainOk-tracking**: `proofCode' rs acc` es una cadena válida desde `⌜acc⌝`.
    Inducción sobre `rs`; cada línea cumple `lineOk` (esquemas: `lineWF` reconstrucción
    vía `*_concl_code`/`refl`, `premsOf=nil`; mp/gen: premisas en contexto vía
    `In_listFormCode`; thy: código en `axiomsCodeT`). -/
theorem chainOk_track (rs : List Rule) : ∀ (acc L : List Formula), checkAux rs acc = some L →
    axioms ⊢ chainOk (listFormCode acc) (proofCode' rs acc) := by
  induction rs with
  | nil =>
      intro acc L _
      simpa [proofCode'] using chainOk_nil (listFormCode acc)
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
          refine iff_mpr (chainOk_cons (listFormCode acc) (lineCode' acc f r)
            (proofCode' rs (acc ++ [f]))) ?_
          refine Minimal.Axioms.and_intro ?lineOk ?rest
          case rest =>
            -- contexto siguiente = ⌜acc⌝ ++ [carc lineCode'] =eq ⌜acc++[f]⌝
            have hC : axioms ⊢
                (concat (listFormCode acc) (cons (carc (lineCode' acc f r)) nil) =eq
                  listFormCode (acc ++ [f])) :=
              FOL.derive_eq_trans
                (Full.eq_congr_concat_left (congr_cons_head (carc_cons (formCode f) (lineJustif acc r))))
                (concat_listFormCode_singleton acc f)
            exact chainOk_subst1 (FOL.derive_eq_symm hC) ihf
          case lineOk =>
            cases r with
            | p1 A B =>
                have hf : f = (A ⇒ (B ⇒ A)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_p1 _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_p1 _ _ _)) (allIn_nil (listFormCode acc)))
            | p2 A B C =>
                have hf : f = ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_p2 _ _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_p2 _ _ _ _)) (allIn_nil (listFormCode acc)))
            | c1 A B =>
                have hf : f = (A ⇒ (B ⇒ (A ∧ B))) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_c1 _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_c1 _ _ _)) (allIn_nil (listFormCode acc)))
            | c2 A B =>
                have hf : f = ((A ∧ B) ⇒ A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_c2 _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_c2 _ _ _)) (allIn_nil (listFormCode acc)))
            | c3 A B =>
                have hf : f = ((A ∧ B) ⇒ B) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_c3 _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_c3 _ _ _)) (allIn_nil (listFormCode acc)))
            | j1 A B =>
                have hf : f = (A ⇒ (A ∨ B)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_j1 _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_j1 _ _ _)) (allIn_nil (listFormCode acc)))
            | j2 A B =>
                have hf : f = (B ⇒ (A ∨ B)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_j2 _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_j2 _ _ _)) (allIn_nil (listFormCode acc)))
            | j3 A B C =>
                have hf : f = ((A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C))) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_j3 _ _ _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_j3 _ _ _ _)) (allIn_nil (listFormCode acc)))
            | efq A =>
                have hf : f = (⊥ ⇒ A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_efq _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_efq _ _)) (allIn_nil (listFormCode acc)))
            | q1 A t =>
                have hf : f = ((Formula.forall A) ⇒ substFormula 0 t A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro
                  (iff_mpr (lineWF_q1 _ _ _) (FOL.derive_eq_symm (q1_concl_code A t)))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_q1 _ _ _)) (allIn_nil (listFormCode acc)))
            | q2 A t =>
                have hf : f = (substFormula 0 t A ⇒ Formula.ex A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro
                  (iff_mpr (lineWF_q2 _ _ _) (FOL.derive_eq_symm (q2_concl_code A t)))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_q2 _ _ _)) (allIn_nil (listFormCode acc)))
            | q3 A B =>
                have hf : f = ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ ((Formula.ex A) ⇒ B)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine Minimal.Axioms.and_intro (iff_mpr (lineWF_q3 _ _ _) ?_)
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_q3 _ _ _)) (allIn_nil (listFormCode acc)))
                -- formCode q3-concl =eq implc (forallc (implc A (liftfc zero B))) (implc (exc A) B)
                exact FOL.derive_eq_symm
                  (congr_bin1 (congr_un (congr_bin2 (liftFormula_arith 0 B))))
            | eqrefl t =>
                have hf : f = (t ≐ t) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_eqrefl _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_eqrefl _ _)) (allIn_nil (listFormCode acc)))
            | leibniz A t₁ t₂ =>
                have hf : f = ((t₁ ≐ t₂) ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro
                  (iff_mpr (lineWF_leibniz _ _ _ _) (FOL.derive_eq_symm (leibniz_concl_code A t₁ t₂)))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_leibniz _ _ _ _)) (allIn_nil (listFormCode acc)))
            | p3 A =>
                have hf : f = (((A ⇒ ⊥) ⇒ ⊥) ⇒ A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact Minimal.Axioms.and_intro (iff_mpr (lineWF_p3 _ _) (Derives.refl axioms _))
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_p3 _ _)) (allIn_nil (listFormCode acc)))
            | ind A =>
                have hf : f = Full.inductionFormula A := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine Minimal.Axioms.and_intro (iff_mpr (lineWF_ind _ _) ?_)
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_ind _ _)) (allIn_nil (listFormCode acc)))
                rw [termCodeM_eq zero, termCodeM_eq (succ (Term.var 0))]
                exact FOL.derive_eq_symm (ind_concl_code A)
            | qconf P C =>
                have hf : f = ROBINSON_PlusPlus.Meta.Hilbert.confinementFormula P C := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine Minimal.Axioms.and_intro (iff_mpr (lineWF_qconf _ _ _) ?_)
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_qconf _ _ _)) (allIn_nil (listFormCode acc)))
                exact FOL.derive_eq_symm
                  (congr_bin1 (congr_un (congr_bin1 (liftFormula_arith 0 P))))
            | listInd A =>
                have hf : f = ROBINSON_PlusPlus.Meta.Hilbert.listInductionFormula A := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine Minimal.Axioms.and_intro (iff_mpr (lineWF_listInd _ _) ?_)
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_listInd _ _)) (allIn_nil (listFormCode acc)))
                rw [termCodeM_eq nil, termCodeM_eq (cons (Term.var 1) (Term.var 0))]
                exact FOL.derive_eq_symm (ROBINSON_PlusPlus.Meta.ListInductionArith.listInd_concl_code A)
            | thy k =>
                have hmem : f ∈ axioms :=
                  List.mem_of_getElem? (by simpa only [stepConcl] using hsc)
                simp only [lineCode', lineJustif]
                refine Minimal.Axioms.and_intro (iff_mpr (lineWF_thy _) ?_)
                  (allIn_subst2 (FOL.derive_eq_symm (premsOf_thy _)) (allIn_nil (listFormCode acc)))
                exact inAxiomsCodeT hmem
            | mp i j =>
                rcases hi : acc[i]? with _ | fi
                · simp [stepConcl, hi] at hsc
                rcases hj : acc[j]? with _ | fj
                · simp [stepConcl, hi, hj] at hsc
                rcases hm : mpConcl fi fj with _ | fmp
                · simp [stepConcl, hi, hj, hm] at hsc
                have hffmp : f = fmp := by
                  simp only [stepConcl, hi, hj, hm, Option.bind_some, Option.some.injEq] at hsc
                  exact hsc.symm
                subst hffmp
                have hfi_eq : fi = (fj ⇒ f) := mpConcl_eq hm
                simp only [lineCode', lineJustif, hj, Option.getD_some]
                refine Minimal.Axioms.and_intro (lineWF_mp _ _) ?_
                refine allIn_subst2 (FOL.derive_eq_symm (premsOf_mp (formCode f) (formCode fj))) ?_
                refine iff_mpr (allIn_cons (listFormCode acc) (implc (formCode fj) (formCode f))
                  (cons (formCode fj) nil)) ?_
                refine Minimal.Axioms.and_intro ?_ ?_
                · have hin : axioms ⊢ In (formCode fi) (listFormCode acc) :=
                    In_listFormCode (List.mem_of_getElem? hi)
                  rw [hfi_eq] at hin; exact hin
                · refine iff_mpr (allIn_cons (listFormCode acc) (formCode fj) nil) ?_
                  exact Minimal.Axioms.and_intro (In_listFormCode (List.mem_of_getElem? hj))
                    (allIn_nil (listFormCode acc))
            | gen i =>
                rcases hi : acc[i]? with _ | fi
                · simp [stepConcl, hi] at hsc
                have hf : f = Formula.forall fi := by
                  simp only [stepConcl, hi, Option.map_some, Option.some.injEq] at hsc
                  exact hsc.symm
                subst hf
                simp only [lineCode', lineJustif, hi, Option.getD_some]
                refine Minimal.Axioms.and_intro
                  (iff_mpr (lineWF_gen (formCode (Formula.forall fi)) (formCode fi))
                    (Derives.refl axioms _)) ?_
                refine allIn_subst2 (FOL.derive_eq_symm (premsOf_gen (formCode (Formula.forall fi))
                  (formCode fi))) ?_
                refine iff_mpr (allIn_cons (listFormCode acc) (formCode fi) nil) ?_
                exact Minimal.Axioms.and_intro (In_listFormCode (List.mem_of_getElem? hi))
                  (allIn_nil (listFormCode acc))

/-! ### Representabilidad positiva (D1) con el verificador estructural -/

/-- **`repr_pos'` (D1 real, estructural)**: toda demostración de Hilbert `Prf φ` se
    internaliza como `axioms ⊢ provCodeC' φ`. Combina `chainOk_track` (validez) y
    `runFn_track`/`In_runFn_of_mem` (la conclusión `⌜φ⌝` aparece). -/
theorem repr_pos' {φ : Formula} (h : Prf φ) : axioms ⊢ provCodeC' φ := by
  obtain ⟨rs, L, hchk, hmem⟩ := prf_iff_derivation.mp h
  have hchk' : checkAux rs [] = some L := by simpa [checkProof] using hchk
  exact provCodeC'_intro φ (proofCode' rs [])
    (chainOk_track rs [] L hchk') (In_runFn_of_mem hchk' hmem)

end ROBINSON_PlusPlus.Meta.Representability2

export ROBINSON_PlusPlus.Meta.Representability2 (
  lineJustif
  lineCode'
  proofCode'
  runFn_track
  In_runFn_of_mem
  chainOk_track
  repr_pos'
)

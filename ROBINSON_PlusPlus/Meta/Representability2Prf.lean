/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.Representability2

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
open ROBINSON_PlusPlus.Meta.Representability2
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Representability2Prf

/-!
## META — NIVEL D real: representabilidad positiva (D1) re-nivelada a `Prf`

Porte finitario de `Representability2` (encoder `runFn`/`chainOk` + tracking) a
`Prf`, culminando en **`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`** (necesitación
internalizada al nivel del cálculo finitario, lo que necesita la cadena HBL hacia
Gödel II real). Reusa los defs system-agnósticos `lineJustif`/`lineCode'`/`proofCode'`
de `Representability2` y los lemas `Prf` de `ReprPrf`/`ArithPrf`; cada prueba espeja
su versión `axioms ⊢`.
-/

/-! ### `concat`/`In` sobre códigos de listas en `Prf` -/

/-- `concat ⌜a⌝ ⌜b⌝ =eq ⌜a ++ b⌝` en `Prf`. -/
theorem prf_concat_listFormCode : ∀ (a b : List Formula),
    Prf (concat (listFormCode a) (listFormCode b) =eq listFormCode (a ++ b))
  | [], b => by simpa [listFormCode] using prf_concat_nil_eq (listFormCode b)
  | f :: fs, b => by
      simp only [listFormCode, List.cons_append]
      exact prf_eq_trans (prf_concat_cons_eq (formCode f) (listFormCode fs) (listFormCode b))
        (prf_congr_cons_tail (prf_concat_listFormCode fs b))

/-- `concat ⌜acc⌝ [⌜f⌝] =eq ⌜acc ++ [f]⌝` en `Prf`. -/
theorem prf_concat_listFormCode_singleton (acc : List Formula) (f : Formula) :
    Prf (concat (listFormCode acc) (cons (formCode f) nil) =eq listFormCode (acc ++ [f])) := by
  simpa [listFormCode] using prf_concat_listFormCode acc [f]

/-! ### runFn-tracking en `Prf` (mitad `In ⌜φ⌝`) -/

theorem prf_runFn_track (rs : List Rule) : ∀ (acc L : List Formula), checkAux rs acc = some L →
    Prf (runFn (listFormCode acc) (proofCode' rs acc) =eq listFormCode L) := by
  induction rs with
  | nil =>
      intro acc L h
      simp only [checkAux, Option.some.injEq] at h
      subst h
      simpa [proofCode'] using prf_runFn_nil (listFormCode acc)
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
          refine prf_eq_trans
            (prf_runFn_cons (listFormCode acc) (lineCode' acc f r) (proofCode' rs (acc ++ [f]))) ?_
          have hcarc : Prf (carc (lineCode' acc f r) =eq formCode f) :=
            prf_carc_cons (formCode f) (lineJustif acc r)
          refine prf_eq_trans
            (prf_congr_runFn_1 (prf_eq_trans (prf_congr_concat_left (prf_congr_cons_head hcarc))
              (prf_concat_listFormCode_singleton acc f))) ?_
          exact ihf

/-! ### Pertenencia object de `φ` en las conclusiones, en `Prf` -/

theorem prf_In_runFn_of_mem {rs : List Rule} {L : List Formula} {φ : Formula}
    (hchk : checkAux rs [] = some L) (hmem : φ ∈ L) :
    Prf (In (formCode φ) (runFn nil (proofCode' rs []))) := by
  have htrack : Prf (runFn nil (proofCode' rs []) =eq listFormCode L) := by
    simpa [listFormCode] using prf_runFn_track rs [] L hchk
  exact prf_eq_subst_in (prf_eq_symm htrack) (prf_In_listFormCode hmem)

/-! ### Pertenencia de códigos de axioma a `axiomsCodeT`, en `Prf`

**Meta-axioma de codificación finitario** `prf_axiomsCodeT_eq`: el anclaje del constante opaco
`axiomsCodeT` a la lista explícita `listFormCodeM axioms`, a nivel del cálculo `Prf` (espejo de
`ax_axiomsCodeT_eq`, que vive a nivel `axioms ⊢`; no derivable de él porque `Prf → ⊢` es de una
sola dirección). Es **el único postulado de codificación** de la capa `Prf`: con él, `prf_inAxC`
(la pertenencia de cada código de axioma) pasa a ser **TEOREMA** — igual que en `⊢` `ax_inAxC` se
deriva del anclaje `ax_axiomsCodeT_eq`. -/
axiom prf_axiomsCodeT_eq : Prf (axiomsCodeT =eq listFormCodeM axioms)

/-- **Pertenencia POSITIVA en `Prf`** de un código de fórmula a `listFormCodeM L` (recursión
    estructural sobre `L`, sin materializar el término): cabeza = `prf_in_cons_head`, cola =
    `prf_in_cons_tail`. Espejo `Prf` de `prf_In_listFormCodeM` (nivel `⊢`). -/
theorem prf_In_listFormCodeM_prf (φ : Formula) :
    ∀ (L : List Formula), List.Mem φ L → Prf (In (formCodeM φ) (listFormCodeM L))
  | [], hmem => by cases hmem
  | g :: gs, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact prf_in_cons_head (formCodeM φ) (listFormCodeM gs)
      · exact prf_in_cons_tail (formCodeM g) (prf_In_listFormCodeM_prf φ gs htail)

/-- **`prf_inAxC` — ahora TEOREMA** (antes meta-axioma): la pertenencia del código de un axioma a
    `axiomsCodeT`, derivada del anclaje `prf_axiomsCodeT_eq` + la pertenencia positiva a la lista
    explícita (`prf_In_listFormCodeM_prf`) + Leibniz en el 2º argumento de `In` (`prf_eq_subst_in`). -/
theorem prf_inAxC (a : Formula) (h : a ∈ axioms) : Prf (In (formCodeM a) axiomsCodeT) :=
  prf_eq_subst_in (prf_eq_symm prf_axiomsCodeT_eq) (prf_In_listFormCodeM_prf a axioms h)

/-- Pertenencia del código de un axioma a `axiomsCodeT` en `Prf` (vía `prf_inAxC`
    + puente `formCodeM_eq`). Reusado en el caso `thy`. -/
private theorem prf_inAxiomsCodeT {f : Formula} (hmem : f ∈ axioms) :
    Prf (In (formCode f) axiomsCodeT) := by
  have h0 : Prf (In (formCodeM f) axiomsCodeT) := prf_inAxC f hmem
  rwa [formCodeM_eq] at h0

/-! ### chainOk-tracking en `Prf` (validez de la cadena) -/

theorem prf_chainOk_track (rs : List Rule) : ∀ (acc L : List Formula), checkAux rs acc = some L →
    Prf (chainOk (listFormCode acc) (proofCode' rs acc)) := by
  induction rs with
  | nil =>
      intro acc L _
      simpa [proofCode'] using prf_chainOk_nil (listFormCode acc)
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
          refine prf_iff_mpr (prf_chainOk_cons (listFormCode acc) (lineCode' acc f r)
            (proofCode' rs (acc ++ [f]))) ?_
          refine prf_and_intro ?lineOk ?rest
          case rest =>
            have hC : Prf
                (concat (listFormCode acc) (cons (carc (lineCode' acc f r)) nil) =eq
                  listFormCode (acc ++ [f])) :=
              prf_eq_trans
                (prf_congr_concat_left (prf_congr_cons_head (prf_carc_cons (formCode f) (lineJustif acc r))))
                (prf_concat_listFormCode_singleton acc f)
            exact prf_chainOk_subst1 (prf_eq_symm hC) ihf
          case lineOk =>
            cases r with
            | p1 A B =>
                have hf : f = (A ⇒ (B ⇒ A)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_p1 _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_p1 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | p2 A B C =>
                have hf : f = ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_p2 _ _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_p2 _ _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | c1 A B =>
                have hf : f = (A ⇒ (B ⇒ (A ∧ B))) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_c1 _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_c1 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | c2 A B =>
                have hf : f = ((A ∧ B) ⇒ A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_c2 _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_c2 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | c3 A B =>
                have hf : f = ((A ∧ B) ⇒ B) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_c3 _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_c3 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | j1 A B =>
                have hf : f = (A ⇒ (A ∨ B)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_j1 _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_j1 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | j2 A B =>
                have hf : f = (B ⇒ (A ∨ B)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_j2 _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_j2 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | j3 A B C =>
                have hf : f = ((A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C))) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_j3 _ _ _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_j3 _ _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | efq A =>
                have hf : f = (⊥ ⇒ A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_efq _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_efq _ _)) (prf_allIn_nil (listFormCode acc)))
            | q1 A t =>
                have hf : f = ((Formula.forall A) ⇒ substFormula 0 t A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro
                  (prf_iff_mpr (prf_lineWF_q1 _ _ _ (prf_hasWitF_fc A) (prf_hasWit_tc t)) (prf_eq_symm (prf_q1_concl_code A t)))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_q1 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | q2 A t =>
                have hf : f = (substFormula 0 t A ⇒ Formula.ex A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro
                  (prf_iff_mpr (prf_lineWF_q2 _ _ _ (prf_hasWitF_fc A) (prf_hasWit_tc t)) (prf_eq_symm (prf_q2_concl_code A t)))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_q2 _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | q3 A B =>
                have hf : f = ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ ((Formula.ex A) ⇒ B)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine prf_and_intro (prf_iff_mpr (prf_lineWF_q3 _ _ _ (prf_hasWitF_fc B)) ?_)
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_q3 _ _ _)) (prf_allIn_nil (listFormCode acc)))
                exact prf_eq_symm
                  (prf_congr_bin1 (prf_congr_un (prf_congr_bin2 (prf_liftFormula_arith 0 B))))
            | eqrefl t =>
                have hf : f = (t ≐ t) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_eqrefl _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_eqrefl _ _)) (prf_allIn_nil (listFormCode acc)))
            | leibniz A t₁ t₂ =>
                have hf : f = ((t₁ ≐ t₂) ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A)) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro
                  (prf_iff_mpr (prf_lineWF_leibniz _ _ _ _ (prf_hasWitF_fc A) (prf_hasWit_tc t₁) (prf_hasWit_tc t₂)) (prf_eq_symm (prf_leibniz_concl_code A t₁ t₂)))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_leibniz _ _ _ _)) (prf_allIn_nil (listFormCode acc)))
            | p3 A =>
                have hf : f = (((A ⇒ ⊥) ⇒ ⊥) ⇒ A) := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                exact prf_and_intro (prf_iff_mpr (prf_lineWF_p3 _ _) (prf_refl _))
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_p3 _ _)) (prf_allIn_nil (listFormCode acc)))
            | ind A =>
                have hf : f = Full.inductionFormula A := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine prf_and_intro (prf_iff_mpr (prf_lineWF_ind _ _ (prf_hasWitF_fc A)) ?_)
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_ind _ _)) (prf_allIn_nil (listFormCode acc)))
                rw [termCodeM_eq zero, termCodeM_eq (succ (Term.var 0))]
                exact prf_eq_symm (prf_ind_concl_code A)
            | qconf P C =>
                have hf : f = ROBINSON_PlusPlus.Meta.Hilbert.confinementFormula P C := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine prf_and_intro (prf_iff_mpr (prf_lineWF_qconf _ _ _ (prf_hasWitF_fc P)) ?_)
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_qconf _ _ _)) (prf_allIn_nil (listFormCode acc)))
                exact prf_eq_symm
                  (prf_congr_bin1 (prf_congr_un (prf_congr_bin1 (prf_liftFormula_arith 0 P))))
            | listInd A =>
                have hf : f = ROBINSON_PlusPlus.Meta.Hilbert.listInductionFormula A := by
                  simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
                subst hf; simp only [lineCode', lineJustif]
                refine prf_and_intro (prf_iff_mpr (prf_lineWF_listInd _ _ (prf_hasWitF_fc A)) ?_)
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_listInd _ _)) (prf_allIn_nil (listFormCode acc)))
                rw [termCodeM_eq nil, termCodeM_eq (cons (Term.var 1) (Term.var 0))]
                exact prf_eq_symm (prf_listInd_concl_code A)
            | thy k =>
                have hmem : f ∈ axioms :=
                  List.mem_of_getElem? (by simpa only [stepConcl] using hsc)
                simp only [lineCode', lineJustif]
                refine prf_and_intro (prf_iff_mpr (prf_lineWF_thy _) ?_)
                  (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_thy _)) (prf_allIn_nil (listFormCode acc)))
                exact prf_inAxiomsCodeT hmem
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
                refine prf_and_intro (prf_lineWF_mp _ _) ?_
                refine prf_allIn_subst2 (prf_eq_symm (prf_premsOf_mp (formCode f) (formCode fj))) ?_
                refine prf_iff_mpr (prf_allIn_cons (listFormCode acc) (implc (formCode fj) (formCode f))
                  (cons (formCode fj) nil)) ?_
                refine prf_and_intro ?_ ?_
                · have hin : Prf (In (formCode fi) (listFormCode acc)) :=
                    prf_In_listFormCode (List.mem_of_getElem? hi)
                  rw [hfi_eq] at hin; exact hin
                · refine prf_iff_mpr (prf_allIn_cons (listFormCode acc) (formCode fj) nil) ?_
                  exact prf_and_intro (prf_In_listFormCode (List.mem_of_getElem? hj))
                    (prf_allIn_nil (listFormCode acc))
            | gen i =>
                rcases hi : acc[i]? with _ | fi
                · simp [stepConcl, hi] at hsc
                have hf : f = Formula.forall fi := by
                  simp only [stepConcl, hi, Option.map_some, Option.some.injEq] at hsc
                  exact hsc.symm
                subst hf
                simp only [lineCode', lineJustif, hi, Option.getD_some]
                refine prf_and_intro
                  (prf_iff_mpr (prf_lineWF_gen (formCode (Formula.forall fi)) (formCode fi))
                    (prf_refl _)) ?_
                refine prf_allIn_subst2 (prf_eq_symm (prf_premsOf_gen (formCode (Formula.forall fi))
                  (formCode fi))) ?_
                refine prf_iff_mpr (prf_allIn_cons (listFormCode acc) (formCode fi) nil) ?_
                exact prf_and_intro (prf_In_listFormCode (List.mem_of_getElem? hi))
                  (prf_allIn_nil (listFormCode acc))

/-! ### Empaquetado `provCodeC'` (intro) y representabilidad positiva en `Prf` -/

/-- **Introducción** de `provCodeC' φ` en `Prf`. -/
theorem provCodeC'_intro_prf (φ : Formula) (p : Term)
    (h1 : Prf (chainOk nil p)) (h2 : Prf (In (formCode φ) (runFn nil p))) :
    Prf (provCodeC' φ) := by
  have hbody : Prf (land (chainOk nil p) (In (formCode φ) (runFn nil p))) :=
    prf_and_intro h1 h2
  have hex : Prf (Formula.ex (land (chainOk nil (.var 0))
      (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0))))) :=
    prf_ex_intro
      (A := land (chainOk nil (.var 0)) (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0)))) p
      (by simpa [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
            FOL.substTerm_liftTerm] using hbody)
  simpa [provCodeC', provFormulaC', substFormula, substTerm, substTerms, land, chainOk, In, runFn,
    nil, zero, FOL.substTerm_liftTerm] using hex

/-- **`repr_pos'_prf` (D1 real, finitario)**: toda demostración de Hilbert `Prf φ`
    se internaliza como `Prf (provCodeC' φ)`. Necesitación internalizada al nivel del
    cálculo finitario `Prf` (cimiento de la cadena HBL hacia Gödel II real). -/
theorem repr_pos'_prf {φ : Formula} (h : Prf φ) : Prf (provCodeC' φ) := by
  obtain ⟨rs, L, hchk, hmem⟩ := prf_iff_derivation.mp h
  have hchk' : checkAux rs [] = some L := by simpa [checkProof] using hchk
  exact provCodeC'_intro_prf φ (proofCode' rs [])
    (prf_chainOk_track rs [] L hchk') (prf_In_runFn_of_mem hchk' hmem)

end ROBINSON_PlusPlus.Meta.Representability2Prf

export ROBINSON_PlusPlus.Meta.Representability2Prf (
  prf_concat_listFormCode
  prf_concat_listFormCode_singleton
  prf_runFn_track
  prf_In_runFn_of_mem
  prf_inAxC
  prf_chainOk_track
  provCodeC'_intro_prf
  repr_pos'_prf
)

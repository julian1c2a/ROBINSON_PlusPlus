/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Meta.HilbertSeq
import ROBINSON_PlusPlus.Meta.Induction
import ROBINSON_PlusPlus.Minimal.Theorems.Block6

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.StepArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Induction

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Representability

/-!
## META — NIVEL D (real): representabilidad positiva  (Fase 2.5)

Cierra la dirección **positiva** del puente de demostrabilidad object:

> `repr_pos : Prf φ → axioms ⊢ provCodeC φ`

es decir, de una demostración finitaria de Hilbert `Prf φ` se construye, **dentro
de la teoría**, una prueba de la fórmula Σ₁ `provCodeC φ = ∃p, In ⌜φ⌝
(validProofFn nil p)`. Es lo único que **D1 (necesitación, Fase 3)** necesita.

**Encoder object propio.** El verificador `validProofFn` espera que las líneas
`mp`/`gen` transporten los **códigos de las fórmulas** premisa/conclusión (las
comprueba por pertenencia con `In`), no índices de línea. El `ruleCode` de la
Fase 1c (para `Dem`) transporta índices, por lo que aquí se define un encoder
**a medida** `proofCode`/`lineCode` alineado con `validProofFn`: recorre la
secuencia acumulando conclusiones y emite cada línea con los códigos resueltos.
Como `provFormulaC` cuantifica sobre **cualquier** código de prueba, basta
exhibir éste.

La **inducción de seguimiento** `vpf_run` demuestra que `validProofFn` calcula,
sobre `proofCode rs acc`, el código object de la lista de conclusiones de
`checkAux rs acc`; cada paso usa el step-lemma `vpf_*` correspondiente (los
esquemas de sustitución Q1/Q2/Q3/Leibniz, vía los `*_concl_code` de StepArith).
-/

/-! ### Código object de una lista de fórmulas -/

/-- Código object de una lista de fórmulas (lista `cons` de sus `formCode`). -/
def listFormCode : List Formula → Term
  | [] => nil
  | f :: fs => cons (formCode f) (listFormCode fs)

/-! ### Congruencias auxiliares (patrón `Derives.subst`) -/

/-- Congruencia de `validProofFn` en el 1er argumento (acumulador). -/
theorem congr_vpf_checked {c₁ c₂ rest : Term} (h : axioms ⊢ (c₁ =eq c₂)) :
    axioms ⊢ (validProofFn c₁ rest =eq validProofFn c₂ rest) := by
  let f : Formula :=
    Formula.eq (validProofFn (liftTerm 0 c₁) (liftTerm 0 rest)) (validProofFn (.var 0) (liftTerm 0 rest))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (validProofFn c₁ rest) (validProofFn s rest) := by
    intro s
    simp only [f, substFormula, validProofFn, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ Derives.subst axioms c₁ c₂ f h ((hS c₁) ▸ Derives.refl axioms (validProofFn c₁ rest))

/-- Congruencia de `concat` en el 2º argumento. -/
theorem congr_concat2 {T a b : Term} (h : axioms ⊢ (a =eq b)) :
    axioms ⊢ (concat T a =eq concat T b) := by
  let f : Formula := Formula.eq (concat (liftTerm 0 T) (liftTerm 0 a)) (concat (liftTerm 0 T) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (concat T a) (concat T s) := by
    intro s
    simp only [f, substFormula, concat, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst axioms a b f h ((hS a) ▸ Derives.refl axioms (concat T a))

/-! ### Cómputo de `concat` sobre códigos de listas -/

/-- `concat nil X = X` (ax_C1). -/
theorem concat_nil_eq (X : Term) : axioms ⊢ (concat nil X =eq X) := by
  have hh := spec (ax (show ax_C1_concat_nil ∈ axioms by simp [axioms])) X
  simp [ax_C1_concat_nil, substFormula, substTerm, substTerms, concat, nil, zero] at hh
  exact hh

/-- `concat (cons h t) X = cons h (concat t X)` (ax_C2). -/
theorem concat_cons_eq (h t X : Term) : axioms ⊢ (concat (cons h t) X =eq cons h (concat t X)) := by
  have hh := spec (spec (spec (ax (show ax_C2_concat_cons ∈ axioms by simp [axioms])) h) t) X
  simp [ax_C2_concat_cons, substFormula, substTerm, substTerms, concat, cons, nil, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- `concat ⌜a⌝ ⌜b⌝ = ⌜a ++ b⌝` (sobre códigos de listas de fórmulas). -/
theorem concat_listFormCode : ∀ (a b : List Formula),
    axioms ⊢ (concat (listFormCode a) (listFormCode b) =eq listFormCode (a ++ b))
  | [], b => by simpa [listFormCode] using concat_nil_eq (listFormCode b)
  | f :: fs, b => by
      simp only [listFormCode, List.cons_append]
      exact FOL.derive_eq_trans (concat_cons_eq (formCode f) (listFormCode fs) (listFormCode b))
        (congr_cons_tail (concat_listFormCode fs b))

/-! ### Pertenencia object en una lista codificada -/

/-- `In x (cons x t)` (ax_L2 + or-intro-left). -/
theorem in_cons_head (x t : Term) : axioms ⊢ In x (cons x t) := by
  have h_axL2 := ax (show ax_L2_in_cons ∈ axioms by simp [axioms])
  have hiff := by
    have hh := spec (spec (spec h_axL2 x) x) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  exact iff_mpr hiff (FOL.MetaRules.or_intro_left (eq_refl x))

/-- `In x t → In x (cons h t)` (ax_L2 + or-intro-right). -/
theorem in_cons_tail (hd : Term) {x t : Term} (hx : axioms ⊢ In x t) :
    axioms ⊢ In x (cons hd t) := by
  have h_axL2 := ax (show ax_L2_in_cons ∈ axioms by simp [axioms])
  have hiff := by
    have hh := spec (spec (spec h_axL2 x) hd) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  exact iff_mpr hiff (FOL.MetaRules.or_intro_right hx)

/-- Reflexión de pertenencia: `g ∈ l ⟹ axioms ⊢ In ⌜g⌝ ⌜l⌝`. -/
theorem In_listFormCode {g : Formula} : ∀ {l : List Formula},
    List.Mem g l → axioms ⊢ In (formCode g) (listFormCode l)
  | [], hmem => by cases hmem
  | x :: xs, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst heq; exact in_cons_head (formCode g) (listFormCode xs)
      · exact in_cons_tail (formCode x) (In_listFormCode htail)

/-! ### Puente `formCodeM = formCode`

La codificación local de `Minimal` (`formCodeM`, con `numeralM`) coincide con la
de `Meta/Provability` (`formCode`, con `Godel.numeral`); vía `numeralM_eq`. Permite
relacionar `axiomsCodeT` (anclado a `listFormCodeM coreAxioms`) con la pertenencia
`In_listFormCode` (que usa `formCode`). -/

theorem charsCodeM_eq : ∀ cs : List Char, charsCodeM cs = charsCode cs
  | []      => rfl
  | _ :: cs => by simp only [charsCodeM, charsCode, numeralM_eq, charsCodeM_eq cs]

theorem strCodeM_eq (s : String) : strCodeM s = strCode s := charsCodeM_eq s.toList

mutual
theorem termCodeM_eq : ∀ t : Term, termCodeM t = termCode t
  | .var _    => by simp only [termCodeM, termCode, numeralM_eq]
  | .func s ts => by simp only [termCodeM, termCode, numeralM_eq, strCodeM_eq, termsCodeM_eq ts]
theorem termsCodeM_eq : ∀ ts : List Term, termsCodeM ts = termsCode ts
  | []      => rfl
  | t :: ts => by simp only [termsCodeM, termsCode, termCodeM_eq t, termsCodeM_eq ts]
end

theorem formCodeM_eq : ∀ φ : Formula, formCodeM φ = formCode φ
  | .bottom    => by simp only [formCodeM, formCode, numeralM_eq]
  | .atom _ _  => by simp only [formCodeM, formCode, numeralM_eq, strCodeM_eq, termsCodeM_eq]
  | .eq _ _    => by simp only [formCodeM, formCode, numeralM_eq, termCodeM_eq]
  | .impl a b  => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a, formCodeM_eq b]
  | .forall a  => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a]
  | .and a b   => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a, formCodeM_eq b]
  | .or a b    => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a, formCodeM_eq b]
  | .ex a      => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a]

theorem listFormCodeM_eq : ∀ L : List Formula, listFormCodeM L = listFormCode L
  | []      => rfl
  | f :: fs => by simp only [listFormCodeM, listFormCode, formCodeM_eq f, listFormCodeM_eq fs]

/-! ### Encoder object de demostraciones (a medida de `validProofFn`) -/

/-- Código object de una línea, dada la conclusión `f` ya computada y el
    acumulador `acc`. Las reglas-esquema usan sus parámetros; `mp`/`gen`
    transportan los códigos de las fórmulas (no índices); `thy` el código del
    axioma (= `f`). -/
def lineCode (acc : List Formula) (f : Formula) : Rule → Term
  | .p1 A B => cons (numeral 0) (cons (formCode A) (cons (formCode B) nil))
  | .p2 A B C => cons (numeral 1) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .c1 A B => cons (numeral 2) (cons (formCode A) (cons (formCode B) nil))
  | .c2 A B => cons (numeral 3) (cons (formCode A) (cons (formCode B) nil))
  | .c3 A B => cons (numeral 4) (cons (formCode A) (cons (formCode B) nil))
  | .j1 A B => cons (numeral 5) (cons (formCode A) (cons (formCode B) nil))
  | .j2 A B => cons (numeral 6) (cons (formCode A) (cons (formCode B) nil))
  | .j3 A B C => cons (numeral 7) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .efq A => cons (numeral 8) (cons (formCode A) nil)
  | .q1 A t => cons (numeral 9) (cons (formCode A) (cons (termCode t) nil))
  | .q2 A t => cons (numeral 10) (cons (formCode A) (cons (termCode t) nil))
  | .q3 A B => cons (numeral 11) (cons (formCode A) (cons (formCode B) nil))
  | .eqrefl t => cons (numeral 12) (cons (termCode t) nil)
  | .leibniz A t₁ t₂ =>
      cons (numeral 13) (cons (formCode A) (cons (termCode t₁) (cons (termCode t₂) nil)))
  | .p3 A => cons (numeral 14) (cons (formCode A) nil)
  | .ind A => cons (numeral 18) (cons (formCode A) nil)
  | .qconf P C => cons (numeral 19) (cons (formCode P) (cons (formCode C) nil))
  | .thy _ => cons (numeral 15) (cons (formCode f) nil)
  | .mp _ j => cons (numeral 16) (cons (formCode f) (cons (formCode ((acc[j]?).getD Formula.bottom)) nil))
  | .gen i => cons (numeral 17) (cons (formCode ((acc[i]?).getD Formula.bottom)) nil)

/-- Código object de una demostración-secuencia, alineado con `validProofFn`. -/
def proofCode : List Rule → List Formula → Term
  | [], _ => nil
  | r :: rs, acc =>
      match stepConcl acc r with
      | some f => cons (lineCode acc f r) (proofCode rs (acc ++ [f]))
      | none => nil

/-! ### Inducción de seguimiento -/

/-- **Seguimiento del verificador**: sobre `proofCode rs acc`, `validProofFn`
    calcula el código de la lista de conclusiones que `checkAux rs acc` produce. -/
theorem vpf_run (rs : List Rule) : ∀ (acc L : List Formula), checkAux rs acc = some L →
    axioms ⊢ (validProofFn (listFormCode acc) (proofCode rs acc) =eq listFormCode L) := by
  induction rs with
  | nil =>
      intro acc L h
      simp only [checkAux, Option.some.injEq] at h
      subst h
      simpa [proofCode] using vpf_nil (listFormCode acc)
  | cons r rs ih =>
      intro acc L h
      cases hsc : stepConcl acc r with
      | none => simp [checkAux, hsc] at h
      | some f =>
          have hcheck : checkAux rs (acc ++ [f]) = some L := by
            have h2 := h; simp only [checkAux, hsc] at h2; exact h2
          have ihf := ih (acc ++ [f]) L hcheck
          have hmerge : axioms ⊢
              (validProofFn (concat (listFormCode acc) (cons (formCode f) nil)) (proofCode rs (acc ++ [f]))
                =eq validProofFn (listFormCode (acc ++ [f])) (proofCode rs (acc ++ [f]))) :=
            congr_vpf_checked (by simpa [listFormCode] using concat_listFormCode acc [f])
          rw [show proofCode (r :: rs) acc = cons (lineCode acc f r) (proofCode rs (acc ++ [f]))
                from by simp [proofCode, hsc]]
          refine FOL.derive_eq_trans ?_ (FOL.derive_eq_trans hmerge ihf)
          -- queda el paso `validProofFn acc (cons (lineCode …) rest) =eq validProofFn (concat acc [⌜f⌝]) rest`
          clear hmerge ihf hcheck h
          cases r with
          | p1 A B =>
              have hf : f = (A ⇒ (B ⇒ A)) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_p1 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))
          | p2 A B C =>
              have hf : f = ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_p2 (listFormCode acc) (formCode A) (formCode B) (formCode C) (proofCode rs (acc ++ [_]))
          | c1 A B =>
              have hf : f = (A ⇒ (B ⇒ (A ∧ B))) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_c1 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))
          | c2 A B =>
              have hf : f = ((A ∧ B) ⇒ A) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_c2 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))
          | c3 A B =>
              have hf : f = ((A ∧ B) ⇒ B) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_c3 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))
          | j1 A B =>
              have hf : f = (A ⇒ (A ∨ B)) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_j1 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))
          | j2 A B =>
              have hf : f = (B ⇒ (A ∨ B)) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_j2 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))
          | j3 A B C =>
              have hf : f = ((A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C))) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_j3 (listFormCode acc) (formCode A) (formCode B) (formCode C) (proofCode rs (acc ++ [_]))
          | efq A =>
              have hf : f = (⊥ ⇒ A) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_efq (listFormCode acc) (formCode A) (proofCode rs (acc ++ [_]))
          | q1 A t =>
              have hf : f = ((Formula.forall A) ⇒ substFormula 0 t A) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              refine FOL.derive_eq_trans
                (vpf_q1 (listFormCode acc) (formCode A) (termCode t) (proofCode rs (acc ++ [_]))) ?_
              exact congr_vpf_checked (congr_concat2 (congr_cons_head (q1_concl_code A t)))
          | q2 A t =>
              have hf : f = (substFormula 0 t A ⇒ Formula.ex A) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              refine FOL.derive_eq_trans
                (vpf_q2 (listFormCode acc) (formCode A) (termCode t) (proofCode rs (acc ++ [_]))) ?_
              exact congr_vpf_checked (congr_concat2 (congr_cons_head (q2_concl_code A t)))
          | q3 A B =>
              have hf : f = ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ ((Formula.ex A) ⇒ B)) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              refine FOL.derive_eq_trans
                (vpf_q3 (listFormCode acc) (formCode A) (formCode B) (proofCode rs (acc ++ [_]))) ?_
              exact congr_vpf_checked (congr_concat2 (congr_cons_head
                (congr_bin1 (congr_un (congr_bin2 (liftFormula_arith 0 B))))))
          | eqrefl t =>
              have hf : f = (t ≐ t) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_eqrefl (listFormCode acc) (termCode t) (proofCode rs (acc ++ [_]))
          | leibniz A t₁ t₂ =>
              have hf : f = ((t₁ ≐ t₂) ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A)) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              refine FOL.derive_eq_trans
                (vpf_leibniz (listFormCode acc) (formCode A) (termCode t₁) (termCode t₂)
                  (proofCode rs (acc ++ [_]))) ?_
              exact congr_vpf_checked (congr_concat2 (congr_cons_head (leibniz_concl_code A t₁ t₂)))
          | p3 A =>
              have hf : f = (((A ⇒ ⊥) ⇒ ⊥) ⇒ A) := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              exact vpf_p3 (listFormCode acc) (formCode A) (proofCode rs (acc ++ [_]))
          | ind A =>
              have hf : f = Full.inductionFormula A := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              refine FOL.derive_eq_trans
                (vpf_ind (listFormCode acc) (formCode A) (proofCode rs (acc ++ [_]))) ?_
              refine congr_vpf_checked (congr_concat2 (congr_cons_head ?_))
              rw [termCodeM_eq zero, termCodeM_eq (succ (Term.var 0))]
              exact ind_concl_code A
          | qconf P C =>
              have hf : f = ROBINSON_PlusPlus.Meta.Hilbert.confinementFormula P C := by
                simp only [stepConcl, Option.some.injEq] at hsc; exact hsc.symm
              subst hf; simp only [lineCode]
              refine FOL.derive_eq_trans
                (vpf_qconf (listFormCode acc) (formCode P) (formCode C) (proofCode rs (acc ++ [_]))) ?_
              exact congr_vpf_checked (congr_concat2 (congr_cons_head
                (congr_bin1 (congr_un (congr_bin1 (liftFormula_arith 0 P))))))
          | thy k =>
              have hmem : f ∈ axioms := List.mem_of_getElem? (by simpa only [stepConcl] using hsc)
              simp only [lineCode]
              refine vpf_thy (listFormCode acc) (formCode f) (proofCode rs (acc ++ [f])) ?_
              -- objetivo: `axioms ⊢ In ⌜f⌝ axiomsCodeT`, vía el meta-axioma `ax_inAxC`
              have h0 : axioms ⊢ In (formCodeM f) axiomsCodeT := ax_inAxC f hmem
              rwa [formCodeM_eq] at h0
          | mp i j =>
              -- f = conclusión del MP; fi = acc[i] = (fj ⇒ f), fj = acc[j]
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
              simp only [lineCode, hj, Option.getD_some]
              refine vpf_mp (listFormCode acc) (formCode f) (formCode fj)
                (proofCode rs (acc ++ [f])) ?_ ?_
              · have hin : axioms ⊢ In (formCode fi) (listFormCode acc) :=
                  In_listFormCode (List.mem_of_getElem? hi)
                rw [hfi_eq] at hin; exact hin
              · exact In_listFormCode (List.mem_of_getElem? hj)
          | gen i =>
              rcases hi : acc[i]? with _ | fi
              · simp [stepConcl, hi] at hsc
              have hf : f = Formula.forall fi := by
                simp only [stepConcl, hi, Option.map_some, Option.some.injEq] at hsc
                exact hsc.symm
              subst hf
              simp only [lineCode, hi, Option.getD_some]
              refine vpf_gen (listFormCode acc) (formCode fi) (proofCode rs (acc ++ [Formula.forall fi])) ?_
              exact In_listFormCode (List.mem_of_getElem? hi)

/-! ### Representabilidad positiva -/

/-- **Representabilidad positiva (Fase 2.5)**: toda demostración de Hilbert `Prf φ`
    se internaliza como una prueba de la fórmula Σ₁ `provCodeC φ`. Es la dirección
    que necesita **D1** (necesitación). La dirección negativa (reflexión) se
    difiere a 2.6. -/
theorem repr_pos {φ : Formula} (h : Prf φ) : axioms ⊢ provCodeC φ := by
  obtain ⟨rs, L, hchk, hmem⟩ := prf_iff_derivation.mp h
  have hrun : axioms ⊢ (validProofFn nil (proofCode rs []) =eq listFormCode L) := by
    have hr := vpf_run rs [] L (by simpa [checkProof] using hchk)
    simpa [listFormCode] using hr
  have hin : axioms ⊢ In (formCode φ) (listFormCode L) := In_listFormCode hmem
  have hin2 : axioms ⊢ In (formCode φ) (validProofFn nil (proofCode rs [])) := by
    have ht := Derives.subst axioms (listFormCode L) (validProofFn nil (proofCode rs []))
      (In (liftTerm 0 (formCode φ)) (.var 0)) (FOL.derive_eq_symm hrun)
      (by simpa [substFormula, substTerm, substTerms, In, FOL.substTerm_liftTerm] using hin)
    simpa [substFormula, substTerm, substTerms, In, validProofFn, nil, FOL.substTerm_liftTerm] using ht
  have hex := Derives.intro_ex axioms (In (liftTerm 0 (formCode φ)) (validProofFn nil (.var 0)))
    (proofCode rs [])
    (by simpa [substFormula, substTerm, substTerms, In, validProofFn, nil, FOL.substTerm_liftTerm] using hin2)
  simpa [provCodeC, provFormulaC, substFormula, substTerm, substTerms, In, validProofFn, nil,
    FOL.substTerm_liftTerm] using hex

end ROBINSON_PlusPlus.Meta.Representability

export ROBINSON_PlusPlus.Meta.Representability (
  listFormCode
  proofCode
  vpf_run
  repr_pos
)

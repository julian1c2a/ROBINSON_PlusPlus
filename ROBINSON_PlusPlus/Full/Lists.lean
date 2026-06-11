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

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — Listas: ax_C3 (concat_assoc) y ax_L3 (in_concat) derivados

En `Minimal/`, las listas son Terms codificados vía Cantor (`cons h t := pair h
(succ t)`, `nil := zero`). `ax_induction` (Peano) inducta sobre Terms tratados
como naturales, pero los casos cons-shape NO son alcanzables directamente por
inducción Peano: un `succ k` cualquiera no es necesariamente `cons h t`.

Para derivar `ax_C3` y `ax_L3` añadimos un **meta-axioma** de inducción
estructural sobre listas, parametrizado por una función Lean `φ : Term →
Formula`. Estilo análogo a las meta-reglas FOL (`imp_intro`, `gen`, `or_elim`,
`ex_elim`) — no es `axiom` object-level con `Formula → Formula`, sino una
regla meta que toma derivaciones Lean.

**Nota conceptual**: el meta-axioma concluye `∀ L : Term, Γ ⊢ φ L` (sobre todos
los Terms, no solo listas). Implícitamente afirma que la inducción base
nil + paso cons cubre toda forma alcanzable de `concat`/`In` sobre cualquier
Term — una elección de Full análoga a la elección de Peano-induction sobre
todos los Terms para ax_induction. (Con 3 binders esto generalizaría a
inducción sobre ordinales / W-types arbitrarios.)
-/

/-! ### Meta-axioma: ax_list_induction -/

/-- **Meta-axioma de inducción estructural sobre listas**.

    Estilo `imp_intro`/`gen`: parametrizado por una función Lean
    `φ : Term → Formula`, toma derivaciones del caso base (`φ nil`) y del paso
    (`∀h t, φ t → φ (cons h t)`), y produce `∀L, φ L`.

    Conservativo respecto a `Minimal`: en `Minimal`, ax_C3 y ax_L3 son axiomas;
    en `Full` con este meta-axioma se derivan como teoremas. -/
axiom ax_list_induction {Γ : List Formula} (φ : Term → Formula)
  (base : Γ ⊢ φ nil)
  (step : ∀ h t : Term, Γ ⊢ φ t → Γ ⊢ φ (cons h t)) :
  ∀ L : Term, Γ ⊢ φ L

/-! ### Helpers de congruencia para cons, concat, In -/

/-- `cons` respeta la igualdad en su segundo argumento. -/
theorem eq_congr_cons_right_full (x : Term) {a b : Term}
    (h : axioms ⊢ (a ≐ b)) : axioms ⊢ (cons x a ≐ cons x b) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 x) (liftTerm 0 a)) (cons (liftTerm 0 x) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons x a) (cons x s) := by
    intro s
    simp only [f, substFormula, cons, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst axioms a b f h ((hS a) ▸ Derives.refl axioms (cons x a))

/-- `concat` respeta la igualdad en su segundo argumento. -/
theorem eq_congr_concat_left {u t₁ t₂ : Term} (h : axioms ⊢ (t₁ ≐ t₂)) :
    axioms ⊢ (concat u t₁ ≐ concat u t₂) := by
  let f : Formula := Formula.eq (concat (liftTerm 0 u) (liftTerm 0 t₁)) (concat (liftTerm 0 u) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (concat u t₁) (concat u s) := by
    intro s
    simp only [f, substFormula, concat, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst axioms t₁ t₂ f h ((hS t₁) ▸ Derives.refl axioms (concat u t₁))

/-- `concat` respeta la igualdad en su primer argumento. -/
theorem eq_congr_concat_right {t₁ t₂ : Term} (u : Term) (h : axioms ⊢ (t₁ ≐ t₂)) :
    axioms ⊢ (concat t₁ u ≐ concat t₂ u) := by
  let f : Formula := Formula.eq (concat (liftTerm 0 t₁) (liftTerm 0 u)) (concat (.var 0) (liftTerm 0 u))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (concat t₁ u) (concat s u) := by
    intro s
    simp only [f, substFormula, concat, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst axioms t₁ t₂ f h ((hS t₁) ▸ Derives.refl axioms (concat t₁ u))

/-- Substitución bajo `In`: de `t₁ ≐ t₂` y `In x t₁` deriva `In x t₂`. -/
theorem eq_subst_in {x t₁ t₂ : Term}
    (h_eq : axioms ⊢ (t₁ ≐ t₂)) (h_in : axioms ⊢ In x t₁) :
    axioms ⊢ In x t₂ := by
  let f : Formula := In (liftTerm 0 x) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = In x s := by
    intro s
    simp only [f, substFormula, In, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst axioms t₁ t₂ f h_eq ((hS t₁) ▸ h_in)

/-- Helper: construcción de un `iff` a partir de las dos implicaciones meta. -/
private theorem iff_intro {a b : Formula}
    (h1 : axioms ⊢ a → axioms ⊢ b) (h2 : axioms ⊢ b → axioms ⊢ a) :
    axioms ⊢ iff a b :=
  Minimal.Axioms.and_intro
    (Minimal.Axioms.imp_intro h1)
    (Minimal.Axioms.imp_intro h2)

/-! ### ax_C3 derivado: asociatividad de concat -/

/-- `concat_assoc_pointwise L M N : axioms ⊢ ((L##M)##N ≐ L##(M##N))`.

    Por inducción estructural sobre L (con M, N como parámetros Lean). -/
theorem concat_assoc_pointwise (L M N : Term) :
    axioms ⊢ (concat (concat L M) N ≐ concat L (concat M N)) := by
  have base : axioms ⊢ (concat (concat nil M) N ≐ concat nil (concat M N)) := by
    -- ax_C1: nil ## L = L. So nil ## M = M y nil ## (M##N) = M##N.
    -- LHS: (nil ## M) ## N = M ## N. RHS: nil ## (M ## N) = M ## N. ✓
    have h_C1 := ax (by simp [axioms] : ax_C1_concat_nil ∈ axioms)
    have h_nil_M : axioms ⊢ (concat nil M ≐ M) := by
      have hh := spec h_C1 M
      simp [substFormula, substTerm, substTerms, concat, nil, zero] at hh
      exact hh
    have h_nil_MN : axioms ⊢ (concat nil (concat M N) ≐ concat M N) := by
      have hh := spec h_C1 (concat M N)
      simp [substFormula, substTerm, substTerms, concat, nil, zero] at hh
      exact hh
    have h_lhs : axioms ⊢ (concat (concat nil M) N ≐ concat M N) :=
      eq_congr_concat_right N h_nil_M
    exact FOL.derive_eq_trans h_lhs (eq_symm h_nil_MN)
  have step : ∀ h t : Term,
    axioms ⊢ (concat (concat t M) N ≐ concat t (concat M N)) →
    axioms ⊢ (concat (concat (cons h t) M) N ≐ concat (cons h t) (concat M N)) := by
    intro h t IH
    -- ax_C2: ∀h t L, concat (cons h t) L = cons h (concat t L)
    have h_C2 := ax (by simp [axioms] : ax_C2_concat_cons ∈ axioms)
    -- ax_C2 inst en (h, t, M): (cons h t) ## M = cons h (t ## M)
    have h_cht_M : axioms ⊢ (concat (cons h t) M ≐ cons h (concat t M)) := by
      have hh := spec (spec (spec h_C2 h) t) M
      simp [substFormula, substTerm, substTerms, concat, cons,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    -- ax_C2 inst en (h, t, M##N): (cons h t) ## (M##N) = cons h (t ## (M##N))
    have h_cht_MN : axioms ⊢ (concat (cons h t) (concat M N) ≐
                              cons h (concat t (concat M N))) := by
      have hh := spec (spec (spec h_C2 h) t) (concat M N)
      simp [substFormula, substTerm, substTerms, concat, cons,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    -- ax_C2 inst en (h, t##M, N): (cons h (t##M)) ## N = cons h ((t##M) ## N)
    have h_ctM_N : axioms ⊢ (concat (cons h (concat t M)) N ≐
                              cons h (concat (concat t M) N)) := by
      have hh := spec (spec (spec h_C2 h) (concat t M)) N
      simp [substFormula, substTerm, substTerms, concat, cons,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    -- LHS: (cons h t ## M) ## N. Reescribir cons h t ## M con h_cht_M.
    have step1 : axioms ⊢ (concat (concat (cons h t) M) N ≐
                            concat (cons h (concat t M)) N) :=
      eq_congr_concat_right N h_cht_M
    -- step1 + h_ctM_N: LHS = cons h ((t##M) ## N)
    have step2 : axioms ⊢ (concat (concat (cons h t) M) N ≐
                            cons h (concat (concat t M) N)) :=
      FOL.derive_eq_trans step1 h_ctM_N
    -- IH: (t##M)##N = t##(M##N). Congruencia cons:
    have step3 : axioms ⊢ (cons h (concat (concat t M) N) ≐
                            cons h (concat t (concat M N))) :=
      eq_congr_cons_right_full h IH
    -- step2 + step3: LHS = cons h (t##(M##N))
    have step4 : axioms ⊢ (concat (concat (cons h t) M) N ≐
                            cons h (concat t (concat M N))) :=
      FOL.derive_eq_trans step2 step3
    -- RHS = cons h t ## (M##N) = cons h (t##(M##N)) por h_cht_MN
    exact FOL.derive_eq_trans step4 (eq_symm h_cht_MN)
  exact ax_list_induction
    (fun L' => Formula.eq (concat (concat L' M) N) (concat L' (concat M N)))
    base step L

/-- **`ax_C3` como teorema en Full**: `⊢ ax_C3_concat_assoc`. -/
theorem concat_assoc_thm : axioms ⊢ ax_C3_concat_assoc := by
  unfold ax_C3_concat_assoc forall_3
  apply gen; intro L
  apply gen; intro M
  apply gen; intro N
  simp [substFormula, substTerm, substTerms, concat,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact concat_assoc_pointwise L M N

/-! ### ax_L3 derivado: distribución de In sobre concat -/

/-- `in_concat_pointwise x M L : axioms ⊢ (In(x, L##M) ⇔ In(x,L) ∨ In(x,M))`.

    Por inducción estructural sobre L (con x, M como parámetros Lean). -/
theorem in_concat_pointwise (x M L : Term) :
    axioms ⊢ iff (In x (concat L M)) (lor (In x L) (In x M)) := by
  have base : axioms ⊢ iff (In x (concat nil M)) (lor (In x nil) (In x M)) := by
    -- nil ## M = M (ax_C1). In(x, nil) es false (ax_L1).
    -- ⇔: In x M ⇔ (In x nil ∨ In x M).
    have h_C1 := ax (by simp [axioms] : ax_C1_concat_nil ∈ axioms)
    have h_L1 := ax (by simp [axioms] : ax_L1_in_nil ∈ axioms)
    have h_nil_M : axioms ⊢ (concat nil M ≐ M) := by
      have hh := spec h_C1 M
      simp [substFormula, substTerm, substTerms, concat, nil, zero] at hh
      exact hh
    have h_M_nilM : axioms ⊢ (M ≐ concat nil M) := eq_symm h_nil_M
    have h_not_in_nil : axioms ⊢ neg (In x nil) := by
      have hh := spec h_L1 x
      simp [substFormula, substTerm, substTerms, In, nil, zero] at hh
      exact hh
    apply iff_intro
    · -- forward: In(x, nil##M) → In(x,nil) ∨ In(x,M)
      intro h_in_nilM
      have h_in_M : axioms ⊢ In x M := eq_subst_in h_nil_M h_in_nilM
      exact Minimal.Axioms.or_intro_right h_in_M
    · -- backward: (In(x,nil) ∨ In(x,M)) → In(x, nil##M)
      intro h_disj
      apply Minimal.Axioms.or_elim h_disj
      · -- caso In x nil: contradice ax_L1, ⊥ implica todo
        intro h_in_nil
        exact false_elim (mp h_not_in_nil h_in_nil)
      · -- caso In x M: reescribir M = nil##M
        intro h_in_M
        exact eq_subst_in h_M_nilM h_in_M
  have step : ∀ h t : Term,
    axioms ⊢ iff (In x (concat t M)) (lor (In x t) (In x M)) →
    axioms ⊢ iff (In x (concat (cons h t) M)) (lor (In x (cons h t)) (In x M)) := by
    intro h t IH
    have h_C2 := ax (by simp [axioms] : ax_C2_concat_cons ∈ axioms)
    have h_L2 := ax (by simp [axioms] : ax_L2_in_cons ∈ axioms)
    -- ax_C2 inst (h, t, M): cons h t ## M = cons h (t ## M)
    have h_cht_M : axioms ⊢ (concat (cons h t) M ≐ cons h (concat t M)) := by
      have hh := spec (spec (spec h_C2 h) t) M
      simp [substFormula, substTerm, substTerms, concat, cons,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    have h_M_cht : axioms ⊢ (cons h (concat t M) ≐ concat (cons h t) M) :=
      eq_symm h_cht_M
    -- ax_L2 inst (x, h, t##M): In(x, cons h (t##M)) ⇔ (x=h ∨ In(x, t##M))
    have h_L2_tm : axioms ⊢ iff (In x (cons h (concat t M)))
                          (lor (x ≐ h) (In x (concat t M))) := by
      have hh := spec (spec (spec h_L2 x) h) (concat t M)
      simp [substFormula, substTerm, substTerms, In, cons, lor, iff,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    -- ax_L2 inst (x, h, t): In(x, cons h t) ⇔ (x=h ∨ In(x, t))
    have h_L2_t : axioms ⊢ iff (In x (cons h t)) (lor (x ≐ h) (In x t)) := by
      have hh := spec (spec (spec h_L2 x) h) t
      simp [substFormula, substTerm, substTerms, In, cons, lor, iff,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    apply iff_intro
    · -- forward: In(x, cons h t ## M) → In(x, cons h t) ∨ In(x, M)
      intro h_in_chtM
      -- reescribir cons h t ## M = cons h (t##M)
      have h_in_chtM' : axioms ⊢ In x (cons h (concat t M)) :=
        eq_subst_in h_cht_M h_in_chtM
      -- aplicar h_L2_tm forward: x=h ∨ In x (t##M)
      have h_disj1 : axioms ⊢ lor (x ≐ h) (In x (concat t M)) :=
        iff_mp h_L2_tm h_in_chtM'
      apply Minimal.Axioms.or_elim h_disj1
      · -- caso x = h: In(x, cons h t) ← (x=h ∨ In x t) ← or_intro_left
        intro h_xh
        have h_disj_xhVin : axioms ⊢ lor (x ≐ h) (In x t) :=
          Minimal.Axioms.or_intro_left h_xh
        have h_in_cht : axioms ⊢ In x (cons h t) := iff_mpr h_L2_t h_disj_xhVin
        exact Minimal.Axioms.or_intro_left h_in_cht
      · -- caso In x (t##M): aplicar IH forward → In x t ∨ In x M
        intro h_in_tM
        have h_disj2 : axioms ⊢ lor (In x t) (In x M) := iff_mp IH h_in_tM
        apply Minimal.Axioms.or_elim h_disj2
        · -- In x t: → In(x, cons h t) → or_intro_left
          intro h_in_t
          have h_disj_xhVin : axioms ⊢ lor (x ≐ h) (In x t) :=
            Minimal.Axioms.or_intro_right h_in_t
          have h_in_cht : axioms ⊢ In x (cons h t) := iff_mpr h_L2_t h_disj_xhVin
          exact Minimal.Axioms.or_intro_left h_in_cht
        · -- In x M: → or_intro_right
          intro h_in_M
          exact Minimal.Axioms.or_intro_right h_in_M
    · -- backward: In(x, cons h t) ∨ In(x, M) → In(x, cons h t ## M)
      intro h_disj
      apply Minimal.Axioms.or_elim h_disj
      · -- caso In(x, cons h t): aplicar h_L2_t forward → x=h ∨ In x t
        intro h_in_cht
        have h_disj_xhVin : axioms ⊢ lor (x ≐ h) (In x t) := iff_mp h_L2_t h_in_cht
        apply Minimal.Axioms.or_elim h_disj_xhVin
        · -- x = h: → In(x, cons h (t##M)) via h_L2_tm backward + or_intro_left
          intro h_xh
          have h_disj_xhVintm : axioms ⊢ lor (x ≐ h) (In x (concat t M)) :=
            Minimal.Axioms.or_intro_left h_xh
          have h_in_chtm : axioms ⊢ In x (cons h (concat t M)) :=
            iff_mpr h_L2_tm h_disj_xhVintm
          exact eq_subst_in h_M_cht h_in_chtm
        · -- In x t: → In x (t##M) via IH backward (con or_intro_left), luego ax_L2 backward, luego eq_subst
          intro h_in_t
          have h_disj_inttM : axioms ⊢ lor (In x t) (In x M) :=
            Minimal.Axioms.or_intro_left h_in_t
          have h_in_tM : axioms ⊢ In x (concat t M) := iff_mpr IH h_disj_inttM
          have h_disj_xhVintm : axioms ⊢ lor (x ≐ h) (In x (concat t M)) :=
            Minimal.Axioms.or_intro_right h_in_tM
          have h_in_chtm : axioms ⊢ In x (cons h (concat t M)) :=
            iff_mpr h_L2_tm h_disj_xhVintm
          exact eq_subst_in h_M_cht h_in_chtm
      · -- caso In x M: → In x (t##M) via IH backward + or_intro_right, luego ax_L2 backward, luego eq_subst
        intro h_in_M
        have h_disj_inttM : axioms ⊢ lor (In x t) (In x M) :=
          Minimal.Axioms.or_intro_right h_in_M
        have h_in_tM : axioms ⊢ In x (concat t M) := iff_mpr IH h_disj_inttM
        have h_disj_xhVintm : axioms ⊢ lor (x ≐ h) (In x (concat t M)) :=
          Minimal.Axioms.or_intro_right h_in_tM
        have h_in_chtm : axioms ⊢ In x (cons h (concat t M)) :=
          iff_mpr h_L2_tm h_disj_xhVintm
        exact eq_subst_in h_M_cht h_in_chtm
  exact ax_list_induction
    (fun L' => iff (In x (concat L' M)) (lor (In x L') (In x M)))
    base step L

/-- **`ax_L3` como teorema en Full**: `⊢ ax_L3_in_concat`. -/
theorem in_concat_thm : axioms ⊢ ax_L3_in_concat := by
  unfold ax_L3_in_concat forall_3
  apply gen; intro x
  apply gen; intro L
  apply gen; intro M
  simp [substFormula, substTerm, substTerms, In, concat, lor, iff,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact in_concat_pointwise x M L

end ROBINSON_PlusPlus.Full

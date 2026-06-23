/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Full.Lists

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.StepArith
open ROBINSON_PlusPlus.Meta.CheckArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ProofChain

/-!
## META — NIVEL D real: verificador estructural `runFn` (Fase R1)

Hacia **D2/D3 → Gödel II real**. La `validProofFn` (CheckArith) tiene ecuaciones
**condicionales** y opacas: solo reduce sobre códigos de prueba concretos, lo que
basta para la dirección positiva (`repr_pos`, Gödel I real) pero **bloquea** el
razonamiento object-level sobre testigos de prueba ARBITRARIOS que D2/D3 exigen.

`runFn` lo resuelve: cada línea lleva su conclusión incorporada como cabeza
(`line = cons ⌜concl⌝ justif`), así `runFn c (cons line rest) = runFn (c ++ [carc
line]) rest` reduce **uniformemente** vía `carc`, sin depender de la regla. Eso
habilita la **inducción estructural object-level** (`Full.ax_list_induction`).

Esta fase establece los **fundamentos**: ecuaciones de `runFn`, congruencias, y la
**compositividad** `runFn c (p ++ s) =eq runFn (runFn c p) s` (lema angular de
D2/D3). El acumulador `c` se generaliza como **∀ object** dentro de la propiedad
inductiva (los `liftTerm 0` se cancelan con la sustitución del testigo de `gen`).
-/

/-! ### Ecuaciones de `runFn` (re-derivadas de `Minimal.axioms`) -/

/-- `runFn c nil =eq c`. -/
theorem runFn_nil (c : Term) : axioms ⊢ (runFn c nil =eq c) := by
  have hh := spec (ax (show ax_runFn_nil ∈ axioms by simp [axioms])) c
  simp [ax_runFn_nil, substFormula, substTerm, substTerms, runFn, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `runFn c (cons line rest) =eq runFn (concat c [carc line]) rest`. -/
theorem runFn_cons (c line rest : Term) :
    axioms ⊢ (runFn c (cons line rest) =eq runFn (concat c (cons (carc line) nil)) rest) := by
  have hh := spec (spec (spec (ax (show ax_runFn_cons ∈ axioms by simp [axioms])) c) line) rest
  simp [ax_runFn_cons, substFormula, substTerm, substTerms, runFn, concat, carc, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Congruencias de `runFn` (patrón `Derives.subst`) -/

/-- Congruencia de `runFn` en el 1er argumento (acumulador). -/
theorem congr_runFn_1 {c₁ c₂ rest : Term} (h : axioms ⊢ (c₁ =eq c₂)) :
    axioms ⊢ (runFn c₁ rest =eq runFn c₂ rest) := by
  let f : Formula := Formula.eq (runFn (liftTerm 0 c₁) (liftTerm 0 rest)) (runFn (.var 0) (liftTerm 0 rest))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (runFn c₁ rest) (runFn s rest) := by
    intro s
    simp only [f, substFormula, runFn, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ Derives.subst axioms c₁ c₂ f h ((hS c₁) ▸ Derives.refl axioms (runFn c₁ rest))

/-- Congruencia de `runFn` en el 2º argumento (resto). -/
theorem congr_runFn_2 {c a b : Term} (h : axioms ⊢ (a =eq b)) :
    axioms ⊢ (runFn c a =eq runFn c b) := by
  let f : Formula := Formula.eq (runFn (liftTerm 0 c) (liftTerm 0 a)) (runFn (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (runFn c a) (runFn c s) := by
    intro s
    simp only [f, substFormula, runFn, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst axioms a b f h ((hS a) ▸ Derives.refl axioms (runFn c a))

/-! ### `concat` sobre `nil`/`cons` (re-derivado local) -/

/-- `concat nil X =eq X` (ax_C1). -/
theorem concat_nil_eq (X : Term) : axioms ⊢ (concat nil X =eq X) := by
  have hh := spec (ax (show ax_C1_concat_nil ∈ axioms by simp [axioms])) X
  simp [ax_C1_concat_nil, substFormula, substTerm, substTerms, concat, nil, zero] at hh
  exact hh

/-- `concat (cons h t) X =eq cons h (concat t X)` (ax_C2). -/
theorem concat_cons_eq (h t X : Term) :
    axioms ⊢ (concat (cons h t) X =eq cons h (concat t X)) := by
  have hh := spec (spec (spec (ax (show ax_C2_concat_cons ∈ axioms by simp [axioms])) h) t) X
  simp [ax_C2_concat_cons, substFormula, substTerm, substTerms, concat, cons, nil, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Compositividad de `runFn` (inducción estructural, acumulador ∀ object) -/

/-- Propiedad inductiva: `∀c. runFn c (p ++ s) =eq runFn (runFn c p) s`, con el
    acumulador `c` como `∀` object (`.var 0`) para que la HI aplique al contexto
    cambiado en el paso. `p`, `s` van `liftTerm 0` bajo el binder. -/
def compProp (s p : Term) : Formula :=
  Formula.forall
    (Formula.eq (runFn (.var 0) (concat (liftTerm 0 p) (liftTerm 0 s)))
                (runFn (runFn (.var 0) (liftTerm 0 p)) (liftTerm 0 s)))

/-- Instancia puntual de `compProp` en un acumulador concreto `c`. -/
theorem compProp_spec {s p : Term} (h : axioms ⊢ compProp s p) (c : Term) :
    axioms ⊢ (runFn c (concat p s) =eq runFn (runFn c p) s) := by
  have hc := spec h c
  simpa [compProp, substFormula, substTerm, substTerms, runFn, concat,
    FOL.substTerm_liftTerm] using hc

/-- **Compositividad** (núcleo de D2/D3): `runFn c (p ++ s) =eq runFn (runFn c p) s`.
    Por inducción estructural sobre `p` (`Full.ax_list_induction`), con `c`
    generalizado como `∀` object. -/
theorem runFn_concat (c p s : Term) :
    axioms ⊢ (runFn c (concat p s) =eq runFn (runFn c p) s) := by
  have key : axioms ⊢ compProp s p := by
    refine Full.ax_list_induction (fun L => compProp s L) ?base ?step p
    · -- base: ∀c. runFn c (nil ++ s) =eq runFn (runFn c nil) s
      apply gen; intro c
      simp only [compProp, substFormula, substTerm, substTerms, runFn, concat,
        FOL.substTerm_liftTerm]
      -- objetivo: runFn c (concat nil s) =eq runFn (runFn c nil) s
      exact FOL.derive_eq_trans (congr_runFn_2 (concat_nil_eq s))
        (FOL.derive_eq_symm (congr_runFn_1 (runFn_nil c)))
    · -- paso: HI a contexto cambiado
      intro h t IH
      apply gen; intro c
      simp only [compProp, substFormula, substTerm, substTerms, runFn, concat,
        FOL.substTerm_liftTerm]
      -- objetivo: runFn c (concat (cons h t) s) =eq runFn (runFn c (cons h t)) s
      -- LHS: concat (cons h t) s = cons h (concat t s); runFn_cons
      have lhs1 : axioms ⊢
          (runFn c (concat (cons h t) s) =eq runFn c (cons h (concat t s))) :=
        congr_runFn_2 (concat_cons_eq h t s)
      have lhs2 : axioms ⊢
          (runFn c (cons h (concat t s)) =eq
            runFn (concat c (cons (carc h) nil)) (concat t s)) :=
        runFn_cons c h (concat t s)
      -- HI en el contexto cambiado
      have ihc : axioms ⊢
          (runFn (concat c (cons (carc h) nil)) (concat t s) =eq
            runFn (runFn (concat c (cons (carc h) nil)) t) s) :=
        compProp_spec IH (concat c (cons (carc h) nil))
      -- RHS: runFn c (cons h t) = runFn (concat c [carc h]) t; runFn_cons + congr
      have rhs1 : axioms ⊢
          (runFn (runFn c (cons h t)) s =eq
            runFn (runFn (concat c (cons (carc h) nil)) t) s) :=
        congr_runFn_1 (runFn_cons c h t)
      exact FOL.derive_eq_trans lhs1
        (FOL.derive_eq_trans lhs2 (FOL.derive_eq_trans ihc (FOL.derive_eq_symm rhs1)))
  exact compProp_spec key c

/-! ### Pertenencia `In`: primitivos (re-derivados local) -/

/-- `In x (cons x t)` (ax_L2 + or-intro-left). -/
theorem in_cons_head (x t : Term) : axioms ⊢ In x (cons x t) := by
  have h_axL2 := ax (show ax_L2_in_cons ∈ axioms by simp [axioms])
  have hiff : axioms ⊢ (In x (cons x t) ⇔ lor (x =eq x) (In x t)) := by
    have hh := spec (spec (spec h_axL2 x) x) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  exact iff_mpr hiff (FOL.MetaRules.or_intro_left (eq_refl x))

/-- `In x t → In x (cons hd t)` (ax_L2 + or-intro-right). -/
theorem in_cons_tail (hd : Term) {x t : Term} (hx : axioms ⊢ In x t) :
    axioms ⊢ In x (cons hd t) := by
  have h_axL2 := ax (show ax_L2_in_cons ∈ axioms by simp [axioms])
  have hiff : axioms ⊢ (In x (cons hd t) ⇔ lor (x =eq hd) (In x t)) := by
    have hh := spec (spec (spec h_axL2 x) hd) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  exact iff_mpr hiff (FOL.MetaRules.or_intro_right hx)

/-! ### Ecuaciones de `allIn` / `chainOk` -/

/-- `allIn c nil` (vacuamente). -/
theorem allIn_nil (c : Term) : axioms ⊢ allIn c nil := by
  have hh := spec (ax (show ax_allIn_nil ∈ axioms by simp [axioms])) c
  simpa [ax_allIn_nil, substFormula, substTerm, substTerms, allIn, nil, zero,
    FOL.substTerm_liftTerm] using hh

/-- `allIn c (cons x t) ⇔ In x c ∧ allIn c t`. -/
theorem allIn_cons (c x t : Term) :
    axioms ⊢ (allIn c (cons x t) ⇔ land (In x c) (allIn c t)) := by
  have hh := spec (spec (spec (ax (show ax_allIn_cons ∈ axioms by simp [axioms])) c) x) t
  simp [ax_allIn_cons, substFormula, substTerm, substTerms, allIn, In, land, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- `chainOk c nil`. -/
theorem chainOk_nil (c : Term) : axioms ⊢ chainOk c nil := by
  have hh := spec (ax (show ax_chainOk_nil ∈ axioms by simp [axioms])) c
  simpa [ax_chainOk_nil, substFormula, substTerm, substTerms, chainOk, nil, zero,
    FOL.substTerm_liftTerm] using hh

/-- `chainOk c (cons line rest) ⇔ lineOk c line ∧ chainOk (c ++ [carc line]) rest`. -/
theorem chainOk_cons (c line rest : Term) :
    axioms ⊢ (chainOk c (cons line rest) ⇔
      land (lineOk c line) (chainOk (concat c (cons (carc line) nil)) rest)) := by
  have hh := spec (spec (spec (ax (show ax_chainOk_cons ∈ axioms by simp [axioms])) c) line) rest
  simp [ax_chainOk_cons, substFormula, substTerm, substTerms, chainOk, lineOk, lineWF, allIn,
    premsOf, land, concat, carc, cons, nil, zero, succ, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Monotonía en el contexto (clave para D2) -/

/-- **Monotonía de `In`**: `In x c → In x (c0 ++ c)` (el contexto crece por la
    izquierda). Por inducción estructural sobre `c0`. -/
theorem In_mono (x c c0 : Term) (h : axioms ⊢ In x c) : axioms ⊢ In x (concat c0 c) := by
  have key := Full.ax_list_induction (fun L => Formula.impl (In x c) (In x (concat L c)))
    (by apply Minimal.Axioms.imp_intro; intro hin
        exact Full.eq_subst_in (FOL.derive_eq_symm (concat_nil_eq c)) hin)
    (by intro hd t IH
        apply Minimal.Axioms.imp_intro; intro hin
        exact Full.eq_subst_in (FOL.derive_eq_symm (concat_cons_eq hd t c))
          (in_cons_tail hd (mp IH hin)))
  exact mp (key c0) h

/-- **Monotonía de `allIn`**: `allIn c L → allIn (c0 ++ c) L`. Por inducción sobre `L`
    (uniforme; usa `In_mono`). -/
theorem allIn_mono (c c0 L : Term) (h : axioms ⊢ allIn c L) :
    axioms ⊢ allIn (concat c0 c) L := by
  have key := Full.ax_list_induction
    (fun M => Formula.impl (allIn c M) (allIn (concat c0 c) M))
    (by apply Minimal.Axioms.imp_intro; intro _; exact allIn_nil (concat c0 c))
    (by intro hd t IH
        apply Minimal.Axioms.imp_intro; intro hM
        have hconj : axioms ⊢ land (In hd c) (allIn c t) := iff_mp (allIn_cons c hd t) hM
        have hIn2 : axioms ⊢ In hd (concat c0 c) :=
          In_mono hd c c0 (Minimal.Axioms.and_elim_left hconj)
        have hrest2 : axioms ⊢ allIn (concat c0 c) t :=
          mp IH (Minimal.Axioms.and_elim_right hconj)
        exact iff_mpr (allIn_cons (concat c0 c) hd t)
          (Minimal.Axioms.and_intro hIn2 hrest2))
  exact mp (key L) h

/-- **Monotonía de `lineOk`**: `lineOk c line → lineOk (c0 ++ c) line` para línea
    ARBITRARIA (la parte dependiente del contexto es `allIn`, monótona; `lineWF` es
    independiente del contexto). -/
theorem lineOk_mono (c c0 line : Term) (h : axioms ⊢ lineOk c line) :
    axioms ⊢ lineOk (concat c0 c) line :=
  Minimal.Axioms.and_intro (Minimal.Axioms.and_elim_left h)
    (allIn_mono c c0 (premsOf line) (Minimal.Axioms.and_elim_right h))

/-! ### R3 — `concat` identidad derecha, congruencias de `chainOk`, `In_mono_right` -/

/-- `concat X nil =eq X` (identidad por la derecha; inducción sobre `X`). -/
theorem concat_nil_right (X : Term) : axioms ⊢ (concat X nil =eq X) := by
  have key := Full.ax_list_induction (fun L => Formula.eq (concat L nil) L)
    (concat_nil_eq nil)
    (by intro h t IH
        exact FOL.derive_eq_trans (concat_cons_eq h t nil) (congr_cons_tail IH))
  exact key X

/-- Congruencia de `chainOk` en el 1er argumento (acumulador). -/
theorem chainOk_subst1 {c₁ c₂ p : Term} (h : axioms ⊢ (c₁ =eq c₂))
    (hok : axioms ⊢ chainOk c₁ p) : axioms ⊢ chainOk c₂ p := by
  let f : Formula := chainOk (.var 0) (liftTerm 0 p)
  have hS : ∀ s : Term, substFormula 0 s f = chainOk s p := by
    intro s; simp only [f, chainOk, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ Derives.subst axioms c₁ c₂ f h ((hS c₁) ▸ hok)

/-- Congruencia de `chainOk` en el 2º argumento (cadena). -/
theorem chainOk_subst2 {c p₁ p₂ : Term} (h : axioms ⊢ (p₁ =eq p₂))
    (hok : axioms ⊢ chainOk c p₁) : axioms ⊢ chainOk c p₂ := by
  let f : Formula := chainOk (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = chainOk c s := by
    intro s; simp only [f, chainOk, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS p₂) ▸ Derives.subst axioms p₁ p₂ f h ((hS p₁) ▸ hok)

/-- Congruencia de `allIn` en el 2º argumento (lista). -/
theorem allIn_subst2 {c L₁ L₂ : Term} (h : axioms ⊢ (L₁ =eq L₂))
    (hok : axioms ⊢ allIn c L₁) : axioms ⊢ allIn c L₂ := by
  let f : Formula := allIn (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = allIn c s := by
    intro s; simp only [f, allIn, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS L₂) ▸ Derives.subst axioms L₁ L₂ f h ((hS L₁) ▸ hok)

/-- **Monotonía de `In` por la derecha**: `In x L → In x (L ++ M)`. Inducción sobre `L`. -/
theorem In_mono_right (x M L : Term) (h : axioms ⊢ In x L) : axioms ⊢ In x (concat L M) := by
  have key := Full.ax_list_induction (fun K => Formula.impl (In x K) (In x (concat K M)))
    (by apply Minimal.Axioms.imp_intro; intro hin
        have hnotin := spec (ax (show ax_L1_in_nil ∈ axioms by simp [axioms])) x
        simp only [ax_L1_in_nil, substFormula, substTerm, substTerms, In, neg, nil, zero,
          FOL.substTerm_liftTerm] at hnotin
        exact mp FOL.Theorems.Neg.explosion_impl (mp hnotin hin))
    (by intro hd t IH
        apply Minimal.Axioms.imp_intro; intro hin
        have hiff : axioms ⊢ (In x (cons hd t) ⇔ lor (x =eq hd) (In x t)) := by
          have hh := spec (spec (spec (ax (show ax_L2_in_cons ∈ axioms by simp [axioms])) x) hd) t
          simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
          exact hh
        refine Minimal.Axioms.or_elim (iff_mp hiff hin) ?_ ?_
        · intro hxhd
          have inc : axioms ⊢ In x (cons hd (concat t M)) :=
            Full.eq_subst_in (congr_cons_head hxhd) (in_cons_head x (concat t M))
          exact Full.eq_subst_in (FOL.derive_eq_symm (concat_cons_eq hd t M)) inc
        · intro hxt
          have inc : axioms ⊢ In x (cons hd (concat t M)) := in_cons_tail hd (mp IH hxt)
          exact Full.eq_subst_in (FOL.derive_eq_symm (concat_cons_eq hd t M)) inc)
  exact mp (key L) h

/-! ### R3 — Debilitamiento de `runFn` -/

/-- Propiedad inductiva del debilitamiento: `∀c. runFn c p =eq c ++ runFn nil p`. -/
def weakProp (p : Term) : Formula :=
  Formula.forall
    (Formula.eq (runFn (.var 0) (liftTerm 0 p)) (concat (.var 0) (runFn nil (liftTerm 0 p))))

theorem weakProp_spec {p : Term} (h : axioms ⊢ weakProp p) (c : Term) :
    axioms ⊢ (runFn c p =eq concat c (runFn nil p)) := by
  have hc := spec h c
  simpa [weakProp, substFormula, substTerm, substTerms, runFn, concat, nil, zero,
    FOL.substTerm_liftTerm] using hc

/-- **Debilitamiento de `runFn`**: correr desde el acumulador `c` antepone `c` al
    resultado desde vacío: `runFn c p =eq c ++ runFn nil p`. Por inducción sobre `p`
    (acumulador `∀` object; usa `concat_assoc`). -/
theorem runFn_weaken (c p : Term) : axioms ⊢ (runFn c p =eq concat c (runFn nil p)) := by
  have key : axioms ⊢ weakProp p := by
    refine Full.ax_list_induction (fun L => weakProp L) ?base ?step p
    · apply gen; intro c
      simp only [weakProp, substFormula, substTerm, substTerms, runFn, concat, nil, zero,
        FOL.substTerm_liftTerm]
      -- runFn c nil =eq concat c (runFn nil nil)
      exact FOL.derive_eq_trans (runFn_nil c)
        (FOL.derive_eq_symm (FOL.derive_eq_trans
          (Full.eq_congr_concat_left (runFn_nil nil)) (concat_nil_right c)))
    · intro h t IH
      apply gen; intro c
      simp only [weakProp, substFormula, substTerm, substTerms, runFn, concat, nil, zero,
        FOL.substTerm_liftTerm]
      -- runFn c (cons h t) =eq concat c (runFn nil (cons h t))
      have L1 : axioms ⊢ (runFn c (cons h t) =eq runFn (concat c (cons (carc h) nil)) t) :=
        runFn_cons c h t
      have L2 : axioms ⊢
          (runFn (concat c (cons (carc h) nil)) t =eq
            concat (concat c (cons (carc h) nil)) (runFn nil t)) :=
        weakProp_spec IH (concat c (cons (carc h) nil))
      have L3 : axioms ⊢
          (concat (concat c (cons (carc h) nil)) (runFn nil t) =eq
            concat c (concat (cons (carc h) nil) (runFn nil t))) :=
        Full.concat_assoc_pointwise c (cons (carc h) nil) (runFn nil t)
      have Lhs : axioms ⊢
          (runFn c (cons h t) =eq concat c (concat (cons (carc h) nil) (runFn nil t))) :=
        FOL.derive_eq_trans L1 (FOL.derive_eq_trans L2 L3)
      have R1 : axioms ⊢ (runFn nil (cons h t) =eq runFn (concat nil (cons (carc h) nil)) t) :=
        runFn_cons nil h t
      have R2 : axioms ⊢
          (runFn (concat nil (cons (carc h) nil)) t =eq runFn (cons (carc h) nil) t) :=
        congr_runFn_1 (concat_nil_eq (cons (carc h) nil))
      have R3 : axioms ⊢
          (runFn (cons (carc h) nil) t =eq concat (cons (carc h) nil) (runFn nil t)) :=
        weakProp_spec IH (cons (carc h) nil)
      have Rin : axioms ⊢
          (runFn nil (cons h t) =eq concat (cons (carc h) nil) (runFn nil t)) :=
        FOL.derive_eq_trans R1 (FOL.derive_eq_trans R2 R3)
      have Rhs : axioms ⊢
          (concat c (runFn nil (cons h t)) =eq concat c (concat (cons (carc h) nil) (runFn nil t))) :=
        Full.eq_congr_concat_left Rin
      exact FOL.derive_eq_trans Lhs (FOL.derive_eq_symm Rhs)
  exact weakProp_spec key c

/-! ### R3 — Composición y monotonía de `chainOk` -/

/-- Construcción de `⇔` a partir de las dos implicaciones meta. -/
theorem iff_intro_local {a b : Formula}
    (h1 : axioms ⊢ a → axioms ⊢ b) (h2 : axioms ⊢ b → axioms ⊢ a) :
    axioms ⊢ (a ⇔ b) :=
  Minimal.Axioms.and_intro (Minimal.Axioms.imp_intro h1) (Minimal.Axioms.imp_intro h2)

/-- Propiedad inductiva de la composición de `chainOk`. -/
def compChainProp (s p : Term) : Formula :=
  Formula.forall
    ((chainOk (.var 0) (concat (liftTerm 0 p) (liftTerm 0 s))) ⇔
      land (chainOk (.var 0) (liftTerm 0 p)) (chainOk (runFn (.var 0) (liftTerm 0 p)) (liftTerm 0 s)))

theorem compChainProp_spec {s p : Term} (h : axioms ⊢ compChainProp s p) (c : Term) :
    axioms ⊢ (chainOk c (concat p s) ⇔
      land (chainOk c p) (chainOk (runFn c p) s)) := by
  have hc := spec h c
  simpa [compChainProp, substFormula, substTerm, substTerms, chainOk, runFn, concat, land, iff,
    FOL.substTerm_liftTerm] using hc

/-- **Composición de `chainOk`**: `chainOk c (p ++ s) ⇔ chainOk c p ∧ chainOk (runFn c p) s`.
    Inducción sobre `p` (acumulador `∀` object). -/
theorem chainOk_concat (c p s : Term) :
    axioms ⊢ (chainOk c (concat p s) ⇔ land (chainOk c p) (chainOk (runFn c p) s)) := by
  have key : axioms ⊢ compChainProp s p := by
    refine Full.ax_list_induction (fun L => compChainProp s L) ?base ?step p
    · apply gen; intro c
      simp [compChainProp, substFormula, substTerm, substTerms, chainOk, runFn, concat, land, iff,
        FOL.substTerm_liftTerm]
      apply Minimal.Axioms.and_intro
      · apply Minimal.Axioms.imp_intro; intro hL
        have hs : axioms ⊢ chainOk c s := chainOk_subst2 (concat_nil_eq s) hL
        exact Minimal.Axioms.and_intro (chainOk_nil c)
          (chainOk_subst1 (FOL.derive_eq_symm (runFn_nil c)) hs)
      · apply Minimal.Axioms.imp_intro; intro hR
        have hs : axioms ⊢ chainOk c s :=
          chainOk_subst1 (runFn_nil c) (Minimal.Axioms.and_elim_right hR)
        exact chainOk_subst2 (FOL.derive_eq_symm (concat_nil_eq s)) hs
    · intro h t IH
      apply gen; intro c
      simp [compChainProp, substFormula, substTerm, substTerms, chainOk, runFn, concat, land, iff,
        FOL.substTerm_liftTerm]
      apply Minimal.Axioms.and_intro
      · apply Minimal.Axioms.imp_intro; intro hL
        -- hL : chainOk c (concat (cons h t) s)
        have h1 : axioms ⊢ chainOk c (cons h (concat t s)) :=
          chainOk_subst2 (concat_cons_eq h t s) hL
        have hsplit := iff_mp (chainOk_cons c h (concat t s)) h1
        have hA : axioms ⊢ lineOk c h := Minimal.Axioms.and_elim_left hsplit
        have hrest : axioms ⊢ chainOk (concat c (cons (carc h) nil)) (concat t s) :=
          Minimal.Axioms.and_elim_right hsplit
        have hBC := iff_mp (compChainProp_spec IH (concat c (cons (carc h) nil))) hrest
        have hB : axioms ⊢ chainOk (concat c (cons (carc h) nil)) t :=
          Minimal.Axioms.and_elim_left hBC
        have hC : axioms ⊢ chainOk (runFn (concat c (cons (carc h) nil)) t) s :=
          Minimal.Axioms.and_elim_right hBC
        have hcons : axioms ⊢ chainOk c (cons h t) :=
          iff_mpr (chainOk_cons c h t) (Minimal.Axioms.and_intro hA hB)
        have hrun : axioms ⊢ chainOk (runFn c (cons h t)) s :=
          chainOk_subst1 (FOL.derive_eq_symm (runFn_cons c h t)) hC
        exact Minimal.Axioms.and_intro hcons hrun
      · apply Minimal.Axioms.imp_intro; intro hR
        have hcons : axioms ⊢ chainOk c (cons h t) := Minimal.Axioms.and_elim_left hR
        have hrun : axioms ⊢ chainOk (runFn c (cons h t)) s := Minimal.Axioms.and_elim_right hR
        have hsplit := iff_mp (chainOk_cons c h t) hcons
        have hA : axioms ⊢ lineOk c h := Minimal.Axioms.and_elim_left hsplit
        have hB : axioms ⊢ chainOk (concat c (cons (carc h) nil)) t :=
          Minimal.Axioms.and_elim_right hsplit
        have hC : axioms ⊢ chainOk (runFn (concat c (cons (carc h) nil)) t) s :=
          chainOk_subst1 (runFn_cons c h t) hrun
        have hrec : axioms ⊢ chainOk (concat c (cons (carc h) nil)) (concat t s) :=
          iff_mpr (compChainProp_spec IH (concat c (cons (carc h) nil)))
            (Minimal.Axioms.and_intro hB hC)
        have hbig : axioms ⊢ chainOk c (cons h (concat t s)) :=
          iff_mpr (chainOk_cons c h (concat t s)) (Minimal.Axioms.and_intro hA hrec)
        exact chainOk_subst2 (FOL.derive_eq_symm (concat_cons_eq h t s)) hbig
  exact compChainProp_spec key c

/-- Propiedad inductiva de la monotonía de `chainOk`. -/
def monoChainProp (c0 p : Term) : Formula :=
  Formula.forall
    (Formula.impl (chainOk (.var 0) (liftTerm 0 p))
                  (chainOk (concat (liftTerm 0 c0) (.var 0)) (liftTerm 0 p)))

theorem monoChainProp_spec {c0 p : Term} (h : axioms ⊢ monoChainProp c0 p) (c : Term) :
    axioms ⊢ (chainOk c p ⇒ chainOk (concat c0 c) p) := by
  have hc := spec h c
  simpa [monoChainProp, substFormula, substTerm, substTerms, chainOk, concat,
    FOL.substTerm_liftTerm] using hc

/-- **Monotonía de `chainOk` en el contexto**: `chainOk c p → chainOk (c0 ++ c) p`.
    Inducción sobre `p` (acumulador `∀` object; usa `lineOk_mono` y `concat_assoc`). -/
theorem chainOk_mono (c0 c p : Term) (h : axioms ⊢ chainOk c p) :
    axioms ⊢ chainOk (concat c0 c) p := by
  have key : axioms ⊢ monoChainProp c0 p := by
    refine Full.ax_list_induction (fun L => monoChainProp c0 L) ?base ?step p
    · apply gen; intro c
      simp [monoChainProp, substFormula, substTerm, substTerms, chainOk, concat,
        FOL.substTerm_liftTerm]
      exact Minimal.Axioms.imp_intro (fun _ => chainOk_nil (concat c0 c))
    · intro h t IH
      apply gen; intro c
      simp [monoChainProp, substFormula, substTerm, substTerms, chainOk, concat,
        FOL.substTerm_liftTerm]
      refine Minimal.Axioms.imp_intro (fun hc => ?_)
      have hsplit := iff_mp (chainOk_cons c h t) hc
      have hA : axioms ⊢ lineOk c h := Minimal.Axioms.and_elim_left hsplit
      have hB : axioms ⊢ chainOk (concat c (cons (carc h) nil)) t :=
        Minimal.Axioms.and_elim_right hsplit
      have hA' : axioms ⊢ lineOk (concat c0 c) h := lineOk_mono c c0 h hA
      have hBmid : axioms ⊢ chainOk (concat c0 (concat c (cons (carc h) nil))) t :=
        mp (monoChainProp_spec IH (concat c (cons (carc h) nil))) hB
      have hB' : axioms ⊢ chainOk (concat (concat c0 c) (cons (carc h) nil)) t :=
        chainOk_subst1 (FOL.derive_eq_symm
          (Full.concat_assoc_pointwise c0 c (cons (carc h) nil))) hBmid
      exact iff_mpr (chainOk_cons (concat c0 c) h t) (Minimal.Axioms.and_intro hA' hB')
  exact mp (monoChainProp_spec key c) h

/-! ### R4 — predicado de demostrabilidad nuevo `provCodeC'` + validez de reglas -/

/-- **Predicado de demostrabilidad object (estructural)** Σ₁:
    `∃p, chainOk nil p ∧ In x (runFn nil p)` — "existe una cadena de prueba válida
    `p` cuyas conclusiones contienen `x`". Reemplaza `provFormulaC` (validProofFn)
    por el verificador estructural, apto para D2/D3. -/
def provFormulaC' : Formula :=
  Formula.ex (land (chainOk nil (.var 0)) (In (.var 1) (runFn nil (.var 0))))

/-- `Prov'(⌜φ⌝)` estructural. -/
noncomputable def provCodeC' (φ : Formula) : Formula := substFormula 0 (formCode φ) provFormulaC'

/-- Validez (independiente del contexto) de una línea **mp**: incondicional. -/
theorem lineWF_mp (concl premA : Term) :
    axioms ⊢ lineWF (cons concl (cons (numeralM 16) (cons premA nil))) := by
  have hh := spec (spec (ax (show ax_lineWF_mp ∈ axioms by simp [axioms])) concl) premA
  simpa [ax_lineWF_mp, substFormula, substTerm, substTerms, lineWF, numeralM, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hh

/-- Premisas de una línea **mp**: `[⌜A⇒B⌝, ⌜A⌝]`. -/
theorem premsOf_mp (concl premA : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 16) (cons premA nil))) =eq
      cons (implc premA concl) (cons premA nil)) := by
  have hh := spec (spec (ax (show ax_premsOf_mp ∈ axioms by simp [axioms])) concl) premA
  simp [ax_premsOf_mp, substFormula, substTerm, substTerms, premsOf, implc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Validez de una línea **gen**: incondicional. -/
theorem lineWF_gen (concl body : Term) :
    axioms ⊢ lineWF (cons concl (cons (numeralM 17) (cons body nil))) := by
  have hh := spec (spec (ax (show ax_lineWF_gen ∈ axioms by simp [axioms])) concl) body
  simpa [ax_lineWF_gen, substFormula, substTerm, substTerms, lineWF, numeralM, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hh

/-- Premisas de una línea **gen**: `[body]`. -/
theorem premsOf_gen (concl body : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 17) (cons body nil))) =eq cons body nil) := by
  have hh := spec (spec (ax (show ax_premsOf_gen ∈ axioms by simp [axioms])) concl) body
  simp [ax_premsOf_gen, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Validez de una línea **thy**: el código es un axioma de la teoría. -/
theorem lineWF_thy (concl : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 15) nil)) ⇔ In concl axiomsCodeT) := by
  have hh := spec (ax (show ax_lineWF_thy ∈ axioms by simp [axioms])) concl
  simp [ax_lineWF_thy, substFormula, substTerm, substTerms, lineWF, In, axiomsCodeT, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Premisas de una línea **thy**: ninguna. -/
theorem premsOf_thy (concl : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 15) nil)) =eq nil) := by
  have hh := spec (ax (show ax_premsOf_thy ∈ axioms by simp [axioms])) concl
  simp [ax_premsOf_thy, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `lineWF`/`premsOf` de los esquemas proposicionales (teoremas) -/

/-- P1. -/
theorem lineWF_p1 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 0) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b a))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_p1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_p1, substFormula, substTerm, substTerms, lineWF, implc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_p1 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 0) (cons a (cons b nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_p1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_p1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- P2. -/
theorem lineWF_p2 (concl a b c : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) ⇔
      (concl =eq implc (implc a (implc b c)) (implc (implc a b) (implc a c)))) := by
  have hh := spec (spec (spec (spec (ax (show ax_lineWF_p2 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_lineWF_p2, substFormula, substTerm, substTerms, lineWF, implc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_p2 (concl a b c : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) =eq nil) := by
  have hh := spec (spec (spec (spec (ax (show ax_premsOf_p2 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_premsOf_p2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- C1. -/
theorem lineWF_c1 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 2) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b (andc a b)))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_c1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_c1, substFormula, substTerm, substTerms, lineWF, implc, andc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_c1 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 2) (cons a (cons b nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_c1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- C2. -/
theorem lineWF_c2 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 3) (cons a (cons b nil)))) ⇔
      (concl =eq implc (andc a b) a)) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_c2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_c2, substFormula, substTerm, substTerms, lineWF, implc, andc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_c2 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 3) (cons a (cons b nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_c2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- C3. -/
theorem lineWF_c3 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 4) (cons a (cons b nil)))) ⇔
      (concl =eq implc (andc a b) b)) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_c3 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_c3, substFormula, substTerm, substTerms, lineWF, implc, andc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_c3 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 4) (cons a (cons b nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_c3 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J1. -/
theorem lineWF_j1 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 5) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (orc a b))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_j1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_j1, substFormula, substTerm, substTerms, lineWF, implc, orc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_j1 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 5) (cons a (cons b nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_j1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_j1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J2. -/
theorem lineWF_j2 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 6) (cons a (cons b nil)))) ⇔
      (concl =eq implc b (orc a b))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_j2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_j2, substFormula, substTerm, substTerms, lineWF, implc, orc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_j2 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 6) (cons a (cons b nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_j2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_j2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J3. -/
theorem lineWF_j3 (concl a b c : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) ⇔
      (concl =eq implc (orc a b) (implc (implc a c) (implc (implc b c) c)))) := by
  have hh := spec (spec (spec (spec (ax (show ax_lineWF_j3 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_lineWF_j3, substFormula, substTerm, substTerms, lineWF, implc, orc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_j3 (concl a b c : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) =eq nil) := by
  have hh := spec (spec (spec (spec (ax (show ax_premsOf_j3 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_premsOf_j3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- EFQ. -/
theorem lineWF_efq (concl a : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 8) (cons a nil))) ⇔ (concl =eq implc botc a)) := by
  have hh := spec (spec (ax (show ax_lineWF_efq ∈ axioms by simp [axioms])) concl) a
  simp [ax_lineWF_efq, substFormula, substTerm, substTerms, lineWF, implc, botc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_efq (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 8) (cons a nil))) =eq nil) := by
  have hh := spec (spec (ax (show ax_premsOf_efq ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_efq, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- EQREFL. -/
theorem lineWF_eqrefl (concl t : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 12) (cons t nil))) ⇔ (concl =eq eqc t t)) := by
  have hh := spec (spec (ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms])) concl) t
  simp [ax_lineWF_eqrefl, substFormula, substTerm, substTerms, lineWF, eqc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_eqrefl (concl t : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 12) (cons t nil))) =eq nil) := by
  have hh := spec (spec (ax (show ax_premsOf_eqrefl ∈ axioms by simp [axioms])) concl) t
  simp [ax_premsOf_eqrefl, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- P3. -/
theorem lineWF_p3 (concl a : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 14) (cons a nil))) ⇔
      (concl =eq implc (implc (implc a botc) botc) a)) := by
  have hh := spec (spec (ax (show ax_lineWF_p3 ∈ axioms by simp [axioms])) concl) a
  simp [ax_lineWF_p3, substFormula, substTerm, substTerms, lineWF, implc, botc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem premsOf_p3 (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 14) (cons a nil))) =eq nil) := by
  have hh := spec (spec (ax (show ax_premsOf_p3 ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_p3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `lineWF`/`premsOf` de los esquemas de sustitución (teoremas) -/

/-- Q1. -/
theorem lineWF_q1 (concl A t : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 9) (cons A (cons t nil)))) ⇔
      (concl =eq implc (forallc A) (substfc zero t A))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_q1 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_lineWF_q1, substFormula, substTerm, substTerms, lineWF, implc, forallc, substfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_q1 (concl A t : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 9) (cons A (cons t nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_q1 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_premsOf_q1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- Q2. -/
theorem lineWF_q2 (concl A t : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 10) (cons A (cons t nil)))) ⇔
      (concl =eq implc (substfc zero t A) (exc A))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_q2 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_lineWF_q2, substFormula, substTerm, substTerms, lineWF, implc, exc, substfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_q2 (concl A t : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 10) (cons A (cons t nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_q2 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_premsOf_q2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- Q3. -/
theorem lineWF_q3 (concl A B : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 11) (cons A (cons B nil)))) ⇔
      (concl =eq implc (forallc (implc A (liftfc zero B))) (implc (exc A) B))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_q3 ∈ axioms by simp [axioms])) concl) A) B
  simp [ax_lineWF_q3, substFormula, substTerm, substTerms, lineWF, implc, forallc, exc, liftfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_q3 (concl A B : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 11) (cons A (cons B nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_q3 ∈ axioms by simp [axioms])) concl) A) B
  simp [ax_premsOf_q3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- LEIBNIZ. -/
theorem lineWF_leibniz (concl A t₁ t₂ : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) ⇔
      (concl =eq implc (eqc t₁ t₂) (implc (substfc zero t₁ A) (substfc zero t₂ A)))) := by
  have hh := spec (spec (spec (spec (ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms])) concl) A) t₁) t₂
  simp [ax_lineWF_leibniz, substFormula, substTerm, substTerms, lineWF, implc, eqc, substfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh
theorem premsOf_leibniz (concl A t₁ t₂ : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) =eq nil) := by
  have hh := spec (spec (spec (spec (ax (show ax_premsOf_leibniz ∈ axioms by simp [axioms])) concl) A) t₁) t₂
  simp [ax_premsOf_leibniz, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh

/-- IND (códigos cerrados `termCodeM`, gestionados por clausura como en `vpf_ind`). -/
theorem lineWF_ind (concl a : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 18) (cons a nil))) ⇔
      (concl =eq implc (substfc zero (termCodeM zero) a)
        (implc (forallc (implc a (substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) a))))
               (forallc a)))) := by
  have hh := spec (spec (ax (show ax_lineWF_ind ∈ axioms by simp [axioms])) concl) a
  simp [ax_lineWF_ind, substFormula, substTerm, substTerms, lineWF, implc, forallc, substfc, liftfc,
    numeralM, cons, nil, zero, succ, iff, substTerm_termCodeM, substTerm_numeralM, substTerm_nil,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_ind (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 18) (cons a nil))) =eq nil) := by
  have hh := spec (spec (ax (show ax_premsOf_ind ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_ind, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- QCONF (tag 19, [P,C]): confinamiento ∀. -/
theorem lineWF_qconf (concl P C : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 19) (cons P (cons C nil)))) ⇔
      (concl =eq implc (forallc (implc (liftfc zero P) C)) (implc P (forallc C)))) := by
  have hh := spec (spec (spec (ax (show ax_lineWF_qconf ∈ axioms by simp [axioms])) concl) P) C
  simp [ax_lineWF_qconf, substFormula, substTerm, substTerms, lineWF, implc, forallc, liftfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem premsOf_qconf (concl P C : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 19) (cons P (cons C nil)))) =eq nil) := by
  have hh := spec (spec (spec (ax (show ax_premsOf_qconf ∈ axioms by simp [axioms])) concl) P) C
  simp [ax_premsOf_qconf, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-! ### Empaquetado de `provCodeC'` (intro/elim del `∃`) -/

/-- **Introducción** de `provCodeC' φ`: exhibe una cadena `p` válida que concluye `⌜φ⌝`. -/
theorem provCodeC'_intro (φ : Formula) (p : Term)
    (h1 : axioms ⊢ chainOk nil p) (h2 : axioms ⊢ In (formCode φ) (runFn nil p)) :
    axioms ⊢ provCodeC' φ := by
  have hbody : axioms ⊢ land (chainOk nil p) (In (formCode φ) (runFn nil p)) :=
    Minimal.Axioms.and_intro h1 h2
  have hex := Derives.intro_ex axioms
    (land (chainOk nil (.var 0)) (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0)))) p
    (by simpa [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
          FOL.substTerm_liftTerm] using hbody)
  simpa [provCodeC', provFormulaC', substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    FOL.substTerm_liftTerm] using hex

/-- **Eliminación** de `provCodeC' φ`: para probar `C`, basta hacerlo dado un testigo
    `p` con `chainOk nil p` y `In ⌜φ⌝ (runFn nil p)`. -/
theorem provCodeC'_elim {φ : Formula} {C : Formula} (h : axioms ⊢ provCodeC' φ)
    (k : ∀ p : Term, axioms ⊢ chainOk nil p → axioms ⊢ In (formCode φ) (runFn nil p) →
      axioms ⊢ C) : axioms ⊢ C := by
  have h' : axioms ⊢ Formula.ex (land (chainOk nil (.var 0)) (In (liftTerm 0 (formCode φ)) (runFn nil (.var 0)))) := by
    simpa [provCodeC', provFormulaC', substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
      FOL.substTerm_liftTerm] using h
  apply Minimal.Axioms.ex_elim h'
  intro p hp
  have hp' : axioms ⊢ land (chainOk nil p) (In (formCode φ) (runFn nil p)) := by
    simpa [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
      FOL.substTerm_liftTerm] using hp
  exact k p (Minimal.Axioms.and_elim_left hp') (Minimal.Axioms.and_elim_right hp')

end ROBINSON_PlusPlus.Meta.ProofChain

export ROBINSON_PlusPlus.Meta.ProofChain (
  runFn_nil
  runFn_cons
  congr_runFn_1
  congr_runFn_2
  concat_nil_eq
  concat_cons_eq
  runFn_concat
  in_cons_head
  in_cons_tail
  allIn_nil
  allIn_cons
  chainOk_nil
  chainOk_cons
  In_mono
  allIn_mono
  lineOk_mono
  concat_nil_right
  chainOk_subst1
  chainOk_subst2
  allIn_subst2
  In_mono_right
  runFn_weaken
  chainOk_concat
  chainOk_mono
  provFormulaC'
  provCodeC'
  lineWF_mp
  premsOf_mp
  lineWF_gen
  premsOf_gen
  lineWF_thy
  premsOf_thy
  provCodeC'_intro
  provCodeC'_elim
)

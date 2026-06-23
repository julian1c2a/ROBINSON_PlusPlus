/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.Representability

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.SubstArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ReprPrf

/-!
## META — NIVEL D real: re-nivelación de la cadena a `Prf` (hacia Gödel II real)

Para Gödel II real (`ConsistentH → ¬ Prf Con'`) la cadena HBL debe vivir en el
cálculo **finitario `Prf`** (no en `axioms ⊢`), porque `provCodeC'` rastrea `Prf` y
`¬⊢Con'` es falso (el ω-sistema es sólido). El refactor `Prf.thy → axioms` lo
habilitó: `Prf` ya puede usar TODO axioma (incluida la maquinaria de coding) vía
`thy`.

**Infraestructura de porte.** Los lemas-ecuación del verificador se demostraron a
nivel `axioms ⊢` con `ax`(=`Derives.hyp`/thy) + `spec`(=`elim_forall`) + `simp`. Su
contraparte `Prf` usa `prf_ax`(=`Prf₀.thy`) + `prf_spec`(=`q1`+`mp`) + el MISMO
`simp` (que solo manipula la igualdad meta de fórmulas). Esta sonda valida el patrón.
-/

/-- **Axioma como teorema de `Prf`** (regla `thy`, ahora sobre todo `axioms`). -/
theorem prf_ax {f : Formula} (h : f ∈ axioms) : Prf f := Prf.incl (Prf₀.thy f h)

/-- **Especialización en `Prf`** (instancia del esquema `q1` + `mp`): de `Prf (∀A)`
    y un término `t` sale `Prf (A[t])`. Contraparte finitaria de `spec`. -/
theorem prf_spec {A : Formula} (h : Prf (Formula.forall A)) (t : Term) :
    Prf (substFormula 0 t A) :=
  Prf.mp _ _ (Prf.incl (Prf₀.q1 A t)) h

/-- **Modus ponens en `Prf`** (alias cómodo). -/
theorem prf_mp {A B : Formula} (hAB : Prf (A ⇒ B)) (hA : Prf A) : Prf B :=
  Prf.mp A B hAB hA

/-! ### Sonda: ecuaciones de `runFn`/`chainOk` portadas a `Prf` -/

/-- `Prf (runFn c nil =eq c)` (porte de `runFn_nil`). -/
theorem prf_runFn_nil (c : Term) : Prf (runFn c nil =eq c) := by
  have hh := prf_spec (prf_ax (show ax_runFn_nil ∈ axioms by simp [axioms])) c
  simp [ax_runFn_nil, substFormula, substTerm, substTerms, runFn, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `Prf (runFn c (cons line rest) =eq runFn (concat c [carc line]) rest)`. -/
theorem prf_runFn_cons (c line rest : Term) :
    Prf (runFn c (cons line rest) =eq runFn (concat c (cons (carc line) nil)) rest) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax_runFn_cons ∈ axioms by simp [axioms])) c) line) rest
  simp [ax_runFn_cons, substFormula, substTerm, substTerms, runFn, concat, carc, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Primitivos lógicos en `Prf` (igualdad, Leibniz, ∧, ⇔, ∨) -/

/-- Reflexividad de la igualdad en `Prf`. -/
theorem prf_refl (t : Term) : Prf (t =eq t) := Prf.incl (Prf₀.eqrefl t)

/-- **Leibniz en `Prf`**: de `Prf (t₁ ≐ t₂)` y `Prf (A[t₁])` sale `Prf (A[t₂])`. -/
theorem prf_leibniz_subst {A : Formula} {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂))
    (hA : Prf (substFormula 0 t₁ A)) : Prf (substFormula 0 t₂ A) :=
  prf_mp (prf_mp (Prf.incl (Prf₀.leibniz A t₁ t₂)) h) hA

theorem prf_and_intro {a b : Formula} (ha : Prf a) (hb : Prf b) : Prf (a ∧ b) :=
  prf_mp (prf_mp (Prf.incl (Prf₀.c1 a b)) ha) hb
theorem prf_and_elim_left {a b : Formula} (h : Prf (a ∧ b)) : Prf a :=
  prf_mp (Prf.incl (Prf₀.c2 a b)) h
theorem prf_and_elim_right {a b : Formula} (h : Prf (a ∧ b)) : Prf b :=
  prf_mp (Prf.incl (Prf₀.c3 a b)) h
/-- `iff a b = (a⇒b) ∧ (b⇒a)`; `iff_mpr` extrae `b⇒a` y aplica MP. -/
theorem prf_iff_mpr {a b : Formula} (h : Prf (a ⇔ b)) (hb : Prf b) : Prf a :=
  prf_mp (prf_and_elim_right h) hb
theorem prf_iff_mp {a b : Formula} (h : Prf (a ⇔ b)) (ha : Prf a) : Prf b :=
  prf_mp (prf_and_elim_left h) ha
theorem prf_or_intro_left {a b : Formula} (ha : Prf a) : Prf (a ∨ b) :=
  prf_mp (Prf.incl (Prf₀.j1 a b)) ha
theorem prf_or_intro_right {a b : Formula} (hb : Prf b) : Prf (a ∨ b) :=
  prf_mp (Prf.incl (Prf₀.j2 a b)) hb

/-- Transitividad de `=eq` en `Prf` (vía Leibniz sobre `· =eq c`). -/
theorem prf_eq_trans {a b c : Term} (h1 : Prf (a =eq b)) (h2 : Prf (b =eq c)) : Prf (a =eq c) := by
  let f : Formula := Formula.eq (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq a s := by
    intro s; simp only [f, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c) ▸ prf_leibniz_subst (A := f) h2 ((hS b) ▸ h1)

/-- Simetría de `=eq` en `Prf`. -/
theorem prf_eq_symm {a b : Term} (h : Prf (a =eq b)) : Prf (b =eq a) := by
  let f : Formula := Formula.eq (.var 0) (liftTerm 0 a)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq s a := by
    intro s; simp only [f, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl a)

/-! ### Congruencias en `Prf` (vía `prf_leibniz_subst`) -/

theorem prf_congr_cons_head {h₁ h₂ t : Term} (hh : Prf (h₁ =eq h₂)) :
    Prf (cons h₁ t =eq cons h₂ t) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 h₁) (liftTerm 0 t)) (cons (.var 0) (liftTerm 0 t))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons h₁ t) (cons s t) := by
    intro s; simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS h₂) ▸ prf_leibniz_subst (A := f) hh ((hS h₁) ▸ prf_refl (cons h₁ t))

theorem prf_congr_cons_tail {h t₁ t₂ : Term} (hh : Prf (t₁ =eq t₂)) :
    Prf (cons h t₁ =eq cons h t₂) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 h) (liftTerm 0 t₁)) (cons (liftTerm 0 h) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons h t₁) (cons h s) := by
    intro s; simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) hh ((hS t₁) ▸ prf_refl (cons h t₁))

theorem prf_congr_runFn_1 {c₁ c₂ rest : Term} (h : Prf (c₁ =eq c₂)) :
    Prf (runFn c₁ rest =eq runFn c₂ rest) := by
  let f : Formula := Formula.eq (runFn (liftTerm 0 c₁) (liftTerm 0 rest)) (runFn (.var 0) (liftTerm 0 rest))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (runFn c₁ rest) (runFn s rest) := by
    intro s; simp only [f, substFormula, runFn, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ prf_leibniz_subst (A := f) h ((hS c₁) ▸ prf_refl (runFn c₁ rest))

theorem prf_congr_runFn_2 {c a b : Term} (h : Prf (a =eq b)) :
    Prf (runFn c a =eq runFn c b) := by
  let f : Formula := Formula.eq (runFn (liftTerm 0 c) (liftTerm 0 a)) (runFn (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (runFn c a) (runFn c s) := by
    intro s; simp only [f, substFormula, runFn, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (runFn c a))

theorem prf_congr_concat_left {u t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) :
    Prf (concat u t₁ =eq concat u t₂) := by
  let f : Formula := Formula.eq (concat (liftTerm 0 u) (liftTerm 0 t₁)) (concat (liftTerm 0 u) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (concat u t₁) (concat u s) := by
    intro s; simp only [f, substFormula, concat, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (concat u t₁))

theorem prf_chainOk_subst1 {c₁ c₂ p : Term} (h : Prf (c₁ =eq c₂)) (hok : Prf (chainOk c₁ p)) :
    Prf (chainOk c₂ p) := by
  let f : Formula := chainOk (.var 0) (liftTerm 0 p)
  have hS : ∀ s : Term, substFormula 0 s f = chainOk s p := by
    intro s; simp only [f, chainOk, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ prf_leibniz_subst (A := f) h ((hS c₁) ▸ hok)

theorem prf_allIn_subst2 {c L₁ L₂ : Term} (h : Prf (L₁ =eq L₂)) (hok : Prf (allIn c L₁)) :
    Prf (allIn c L₂) := by
  let f : Formula := allIn (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = allIn c s := by
    intro s; simp only [f, allIn, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS L₂) ▸ prf_leibniz_subst (A := f) h ((hS L₁) ▸ hok)

/-- Sustitución bajo `In` (2º arg) en `Prf`. -/
theorem prf_eq_subst_in {x t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) (hin : Prf (In x t₁)) :
    Prf (In x t₂) := by
  let f : Formula := In (liftTerm 0 x) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = In x s := by
    intro s; simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ hin)

/-! ### Ecuaciones `Prf` de `carc`/`concat`/`chainOk`/`allIn` -/

theorem prf_carc_cons (h t : Term) : Prf (carc (cons h t) =eq h) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_carc ∈ axioms by simp [axioms])) h) t
  simp [ax_carc, substFormula, substTerm, substTerms, carc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_concat_nil_eq (X : Term) : Prf (concat nil X =eq X) := by
  have hh := prf_spec (prf_ax (show ax_C1_concat_nil ∈ axioms by simp [axioms])) X
  simp [ax_C1_concat_nil, substFormula, substTerm, substTerms, concat, nil, zero] at hh
  exact hh

theorem prf_concat_cons_eq (h t X : Term) : Prf (concat (cons h t) X =eq cons h (concat t X)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_C2_concat_cons ∈ axioms by simp [axioms])) h) t) X
  simp [ax_C2_concat_cons, substFormula, substTerm, substTerms, concat, cons, nil, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_chainOk_nil (c : Term) : Prf (chainOk c nil) := by
  have hh := prf_spec (prf_ax (show ax_chainOk_nil ∈ axioms by simp [axioms])) c
  simpa [ax_chainOk_nil, substFormula, substTerm, substTerms, chainOk, nil, zero,
    FOL.substTerm_liftTerm] using hh

theorem prf_chainOk_cons (c line rest : Term) :
    Prf (chainOk c (cons line rest) ⇔
      land (lineOk c line) (chainOk (concat c (cons (carc line) nil)) rest)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_chainOk_cons ∈ axioms by simp [axioms])) c) line) rest
  simp [ax_chainOk_cons, substFormula, substTerm, substTerms, chainOk, lineOk, lineWF, allIn,
    premsOf, land, concat, carc, cons, nil, zero, succ, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_allIn_nil (c : Term) : Prf (allIn c nil) := by
  have hh := prf_spec (prf_ax (show ax_allIn_nil ∈ axioms by simp [axioms])) c
  simpa [ax_allIn_nil, substFormula, substTerm, substTerms, allIn, nil, zero,
    FOL.substTerm_liftTerm] using hh

theorem prf_allIn_cons (c x t : Term) :
    Prf (allIn c (cons x t) ⇔ land (In x c) (allIn c t)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_allIn_cons ∈ axioms by simp [axioms])) c) x) t
  simp [ax_allIn_cons, substFormula, substTerm, substTerms, allIn, In, land, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `In`-primitivos en `Prf` -/

theorem prf_in_cons_head (x t : Term) : Prf (In x (cons x t)) := by
  have hiff : Prf (In x (cons x t) ⇔ lor (x =eq x) (In x t)) := by
    have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_L2_in_cons ∈ axioms by simp [axioms])) x) x) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  exact prf_iff_mpr hiff (prf_or_intro_left (prf_refl x))

theorem prf_in_cons_tail (hd : Term) {x t : Term} (hx : Prf (In x t)) : Prf (In x (cons hd t)) := by
  have hiff : Prf (In x (cons hd t) ⇔ lor (x =eq hd) (In x t)) := by
    have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_L2_in_cons ∈ axioms by simp [axioms])) x) hd) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  exact prf_iff_mpr hiff (prf_or_intro_right hx)

/-- `g ∈ l ⟹ Prf (In ⌜g⌝ ⌜l⌝)`. -/
theorem prf_In_listFormCode {g : Formula} : ∀ {l : List Formula},
    List.Mem g l → Prf (In (formCode g) (listFormCode l))
  | [], hmem => by cases hmem
  | x :: xs, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst heq; exact prf_in_cons_head (formCode g) (listFormCode xs)
      · exact prf_in_cons_tail (formCode x) (prf_In_listFormCode htail)

/-! ### Validez `Prf` de las reglas de inferencia (mp/gen/thy) -/

theorem prf_lineWF_mp (concl premA : Term) :
    Prf (lineWF (cons concl (cons (numeralM 16) (cons premA nil)))) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms])) concl) premA
  simpa [ax_lineWF_mp, substFormula, substTerm, substTerms, lineWF, numeralM, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hh

theorem prf_premsOf_mp (concl premA : Term) :
    Prf (premsOf (cons concl (cons (numeralM 16) (cons premA nil))) =eq
      cons (implc premA concl) (cons premA nil)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_mp ∈ axioms by simp [axioms])) concl) premA
  simp [ax_premsOf_mp, substFormula, substTerm, substTerms, premsOf, implc, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_lineWF_gen (concl body : Term) :
    Prf (lineWF (cons concl (cons (numeralM 17) (cons body nil)))) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms])) concl) body
  simpa [ax_lineWF_gen, substFormula, substTerm, substTerms, lineWF, numeralM, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hh

theorem prf_premsOf_gen (concl body : Term) :
    Prf (premsOf (cons concl (cons (numeralM 17) (cons body nil))) =eq cons body nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_gen ∈ axioms by simp [axioms])) concl) body
  simp [ax_premsOf_gen, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_lineWF_thy (concl : Term) :
    Prf (lineWF (cons concl (cons (numeralM 15) nil)) ⇔ In concl axiomsCodeT) := by
  have hh := prf_spec (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms])) concl
  simp [ax_lineWF_thy, substFormula, substTerm, substTerms, lineWF, In, axiomsCodeT, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

theorem prf_premsOf_thy (concl : Term) :
    Prf (premsOf (cons concl (cons (numeralM 15) nil)) =eq nil) := by
  have hh := prf_spec (prf_ax (show ax_premsOf_thy ∈ axioms by simp [axioms])) concl
  simp [ax_premsOf_thy, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `lineWF`/`premsOf` de los esquemas proposicionales en `Prf` (porte de ProofChain) -/

/-- P1. -/
theorem prf_lineWF_p1 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 0) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b a))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_p1, substFormula, substTerm, substTerms, lineWF, implc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_p1 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 0) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_p1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_p1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- P2. -/
theorem prf_lineWF_p2 (concl a b c : Term) :
    Prf (lineWF (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) ⇔
      (concl =eq implc (implc a (implc b c)) (implc (implc a b) (implc a c)))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_lineWF_p2, substFormula, substTerm, substTerms, lineWF, implc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_p2 (concl a b c : Term) :
    Prf (premsOf (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_p2 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_premsOf_p2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- C1. -/
theorem prf_lineWF_c1 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 2) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b (andc a b)))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_c1, substFormula, substTerm, substTerms, lineWF, implc, andc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_c1 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 2) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- C2. -/
theorem prf_lineWF_c2 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 3) (cons a (cons b nil)))) ⇔
      (concl =eq implc (andc a b) a)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_c2, substFormula, substTerm, substTerms, lineWF, implc, andc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_c2 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 3) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- C3. -/
theorem prf_lineWF_c3 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 4) (cons a (cons b nil)))) ⇔
      (concl =eq implc (andc a b) b)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_c3, substFormula, substTerm, substTerms, lineWF, implc, andc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_c3 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 4) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c3 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J1. -/
theorem prf_lineWF_j1 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 5) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (orc a b))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_j1, substFormula, substTerm, substTerms, lineWF, implc, orc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_j1 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 5) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_j1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J2. -/
theorem prf_lineWF_j2 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 6) (cons a (cons b nil)))) ⇔
      (concl =eq implc b (orc a b))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_lineWF_j2, substFormula, substTerm, substTerms, lineWF, implc, orc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_j2 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 6) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_j2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J3. -/
theorem prf_lineWF_j3 (concl a b c : Term) :
    Prf (lineWF (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) ⇔
      (concl =eq implc (orc a b) (implc (implc a c) (implc (implc b c) c)))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_lineWF_j3, substFormula, substTerm, substTerms, lineWF, implc, orc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_j3 (concl a b c : Term) :
    Prf (premsOf (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j3 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_premsOf_j3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- EFQ. -/
theorem prf_lineWF_efq (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 8) (cons a nil))) ⇔ (concl =eq implc botc a)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms])) concl) a
  simp [ax_lineWF_efq, substFormula, substTerm, substTerms, lineWF, implc, botc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_efq (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 8) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_efq ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_efq, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- EQREFL. -/
theorem prf_lineWF_eqrefl (concl t : Term) :
    Prf (lineWF (cons concl (cons (numeralM 12) (cons t nil))) ⇔ (concl =eq eqc t t)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms])) concl) t
  simp [ax_lineWF_eqrefl, substFormula, substTerm, substTerms, lineWF, eqc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_eqrefl (concl t : Term) :
    Prf (premsOf (cons concl (cons (numeralM 12) (cons t nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_eqrefl ∈ axioms by simp [axioms])) concl) t
  simp [ax_premsOf_eqrefl, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- P3. -/
theorem prf_lineWF_p3 (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 14) (cons a nil))) ⇔
      (concl =eq implc (implc (implc a botc) botc) a)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms])) concl) a
  simp [ax_lineWF_p3, substFormula, substTerm, substTerms, lineWF, implc, botc, numeralM, cons, nil,
    zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh
theorem prf_premsOf_p3 (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 14) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_p3 ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_p3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `lineWF`/`premsOf` de los esquemas de sustitución en `Prf` (porte de ProofChain) -/

/-- Q1. -/
theorem prf_lineWF_q1 (concl A t : Term) :
    Prf (lineWF (cons concl (cons (numeralM 9) (cons A (cons t nil)))) ⇔
      (concl =eq implc (forallc A) (substfc zero t A))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_lineWF_q1, substFormula, substTerm, substTerms, lineWF, implc, forallc, substfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_q1 (concl A t : Term) :
    Prf (premsOf (cons concl (cons (numeralM 9) (cons A (cons t nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q1 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_premsOf_q1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- Q2. -/
theorem prf_lineWF_q2 (concl A t : Term) :
    Prf (lineWF (cons concl (cons (numeralM 10) (cons A (cons t nil)))) ⇔
      (concl =eq implc (substfc zero t A) (exc A))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_lineWF_q2, substFormula, substTerm, substTerms, lineWF, implc, exc, substfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_q2 (concl A t : Term) :
    Prf (premsOf (cons concl (cons (numeralM 10) (cons A (cons t nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q2 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_premsOf_q2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- Q3. -/
theorem prf_lineWF_q3 (concl A B : Term) :
    Prf (lineWF (cons concl (cons (numeralM 11) (cons A (cons B nil)))) ⇔
      (concl =eq implc (forallc (implc A (liftfc zero B))) (implc (exc A) B))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms])) concl) A) B
  simp [ax_lineWF_q3, substFormula, substTerm, substTerms, lineWF, implc, forallc, exc, liftfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_q3 (concl A B : Term) :
    Prf (premsOf (cons concl (cons (numeralM 11) (cons A (cons B nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q3 ∈ axioms by simp [axioms])) concl) A) B
  simp [ax_premsOf_q3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- LEIBNIZ. -/
theorem prf_lineWF_leibniz (concl A t₁ t₂ : Term) :
    Prf (lineWF (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) ⇔
      (concl =eq implc (eqc t₁ t₂) (implc (substfc zero t₁ A) (substfc zero t₂ A)))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms])) concl) A) t₁) t₂
  simp [ax_lineWF_leibniz, substFormula, substTerm, substTerms, lineWF, implc, eqc, substfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh
theorem prf_premsOf_leibniz (concl A t₁ t₂ : Term) :
    Prf (premsOf (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_leibniz ∈ axioms by simp [axioms])) concl) A) t₁) t₂
  simp [ax_premsOf_leibniz, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh

/-- IND (códigos cerrados `termCodeM`, gestionados por clausura como en `vpf_ind`). -/
theorem prf_lineWF_ind (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 18) (cons a nil))) ⇔
      (concl =eq implc (substfc zero (termCodeM zero) a)
        (implc (forallc (implc a (substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) a))))
               (forallc a)))) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_lineWF_ind ∈ axioms by simp [axioms])) concl) a
  simp [ax_lineWF_ind, substFormula, substTerm, substTerms, lineWF, implc, forallc, substfc, liftfc,
    numeralM, cons, nil, zero, succ, iff, substTerm_termCodeM, substTerm_numeralM, substTerm_nil,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_ind (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 18) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_ind ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_ind, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- QCONF (tag 19, [P,C]): confinamiento ∀, en `Prf`. -/
theorem prf_lineWF_qconf (concl P C : Term) :
    Prf (lineWF (cons concl (cons (numeralM 19) (cons P (cons C nil)))) ⇔
      (concl =eq implc (forallc (implc (liftfc zero P) C)) (implc P (forallc C)))) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms])) concl) P) C
  simp [ax_lineWF_qconf, substFormula, substTerm, substTerms, lineWF, implc, forallc, liftfc, numeralM,
    cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh
theorem prf_premsOf_qconf (concl P C : Term) :
    Prf (premsOf (cons concl (cons (numeralM 19) (cons P (cons C nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_qconf ∈ axioms by simp [axioms])) concl) P) C
  simp [ax_premsOf_qconf, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

end ROBINSON_PlusPlus.Meta.ReprPrf

export ROBINSON_PlusPlus.Meta.ReprPrf (
  prf_ax
  prf_spec
  prf_mp
  prf_refl
  prf_leibniz_subst
  prf_and_intro
  prf_iff_mpr
  prf_iff_mp
  prf_eq_trans
  prf_eq_symm
  prf_congr_cons_head
  prf_congr_cons_tail
  prf_congr_runFn_1
  prf_congr_runFn_2
  prf_congr_concat_left
  prf_chainOk_subst1
  prf_allIn_subst2
  prf_eq_subst_in
  prf_carc_cons
  prf_concat_nil_eq
  prf_concat_cons_eq
  prf_runFn_nil
  prf_runFn_cons
  prf_chainOk_nil
  prf_chainOk_cons
  prf_allIn_nil
  prf_allIn_cons
  prf_in_cons_head
  prf_in_cons_tail
  prf_In_listFormCode
  prf_lineWF_mp
  prf_premsOf_mp
  prf_lineWF_gen
  prf_premsOf_gen
  prf_lineWF_thy
  prf_premsOf_thy
  prf_lineWF_p1
  prf_premsOf_p1
  prf_lineWF_p2
  prf_premsOf_p2
  prf_lineWF_c1
  prf_premsOf_c1
  prf_lineWF_c2
  prf_premsOf_c2
  prf_lineWF_c3
  prf_premsOf_c3
  prf_lineWF_j1
  prf_premsOf_j1
  prf_lineWF_j2
  prf_premsOf_j2
  prf_lineWF_j3
  prf_premsOf_j3
  prf_lineWF_efq
  prf_premsOf_efq
  prf_lineWF_eqrefl
  prf_premsOf_eqrefl
  prf_lineWF_p3
  prf_premsOf_p3
  prf_lineWF_q1
  prf_premsOf_q1
  prf_lineWF_q2
  prf_premsOf_q2
  prf_lineWF_q3
  prf_premsOf_q3
  prf_lineWF_leibniz
  prf_premsOf_leibniz
  prf_lineWF_ind
  prf_premsOf_ind
  prf_lineWF_qconf
  prf_premsOf_qconf
)

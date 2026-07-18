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
set_option maxRecDepth 16000

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

/-! ### §44 — toolkit para los esquemas `lineWF` en forma de ACCESORES

Los `ax_lineWF_<tag>` están en forma de accesores (`carc`/`nthc`), no de forma explícita: es lo que los
hace aplicables a líneas **abstractas** (§44, `Meta/LineWFCases.lean`, §3.23.3 de la doc). Recuperar el
enunciado explícito exige (i) computar los accesores y (ii) **transportar** el bicondicional. `prf_nthc_*`
vive en `NumListPrf`, POSTERIOR a este módulo ⟹ copias locales; y las congruencias de constructor
(`ArithPrf`, también posterior) se reconstruyen aquí desde `prf_congr_cons_head/tail`. -/

/-- `nthc (cons h t) 0 = h` (copia local; `NumListPrf` es posterior). -/
private theorem prf_nthc_zero_loc (h t : Term) : Prf (nthc (cons h t) zero =eq h) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_nthc_zero ∈ axioms by simp [axioms])) h) t
  simpa [ax_nthc_zero, substFormula, substTerm, substTerms, nthc, cons, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hh

/-- `nthc (cons h t) (σ i) = nthc t i` (copia local). -/
private theorem prf_nthc_succ_loc (h t i : Term) :
    Prf (nthc (cons h t) (succ i) =eq nthc t i) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_nthc_succ ∈ axioms by simp [axioms])) h) t) i
  simpa [ax_nthc_succ, substFormula, substTerm, substTerms, nthc, cons, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hh

/-- Congruencia binaria genérica en el tag `T` (sirve para `eqc`/`implc`/`andc`/`orc`), arg 1. -/
theorem prf_congr_bin1 {T x x' y : Term} (h : Prf (x =eq x')) :
    Prf (cons T (cons x (cons y nil)) =eq cons T (cons x' (cons y nil))) :=
  prf_congr_cons_tail (prf_congr_cons_head h)
/-- Congruencia binaria genérica, arg 2. -/
theorem prf_congr_bin2 {T x y y' : Term} (h : Prf (y =eq y')) :
    Prf (cons T (cons x (cons y nil)) =eq cons T (cons x (cons y' nil))) :=
  prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head h))
/-- Congruencia unaria genérica (sirve para `forallc`/`exc`). -/
theorem prf_congr_un {T x x' : Term} (h : Prf (x =eq x')) :
    Prf (cons T (cons x nil) =eq cons T (cons x' nil)) :=
  prf_congr_cons_tail (prf_congr_cons_head h)

/-- Congruencia binaria completa (ambos args). -/
theorem prf_congr_bin {T x x' y y' : Term} (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (cons T (cons x (cons y nil)) =eq cons T (cons x' (cons y' nil))) :=
  prf_eq_trans (prf_congr_bin1 hx) (prf_congr_bin2 hy)

/-- Congruencia de `substfc` en arg2 (copia local privada; la pública vive en `ArithPrf`, posterior). -/
private theorem prf_congr_substfc_a2_loc {x z a b : Term} (h : Prf (a =eq b)) :
    Prf (substfc x a z =eq substfc x b z) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 x) (liftTerm 0 a) (liftTerm 0 z))
                                 (substfc (liftTerm 0 x) (.var 0) (liftTerm 0 z))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc x a z) (substfc x s z) := by
    intro s; simp only [f, substFormula, substfc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (substfc x a z))
/-- Congruencia de `substfc` en arg3 (copia local privada). -/
private theorem prf_congr_substfc_a3_loc {x t a b : Term} (h : Prf (a =eq b)) :
    Prf (substfc x t a =eq substfc x t b) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 x) (liftTerm 0 t) (liftTerm 0 a))
                                 (substfc (liftTerm 0 x) (liftTerm 0 t) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc x t a) (substfc x t s) := by
    intro s; simp only [f, substfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (substfc x t a))
/-- Congruencia de `liftfc` en arg2 (copia local privada). -/
private theorem prf_congr_liftfc_a2_loc {c a b : Term} (h : Prf (a =eq b)) :
    Prf (liftfc c a =eq liftfc c b) := by
  let f : Formula := Formula.eq (liftfc (liftTerm 0 c) (liftTerm 0 a)) (liftfc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftfc c a) (liftfc c s) := by
    intro s; simp only [f, liftfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (liftfc c a))

-- (los wrappers por‑constructor `prf_congr_implc`/`andc`/… se omiten: colisionan con copias
-- locales de módulos posteriores; las pruebas usan las genéricas `prf_congr_bin`/`prf_congr_un`.)

/-- Transporte de `lineWF L ⇔ (x =eq y)` por igualdades provables en ambos lados. Vale para los 21
    tags: `lineWF L` es un ÁTOMO (sin binders) ⟹ el cancel lift/subst va por `substTerm_liftTerm`
    (el cancel general a nivel fórmula es FALSO, ver `FOL/Theorems/Quantifiers.lean`). -/
theorem prf_lineWF_iff_transport {L x x' y y' : Term}
    (h : Prf (lineWF L ⇔ (x =eq y))) (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (lineWF L ⇔ (x' =eq y')) := by
  have h1 : Prf (lineWF L ⇔ (x' =eq y)) := by
    let A : Formula := iff (lineWF (liftTerm 0 L)) (Formula.eq (.var 0) (liftTerm 0 y))
    have hS : ∀ s : Term, substFormula 0 s A = iff (lineWF L) (Formula.eq s y) := by
      intro s
      simp only [A, iff, lineWF, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
    exact (hS x') ▸ prf_leibniz_subst (A := A) hx ((hS x) ▸ h)
  let B : Formula := iff (lineWF (liftTerm 0 L)) (Formula.eq (liftTerm 0 x') (.var 0))
  have hS : ∀ s : Term, substFormula 0 s B = iff (lineWF L) (Formula.eq x' s) := by
    intro s
    simp only [B, iff, lineWF, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y') ▸ prf_leibniz_subst (A := B) hy ((hS y) ▸ h1)


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
    Prf (lineWF (cons concl (cons (numeralM 17) (cons body (nil)))) ⇔
      (concl =eq forallc (body))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 17) (cons body (nil))))
  simp only [ax_lineWF_gen, substFormula, substTerm, substTerms, lineWF, carc, nthc, forallc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 17) (cons body (nil)))) (succ zero) =eq numeralM 17) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 17) (cons body (nil)))) =eq concl) := prf_carc_cons _ _
  have h_body : Prf (nthc (cons concl (cons (numeralM 17) (cons body (nil)))) (numeralM 2) =eq body) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_un (h_body))
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

/-- P1. Recuperado del axioma en forma de accesores (§44): instanciar en la línea explícita,
    descargar la hipótesis del tag (`nthc L 1 =eq 0`) por cómputo, y transportar los accesores
    (`carc L → concl`, `nthc L 2/3 → a/b`). -/
theorem prf_lineWF_p1 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 0) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b a))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 0) (cons a (cons b nil))))
  simp only [ax_lineWF_p1, substFormula, substTerm, substTerms, lineWF, carc, nthc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 0) (cons a (cons b nil)))) (succ zero)
      =eq numeralM 0) :=
    prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 0) (cons a (cons b nil)))) =eq concl) :=
    prf_carc_cons _ _
  have h2 : Prf (nthc (cons concl (cons (numeralM 0) (cons a (cons b nil)))) (numeralM 2) =eq a) :=
    prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h3 : Prf (nthc (cons concl (cons (numeralM 0) (cons a (cons b nil)))) (numeralM 3) =eq b) :=
    prf_eq_trans (prf_nthc_succ_loc _ _ _)
      (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin h2 (prf_congr_bin h3 h2))
theorem prf_premsOf_p1 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 0) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_p1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_p1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- P2. -/
theorem prf_lineWF_p2 (concl a b c : Term) :
    Prf (lineWF (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil)))))) ⇔
      (concl =eq implc (implc (a) (implc (b) (c))) (implc (implc (a) (b)) (implc (a) (c))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil))))))
  simp only [ax_lineWF_p2, substFormula, substTerm, substTerms, lineWF, carc, nthc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil)))))) (succ zero) =eq numeralM 1) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil)))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil)))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil)))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  have h_c : Prf (nthc (cons concl (cons (numeralM 1) (cons a (cons b (cons c (nil)))))) (numeralM 4) =eq c) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_bin (h_a) (prf_congr_bin (h_b) (h_c))) (prf_congr_bin (prf_congr_bin (h_a) (h_b)) (prf_congr_bin (h_a) (h_c))))
theorem prf_premsOf_p2 (concl a b c : Term) :
    Prf (premsOf (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_p2 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_premsOf_p2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- C1. -/
theorem prf_lineWF_c1 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 2) (cons a (cons b (nil))))) ⇔
      (concl =eq implc (a) (implc (b) (andc (a) (b))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 2) (cons a (cons b (nil)))))
  simp only [ax_lineWF_c1, substFormula, substTerm, substTerms, lineWF, carc, nthc, andc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 2) (cons a (cons b (nil))))) (succ zero) =eq numeralM 2) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 2) (cons a (cons b (nil))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 2) (cons a (cons b (nil))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 2) (cons a (cons b (nil))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (h_a) (prf_congr_bin (h_b) (prf_congr_bin (h_a) (h_b))))
theorem prf_premsOf_c1 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 2) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- C2. -/
theorem prf_lineWF_c2 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 3) (cons a (cons b (nil))))) ⇔
      (concl =eq implc (andc (a) (b)) (a))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 3) (cons a (cons b (nil)))))
  simp only [ax_lineWF_c2, substFormula, substTerm, substTerms, lineWF, carc, nthc, andc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 3) (cons a (cons b (nil))))) (succ zero) =eq numeralM 3) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 3) (cons a (cons b (nil))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 3) (cons a (cons b (nil))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 3) (cons a (cons b (nil))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_bin (h_a) (h_b)) (h_a))
theorem prf_premsOf_c2 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 3) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- C3. -/
theorem prf_lineWF_c3 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 4) (cons a (cons b (nil))))) ⇔
      (concl =eq implc (andc (a) (b)) (b))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 4) (cons a (cons b (nil)))))
  simp only [ax_lineWF_c3, substFormula, substTerm, substTerms, lineWF, carc, nthc, andc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 4) (cons a (cons b (nil))))) (succ zero) =eq numeralM 4) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 4) (cons a (cons b (nil))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 4) (cons a (cons b (nil))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 4) (cons a (cons b (nil))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_bin (h_a) (h_b)) (h_b))
theorem prf_premsOf_c3 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 4) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c3 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_c3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J1. -/
theorem prf_lineWF_j1 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 5) (cons a (cons b (nil))))) ⇔
      (concl =eq implc (a) (orc (a) (b)))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 5) (cons a (cons b (nil)))))
  simp only [ax_lineWF_j1, substFormula, substTerm, substTerms, lineWF, carc, nthc, implc, orc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 5) (cons a (cons b (nil))))) (succ zero) =eq numeralM 5) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 5) (cons a (cons b (nil))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 5) (cons a (cons b (nil))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 5) (cons a (cons b (nil))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (h_a) (prf_congr_bin (h_a) (h_b)))
theorem prf_premsOf_j1 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 5) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j1 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_j1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J2. -/
theorem prf_lineWF_j2 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 6) (cons a (cons b (nil))))) ⇔
      (concl =eq implc (b) (orc (a) (b)))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 6) (cons a (cons b (nil)))))
  simp only [ax_lineWF_j2, substFormula, substTerm, substTerms, lineWF, carc, nthc, implc, orc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 6) (cons a (cons b (nil))))) (succ zero) =eq numeralM 6) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 6) (cons a (cons b (nil))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 6) (cons a (cons b (nil))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 6) (cons a (cons b (nil))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (h_b) (prf_congr_bin (h_a) (h_b)))
theorem prf_premsOf_j2 (concl a b : Term) :
    Prf (premsOf (cons concl (cons (numeralM 6) (cons a (cons b nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j2 ∈ axioms by simp [axioms])) concl) a) b
  simp [ax_premsOf_j2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- J3. -/
theorem prf_lineWF_j3 (concl a b c : Term) :
    Prf (lineWF (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil)))))) ⇔
      (concl =eq implc (orc (a) (b)) (implc (implc (a) (c)) (implc (implc (b) (c)) (c))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil))))))
  simp only [ax_lineWF_j3, substFormula, substTerm, substTerms, lineWF, carc, nthc, implc, orc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil)))))) (succ zero) =eq numeralM 7) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil)))))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil)))))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_b : Prf (nthc (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil)))))) (numeralM 3) =eq b) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  have h_c : Prf (nthc (cons concl (cons (numeralM 7) (cons a (cons b (cons c (nil)))))) (numeralM 4) =eq c) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_bin (h_a) (h_b)) (prf_congr_bin (prf_congr_bin (h_a) (h_c)) (prf_congr_bin (prf_congr_bin (h_b) (h_c)) (h_c))))
theorem prf_premsOf_j3 (concl a b c : Term) :
    Prf (premsOf (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j3 ∈ axioms by simp [axioms])) concl) a) b) c
  simp [ax_premsOf_j3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- EFQ. -/
theorem prf_lineWF_efq (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 8) (cons a (nil)))) ⇔
      (concl =eq implc (botc) (a))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 8) (cons a (nil))))
  simp only [ax_lineWF_efq, substFormula, substTerm, substTerms, lineWF, carc, nthc, botc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 8) (cons a (nil)))) (succ zero) =eq numeralM 8) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 8) (cons a (nil)))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 8) (cons a (nil)))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_refl botc) (h_a))
theorem prf_premsOf_efq (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 8) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_efq ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_efq, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- EQREFL. -/
theorem prf_lineWF_eqrefl (concl t : Term) :
    Prf (lineWF (cons concl (cons (numeralM 12) (cons t (nil)))) ⇔
      (concl =eq eqc (t) (t))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 12) (cons t (nil))))
  simp only [ax_lineWF_eqrefl, substFormula, substTerm, substTerms, lineWF, carc, nthc, eqc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 12) (cons t (nil)))) (succ zero) =eq numeralM 12) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 12) (cons t (nil)))) =eq concl) := prf_carc_cons _ _
  have h_t : Prf (nthc (cons concl (cons (numeralM 12) (cons t (nil)))) (numeralM 2) =eq t) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (h_t) (h_t))
theorem prf_premsOf_eqrefl (concl t : Term) :
    Prf (premsOf (cons concl (cons (numeralM 12) (cons t nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_eqrefl ∈ axioms by simp [axioms])) concl) t
  simp [ax_premsOf_eqrefl, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- P3. -/
theorem prf_lineWF_p3 (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 14) (cons a (nil)))) ⇔
      (concl =eq implc (implc (implc (a) (botc)) (botc)) (a))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 14) (cons a (nil))))
  simp only [ax_lineWF_p3, substFormula, substTerm, substTerms, lineWF, carc, nthc, botc, implc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 14) (cons a (nil)))) (succ zero) =eq numeralM 14) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 14) (cons a (nil)))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 14) (cons a (nil)))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_bin (prf_congr_bin (h_a) (prf_refl botc)) (prf_refl botc)) (h_a))
theorem prf_premsOf_p3 (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 14) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_p3 ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_p3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### `lineWF`/`premsOf` de los esquemas de sustitución en `Prf` (porte de ProofChain) -/

/-- Q1. -/
theorem prf_lineWF_q1 (concl A t : Term) :
    Prf (lineWF (cons concl (cons (numeralM 9) (cons A (cons t (nil))))) ⇔
      (concl =eq implc (forallc (A)) (substfc (zero) (t) (A)))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 9) (cons A (cons t (nil)))))
  simp only [ax_lineWF_q1, substFormula, substTerm, substTerms, lineWF, carc, nthc, forallc, implc, substfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 9) (cons A (cons t (nil))))) (succ zero) =eq numeralM 9) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 9) (cons A (cons t (nil))))) =eq concl) := prf_carc_cons _ _
  have h_A : Prf (nthc (cons concl (cons (numeralM 9) (cons A (cons t (nil))))) (numeralM 2) =eq A) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_t : Prf (nthc (cons concl (cons (numeralM 9) (cons A (cons t (nil))))) (numeralM 3) =eq t) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_un (h_A)) (prf_eq_trans (prf_congr_substfc_a2_loc (h_t)) (prf_congr_substfc_a3_loc (h_A))))
theorem prf_premsOf_q1 (concl A t : Term) :
    Prf (premsOf (cons concl (cons (numeralM 9) (cons A (cons t nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q1 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_premsOf_q1, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- Q2. -/
theorem prf_lineWF_q2 (concl A t : Term) :
    Prf (lineWF (cons concl (cons (numeralM 10) (cons A (cons t (nil))))) ⇔
      (concl =eq implc (substfc (zero) (t) (A)) (exc (A)))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 10) (cons A (cons t (nil)))))
  simp only [ax_lineWF_q2, substFormula, substTerm, substTerms, lineWF, carc, nthc, exc, implc, substfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 10) (cons A (cons t (nil))))) (succ zero) =eq numeralM 10) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 10) (cons A (cons t (nil))))) =eq concl) := prf_carc_cons _ _
  have h_A : Prf (nthc (cons concl (cons (numeralM 10) (cons A (cons t (nil))))) (numeralM 2) =eq A) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_t : Prf (nthc (cons concl (cons (numeralM 10) (cons A (cons t (nil))))) (numeralM 3) =eq t) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_eq_trans (prf_congr_substfc_a2_loc (h_t)) (prf_congr_substfc_a3_loc (h_A))) (prf_congr_un (h_A)))
theorem prf_premsOf_q2 (concl A t : Term) :
    Prf (premsOf (cons concl (cons (numeralM 10) (cons A (cons t nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q2 ∈ axioms by simp [axioms])) concl) A) t
  simp [ax_premsOf_q2, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- Q3. -/
theorem prf_lineWF_q3 (concl A B : Term) :
    Prf (lineWF (cons concl (cons (numeralM 11) (cons A (cons B (nil))))) ⇔
      (concl =eq implc (forallc (implc (A) (liftfc (zero) (B)))) (implc (exc (A)) (B)))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 11) (cons A (cons B (nil)))))
  simp only [ax_lineWF_q3, substFormula, substTerm, substTerms, lineWF, carc, nthc, exc, forallc, implc, liftfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 11) (cons A (cons B (nil))))) (succ zero) =eq numeralM 11) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 11) (cons A (cons B (nil))))) =eq concl) := prf_carc_cons _ _
  have h_A : Prf (nthc (cons concl (cons (numeralM 11) (cons A (cons B (nil))))) (numeralM 2) =eq A) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_B : Prf (nthc (cons concl (cons (numeralM 11) (cons A (cons B (nil))))) (numeralM 3) =eq B) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_un (prf_congr_bin (h_A) (prf_congr_liftfc_a2_loc (h_B)))) (prf_congr_bin (prf_congr_un (h_A)) (h_B)))
theorem prf_premsOf_q3 (concl A B : Term) :
    Prf (premsOf (cons concl (cons (numeralM 11) (cons A (cons B nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q3 ∈ axioms by simp [axioms])) concl) A) B
  simp [ax_premsOf_q3, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

/-- LEIBNIZ. -/
theorem prf_lineWF_leibniz (concl A t1 t2 : Term) :
    Prf (lineWF (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil)))))) ⇔
      (concl =eq implc (eqc (t1) (t2)) (implc (substfc (zero) (t1) (A)) (substfc (zero) (t2) (A))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil))))))
  simp only [ax_lineWF_leibniz, substFormula, substTerm, substTerms, lineWF, carc, nthc, eqc, implc, substfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil)))))) (succ zero) =eq numeralM 13) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil)))))) =eq concl) := prf_carc_cons _ _
  have h_A : Prf (nthc (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil)))))) (numeralM 2) =eq A) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_t1 : Prf (nthc (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil)))))) (numeralM 3) =eq t1) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  have h_t2 : Prf (nthc (cons concl (cons (numeralM 13) (cons A (cons t1 (cons t2 (nil)))))) (numeralM 4) =eq t2) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_bin (h_t1) (h_t2)) (prf_congr_bin (prf_eq_trans (prf_congr_substfc_a2_loc (h_t1)) (prf_congr_substfc_a3_loc (h_A))) (prf_eq_trans (prf_congr_substfc_a2_loc (h_t2)) (prf_congr_substfc_a3_loc (h_A)))))
theorem prf_premsOf_leibniz (concl A t₁ t₂ : Term) :
    Prf (premsOf (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_leibniz ∈ axioms by simp [axioms])) concl) A) t₁) t₂
  simp [ax_premsOf_leibniz, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerm_liftLiftLiftLift] at hh
  exact hh

/-- IND (códigos cerrados `termCodeM`, gestionados por clausura como en `vpf_ind`). -/
theorem prf_lineWF_ind (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 18) (cons a (nil)))) ⇔
      (concl =eq implc (substfc (zero) (termCodeM zero) (a)) (implc (forallc (implc (a) (substfc (zero) (termCodeM (succ (.var 0))) (liftfc (succ zero) (a))))) (forallc (a))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_ind ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 18) (cons a (nil))))
  simp only [ax_lineWF_ind, substFormula, substTerm, substTerms, lineWF, carc, nthc, forallc, implc, liftfc, substfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 18) (cons a (nil)))) (succ zero) =eq numeralM 18) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 18) (cons a (nil)))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 18) (cons a (nil)))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have hy : Prf ((implc (substfc (zero) (termCodeM zero) (nthc (cons concl (cons (numeralM 18) (cons a (nil)))) (numeralM 2))) (implc (forallc (implc (nthc (cons concl (cons (numeralM 18) (cons a (nil)))) (numeralM 2)) (substfc (zero) (termCodeM (succ (.var 0))) (liftfc (succ zero) (nthc (cons concl (cons (numeralM 18) (cons a (nil)))) (numeralM 2)))))) (forallc (nthc (cons concl (cons (numeralM 18) (cons a (nil)))) (numeralM 2))))) =eq implc (substfc (zero) (termCodeM zero) (a)) (implc (forallc (implc (a) (substfc (zero) (termCodeM (succ (.var 0))) (liftfc (succ zero) (a))))) (forallc (a)))) :=
    prf_congr_bin (prf_congr_substfc_a3_loc (h_a)) (prf_congr_bin (prf_congr_un (prf_congr_bin (h_a) (prf_congr_substfc_a3_loc (prf_congr_liftfc_a2_loc (h_a))))) (prf_congr_un (h_a)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc hy
theorem prf_premsOf_ind (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 18) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_ind ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_ind, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- LISTIND (tag 20, [A]): inducción de listas, en `Prf`. -/
theorem prf_lineWF_listInd (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 20) (cons a (nil)))) ⇔
      (concl =eq implc (substfc (zero) (termCodeM nil) (a)) (implc (forallc (forallc (implc (liftfc (succ zero) (a)) (substfc (zero) (termCodeM (cons (.var 1) (.var 0))) (liftfc (succ (succ zero)) (liftfc (succ zero) (a))))))) (forallc (a))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_listInd ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 20) (cons a (nil))))
  simp only [ax_lineWF_listInd, substFormula, substTerm, substTerms, lineWF, carc, nthc, forallc, implc, liftfc, substfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 20) (cons a (nil)))) (succ zero) =eq numeralM 20) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 20) (cons a (nil)))) =eq concl) := prf_carc_cons _ _
  have h_a : Prf (nthc (cons concl (cons (numeralM 20) (cons a (nil)))) (numeralM 2) =eq a) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have hy : Prf ((implc (substfc (zero) (termCodeM nil) (nthc (cons concl (cons (numeralM 20) (cons a (nil)))) (numeralM 2))) (implc (forallc (forallc (implc (liftfc (succ zero) (nthc (cons concl (cons (numeralM 20) (cons a (nil)))) (numeralM 2))) (substfc (zero) (termCodeM (cons (.var 1) (.var 0))) (liftfc (succ (succ zero)) (liftfc (succ zero) (nthc (cons concl (cons (numeralM 20) (cons a (nil)))) (numeralM 2)))))))) (forallc (nthc (cons concl (cons (numeralM 20) (cons a (nil)))) (numeralM 2))))) =eq implc (substfc (zero) (termCodeM nil) (a)) (implc (forallc (forallc (implc (liftfc (succ zero) (a)) (substfc (zero) (termCodeM (cons (.var 1) (.var 0))) (liftfc (succ (succ zero)) (liftfc (succ zero) (a))))))) (forallc (a)))) :=
    prf_congr_bin (prf_congr_substfc_a3_loc (h_a)) (prf_congr_bin (prf_congr_un (prf_congr_un (prf_congr_bin (prf_congr_liftfc_a2_loc (h_a)) (prf_congr_substfc_a3_loc (prf_congr_liftfc_a2_loc (prf_congr_liftfc_a2_loc (h_a))))))) (prf_congr_un (h_a)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc hy
theorem prf_premsOf_listInd (concl a : Term) :
    Prf (premsOf (cons concl (cons (numeralM 20) (cons a nil))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_premsOf_listInd ∈ axioms by simp [axioms])) concl) a
  simp [ax_premsOf_listInd, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- QCONF (tag 19, [P,C]): confinamiento ∀, en `Prf`. -/
theorem prf_lineWF_qconf (concl P Cc : Term) :
    Prf (lineWF (cons concl (cons (numeralM 19) (cons P (cons Cc (nil))))) ⇔
      (concl =eq implc (forallc (implc (liftfc (zero) (P)) (Cc))) (implc (P) (forallc (Cc))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 19) (cons P (cons Cc (nil)))))
  simp only [ax_lineWF_qconf, substFormula, substTerm, substTerms, lineWF, carc, nthc, forallc, implc, liftfc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  have htag : Prf (nthc (cons concl (cons (numeralM 19) (cons P (cons Cc (nil))))) (succ zero) =eq numeralM 19) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)
  have hc : Prf (carc (cons concl (cons (numeralM 19) (cons P (cons Cc (nil))))) =eq concl) := prf_carc_cons _ _
  have h_P : Prf (nthc (cons concl (cons (numeralM 19) (cons P (cons Cc (nil))))) (numeralM 2) =eq P) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _))
  have h_Cc : Prf (nthc (cons concl (cons (numeralM 19) (cons P (cons Cc (nil))))) (numeralM 3) =eq Cc) := prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_eq_trans (prf_nthc_succ_loc _ _ _) (prf_nthc_zero_loc _ _)))
  exact prf_lineWF_iff_transport (prf_mp hax htag) hc (prf_congr_bin (prf_congr_un (prf_congr_bin (prf_congr_liftfc_a2_loc (h_P)) (h_Cc))) (prf_congr_bin (h_P) (prf_congr_un (h_Cc))))
theorem prf_premsOf_qconf (concl P C : Term) :
    Prf (premsOf (cons concl (cons (numeralM 19) (cons P (cons C nil)))) =eq nil) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_qconf ∈ axioms by simp [axioms])) concl) P) C
  simp [ax_premsOf_qconf, substFormula, substTerm, substTerms, premsOf, numeralM, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift] at hh
  exact hh

end ROBINSON_PlusPlus.Meta.ReprPrf

export ROBINSON_PlusPlus.Meta.ReprPrf (
  prf_congr_bin1 prf_congr_bin2 prf_congr_un prf_congr_bin
  prf_lineWF_iff_transport
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
  prf_lineWF_listInd
  prf_premsOf_listInd
  prf_lineWF_qconf
  prf_premsOf_qconf
)

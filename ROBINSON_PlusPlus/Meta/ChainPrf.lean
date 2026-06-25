/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.HilbertDeduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ChainPrf

/-!
## META — NIVEL D real: lemas de cadena a nivel `Prf` (paso 8)

Port de los lemas de compositividad/monotonía de cadenas (`runFn_concat`,
`chainOk_concat`, `In_mono`, …) al cálculo finitario `Prf`, usando la regla
`Prf.listInd` (inducción de listas) vía el eliminador `prf_list_induction`.
Son los ingredientes de `d2_prf` (concatenación de pruebas + `mp` interno).
-/

/-- **Eliminador de inducción de listas en `Prf`**: de `Prf (Φ[nil])` y
    `Prf (∀h∀t (Φ[t] ⇒ Φ[cons h t]))` sale `Prf (∀L Φ[L])`. -/
theorem prf_list_induction (Φ : Formula)
    (base : Prf (substFormula 0 nil Φ))
    (step : Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 Φ)
              (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 Φ)))))))
    : Prf (Formula.forall Φ) :=
  prf_mp (prf_mp (Prf.listInd Φ) base) step

/-! ### Helpers ecuacionales a nivel `PrfH` (para los cuerpos del `step`, que usan la IH) -/

/-- Leibniz en `PrfH`: de `PrfH Γ (t₁ ≐ t₂)` y `PrfH Γ A[t₁]` sale `PrfH Γ A[t₂]`. -/
theorem PrfH_leibniz_subst {Γ : List Formula} {A : Formula} {t₁ t₂ : Term}
    (h : PrfH Γ (t₁ =eq t₂)) (hA : PrfH Γ (substFormula 0 t₁ A)) : PrfH Γ (substFormula 0 t₂ A) :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.leibniz A t₁ t₂)) h) hA

/-- Transitividad de `=eq` en `PrfH`. -/
theorem PrfH_eq_trans {Γ : List Formula} {a b c : Term}
    (h1 : PrfH Γ (a =eq b)) (h2 : PrfH Γ (b =eq c)) : PrfH Γ (a =eq c) := by
  let f : Formula := Formula.eq (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq a s := by
    intro s; simp only [f, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c) ▸ PrfH_leibniz_subst (A := f) h2 ((hS b) ▸ h1)

/-- Congruencia de `cons` en la cola, en `PrfH`. -/
theorem PrfH_congr_cons_tail {Γ : List Formula} {hd t₁ t₂ : Term}
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (cons hd t₁ =eq cons hd t₂) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 hd) (liftTerm 0 t₁)) (cons (liftTerm 0 hd) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons hd t₁) (cons hd s) := by
    intro s; simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (cons hd t₁)) Γ)

/-- Sustitución bajo `In` (2º arg) en `PrfH`. -/
theorem PrfH_eq_subst_in {Γ : List Formula} {x t₁ t₂ : Term}
    (h : PrfH Γ (t₁ =eq t₂)) (hin : PrfH Γ (In x t₁)) : PrfH Γ (In x t₂) := by
  let f : Formula := In (liftTerm 0 x) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = In x s := by
    intro s; simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ hin)

/-- `In x t → In x (cons hd t)` en `PrfH` (vía `ax_L2` + `j2` + `iff` mpr). -/
theorem PrfH_in_cons_tail {Γ : List Formula} (hd : Term) {x t : Term} (hx : PrfH Γ (In x t)) :
    PrfH Γ (In x (cons hd t)) := by
  have hiff : Prf (In x (cons hd t) ⇔ lor (x =eq hd) (In x t)) := by
    have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_L2_in_cons ∈ axioms by simp [axioms])) x) hd) t
    simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  have hor : PrfH Γ (lor (x =eq hd) (In x t)) :=
    PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.j2 (x =eq hd) (In x t))) hx
  exact PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.c3 _ _)) (prf_to_prfH hiff Γ)) hor

/-- Normalización De Bruijn: `subst 0 s (lift 2 (lift 1 (lift 0 t))) = lift 1 (lift 0 t)`.
    (El parámetro externo `t`, doblemente protegido bajo dos binders del `step`, vuelve
    intacto tras la sustitución del `cons #1 #0`.) -/
theorem norm21 (s t : Term) :
    substTerm 0 s (liftTerm 2 (liftTerm 1 (liftTerm 0 t)))
      = liftTerm 1 (liftTerm 0 t) := by
  have e1 : liftTerm 1 (liftTerm 0 t) = liftTerm 0 (liftTerm 0 t) :=
    (FOL.liftTerm_comm_zero t 0).symm
  have e2 : liftTerm 2 (liftTerm 0 (liftTerm 0 t))
      = liftTerm 0 (liftTerm 1 (liftTerm 0 t)) :=
    (FOL.liftTerm_comm_zero (liftTerm 0 t) 1).symm
  calc substTerm 0 s (liftTerm 2 (liftTerm 1 (liftTerm 0 t)))
      = substTerm 0 s (liftTerm 2 (liftTerm 0 (liftTerm 0 t))) := by rw [e1]
    _ = substTerm 0 s (liftTerm 0 (liftTerm 1 (liftTerm 0 t))) := by rw [e2]
    _ = liftTerm 1 (liftTerm 0 t) := FOL.substTerm_liftTerm _ 0 _

/-! ### Lemas de cadena en `Prf` -/

/-- `concat X nil =eq X` en `Prf` (inducción de listas sobre `X`). -/
theorem prf_concat_nil_right (X : Term) : Prf (concat X nil =eq X) := by
  have key : Prf (Formula.forall (Formula.eq (concat (.var 0) nil) (.var 0))) := by
    refine prf_list_induction (Formula.eq (concat (.var 0) nil) (.var 0)) ?base ?step
    · show Prf (concat nil nil =eq nil); exact prf_concat_nil_eq nil
    · refine Prf.gen _ (Prf.gen _ ?_)
      show Prf (Formula.impl (Formula.eq (concat (.var 0) nil) (.var 0))
        (Formula.eq (concat (cons (.var 1) (.var 0)) nil) (cons (.var 1) (.var 0))))
      refine prf_deduction ?_
      have IH : PrfH [Formula.eq (concat (.var 0) nil) (.var 0)]
          (concat (.var 0) nil =eq (.var 0)) := prfH_hyp_self _
      have hcc : PrfH [Formula.eq (concat (.var 0) nil) (.var 0)]
          (concat (cons (.var 1) (.var 0)) nil =eq cons (.var 1) (concat (.var 0) nil)) :=
        prf_to_prfH (prf_concat_cons_eq (.var 1) (.var 0) nil) _
      exact PrfH_eq_trans hcc (PrfH_congr_cons_tail IH)
  have hX := prf_spec key X
  show Prf (concat X nil =eq X)
  simpa [substFormula, substTerm, substTerms, concat, nil, FOL.substTerm_liftTerm] using hX

/-- **Monotonía de `In` (contexto izq.)** en `Prf`: `Prf (In x c) → Prf (In x (concat c0 c))`.
    Inducción de listas sobre `c0`; `x`,`c` van con `liftTerm 0` (evitan capturar el
    slot de la lista). -/
theorem prf_In_mono (x c c0 : Term) (h : Prf (In x c)) : Prf (In x (concat c0 c)) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 x) (liftTerm 0 c))
      (In (liftTerm 0 x) (concat (.var 0) (liftTerm 0 c))))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (In x c) (In x (concat nil c))) :=
        prf_deduction (PrfH_eq_subst_in
          (prf_to_prfH (prf_eq_symm (prf_concat_nil_eq c)) _) (prfH_hyp_self _))
      simpa only [substFormula, substTerm, substTerms, In, concat, nil, FOL.substTerm_liftTerm] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        In, concat, cons, nil, norm21]
      refine prf_deduction (deduction_aux ?_
        (In (liftTerm 1 (liftTerm 0 x)) (liftTerm 1 (liftTerm 0 c)))
        [Formula.impl (In (liftTerm 1 (liftTerm 0 x)) (liftTerm 1 (liftTerm 0 c)))
            (In (liftTerm 1 (liftTerm 0 x)) (concat (.var 0) (liftTerm 1 (liftTerm 0 c))))] rfl)
      let A : Formula := In (liftTerm 1 (liftTerm 0 x)) (liftTerm 1 (liftTerm 0 c))
      let P : Formula := Formula.impl A
        (In (liftTerm 1 (liftTerm 0 x)) (concat (.var 0) (liftTerm 1 (liftTerm 0 c))))
      have hin : PrfH [A, P] A := PrfH.hyp _ _ (List.Mem.head _)
      have IH : PrfH [A, P] P := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hInt := PrfH.mp _ _ _ IH hin
      have hcons := PrfH_in_cons_tail (.var 1) hInt
      exact PrfH_eq_subst_in
        (prf_to_prfH (prf_eq_symm (prf_concat_cons_eq (.var 1) (.var 0) (liftTerm 1 (liftTerm 0 c)))) _) hcons
  have hkey := prf_spec key c0
  have hk2 : Prf (Formula.impl (In x c) (In x (concat c0 c))) := by
    simpa only [substFormula, substTerm, substTerms, In, concat, FOL.substTerm_liftTerm] using hkey
  exact prf_mp hk2 h

/-! ### Andamiaje para los lemas con acumulador `∀c` interno (frontera D2)

Los lemas restantes de la cadena (`runFn_concat`, `chainOk_concat`, `chainOk_mono`)
generalizan el acumulador como `∀c` **dentro** del predicado inductivo `Φ`. A nivel
`Prf`, eso anida TRES binders en el `step` del eliminador (dos del esquema de listas
`#1`/`#0` + el `∀c` interno), produciendo objetivos enormes que requieren una familia
de lemas de normalización De Bruijn de varios niveles (más allá de `norm21`). Se deja
el helper `PrfH_spec` (∀-elim en `PrfH`) ya verificado para retomar esa frontera. -/

/-- `∀-elim` en `PrfH` (vía `Prf₀.q1` + `mp`). Helper para la HI-`∀c` del `step`. -/
theorem PrfH_spec {Γ : List Formula} {A : Formula} (h : PrfH Γ (Formula.forall A)) (t : Term) :
    PrfH Γ (substFormula 0 t A) :=
  PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.q1 A t)) h

end ROBINSON_PlusPlus.Meta.ChainPrf

export ROBINSON_PlusPlus.Meta.ChainPrf
  (prf_list_induction prf_concat_nil_right prf_In_mono)

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

/-! ### Normalización De Bruijn de profundidad 2 (frontera `∀c` interno)

`norm32`: el parámetro, doblemente protegido (`liftTerm 0 (liftTerm 0 t)`, vars ≥2) y elevado
por el `step` del eliminador (`liftTerm 3 (liftTerm 2 ·)`), vuelve intacto tras
`substTerm 1 (cons #2 #1)` (la var 1 nunca se alcanza). Es la generalización a profundidad 2
de `norm21` y **destraba todos los lemas de cadena con `∀c` interno** (que tienen exactamente
un binder interno → profundidad 2). Prueba por inducción mutua término/lista. -/
mutual
theorem norm32 (z t : Term) :
    substTerm 1 z (liftTerm 3 (liftTerm 2 (liftTerm 0 (liftTerm 0 t))))
      = liftTerm 2 (liftTerm 0 (liftTerm 0 t)) := by
  cases t with
  | var n =>
      simp only [liftTerm, substTerm,
        show ¬ (n < 0) from by omega, show ¬ (n + 1 < 0) from by omega,
        show ¬ (n + 1 + 1 < 2) from by omega, show ¬ (n + 1 + 1 + 1 < 3) from by omega,
        show ¬ (n + 1 + 1 + 1 + 1 = 1) from by omega, show n + 1 + 1 + 1 + 1 > 1 from by omega,
        if_false, if_true]
      congr 1
  | func f ts => simp only [liftTerm, substTerm]; congr 1; exact norm32_terms z ts
theorem norm32_terms (z : Term) (ts : List Term) :
    substTerms 1 z (liftTerms 3 (liftTerms 2 (liftTerms 0 (liftTerms 0 ts))))
      = liftTerms 2 (liftTerms 0 (liftTerms 0 ts)) := by
  cases ts with
  | nil => rfl
  | cons a as =>
      simp only [liftTerms, substTerms]; rw [norm32 z a, norm32_terms z as]
end

/-- Normalización del parámetro `s` tras el `∀-elim` de la HI sobre el acumulador cambiado:
    el lift extra introducido por `liftFormula 0` (confinación) se cancela con el `substTerm 0`
    del `spec`. -/
theorem norm_s (z s : Term) :
    substTerm 0 z (liftTerm 1 (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))
      = liftTerm 2 (liftTerm 0 (liftTerm 0 s)) := by
  have hW : liftTerm 2 (liftTerm 0 (liftTerm 0 s)) = liftTerm 0 (liftTerm 1 (liftTerm 0 s)) :=
    (FOL.liftTerm_comm_zero (liftTerm 0 s) 1).symm
  calc substTerm 0 z (liftTerm 1 (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))
      = substTerm 0 z (liftTerm 1 (liftTerm 0 (liftTerm 1 (liftTerm 0 s)))) := by rw [hW]
    _ = substTerm 0 z (liftTerm 0 (liftTerm 0 (liftTerm 1 (liftTerm 0 s)))) := by
          rw [(FOL.liftTerm_comm_zero (liftTerm 1 (liftTerm 0 s)) 0).symm]
    _ = liftTerm 0 (liftTerm 1 (liftTerm 0 s)) := FOL.substTerm_liftTerm _ 0 z
    _ = liftTerm 2 (liftTerm 0 (liftTerm 0 s)) := hW.symm

/-! ### Helpers `PrfH` de conjunción / bicondicional -/

theorem PrfH_and_intro {Γ : List Formula} {A B : Formula} (ha : PrfH Γ A) (hb : PrfH Γ B) :
    PrfH Γ (land A B) :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.c1 A B)) ha) hb

theorem PrfH_and_elim_left {Γ : List Formula} {A B : Formula} (h : PrfH Γ (land A B)) : PrfH Γ A :=
  PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.c2 A B)) h

theorem PrfH_and_elim_right {Γ : List Formula} {A B : Formula} (h : PrfH Γ (land A B)) : PrfH Γ B :=
  PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.c3 A B)) h

/-- `iff`-mp con un bicondicional **cerrado** (`Prf`) y una hipótesis `PrfH`. -/
theorem PrfH_iff_mp {Γ : List Formula} {A B : Formula} (hiff : Prf (A ⇔ B)) (ha : PrfH Γ A) :
    PrfH Γ B :=
  PrfH.mp Γ _ _ (prf_to_prfH (prf_and_elim_left hiff) Γ) ha

theorem PrfH_iff_mpr {Γ : List Formula} {A B : Formula} (hiff : Prf (A ⇔ B)) (hb : PrfH Γ B) :
    PrfH Γ A :=
  PrfH.mp Γ _ _ (prf_to_prfH (prf_and_elim_right hiff) Γ) hb

/-- Simetría de `=eq` en `PrfH`. -/
theorem PrfH_eq_symm {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) : PrfH Γ (b =eq a) := by
  let f : Formula := Formula.eq (.var 0) (liftTerm 0 a)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq s a := by
    intro s; simp only [f, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl a) Γ)

/-- Congruencia de `concat` en el 2º argumento, en `PrfH`. -/
theorem PrfH_congr_concat_left {Γ : List Formula} {u t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (concat u t₁ =eq concat u t₂) := by
  let f : Formula := Formula.eq (concat (liftTerm 0 u) (liftTerm 0 t₁)) (concat (liftTerm 0 u) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (concat u t₁) (concat u s) := by
    intro s; simp only [f, substFormula, concat, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (concat u t₁)) Γ)

/-- Congruencia de `chainOk` en el 1er argumento (acumulador), en `PrfH`. -/
theorem PrfH_chainOk_subst1 {Γ : List Formula} {c₁ c₂ p : Term} (h : PrfH Γ (c₁ =eq c₂))
    (hok : PrfH Γ (chainOk c₁ p)) : PrfH Γ (chainOk c₂ p) := by
  let f : Formula := chainOk (.var 0) (liftTerm 0 p)
  have hS : ∀ s : Term, substFormula 0 s f = chainOk s p := by
    intro s; simp only [f, chainOk, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ PrfH_leibniz_subst (A := f) h ((hS c₁) ▸ hok)

/-- Congruencia de `chainOk` en el 2º argumento (cadena), en `PrfH`. -/
theorem PrfH_chainOk_subst2 {Γ : List Formula} {c p₁ p₂ : Term} (h : PrfH Γ (p₁ =eq p₂))
    (hok : PrfH Γ (chainOk c p₁)) : PrfH Γ (chainOk c p₂) := by
  let f : Formula := chainOk (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = chainOk c s := by
    intro s; simp only [f, chainOk, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS p₂) ▸ PrfH_leibniz_subst (A := f) h ((hS p₁) ▸ hok)

/-- Congruencia de `allIn` en el 2º argumento (lista), en `PrfH`. -/
theorem PrfH_allIn_subst2 {Γ : List Formula} {c L₁ L₂ : Term} (h : PrfH Γ (L₁ =eq L₂))
    (hok : PrfH Γ (allIn c L₁)) : PrfH Γ (allIn c L₂) := by
  let f : Formula := allIn (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = allIn c s := by
    intro s; simp only [f, allIn, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS L₂) ▸ PrfH_leibniz_subst (A := f) h ((hS L₁) ▸ hok)

/-- `In x t → In x (cons hd t)` ya estaba; aquí `In x (cons x t)` en `PrfH`. -/
theorem PrfH_in_cons_head {Γ : List Formula} (x t : Term) : PrfH Γ (In x (cons x t)) :=
  prf_to_prfH (prf_in_cons_head x t) Γ

/-! ### Lemas de cadena en `Prf` -/

/-- Congruencia de `concat` en el 1er argumento. -/
theorem prf_congr_concat_first {u₁ u₂ t : Term} (h : Prf (u₁ =eq u₂)) :
    Prf (concat u₁ t =eq concat u₂ t) := by
  let f : Formula := Formula.eq (concat (liftTerm 0 u₁) (liftTerm 0 t)) (concat (.var 0) (liftTerm 0 t))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (concat u₁ t) (concat s t) := by
    intro s; simp only [f, substFormula, concat, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS u₂) ▸ prf_leibniz_subst (A := f) h ((hS u₁) ▸ prf_refl (concat u₁ t))

/-- **Asociatividad de `concat` en `Prf`**: `(L ++ M) ++ N =eq L ++ (M ++ N)`.
    Inducción de listas sobre `L` (profundidad 1; `M`,`N` con `liftTerm 0`, normaliza con `norm21`). -/
theorem prf_concat_assoc (M N L : Term) :
    Prf (concat (concat L M) N =eq concat L (concat M N)) := by
  have key : Prf (Formula.forall (Formula.eq
      (concat (concat (.var 0) (liftTerm 0 M)) (liftTerm 0 N))
      (concat (.var 0) (concat (liftTerm 0 M) (liftTerm 0 N))))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (concat (concat nil M) N =eq concat nil (concat M N)) :=
        prf_eq_trans (prf_congr_concat_first (prf_concat_nil_eq M))
          (prf_eq_symm (prf_concat_nil_eq (concat M N)))
      simpa only [substFormula, substTerm, substTerms, concat, nil, zero, if_true,
        FOL.substTerm_liftTerm] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        concat, cons, nil, norm21]
      refine prf_deduction ?_
      have IH : PrfH _ (concat (concat (.var 0) (liftTerm 1 (liftTerm 0 M))) (liftTerm 1 (liftTerm 0 N))
          =eq concat (.var 0) (concat (liftTerm 1 (liftTerm 0 M)) (liftTerm 1 (liftTerm 0 N)))) :=
        prfH_hyp_self _
      -- LHS: concat (concat (cons #1 #0) Mc) Nc → cons #1 (concat (concat #0 Mc) Nc)
      refine PrfH_eq_trans (PrfH_eq_trans
        (prf_to_prfH (prf_congr_concat_first (t := liftTerm 1 (liftTerm 0 N))
          (prf_concat_cons_eq (.var 1) (.var 0) (liftTerm 1 (liftTerm 0 M)))) _)
        (prf_to_prfH (prf_concat_cons_eq (.var 1)
          (concat (.var 0) (liftTerm 1 (liftTerm 0 M))) (liftTerm 1 (liftTerm 0 N))) _))
        (PrfH_eq_trans (PrfH_congr_cons_tail IH) (prf_to_prfH (prf_eq_symm
          (prf_concat_cons_eq (.var 1) (.var 0)
            (concat (liftTerm 1 (liftTerm 0 M)) (liftTerm 1 (liftTerm 0 N))))) _))
  have hL := prf_spec key L
  simpa only [substFormula, substTerm, substTerms, concat, if_true, FOL.substTerm_liftTerm] using hL

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
  simpa [substFormula, substTerm, substTerms, concat, nil, zero, FOL.substTerm_liftTerm] using hX

/-- **Monotonía de `In` (contexto izq.)** en `Prf`: `Prf (In x c) → Prf (In x (concat c0 c))`.
    Inducción de listas sobre `c0`; `x`,`c` van con `liftTerm 0` (evitan capturar el
    slot de la lista). -/
theorem prf_In_mono_imp (x c c0 : Term) : Prf (Formula.impl (In x c) (In x (concat c0 c))) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 x) (liftTerm 0 c))
      (In (liftTerm 0 x) (concat (.var 0) (liftTerm 0 c))))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (In x c) (In x (concat nil c))) :=
        prf_deduction (PrfH_eq_subst_in
          (prf_to_prfH (prf_eq_symm (prf_concat_nil_eq c)) _) (prfH_hyp_self _))
      simpa only [substFormula, substTerm, substTerms, In, concat, nil, zero, if_true,
        FOL.substTerm_liftTerm] using hb
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
  simpa only [substFormula, substTerm, substTerms, In, concat, if_true, FOL.substTerm_liftTerm] using hkey

theorem prf_In_mono (x c c0 : Term) (h : Prf (In x c)) : Prf (In x (concat c0 c)) :=
  prf_mp (prf_In_mono_imp x c c0) h

/-- Eliminación de la disyunción en `PrfH` (vía `Prf₀.j3` + teorema de deducción). -/
theorem PrfH_or_elim {Γ : List Formula} {A B C : Formula} (hor : PrfH Γ (lor A B))
    (hA : PrfH (A :: Γ) C) (hB : PrfH (B :: Γ) C) : PrfH Γ C :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.j3 A B C)) hor)
    (deduction_aux hA A Γ rfl)) (deduction_aux hB B Γ rfl)

/-- Congruencia de `cons` en la cabeza, en `PrfH`. -/
theorem PrfH_congr_cons_head {Γ : List Formula} {hd₁ hd₂ t : Term}
    (h : PrfH Γ (hd₁ =eq hd₂)) : PrfH Γ (cons hd₁ t =eq cons hd₂ t) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 hd₁) (liftTerm 0 t)) (cons (.var 0) (liftTerm 0 t))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons hd₁ t) (cons s t) := by
    intro s; simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS hd₂) ▸ PrfH_leibniz_subst (A := f) h ((hS hd₁) ▸ prf_to_prfH (prf_refl (cons hd₁ t)) Γ)

/-- `In x (cons hd t)` se descompone en `(x =eq hd) ∨ In x t` (cierre `Prf` de `ax_L2`). -/
theorem prf_in_cons_iff (x hd t : Term) :
    Prf (In x (cons hd t) ⇔ lor (x =eq hd) (In x t)) := by
  have hh := prf_spec (prf_spec (prf_spec (prf_ax (show ax_L2_in_cons ∈ axioms by simp [axioms])) x) hd) t
  simp [substFormula, substTerm, substTerms, In, cons, zero, nil, lor, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- `In x nil ⇒ ⊥` (cierre `Prf` de `ax_L1`). -/
theorem prf_not_in_nil (x : Term) : Prf (Formula.impl (In x nil) Formula.bottom) := by
  have hh := prf_spec (prf_ax (show ax_L1_in_nil ∈ axioms by simp [axioms])) x
  simp [ax_L1_in_nil, substFormula, substTerm, substTerms, In, neg, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- **Monotonía de `In` por la derecha** en `Prf`: `Prf (In x L) → Prf (In x (concat L M))`.
    Inducción de listas sobre `L`; `base` vía explosión (`In x nil` es falso), `step`
    vía `or_elim` sobre la descomposición de `ax_L2`. -/
theorem prf_In_mono_right_imp (x M L : Term) :
    Prf (Formula.impl (In x L) (In x (concat L M))) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 x) (.var 0))
      (In (liftTerm 0 x) (concat (.var 0) (liftTerm 0 M))))) := by
    refine prf_list_induction _ ?base ?step
    · -- base: In x nil ⇒ In x (concat nil M) (vacío, por explosión)
      have hb : Prf (Formula.impl (In x nil) (In x (concat nil M))) := by
        refine prf_deduction ?_
        exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq (In x (concat nil M))))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil x) _) (prfH_hyp_self _))
      simpa only [substFormula, substTerm, substTerms, In, concat, nil, zero, if_true,
        FOL.substTerm_liftTerm] using hb
    · -- step
      refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        In, concat, cons, nil, norm21]
      refine prf_deduction (deduction_aux ?_
        (In (liftTerm 1 (liftTerm 0 x)) (cons (.var 1) (.var 0)))
        [Formula.impl (In (liftTerm 1 (liftTerm 0 x)) (.var 0))
            (In (liftTerm 1 (liftTerm 0 x)) (concat (.var 0) (liftTerm 1 (liftTerm 0 M))))] rfl)
      let X : Term := liftTerm 1 (liftTerm 0 x)
      let Mc : Term := liftTerm 1 (liftTerm 0 M)
      let IHf : Formula := Formula.impl (In X (.var 0)) (In X (concat (.var 0) Mc))
      let A : Formula := In X (cons (.var 1) (.var 0))
      -- objetivo: PrfH [A, IHf] (In X (concat (cons #1 #0) Mc))
      refine PrfH_eq_subst_in
        (prf_to_prfH (prf_eq_symm (prf_concat_cons_eq (.var 1) (.var 0) Mc)) _) ?_
      -- ahora: In X (cons #1 (concat #0 Mc))
      have hsplit : PrfH [A, IHf] (lor (X =eq (.var 1)) (In X (.var 0))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_iff X (.var 1) (.var 0))) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · -- caso X =eq #1 : cabeza
        have hxhd : PrfH ((X =eq (.var 1)) :: [A, IHf]) (X =eq (.var 1)) :=
          PrfH.hyp _ _ (List.Mem.head _)
        have hhead : PrfH ((X =eq (.var 1)) :: [A, IHf]) (In X (cons X (concat (.var 0) Mc))) :=
          prf_to_prfH (prf_in_cons_head X (concat (.var 0) Mc)) _
        exact PrfH_eq_subst_in (PrfH_congr_cons_head hxhd) hhead
      · -- caso In X #0 : cola, vía IH
        have hin : PrfH ((In X (.var 0)) :: [A, IHf]) (In X (.var 0)) :=
          PrfH.hyp _ _ (List.Mem.head _)
        have hIH : PrfH ((In X (.var 0)) :: [A, IHf]) IHf :=
          PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        exact PrfH_in_cons_tail (.var 1) (PrfH.mp _ _ _ hIH hin)
  have hkey := prf_spec key L
  simpa only [substFormula, substTerm, substTerms, In, concat, if_true, FOL.substTerm_liftTerm] using hkey

theorem prf_In_mono_right (x M L : Term) (h : Prf (In x L)) : Prf (In x (concat L M)) :=
  prf_mp (prf_In_mono_right_imp x M L) h

/-- **Monotonía de `allIn` (contexto izq.)** en `Prf` (implicación): `allIn c M ⇒ allIn (c0 ++ c) M`.
    Inducción sobre `M`; usa `prf_In_mono_imp`. -/
theorem prf_allIn_mono_imp (c c0 M : Term) :
    Prf (Formula.impl (allIn c M) (allIn (concat c0 c) M)) := by
  have key : Prf (Formula.forall (Formula.impl
      (allIn (liftTerm 0 c) (.var 0))
      (allIn (concat (liftTerm 0 c0) (liftTerm 0 c)) (.var 0)))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (allIn c nil) (allIn (concat c0 c) nil)) :=
        prf_deduction (prf_to_prfH (prf_allIn_nil (concat c0 c)) _)
      simpa only [substFormula, substTerm, substTerms, allIn, concat, nil, zero, if_true,
        FOL.substTerm_liftTerm] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        allIn, concat, cons, nil, norm21]
      refine prf_deduction (deduction_aux ?_
        (allIn (liftTerm 1 (liftTerm 0 c)) (cons (.var 1) (.var 0)))
        [Formula.impl (allIn (liftTerm 1 (liftTerm 0 c)) (.var 0))
            (allIn (concat (liftTerm 1 (liftTerm 0 c0)) (liftTerm 1 (liftTerm 0 c))) (.var 0))] rfl)
      let Cs : Term := liftTerm 1 (liftTerm 0 c)
      let C0s : Term := liftTerm 1 (liftTerm 0 c0)
      let A : Formula := allIn Cs (cons (.var 1) (.var 0))
      let IHf : Formula := Formula.impl (allIn Cs (.var 0)) (allIn (concat C0s Cs) (.var 0))
      have hsplit : PrfH [A, IHf] (land (In (.var 1) Cs) (allIn Cs (.var 0))) :=
        PrfH_iff_mp (prf_allIn_cons Cs (.var 1) (.var 0)) (PrfH.hyp _ _ (List.Mem.head _))
      have hIn : PrfH [A, IHf] (In (.var 1) (concat C0s Cs)) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_In_mono_imp (.var 1) Cs C0s) _) (PrfH_and_elim_left hsplit)
      have hrest : PrfH [A, IHf] (allIn (concat C0s Cs) (.var 0)) :=
        PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) (PrfH_and_elim_right hsplit)
      exact PrfH_iff_mpr (prf_allIn_cons (concat C0s Cs) (.var 1) (.var 0))
        (PrfH_and_intro hIn hrest)
  have hkey := prf_spec key M
  simpa only [substFormula, substTerm, substTerms, allIn, concat, if_true, FOL.substTerm_liftTerm] using hkey

/-- **Monotonía de `lineOk` (contexto izq.)** en `Prf` (implicación):
    `lineOk c line ⇒ lineOk (c0 ++ c) line` (la parte `lineWF` es independiente del contexto). -/
theorem prf_lineOk_mono_imp (c c0 line : Term) :
    Prf (Formula.impl (lineOk c line) (lineOk (concat c0 c) line)) := by
  refine prf_deduction ?_
  refine PrfH_and_intro (PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))) ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_allIn_mono_imp c c0 (premsOf line)) _)
    (PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _)))

/-- Congruencia de `chainOk` en el 2º argumento (cadena). -/
theorem prf_chainOk_subst2 {c p₁ p₂ : Term} (h : Prf (p₁ =eq p₂)) (hok : Prf (chainOk c p₁)) :
    Prf (chainOk c p₂) := by
  let f : Formula := chainOk (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = chainOk c s := by
    intro s; simp only [f, chainOk, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS p₂) ▸ prf_leibniz_subst (A := f) h ((hS p₁) ▸ hok)

/-! ### Lemas de cadena con acumulador `∀c` interno (compositividad de `runFn`)

Los lemas `runFn_concat`/`chainOk_concat`/`chainOk_mono` generalizan el acumulador como
`∀c` **dentro** del predicado inductivo `Φ`. A nivel `Prf`, eso anida TRES binders en el
`step` del eliminador (dos del esquema de listas `#1`/`#0` + el `∀c` interno). El patrón
(**resuelto de raíz**) es:

1. **Normalización De Bruijn de profundidad 2** (`norm32` + `norm_s`): cancela los lifts que
   el `step` y la confinación introducen sobre el parámetro doblemente protegido.
2. **Confinación (`qconf`)**: el objetivo `(∀c. IH[c]) ⇒ (∀c. Concl[c])` es exactamente el RHS
   de `confinementFormula (∀c.IH) Concl` (la IH no contiene `c`), reducido a probar
   `∀c. (↑IH ⇒ Concl[c])` vía `Prf.gen` + `prf_deduction`.
3. **`PrfH_spec`** (∀-elim en `PrfH`) instancia la HI-`∀c` al acumulador cambiado dentro del
   cuerpo; el `substFormula` del `spec` cancela el lift de la confinación (`norm_s`).

`prf_runFn_concat` valida el patrón end-to-end. `chainOk_concat`/`chainOk_mono` lo reutilizan
(misma profundidad 2, mismos `norm32`/`norm_s`). -/

/-- `∀-elim` en `PrfH` (vía `Prf₀.q1` + `mp`). Helper para la HI-`∀c` del `step`. -/
theorem PrfH_spec {Γ : List Formula} {A : Formula} (h : PrfH Γ (Formula.forall A)) (t : Term) :
    PrfH Γ (substFormula 0 t A) :=
  PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prf₀.q1 A t)) h

/-- Predicado inductivo de compositividad de `runFn` con acumulador `∀` object.
    `Ψ(p) = ∀c. runFn c (p ++ s) =eq runFn (runFn c p) s` (lista `p` = `#0`). -/
def prfCompPred (s : Term) : Formula :=
  Formula.forall
    (Formula.eq (runFn (.var 0) (concat (.var 1) (liftTerm 0 (liftTerm 0 s))))
                (runFn (runFn (.var 0) (.var 1)) (liftTerm 0 (liftTerm 0 s))))

/-- Instancia puntual de `prfCompPred` en un acumulador concreto `c`. -/
theorem prfCompPred_spec {s p : Term} (h : Prf (substFormula 0 p (prfCompPred s))) (c : Term) :
    Prf (runFn c (concat p s) =eq runFn (runFn c p) s) := by
  have hc := prf_spec h c
  simpa [prfCompPred, substFormula, substTerm, substTerms, runFn, concat,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hc

/-- **Compositividad de `runFn` en `Prf`** (keystone de `d2_prf`):
    `runFn c (p ++ s) =eq runFn (runFn c p) s`. Inducción de listas sobre `p`
    (acumulador `c` generalizado como `∀` object; normalización vía `norm32`). -/
theorem prf_runFn_concat (c p s : Term) :
    Prf (runFn c (concat p s) =eq runFn (runFn c p) s) := by
  have key : Prf (Formula.forall (prfCompPred s)) := by
    refine prf_list_induction (prfCompPred s) ?base ?step
    · refine Prf.gen _ ?_
      simp only [prfCompPred, substFormula, substTerm, substTerms, runFn, concat, nil,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact prf_eq_trans (prf_congr_runFn_2 (prf_concat_nil_eq _))
        (prf_eq_symm (prf_congr_runFn_1 (prf_runFn_nil _)))
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [prfCompPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        runFn, concat, cons, nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        reduceIte, norm32]
      -- objetivo: (∀c. IH[c]) ⇒ (∀c. Concl[c]); confinación (la IH no contiene c)
      refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
      refine prf_deduction ?_
      have ihc := PrfH_spec
          (A := liftFormula 1 (Formula.eq
            (runFn (.var 0) (concat (.var 1) (liftTerm 2 (liftTerm 0 (liftTerm 0 s)))))
            (runFn (runFn (.var 0) (.var 1)) (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))))
          (Γ := [liftFormula 0 (Formula.forall (Formula.eq
            (runFn (.var 0) (concat (.var 1) (liftTerm 2 (liftTerm 0 (liftTerm 0 s)))))
            (runFn (runFn (.var 0) (.var 1)) (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))))])
        (PrfH.hyp _ _ (List.Mem.head _)) (concat (.var 0) (cons (carc (.var 2)) nil))
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        runFn, concat, cons, nil, carc, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceGT, Nat.reduceSub, reduceIte, norm32, norm_s, FOL.substTerm_liftTerm,
        FOL.substTerm_liftLift] at ihc
      refine PrfH_eq_trans (prf_to_prfH (prf_congr_runFn_2 (c := .var 0)
          (prf_concat_cons_eq (.var 2) (.var 1) (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))) _)
        (PrfH_eq_trans (prf_to_prfH (prf_runFn_cons (.var 0) (.var 2)
            (concat (.var 1) (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))) _)
          (PrfH_eq_trans ihc (prf_to_prfH (prf_eq_symm
            (prf_congr_runFn_1 (rest := liftTerm 2 (liftTerm 0 (liftTerm 0 s)))
              (prf_runFn_cons (.var 0) (.var 2) (.var 1)))) _)))
  exact prfCompPred_spec (prf_spec key p) c

/-- Predicado inductivo de monotonía de `chainOk` con acumulador `∀` object.
    `Ψ(p) = ∀c. chainOk c p ⇒ chainOk (c0 ++ c) p` (lista `p`). -/
def prfMonoPred (c0 : Term) : Formula :=
  Formula.forall (Formula.impl
    (chainOk (.var 0) (.var 1))
    (chainOk (concat (liftTerm 0 (liftTerm 0 c0)) (.var 0)) (.var 1)))

theorem prfMonoPred_spec {c0 p : Term} (h : Prf (substFormula 0 p (prfMonoPred c0))) (c : Term) :
    Prf (Formula.impl (chainOk c p) (chainOk (concat c0 c) p)) := by
  have hc := prf_spec h c
  simpa [prfMonoPred, substFormula, substTerm, substTerms, chainOk, concat,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hc

/-- **Monotonía de `chainOk` en el contexto** en `Prf` (implicación, keystone d2):
    `chainOk c p ⇒ chainOk (c0 ++ c) p`. Inducción sobre `p` (acumulador `∀c`;
    usa `lineOk_mono`, `concat_assoc`, patrón confinación/`norm32`/`norm_s`). -/
theorem prf_chainOk_mono_imp (c0 c p : Term) :
    Prf (Formula.impl (chainOk c p) (chainOk (concat c0 c) p)) := by
  have key : Prf (Formula.forall (prfMonoPred c0)) := by
    refine prf_list_induction (prfMonoPred c0) ?base ?step
    · refine Prf.gen _ ?_
      simp only [prfMonoPred, substFormula, substTerm, substTerms, chainOk, concat, nil,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact prf_deduction (prf_to_prfH (prf_chainOk_nil _) _)
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [prfMonoPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        chainOk, concat, cons, nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        Nat.reduceSub, reduceIte, norm32]
      refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
      refine prf_deduction (deduction_aux ?_ (chainOk (.var 0) (cons (.var 2) (.var 1)))
        [liftFormula 0 (Formula.forall (Formula.impl (chainOk (.var 0) (.var 1))
          (chainOk (concat (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))) (.var 0)) (.var 1))))] rfl)
      let CTX : List Formula := [chainOk (.var 0) (cons (.var 2) (.var 1)),
        liftFormula 0 (Formula.forall (Formula.impl (chainOk (.var 0) (.var 1))
          (chainOk (concat (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))) (.var 0)) (.var 1))))]
      have hsplit : PrfH CTX (land (lineOk (.var 0) (.var 2))
          (chainOk (concat (.var 0) (cons (carc (.var 2)) nil)) (.var 1))) :=
        PrfH_iff_mp (prf_chainOk_cons (.var 0) (.var 2) (.var 1)) (PrfH.hyp _ _ (List.Mem.head _))
      have hA : PrfH CTX (lineOk (concat (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))) (.var 0)) (.var 2)) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lineOk_mono_imp (.var 0)
          (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))) (.var 2)) _) (PrfH_and_elim_left hsplit)
      have ihc := PrfH_spec
          (A := liftFormula 1 (Formula.impl (chainOk (.var 0) (.var 1))
            (chainOk (concat (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))) (.var 0)) (.var 1))))
          (Γ := CTX)
          (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
          (concat (.var 0) (cons (carc (.var 2)) nil))
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        chainOk, concat, cons, nil, carc, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceGT, Nat.reduceSub, reduceIte, norm32, norm_s, FOL.substTerm_liftTerm,
        FOL.substTerm_liftLift] at ihc
      have hB := PrfH.mp _ _ _ ihc (PrfH_and_elim_right hsplit)
      have hB' := PrfH_chainOk_subst1 (prf_to_prfH (prf_eq_symm
        (prf_concat_assoc (.var 0) (cons (carc (.var 2)) nil)
          (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))))) _) hB
      exact PrfH_iff_mpr (prf_chainOk_cons
        (concat (liftTerm 2 (liftTerm 0 (liftTerm 0 c0))) (.var 0)) (.var 2) (.var 1))
        (PrfH_and_intro hA hB')
  exact prfMonoPred_spec (prf_spec key p) c

/-- Predicado inductivo de debilitamiento de `runFn`. `Ψ(p) = ∀c. runFn c p =eq c ++ runFn nil p`. -/
def prfWeakPred : Formula :=
  Formula.forall (Formula.eq (runFn (.var 0) (.var 1)) (concat (.var 0) (runFn nil (.var 1))))

theorem prfWeakPred_spec {p : Term} (h : Prf (substFormula 0 p prfWeakPred)) (c : Term) :
    Prf (runFn c p =eq concat c (runFn nil p)) := by
  have hc := prf_spec h c
  simpa [prfWeakPred, substFormula, substTerm, substTerms, runFn, concat, nil, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hc

/-- **Debilitamiento de `runFn` en `Prf`**: `runFn c p =eq c ++ runFn nil p`. Inducción sobre
    `p` (acumulador `∀c`; usa `concat_assoc`, patrón confinación). -/
theorem prf_runFn_weaken (c p : Term) : Prf (runFn c p =eq concat c (runFn nil p)) := by
  have key : Prf (Formula.forall prfWeakPred) := by
    refine prf_list_induction prfWeakPred ?base ?step
    · refine Prf.gen _ ?_
      simp only [prfWeakPred, substFormula, substTerm, substTerms, runFn, concat, nil,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact prf_eq_trans (prf_runFn_nil _) (prf_eq_symm (prf_eq_trans
        (prf_congr_concat_left (prf_runFn_nil nil)) (prf_concat_nil_right _)))
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [prfWeakPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        runFn, concat, cons, nil, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        Nat.reduceSub, reduceIte, norm32]
      refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
      refine prf_deduction ?_
      let IH0 : Formula := liftFormula 0 (Formula.forall (Formula.eq (runFn (.var 0) (.var 1))
        (concat (.var 0) (runFn nil (.var 1)))))
      have ih1 := PrfH_spec (A := liftFormula 1 (Formula.eq (runFn (.var 0) (.var 1))
            (concat (.var 0) (runFn nil (.var 1))))) (Γ := [IH0])
          (PrfH.hyp _ _ (List.Mem.head _)) (concat (.var 0) (cons (carc (.var 2)) nil))
      have ih2 := PrfH_spec (A := liftFormula 1 (Formula.eq (runFn (.var 0) (.var 1))
            (concat (.var 0) (runFn nil (.var 1))))) (Γ := [IH0])
          (PrfH.hyp _ _ (List.Mem.head _)) (cons (carc (.var 2)) nil)
      simp only [IH0, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        runFn, concat, cons, nil, zero, carc, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceGT, Nat.reduceSub, reduceIte, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at ih1 ih2
      -- Lhs: runFn #0 (cons #2 #1) =eq concat #0 (concat [carc #2] (runFn nil #1))
      have Lhs := PrfH_eq_trans (prf_to_prfH (prf_runFn_cons (.var 0) (.var 2) (.var 1)) [IH0])
        (PrfH_eq_trans ih1 (prf_to_prfH (prf_concat_assoc (cons (carc (.var 2)) nil)
          (runFn nil (.var 1)) (.var 0)) [IH0]))
      -- Rin: runFn nil (cons #2 #1) =eq concat [carc #2] (runFn nil #1)
      have Rin := PrfH_eq_trans (prf_to_prfH (prf_runFn_cons nil (.var 2) (.var 1)) [IH0])
        (PrfH_eq_trans (prf_to_prfH (prf_congr_runFn_1 (rest := .var 1)
          (prf_concat_nil_eq (cons (carc (.var 2)) nil))) [IH0]) ih2)
      exact PrfH_eq_trans Lhs (PrfH_eq_symm (PrfH_congr_concat_left (u := .var 0) Rin))
  exact prfWeakPred_spec (prf_spec key p) c

/-- Cuerpo de la HI de `prf_chainOk_concat` (el `∀`-body del predicado, con `⇔` ya desplegado
    a `∧` de dos `⇒`). Definido aparte para que `simp` lo despliegue al normalizar el `spec`. -/
private def ccIHbody (s : Term) : Formula :=
  land
    (Formula.impl (chainOk (.var 0) (concat (.var 1) (liftTerm 2 (liftTerm 0 (liftTerm 0 s)))))
      (land (chainOk (.var 0) (.var 1))
        (chainOk (runFn (.var 0) (.var 1)) (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))))
    (Formula.impl (land (chainOk (.var 0) (.var 1))
        (chainOk (runFn (.var 0) (.var 1)) (liftTerm 2 (liftTerm 0 (liftTerm 0 s)))))
      (chainOk (.var 0) (concat (.var 1) (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))))

/-- Predicado inductivo de composición de `chainOk` con acumulador `∀` object.
    `Ψ(p) = ∀c. chainOk c (p++s) ⇔ chainOk c p ∧ chainOk (runFn c p) s`. -/
def prfCompChainPred (s : Term) : Formula :=
  Formula.forall
    ((chainOk (.var 0) (concat (.var 1) (liftTerm 0 (liftTerm 0 s)))) ⇔
      land (chainOk (.var 0) (.var 1)) (chainOk (runFn (.var 0) (.var 1)) (liftTerm 0 (liftTerm 0 s))))

theorem prfCompChainPred_spec {s p : Term} (h : Prf (substFormula 0 p (prfCompChainPred s))) (c : Term) :
    Prf ((chainOk c (concat p s)) ⇔ land (chainOk c p) (chainOk (runFn c p) s)) := by
  have hc := prf_spec h c
  simpa [prfCompChainPred, substFormula, substTerm, substTerms, chainOk, runFn, concat, land, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hc

/-- **Composición de `chainOk` en `Prf`** (keystone d2): `chainOk c (p++s) ⇔
    chainOk c p ∧ chainOk (runFn c p) s`. Inducción sobre `p` (acumulador `∀c`;
    patrón confinación/`norm32`/`norm_s`). -/
theorem prf_chainOk_concat (c p s : Term) :
    Prf ((chainOk c (concat p s)) ⇔ land (chainOk c p) (chainOk (runFn c p) s)) := by
  have key : Prf (Formula.forall (prfCompChainPred s)) := by
    refine prf_list_induction (prfCompChainPred s) ?base ?step
    · refine Prf.gen _ ?_
      simp only [prfCompChainPred, substFormula, substTerm, substTerms, liftTerm, liftTerms,
        chainOk, runFn, concat, nil, zero, iff, land, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceGT, Nat.reduceSub, reduceIte, norm_s, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_and_intro (prf_deduction ?fwd) (prf_deduction ?bwd)
      case fwd =>
        have hS : PrfH [chainOk (.var 0) (concat nil (liftTerm 0 s))] (chainOk (.var 0) (liftTerm 0 s)) :=
          PrfH_chainOk_subst2 (prf_to_prfH (prf_concat_nil_eq (liftTerm 0 s)) _)
            (PrfH.hyp _ _ (List.Mem.head _))
        refine PrfH_and_intro (prf_to_prfH (prf_chainOk_nil (.var 0)) _) ?_
        exact PrfH_chainOk_subst1 (prf_to_prfH (prf_eq_symm (prf_runFn_nil (.var 0))) _) hS
      case bwd =>
        have hyp : PrfH [land (chainOk (.var 0) nil) (chainOk (runFn (.var 0) nil) (liftTerm 0 s))]
            (land (chainOk (.var 0) nil) (chainOk (runFn (.var 0) nil) (liftTerm 0 s))) :=
          PrfH.hyp _ _ (List.Mem.head _)
        have hS := PrfH_chainOk_subst1 (prf_to_prfH (prf_runFn_nil (.var 0)) _)
          (PrfH_and_elim_right hyp)
        exact PrfH_chainOk_subst2 (prf_to_prfH (prf_eq_symm (prf_concat_nil_eq (liftTerm 0 s))) _) hS
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [prfCompChainPred, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
        chainOk, runFn, concat, cons, nil, iff, land, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceGT, Nat.reduceSub, reduceIte, norm32]
      refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
      refine prf_deduction ?_
      let S : Term := liftTerm 2 (liftTerm 0 (liftTerm 0 s))
      refine PrfH_and_intro ?fwd ?bwd
      · -- forward
        let FCTX : List Formula := [chainOk (.var 0) (concat (cons (.var 2) (.var 1)) S),
          liftFormula 0 (Formula.forall (ccIHbody s))]
        refine deduction_aux ?_ (chainOk (.var 0) (concat (cons (.var 2) (.var 1)) S))
          [liftFormula 0 (Formula.forall (ccIHbody s))] rfl
        have ihc := PrfH_spec (A := liftFormula 1 (ccIHbody s)) (Γ := FCTX)
            (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
            (concat (.var 0) (cons (carc (.var 2)) nil))
        unfold ccIHbody at ihc
        simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
          chainOk, runFn, concat, cons, nil, carc, zero, land, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
          Nat.reduceGT, Nat.reduceSub, reduceIte, norm32, norm_s, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at ihc
        have h1 : PrfH FCTX (chainOk (.var 0) (cons (.var 2) (concat (.var 1) S))) :=
          PrfH_chainOk_subst2 (prf_to_prfH (prf_concat_cons_eq (.var 2) (.var 1) S) _)
            (PrfH.hyp _ _ (List.Mem.head _))
        have hsplit := PrfH_iff_mp (prf_chainOk_cons (.var 0) (.var 2) (concat (.var 1) S)) h1
        have hBC := PrfH.mp _ _ _ (PrfH_and_elim_left ihc) (PrfH_and_elim_right hsplit)
        refine PrfH_and_intro
          (PrfH_iff_mpr (prf_chainOk_cons (.var 0) (.var 2) (.var 1))
            (PrfH_and_intro (PrfH_and_elim_left hsplit) (PrfH_and_elim_left hBC))) ?_
        exact PrfH_chainOk_subst1 (prf_to_prfH (prf_eq_symm
          (prf_runFn_cons (.var 0) (.var 2) (.var 1))) _) (PrfH_and_elim_right hBC)
      · -- backward
        let BCTX : List Formula := [land (chainOk (.var 0) (cons (.var 2) (.var 1)))
            (chainOk (runFn (.var 0) (cons (.var 2) (.var 1))) S),
          liftFormula 0 (Formula.forall (ccIHbody s))]
        refine deduction_aux ?_ (land (chainOk (.var 0) (cons (.var 2) (.var 1)))
            (chainOk (runFn (.var 0) (cons (.var 2) (.var 1))) S))
          [liftFormula 0 (Formula.forall (ccIHbody s))] rfl
        have ihc := PrfH_spec (A := liftFormula 1 (ccIHbody s)) (Γ := BCTX)
            (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
            (concat (.var 0) (cons (carc (.var 2)) nil))
        unfold ccIHbody at ihc
        simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
          chainOk, runFn, concat, cons, nil, carc, zero, land, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
          Nat.reduceGT, Nat.reduceSub, reduceIte, norm32, norm_s, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at ihc
        have hcons : PrfH BCTX (chainOk (.var 0) (cons (.var 2) (.var 1))) :=
          PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
        have hrun : PrfH BCTX (chainOk (runFn (.var 0) (cons (.var 2) (.var 1))) S) :=
          PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
        have hsplit := PrfH_iff_mp (prf_chainOk_cons (.var 0) (.var 2) (.var 1)) hcons
        have hC := PrfH_chainOk_subst1 (prf_to_prfH (prf_runFn_cons (.var 0) (.var 2) (.var 1)) _) hrun
        have hrec := PrfH.mp _ _ _ (PrfH_and_elim_right ihc)
          (PrfH_and_intro (PrfH_and_elim_right hsplit) hC)
        have hbig := PrfH_iff_mpr (prf_chainOk_cons (.var 0) (.var 2) (concat (.var 1) S))
          (PrfH_and_intro (PrfH_and_elim_left hsplit) hrec)
        exact PrfH_chainOk_subst2 (prf_to_prfH (prf_eq_symm
          (prf_concat_cons_eq (.var 2) (.var 1) S)) _) hbig
  exact prfCompChainPred_spec (prf_spec key p) c

end ROBINSON_PlusPlus.Meta.ChainPrf

export ROBINSON_PlusPlus.Meta.ChainPrf
  (prf_list_induction prf_concat_nil_right prf_In_mono prf_In_mono_imp prf_In_mono_right
   prf_In_mono_right_imp prf_concat_assoc prf_allIn_mono_imp prf_lineOk_mono_imp prf_chainOk_subst2
   prf_runFn_concat prf_chainOk_mono_imp prf_runFn_weaken prf_chainOk_concat
   PrfH_and_intro PrfH_and_elim_left PrfH_and_elim_right PrfH_iff_mp PrfH_iff_mpr
   PrfH_chainOk_subst1 PrfH_chainOk_subst2 PrfH_allIn_subst2 PrfH_eq_subst_in PrfH_in_cons_head)

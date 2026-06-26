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
theorem prf_In_mono_right (x M L : Term) (h : Prf (In x L)) : Prf (In x (concat L M)) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 x) (.var 0))
      (In (liftTerm 0 x) (concat (.var 0) (liftTerm 0 M))))) := by
    refine prf_list_induction _ ?base ?step
    · -- base: In x nil ⇒ In x (concat nil M) (vacío, por explosión)
      have hb : Prf (Formula.impl (In x nil) (In x (concat nil M))) := by
        refine prf_deduction ?_
        exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq (In x (concat nil M))))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil x) _) (prfH_hyp_self _))
      simpa only [substFormula, substTerm, substTerms, In, concat, nil, FOL.substTerm_liftTerm] using hb
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
  have hk2 : Prf (Formula.impl (In x L) (In x (concat L M))) := by
    simpa only [substFormula, substTerm, substTerms, In, concat, FOL.substTerm_liftTerm] using hkey
  exact prf_mp hk2 h

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

end ROBINSON_PlusPlus.Meta.ChainPrf

export ROBINSON_PlusPlus.Meta.ChainPrf
  (prf_list_induction prf_concat_nil_right prf_In_mono prf_In_mono_right prf_runFn_concat)

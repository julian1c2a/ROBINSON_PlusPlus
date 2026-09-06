/-
SONDEO (2026-09-06) — TAREA A: ¿está OBSTRUIDA la FUSIÓN de testigos?

La clausura `prf_hasWitF_substfc` (lo único que separa el árbol del verde, §3.36.5) induce sobre
la estructura del código. En los constructores BINARIOS (`implc a b`) la hipótesis de inducción da
un testigo para CADA subfórmula, y hay que **FUSIONARLOS**. Ayer sólo hizo falta EXTENDER uno
(`prf_wfAll1_cons`), y se midió que **no existe ninguna clausura de testigos bajo `concat`**.

## La pregunta

¿Es la fusión una obstrucción real, o sólo un lema que nadie ha escrito?

## La sospecha que lo desbloquea

`wfAll1 W := ∀i < lenc W. isTermCodeE1 W (nthc W i)` está en forma **INDEXADA**, y `concat` no se
lleva bien con los índices (habría que partir `i < lenc W₁ + lenc W₂`, y no hay aritmética de
`lenc` sobre `concat`). Pero `In` **sí** se lleva bien con `concat`, y el proyecto tiene las DOS
direcciones del puente índice↔pertenencia:

* `prf_boundedIn_of_In` / `prf_In_of_boundedIn`  (`Meta/BoundedInPrf.lean`)
* `prf_In_mono_imp` / `prf_In_mono_right_imp`    (`Meta/ChainPrf.lean`)
* y **ya existe la forma de pertenencia de `wfAll1`**: `prf_isTermCodeE1_of_In`
  (`Meta/CodeWitnessPrf.lean`) — `In c w ⇒ wfAll1 w ⇒ isTermCodeE1 w c`.

⇒ la ruta es **pasar a forma de PERTENENCIA, fusionar allí, y volver**. Los índices no se tocan.

## Lo que mide este sondeo, en orden

1. `prf_in_nthc` — «lo que está en una posición válida, pertenece». No existía.
2. `prf_argsIn_mono_of` / `prf_isTermCodeE1_mono_of` — la monotonía de ayer **GENERALIZADA** a
   cualquier inclusión de testigos dada como implicación objeto. Las de `cons` (ayer) y las de
   `concat` (hoy) pasan a ser corolarios de la misma.
3. `prf_wfAll1_concat` — **LA FUSIÓN**. Si compila, A queda contestada: no hay obstrucción.
-/

import ROBINSON_PlusPlus.Meta.HasWitTcFnPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS
open ROBINSON_PlusPlus.Meta.HasWitTcFnPrf

set_option linter.unusedSimpArgs false

namespace MergeTestigos

/-! ## §1 · «Lo que está en una posición válida, PERTENECE»

El puente que faltaba para entrar en forma de pertenencia. `boundedIn` con testigo el propio
índice, y de ahí `prf_In_of_boundedIn`. -/

theorem prf_in_nthc (L i : Term) :
    Prf (Formula.impl (lt i (lenc L)) (In (nthc L i) L)) := by
  refine prf_deduction ?_
  have hlt : PrfH [lt i (lenc L)] (lt i (lenc L)) := prfH_hyp_self _
  have hsub : substFormula 0 i (land (lt (.var 0) (liftTerm 0 (lenc L)))
      (Formula.eq (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 (nthc L i))))
      = land (lt i (lenc L)) (Formula.eq (nthc L i) (nthc L i)) := by
    simp only [land, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  have hb : PrfH [lt i (lenc L)] (boundedIn (nthc L i) L) := by
    unfold boundedIn
    refine PrfH_ex_intro i ?_
    rw [hsub]
    exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) hlt)
      (prf_to_prfH (prf_refl (nthc L i)) _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_In_of_boundedIn (nthc L i) L) _) hb

/-! ## §2 · La monotonía, GENERALIZADA a cualquier inclusión de testigos

`prf_argsIn_mono` (ayer) estaba clavada a `cons a w`. El testigo sólo entra por `In`, así que la
hipótesis honesta es **la inclusión como implicación objeto**. La hipótesis se pide ya LIFTEADA
porque es la forma en que el `∀` acotado la consume. -/

theorem prf_argsIn_mono_of (w w' Y : Term)
    (hsub : ∀ x : Term, Prf (Formula.impl (In x (liftTerm 0 w)) (In x (liftTerm 0 w')))) :
    Prf (Formula.impl (argsIn w Y) (argsIn w' Y)) := by
  refine prf_mp (Prf.qconf (argsIn w Y) (argsInBody w' Y)) (Prf.gen _ ?_)
  rw [liftF_argsIn]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc Y)))
    [argsIn (liftTerm 0 w) (liftTerm 0 Y)] rfl)
  show PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 w'))
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
      (lt (.var 0) (lenc (liftTerm 0 Y))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
      (argsIn (liftTerm 0 w) (liftTerm 0 Y)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hin := PrfH.mp _ _ _
    (PrfH_inst_argsIn (liftTerm 0 w) (liftTerm 0 Y) (.var 0) hargs) hlt
  exact PrfH.mp _ _ _ (prf_to_prfH (hsub (nthc (liftTerm 0 Y) (.var 0))) _) hin

theorem prf_isTermCodeE1_mono_of (w w' X : Term)
    (hsub : ∀ x : Term, Prf (Formula.impl (In x (liftTerm 0 w)) (In x (liftTerm 0 w')))) :
    Prf (Formula.impl (isTermCodeE1 w X) (isTermCodeE1 w' X)) := by
  unfold isTermCodeE1
  refine prf_or_elim_imp ?_ ?_
  · exact Prf.incl (Prf₀.j1 _ _)
  · refine prf_deduction ?_
    have hh : PrfH [land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))) := prfH_hyp_self _
    have h1 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh
    have h2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hh
    have h2' := PrfH.mp _ _ _
      (prf_to_prfH (prf_argsIn_mono_of w w' (nthc X (numeralM 2)) hsub) _) h2
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
      (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) h1) h2')

/-! ## §3 · LA FUSIÓN

`In` sobre `concat` es un axioma (`ax_L3_in_concat`), así que en forma de pertenencia el caso
sale por `or_elim` sobre las dos mitades. Ni un índice partido. -/

/-- `ax_L3_in_concat` instanciado, en `Prf`. -/
theorem prf_in_concat (x L M : Term) :
    Prf (In x (concat L M) ⇔ lor (In x L) (In x M)) := by
  have h := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax_L3_in_concat ∈ axioms by simp [axioms])) x) L) M
  simp [ax_L3_in_concat, substFormula, substTerm, substTerms, In, concat, lor, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
  exact h

/-- Contexto del `∀` acotado de la fusión. -/
def CTXc (W₁ W₂ : Term) : List Formula :=
  [lt (.var 0) (lenc (concat (liftTerm 0 W₁) (liftTerm 0 W₂))),
   land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))]

/-- 🏁 **LA FUSIÓN**: dos testigos bien formados dan uno bien formado. -/
theorem prf_wfAll1_concat (W₁ W₂ : Term) :
    Prf (Formula.impl (land (wfAll1 W₁) (wfAll1 W₂)) (wfAll1 (concat W₁ W₂))) := by
  refine prf_mp (Prf.qconf (land (wfAll1 W₁) (wfAll1 W₂)) (wfAll1Body (concat W₁ W₂)))
    (Prf.gen _ ?_)
  simp only [liftFormula, liftF_wfAll1, land]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (concat W₁ W₂))))
    [land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))] rfl)
  have hlt : PrfH (CTXc W₁ W₂)
      (lt (.var 0) (lenc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  -- (1) lo que está en una posición válida, PERTENECE al concat
  have hinC : PrfH (CTXc W₁ W₂)
      (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
        (concat (liftTerm 0 W₁) (liftTerm 0 W₂))) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (prf_in_nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) _) hlt
  -- (2) y `In` sobre `concat` SE PARTE — aquí no hay ningún índice que romper
  have hor : PrfH (CTXc W₁ W₂)
      (lor (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₁))
           (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₂))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _))
      (prf_to_prfH (prf_in_concat (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
        (liftTerm 0 W₁) (liftTerm 0 W₂)) _)) hinC
  refine PrfH_or_elim hor ?iz ?dr
  case iz =>
    have hin : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₁) :: CTXc W₁ W₂)
        (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₁)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hand : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₁) :: CTXc W₁ W₂)
        (land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hw1 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isTermCodeE1_of_In (liftTerm 0 W₁)
        (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))) _) hin) hw1
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_mono_of (liftTerm 0 W₁)
      (concat (liftTerm 0 W₁) (liftTerm 0 W₂))
      (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
      (fun x => prf_In_mono_right_imp x (liftTerm 0 (liftTerm 0 W₂))
        (liftTerm 0 (liftTerm 0 W₁)))) _) hnode
  case dr =>
    have hin : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₂) :: CTXc W₁ W₂)
        (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₂)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hand : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₂) :: CTXc W₁ W₂)
        (land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hw2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isTermCodeE1_of_In (liftTerm 0 W₂)
        (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))) _) hin) hw2
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_mono_of (liftTerm 0 W₂)
      (concat (liftTerm 0 W₁) (liftTerm 0 W₂))
      (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
      (fun x => prf_In_mono_imp x (liftTerm 0 (liftTerm 0 W₂))
        (liftTerm 0 (liftTerm 0 W₁)))) _) hnode

end MergeTestigos

/-! ## §4 · FOOTPRINT -/
#print axioms MergeTestigos.prf_in_nthc
#print axioms MergeTestigos.prf_argsIn_mono_of
#print axioms MergeTestigos.prf_wfAll1_concat

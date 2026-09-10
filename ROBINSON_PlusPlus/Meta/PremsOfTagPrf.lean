/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ListEtaPrf
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.LineWFAssemblePrf

/-!
# `premsOf` EVALUADO por TAG, a nivel OBJETO — las 21 ramas

⛔ **La obstrucción que esto levanta** (§13.1 de `Meta/D3ChainDotPrf.lean`): los veintiún
`ax_premsOf_*` hacen *pattern‑matching* sobre un `cons` explícito, luego sobre una línea
**abstracta** «no hay nada que evaluar». Cierto — **mientras no se sepa la longitud**. Y la
longitud sí sale, del bicondicional del `ax_lineWF_*` del mismo tag.

**La cadena, y es la misma para los 21:**

    lineWF t  +  lineTag t ≐ k̄
      ⟹ (bicondicional del tag)     lenc t ≐ n̄
      ⟹ (`prf_eta_lenc`, ListEtaPrf) t ≐ ⟨carc t, carc (cdrc t), …⟩
      ⟹ (`prf_nthc1_carc_cdrc`)      la posición 1 de esa η **es** k̄
      ⟹ (`ax_premsOf_k` instanciado)  premsOf t ≐ R_k

⭐⭐ **Y sale MUCHO más barato de lo que §13.1 estimó.** «21 casos» sugería 21 pruebas; son
**dos lemas genéricos** (`prf_lenc_of_tag`, `prf_premsOf_of_tag`) y **ocho líneas por tag**, todas
con la misma forma. La lección de [[feedback-medir-la-forma]] otra vez, y otra vez en la dirección
barata: **generalizar sale más barato**, porque lo caro era la instancia, no el esquema.

⚠️ **Dos formas de RHS, no una.** `ax_lineWF_mp` es el único cuyo bicondicional **no lleva
condición estructural** (su fidelidad la liga entera `ax_premsOf_mp`); los otros veinte son
`lwfVar ⇔ (lencF n ∧ C)`. De ahí los dos envoltorios `_tag_plain` / `_tag_and`.

⚠️ **Esto es el nivel OBJETO.** La reflexión punteada (`Prov(premsOfT ṫ ≐ (premsOf t)˙)`), que es
lo que la cota de `hbody`(b) consume, va aparte y **encima** de esto.

**Footprint**: la base sancionada.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.ListEtaPrf
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.LineWFAssemblePrf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace ROBINSON_PlusPlus.Meta.PremsOfTagPrf

/-! ## §1 · LOS DOS LEMAS GENÉRICOS -/


/-- La longitud canónica del tag, extraída del bicondicional. Genérica en el RHS `D`: `mp` lo
    tiene SIN condición (`lwfVar ⇔ lencMp`) y los otros veinte con ella. -/
theorem prf_lenc_of_tag {k n : Nat} {D : Formula} (t : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ D))))
    (hD : Prf (substFormula 0 t D ⇒ (lenc t =eq numeralM n))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (lenc t =eq numeralM n))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM k) [lineWF t] rfl)
  have hlw : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (nthc t (succ zero) =eq numeralM k) := PrfH.hyp _ _ (List.Mem.head _)
  have hacc : Prf (Formula.impl (nthc t (succ zero) =eq numeralM k)
      (lineWF t ⇔ substFormula 0 t D)) := by
    have hh := prf_spec hax t
    simpa [iff, substFormula, substFormula_tagF, substFormula_lwfVar] using hh
  have hiff := PrfH.mp _ _ _ (prf_to_prfH hacc _) htagH
  have hD' := PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hiff) hlw
  exact PrfH.mp _ _ _ (prf_to_prfH hD _) hD'

/-- La línea reconstruida CON EL TAG ya sustituido por su numeral. -/
def etaTag (L : Term) (m k : Nat) : Term :=
  cons (carc L) (cons (numeralM k) (etaAt (cdrc (cdrc L)) m))

/-- ⭐ **LA η POR TAG**: el bicondicional da la longitud, y la longitud da la línea entera —
    con el tag ya sustituido por su numeral en la posición 1.

    ⚠️ **Se expone a propósito**, y no sólo como paso interno de `prf_premsOf_of_tag`: la
    reflexión **punteada** de `premsOf` (B1, `Meta/PremsOfDotPrf.lean`) necesita exactamente esta
    igualdad para transportar `ṫ` a `(etaTag t m k)˙`. -/
theorem prf_eta_of_tag {k m : Nat} {D : Formula} (t : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ D))))
    (hD : Prf (substFormula 0 t D ⇒ (lenc t =eq numeralM (m + 2)))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (t =eq etaTag t m k))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM k) [lineWF t] rfl)
  have hlw : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (nthc t (succ zero) =eq numeralM k) := PrfH.hyp _ _ (List.Mem.head _)
  have hlen : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (lenc t =eq numeralM (m + 2)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lenc_of_tag t hax hD) _) hlw) htagH
  have heta : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (t =eq etaAt t (m + 2)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_eta_lenc (m + 2) t) _) hlen
  have hpos1 : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (nthc t (numeralM 1) =eq carc (cdrc t)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_nthc1_carc_cdrc t m) _) hlen
  have htagc : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (carc (cdrc t) =eq numeralM k) := PrfH_eq_trans (PrfH_eq_symm hpos1) htagH
  have hshape : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (etaAt t (m + 2) =eq etaTag t m k) := by
    show PrfH _ (cons (carc t) (cons (carc (cdrc t)) (etaAt (cdrc (cdrc t)) m))
      =eq cons (carc t) (cons (numeralM k) (etaAt (cdrc (cdrc t)) m)))
    exact PrfH_congr_cons_tail (PrfH_congr_cons_head htagc)
  exact PrfH_eq_trans heta hshape

/-- ⭐⭐ `premsOf` EVALUADO a nivel OBJETO, genérico en el tag, la aridad y el valor. -/
theorem prf_premsOf_of_tag {k m : Nat} {D : Formula} (t R : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ D))))
    (hD : Prf (substFormula 0 t D ⇒ (lenc t =eq numeralM (m + 2))))
    (hpre : Prf (premsOf (etaTag t m k) =eq R)) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (premsOf t =eq R))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM k) [lineWF t] rfl)
  have hlw : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (nthc t (succ zero) =eq numeralM k) := PrfH.hyp _ _ (List.Mem.head _)
  have ht : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (t =eq etaTag t m k) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_eta_of_tag t hax hD) _) hlw) htagH
  let A : Formula := Formula.eq (premsOf (.var 0)) (liftTerm 0 R)
  have hS : ∀ s : Term, substFormula 0 s A = Formula.eq (premsOf s) R := by
    intro s
    simp only [A, premsOf, cons, nil, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  exact (hS t) ▸ PrfH_leibniz_subst (A := A) (PrfH_eq_symm ht)
    ((hS (etaTag t m k)) ▸ prf_to_prfH hpre _)


/-! ## §2 · LOS DOS ENVOLTORIOS — según lleve o no condición estructural -/

/-- Envoltorio para los **veinte** tags cuyo bicondicional es `lwfVar ⇔ (lencF n ∧ C)`. -/
theorem prf_premsOf_tag_and {k m : Nat} {C : Formula} (t R : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k)
      (lwfVar ⇔ Formula.and (lencF (m + 2)) C))))
    (hpre : Prf (premsOf (etaTag t m k) =eq R)) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (premsOf t =eq R))) :=
  prf_premsOf_of_tag t R hax
    (by
      have hsub : substFormula 0 t (Formula.and (lencF (m + 2)) C)
          = Formula.and (lenc t =eq numeralM (m + 2)) (substFormula 0 t C) := by
        simp only [substFormula, substFormula_lencF]
      rw [hsub]
      exact prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) (prfH_hyp_self _)))
    hpre

/-- Envoltorio para `mp` (16), el **único** sin condición estructural. -/
theorem prf_premsOf_tag_plain {k m : Nat} (t R : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ lencF (m + 2)))))
    (hpre : Prf (premsOf (etaTag t m k) =eq R)) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (premsOf t =eq R))) :=
  prf_premsOf_of_tag t R hax
    (by rw [substFormula_lencF]; exact prf_deduction (prfH_hyp_self _)) hpre

/-! ## §3 · LAS 21 RAMAS

Ocho líneas cada una, todas con la misma forma: el envoltorio que le toque, el `ax_lineWF_*` del
tag y el `ax_premsOf_*` instanciado en los componentes de la η. -/

/-- Tag 0 (`p1`). -/
theorem prf_premsOf_p1 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 0) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 0) (m := 2) t _
    (prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_p1 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_p1, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 1 (`p2`). -/
theorem prf_premsOf_p2 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 1) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 1) (m := 3) t _
    (prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_p2 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))) (carc (cdrc (cdrc (cdrc (cdrc t)))))
  simpa [ax_premsOf_p2, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 2 (`c1`). -/
theorem prf_premsOf_c1 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 2) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 2) (m := 2) t _
    (prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c1 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_c1, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 3 (`c2`). -/
theorem prf_premsOf_c2 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 3) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 3) (m := 2) t _
    (prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c2 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_c2, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 4 (`c3`). -/
theorem prf_premsOf_c3 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 4) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 4) (m := 2) t _
    (prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_c3 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_c3, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 5 (`j1`). -/
theorem prf_premsOf_j1 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 5) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 5) (m := 2) t _
    (prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j1 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_j1, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 6 (`j2`). -/
theorem prf_premsOf_j2 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 6) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 6) (m := 2) t _
    (prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j2 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_j2, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 7 (`j3`). -/
theorem prf_premsOf_j3 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 7) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 7) (m := 3) t _
    (prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_j3 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))) (carc (cdrc (cdrc (cdrc (cdrc t)))))
  simpa [ax_premsOf_j3, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 8 (`efq`). -/
theorem prf_premsOf_efq (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 8) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 8) (m := 1) t _
    (prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_efq ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_efq, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 9 (`q1`). -/
theorem prf_premsOf_q1 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 9) (m := 2) t _
    (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q1 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_q1, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 10 (`q2`). -/
theorem prf_premsOf_q2 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 10) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 10) (m := 2) t _
    (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q2 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_q2, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 11 (`q3`). -/
theorem prf_premsOf_q3 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 11) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 11) (m := 2) t _
    (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_q3 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_q3, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 12 (`eqrefl`). -/
theorem prf_premsOf_eqrefl (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 12) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 12) (m := 1) t _
    (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_eqrefl ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_eqrefl, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 13 (`leibniz`). -/
theorem prf_premsOf_leibniz (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 13) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 13) (m := 3) t _
    (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_leibniz ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))) (carc (cdrc (cdrc (cdrc (cdrc t)))))
  simpa [ax_premsOf_leibniz, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 14 (`p3`). -/
theorem prf_premsOf_p3 (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 14) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 14) (m := 1) t _
    (prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_p3 ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_p3, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 15 (`thy`). -/
theorem prf_premsOf_thy (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 15) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 15) (m := 0) t _
    (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_ax (show ax_premsOf_thy ∈ axioms by simp [axioms])) (carc t)
  simpa [ax_premsOf_thy, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 16 (`mp`). -/
theorem prf_premsOf_mp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 16) ⇒
      (premsOf t =eq cons (implc (carc (cdrc (cdrc t))) (carc t)) (cons (carc (cdrc (cdrc t))) nil)))) := by
  refine prf_premsOf_tag_plain (k := 16) (m := 1) t _
    (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_mp ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_mp, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 17 (`gen`). -/
theorem prf_premsOf_gen (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 17) ⇒
      (premsOf t =eq cons (carc (cdrc (cdrc t))) nil))) := by
  refine prf_premsOf_tag_and (k := 17) (m := 1) t _
    (prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_gen ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_gen, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 18 (`ind`). -/
theorem prf_premsOf_ind (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 18) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 18) (m := 1) t _
    (prf_ax (show ax_lineWF_ind ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_ind ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_ind, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 19 (`qconf`). -/
theorem prf_premsOf_qconf (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 19) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 19) (m := 2) t _
    (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_spec (prf_ax (show ax_premsOf_qconf ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc t))))
  simpa [ax_premsOf_qconf, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-- Tag 20 (`listInd`). -/
theorem prf_premsOf_listInd (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 20) ⇒
      (premsOf t =eq nil))) := by
  refine prf_premsOf_tag_and (k := 20) (m := 1) t _
    (prf_ax (show ax_lineWF_listInd ∈ axioms by simp [axioms])) ?_
  have h := prf_spec (prf_spec (prf_ax (show ax_premsOf_listInd ∈ axioms by simp [axioms])) (carc t)) (carc (cdrc (cdrc t)))
  simpa [ax_premsOf_listInd, etaTag, etaAt, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift, substTerm_liftLiftLift, substTerms_liftLiftLift,
    substTerm_liftLiftLiftLift, substTerms_liftLiftLiftLift] using h

/-! ## §4 · EL ENSAMBLAJE POR TAGS

Con las 21 ramas, `premsOf t` queda determinado desde `lineWF t` **sin conocer el tag**: la
inversión (`prf_lineWF_inv`) lo entrega, y `pcc_tag_vacuous` cierra la cola `k ≥ 21`.

⚠️ El valor `R` **depende del tag**, así que no hay un único `premsOf t ≐ R` que valga para todos.
Lo que sí sale uniforme es cualquier consecuencia común de los 21 valores — y eso es lo que
`hbody`(b) consumirá. Se deja el ensamblador genérico enunciado sobre esa consecuencia `C`. -/

/-- **Ensamblador por tags de `premsOf`**: si cada valor posible de `premsOf t` implica `C`,
    entonces `lineWF t` implica `C`. -/
theorem prf_of_premsOf_branches (t : Term) (C : Formula)
    (hbranch : ∀ k : Nat, Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ C))) :
    Prf (lineWF t ⇒ C) := by
  have hall : Prf (tagDisj t 20 ⇒ (lineWF t ⇒ C)) :=
    prf_of_tagDisj t _ (fun k => prf_swap_imp (hbranch k)) 20
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hall _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_inv t) _) (prfH_hyp_self _))) (prfH_hyp_self _)

end ROBINSON_PlusPlus.Meta.PremsOfTagPrf

/-! ## `export` — por CONSUMO

Consumidor previsto: la reflexión punteada de la cota de `boundedPremsIn` (`hbody`(b) de D3),
que necesita `premsOf` evaluado antes de poder cruzar `lencT (premsOfT …)`. -/
export ROBINSON_PlusPlus.Meta.PremsOfTagPrf (
  prf_lenc_of_tag etaTag prf_eta_of_tag prf_premsOf_of_tag
  prf_premsOf_tag_and prf_premsOf_tag_plain
  prf_premsOf_p1 prf_premsOf_p2 prf_premsOf_c1 prf_premsOf_c2 prf_premsOf_c3
  prf_premsOf_j1 prf_premsOf_j2 prf_premsOf_j3 prf_premsOf_efq
  prf_premsOf_q1 prf_premsOf_q2 prf_premsOf_q3 prf_premsOf_eqrefl
  prf_premsOf_leibniz prf_premsOf_p3 prf_premsOf_thy prf_premsOf_mp
  prf_premsOf_gen prf_premsOf_ind prf_premsOf_qconf prf_premsOf_listInd
  prf_of_premsOf_branches
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_of_tag
#print axioms ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_mp
#print axioms ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_thy
#print axioms ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_of_premsOf_branches

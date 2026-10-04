/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalNthcPrf
import ROBINSON_PlusPlus.Meta.LineWFConsPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.LineWFConsPrf
open ROBINSON_PlusPlus.Meta.NumListPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

/-!
## META — NIVEL D real (§37): evaluación COMPUESTA `carc (nthc p i)`

Última pieza de evaluación para `hI_dot`: el puente entre el término simbólico `carc (nthc(ṗ, ı̇))`
(que aparece en el código dotado de `boundedCarcIn`) y el valor `(carc (nthc p i))˙`. Compone tres
evaluaciones ya construidas:

* `pcc_eval_nthc` (§35, acotada): `nthc(ṗ, ı̇) = (nthc p i)˙` (dado `i < lenc p`);
* `prf_line_is_cons` (§36): dado `chainOk nil p` e `i < lenc p`, la línea `nthc p i` es un `cons`;
* `pcc_eval_carc` (§28): `carc (cons a b)` evalúa a la cabeza (sobre el `cons`).

La cadena `carcT(nthcT ṗ ı̇) = carcT((nthc p i)˙) = (carc (nthc p i))˙` se hace con **lógica
ecuacional interna en `PrfH`** (las evaluaciones vienen bajo el contexto `chainOk`/`<`), para lo que
se portan los combinadores internos a `PrfH` (`PrfH_mp_code_apply`, `PrfH_leibniz_apply`,
`PrfH_eq_trans_code`).
-/

/-! ### Combinadores del sistema de prueba interno en `PrfH` (versiones bajo contexto) -/

/-- MP interno a nivel de código, en `PrfH`. -/
theorem PrfH_mp_code_apply {Γ : List Formula} {Ac Bc : Term}
    (himp : PrfH Γ (provFromCode (implc Ac Bc))) (ha : PrfH Γ (provFromCode Ac)) :
    PrfH Γ (provFromCode Bc) :=
  PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_mp_code_open Ac Bc) _) himp) ha

/-- Leibniz interno a nivel de código, en `PrfH`. -/
theorem PrfH_leibniz_apply {Γ : List Formula} (Ac t₁ t₂ : Term)
    (heq : PrfH Γ (provFromCode (eqc t₁ t₂)))
    (h1 : PrfH Γ (provFromCode (substfc zero t₁ Ac)))
    (hwA : Prf (hasWitF Ac)) (hw1 : Prf (hasWit t₁)) (hw2 : Prf (hasWit t₂)) :
    PrfH Γ (provFromCode (substfc zero t₂ Ac)) :=
  PrfH_mp_code_apply
    (PrfH_mp_code_apply (prf_to_prfH (pcc_leibniz_code Ac t₁ t₂ hwA hw1 hw2) _) heq) h1

/-- Transitividad interna de `=` a nivel de código, en `PrfH`. -/
theorem PrfH_eq_trans_code {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z)))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) (hwZ : Prf (hasWit Z)) :
    PrfH Γ (provFromCode (eqc X Z)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hY : PrfH Γ (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp Y))) _) h1
  have hZ : PrfH Γ (provFromCode (substfc zero Z Ac)) :=
    PrfH_leibniz_apply Ac Y Z h2 hY
      (prf_hasWitF_eq2 X (varc (numeral 0)) hwX (prf_hasWit_varc (numeral 0))) hwY hwZ
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Z)) _) hZ

/-- **Congruencia interna de `carcT`** (forma implicación): `Prov(⌜X=Y⌝) ⇒ Prov(⌜carcT X = carcT Y⌝)`.
    Leibniz con contexto `Ac := (carcT X = carcT v₀)`; base = reflexividad codificada. -/
theorem pcc_congr_carcT_code_imp (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (carcT X) (carcT Y))) := by
  let Ac : Term := eqc (carcT X) (carcT (varc (numeral 0)))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc (carcT X) (carcT t)) := by
    intro t
    refine prf_eq_trans (prf_substfc_eq zero t (carcT X) (carcT (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_carcT zero t X) (prf_congr_carcT (hX t))
    · exact prf_eq_trans (prf_substtc_carcT zero t (varc (numeral 0)))
        (prf_congr_carcT (prf_substtc_varc0 t))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X))) (prf_provFromCode_eqCodeFn_refl (carcT X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (carcT X) (carcT (varc (numeral 0))) (prf_hasWit_carcT hwX)
        (prf_hasWit_carcT (prf_hasWit_varc (numeral 0)))) hwX hwY)

/-- Congruencia de `carcT` en `PrfH`. -/
theorem PrfH_congr_carcT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (carcT x =eq carcT y) := by
  unfold carcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_congr_cons_head h)))

/-! ### La evaluación compuesta -/

/-- **EVALUACIÓN COMPUESTA `carc (nthc p i)`**: dado `chainOk nil p` e `i < lenc p`,
    `⊢ Prov(⌜ carc (nthc(ṗ, ı̇)) = (carc (nthc p i))˙ ⌝)`. Encadena `pcc_eval_nthc` (nthc → valor),
    `prf_line_is_cons` (la línea es un `cons`) y `pcc_eval_carc` (`carc` sobre el `cons`). Es el
    puente que `hI_dot` necesita para reflejar `carc (nthc p i)` en el cuerpo de `boundedCarcIn`. -/
theorem pcc_eval_carc_nthc (p i : Term) :
    Prf (chainOk nil p ⇒ (lt i (lenc p) ⇒
      provFromCode (eqCodeFn (carcT (nthcT (tcFn p) (tcFn i))) (tcFn (carc (nthc p i)))))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc p)) [chainOk nil p] rfl)
  have hlt : PrfH [lt i (lenc p), chainOk nil p] (lt i (lenc p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hchain : PrfH [lt i (lenc p), chainOk nil p] (chainOk nil p) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hevalN : PrfH [lt i (lenc p), chainOk nil p]
      (provFromCode (eqc (nthcT (tcFn p) (tcFn i)) (tcFn (nthc p i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc p i) _) hlt
  have hcons : PrfH [lt i (lenc p), chainOk nil p]
      (nthc p i =eq cons (carc (nthc p i)) (cdrc (nthc p i))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_line_is_cons p i) _) hchain) hlt
  have hA : PrfH [lt i (lenc p), chainOk nil p]
      (provFromCode (eqc (carcT (nthcT (tcFn p) (tcFn i))) (carcT (tcFn (nthc p i))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_carcT_code_imp (nthcT (tcFn p) (tcFn i)) (tcFn (nthc p i))
      (substtc_inv_nthcT (substtc_inv_tcFn p) (substtc_inv_tcFn i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn p) (prf_hasWit_tcFn i))
      (prf_hasWit_tcFn (nthc p i))) _) hevalN
  have hcodeqB : PrfH [lt i (lenc p), chainOk nil p]
      (eqCodeFn (carcT (tcFn (cons (carc (nthc p i)) (cdrc (nthc p i))))) (tcFn (carc (nthc p i)))
        =eq eqCodeFn (carcT (tcFn (nthc p i))) (tcFn (carc (nthc p i)))) :=
    PrfH_congr_eqCodeFn
      (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl (tcFn (carc (nthc p i)))) _)
  have hB : PrfH [lt i (lenc p), chainOk nil p]
      (provFromCode (eqc (carcT (tcFn (nthc p i))) (tcFn (carc (nthc p i))))) :=
    PrfH_provCode_congr hcodeqB (prf_to_prfH (pcc_eval_carc (carc (nthc p i)) (cdrc (nthc p i))) _)
  exact PrfH_eq_trans_code (carcT (nthcT (tcFn p) (tcFn i))) (carcT (tcFn (nthc p i)))
    (tcFn (carc (nthc p i)))
    (substtc_inv_carcT (substtc_inv_nthcT (substtc_inv_tcFn p) (substtc_inv_tcFn i))) hA hB
    (prf_hasWit_carcT (prf_hasWit_nthcT (prf_hasWit_tcFn p) (prf_hasWit_tcFn i)))
    (prf_hasWit_carcT (prf_hasWit_tcFn (nthc p i)))
    (prf_hasWit_tcFn (carc (nthc p i)))

end ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

export ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf (
  PrfH_mp_code_apply PrfH_leibniz_apply PrfH_eq_trans_code
  pcc_congr_carcT_code_imp PrfH_congr_carcT pcc_eval_carc_nthc
)

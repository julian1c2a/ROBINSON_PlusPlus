/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFMpPrf

/-!
## META — NIVEL D real (B.3c): `lineWF` PUNTEADO, caso `mp` (tag 16)

Tercer caso de `pcc_lineWF_tracked`, y el **más barato de los tres estructurales**: su RHS es
**sólo la cláusula canónica de longitud**.

**Por qué no hay condición estructural.** A diferencia de los esquemas proposicionales (`p1`, `j3`,
`eqrefl`, …), `mp` **no impone nada sobre la conclusión**: la fidelidad de la regla la liga
íntegramente `ax_premsOf_mp`, que exige `implc premA concl` y `premA` entre las premisas de
contexto (y `chainOk` las obliga a estar ya en la cadena). Por eso el esquema estricto es

  `∀. (nthc #0 1 = 16̇) ⇒ (lineWF #0 ⇔ (lenc #0 = 3̇))`

sin segundo conjunto. Consecuencia práctica: el backbone **no lleva `andc`** y no hace falta ningún
reflector de condición — se reduce a un solo MP interno sobre el punteado de longitud.

⚠️ **Esto revisa el hallazgo B.2** (`Meta/LineWFCases.lean`): con el esquema antiguo,
*incondicional*, `mp` **no era refutable vía `lineWF`** (sólo vía `premsOf`). Con el esquema
estricto **sí lo es**, por longitud — es decir, `NegVerifier` gana una vía de refutación, no la
pierde. La solidez no se toca: restringir la FORMA de la línea no cambia qué puede concluirse.
-/

/-! ### Los componentes del bicondicional `ax_lineWF_mp` (ESTRICTO) -/

/-- Antecedente de etiqueta del caso `mp`: `nthc #0 1 = 16̇`. -/
def tagMp : Formula := nthc (.var 0) (succ zero) =eq numeralM 16

/-- Cláusula canónica de longitud (plan A): `lenc #0 = 3̇`. Es el RHS **completo** del caso `mp`. -/
def lencMp : Formula := lenc (.var 0) =eq numeralM 3

/-- El axioma‑accesor estricto, reexpresado con sus componentes (definicional). -/
theorem ax_lineWF_mp_eq :
    ax_lineWF_mp = Formula.forall (Formula.impl tagMp (lwfVar ⇔ lencMp)) := rfl

/-! ### Paso 6a — dirección `⇐` del bicondicional, currificada bajo el tag -/

/-- **Dirección `⇐` del bicondicional `ax_lineWF_mp` estricto, currificada bajo el tag.** -/
theorem prf_lineWF_mp_bwd :
    Prf (Formula.forall (Formula.impl tagMp (Formula.impl lencMp lwfVar))) := by
  refine Prf.gen _ ?_
  refine prf_deduction ?_
  refine deduction_aux ?_ lencMp [tagMp] rfl
  have hax : PrfH [lencMp, tagMp] (Formula.impl tagMp (lwfVar ⇔ lencMp)) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms])) (.var 0)
    have hid : Prf (Formula.impl tagMp (lwfVar ⇔ lencMp)) := by
      simpa [ax_lineWF_mp, tagMp, lencMp, lwfVar, iff, lineWF, lenc, nthc, numeralM, succ, zero,
        cons, nil, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] using hh
    exact prf_to_prfH hid _
  have hiff : PrfH [lencMp, tagMp] (lwfVar ⇔ lencMp) :=
    PrfH.mp _ _ _ hax (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  have hmpr : PrfH [lencMp, tagMp] (Formula.impl lencMp lwfVar) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hiff
  exact PrfH.mp _ _ _ hmpr (PrfH.hyp _ _ (List.Mem.head _))

/-! ### Paso 6b — el bicondicional TRANSPORTADO al nivel del código -/

/-- Código del antecedente de etiqueta, punteado en la línea `t`. -/
def tagDotM (t : Term) : Term := substfc zero (tcFn t) (formCode tagMp)

/-- Código de la cláusula canónica de longitud, punteado en la línea `t`. -/
def lencDotM (t : Term) : Term := substfc zero (tcFn t) (formCode lencMp)

/-- **Columna vertebral del paso 6, caso `mp`**. Más corta que la de `eqrefl`/`thy`: al no haber
    conjunción en el RHS, sólo hay que distribuir el `substfc` sobre **un** `implc`. -/
theorem paso6_backbone_mp (t : Term) :
    Prf (provFromCode (implc (tagDotM t) (implc (lencDotM t) (lwfDot t)))) := by
  have h := pcc_thm_inst _ prf_lineWF_mp_bwd (tcFn t)
  refine prf_mp (prf_provCode_congr ?_) h
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode tagMp)
      (formCode (Formula.impl lencMp lwfVar))) ?_
  refine prf_congr_implc (prf_refl _) ?_
  exact prf_substfc_impl zero (tcFn t) (formCode lencMp) (formCode lwfVar)

/-! ### Paso 6c/6d — los códigos punteados, evaluados y producidos -/

/-- **`TAG_dot` evaluado** (caso `mp`, tag 16). -/
theorem prf_tagDotM_eq (t : Term) :
    Prf (tagDotM t =eq
      eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM 16))) := by
  unfold tagDotM tagMp
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeral 16) (tcFn t))
  refine prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _) ?_
  exact prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeral 1) (tcFn t))

/-- **`Prov(TAG_dot t)`** (caso `mp`), bajo la cota `1 < lenc t` y la igualdad de etiqueta. -/
theorem pcc_tagDotM (t : Term) :
    Prf (lt (succ zero) (lenc t) ⇒
      ((nthc t (succ zero) =eq numeralM 16) ⇒ provFromCode (tagDotM t))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM 16)
    [lt (succ zero) (lenc t)] rfl)
  have hbound : PrfH [nthc t (succ zero) =eq numeralM 16, lt (succ zero) (lenc t)]
      (lt (succ zero) (lenc t)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htag : PrfH [nthc t (succ zero) =eq numeralM 16, lt (succ zero) (lenc t)]
      (nthc t (succ zero) =eq numeralM 16) := PrfH.hyp _ _ (List.Mem.head _)
  have hev : PrfH [nthc t (succ zero) =eq numeralM 16, lt (succ zero) (lenc t)]
      (provFromCode (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero)))
        (tcFn (nthc t (succ zero))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (succ zero)) _) hbound
  have hcodeq : PrfH [nthc t (succ zero) =eq numeralM 16, lt (succ zero) (lenc t)]
      (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero))) (tcFn (nthc t (succ zero)))
        =eq eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM 16))) :=
    PrfH_congr_eqCodeFn
      (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) (prf_to_prfH (prf_tc_numeral 1) _))
      (PrfH_eq_trans (PrfH_congr_tcFn htag) (prf_to_prfH (prf_tc_numeral 16) _))
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_tagDotM_eq t))) _)
    (PrfH_provCode_congr hcodeq hev)

/-- **`LENC_dot` evaluado** (caso `mp`). Coincide con el de `eqrefl` (misma longitud canónica `3̇`)
    salvo por el `formCode` de partida, que es el mismo — se reusa su prueba. -/
theorem prf_lencDotM_eq (t : Term) :
    Prf (lencDotM t =eq eqCodeFn (lencT (tcFn t)) (termCode (numeralM 3))) :=
  prf_lencDot_eq t

/-- **`Prov(LENC_dot t)`** a partir de la igualdad de longitud externa `lenc t = 3̇`. -/
theorem pcc_lencDotM (t : Term) :
    Prf ((lenc t =eq numeralM 3) ⇒ provFromCode (lencDotM t)) := pcc_lencDot t

/-! ### Paso 6g — reflector POR RAMA del caso `mp`, **sin hipótesis de cota** -/

/-- **Reflector por rama, caso `mp`** (accesor estricto, dirección `⇒` descargada): asumido sólo el
    tag `nthc t 1 = 16̇`, `lineWF t` refleja su código punteado. El más corto de los tres: un único
    punteado (la longitud) y un único MP interno. -/
theorem pcc_lineWF_tracked_mp_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 16) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM 16) [lineWF t] rfl)
  let Γ : List Formula := [nthc t (succ zero) =eq numeralM 16, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH Γ (nthc t (succ zero) =eq numeralM 16) := PrfH.hyp _ _ (List.Mem.head _)
  -- accesor ESTRICTO instanciado en `t`, dirección directa (`iff.mp` = c2)
  have hacc : Prf (Formula.impl (nthc t (succ zero) =eq numeralM 16)
      (lineWF t ⇔ (lenc t =eq numeralM 3))) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms])) t
    simpa [ax_lineWF_mp, iff, lineWF, lenc, nthc, numeralM, succ, zero, cons, nil,
      substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] using hh
  have hiff : PrfH Γ (lineWF t ⇔ (lenc t =eq numeralM 3)) :=
    PrfH.mp _ _ _ (prf_to_prfH hacc _) htagH
  have hlencH : PrfH Γ (lenc t =eq numeralM 3) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hiff) hlw
  -- cota DERIVADA de la longitud canónica
  have hb1 : PrfH Γ (lt (succ zero) (lenc t)) :=
    PrfH_lt_subst2 (PrfH_eq_symm hlencH)
      (prf_to_prfH (prf_lt_numeralM (a := 1) (b := 3) (by omega)) _)
  -- los dos punteados + MP interno ×2
  have hTag : PrfH Γ (provFromCode (tagDotM t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_tagDotM t) _) hb1) htagH
  have hLenc : PrfH Γ (provFromCode (lencDotM t)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lencDotM t) _) hlencH
  have hImp : PrfH Γ (provFromCode (implc (lencDotM t) (lwfDot t))) :=
    PrfH_mp_code_apply (prf_to_prfH (paso6_backbone_mp t) _) hTag
  have hLwf : PrfH Γ (provFromCode (lwfDot t)) := PrfH_mp_code_apply hImp hLenc
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_lwfDot_eq t)) _) hLwf

end ROBINSON_PlusPlus.Meta.LineWFMpPrf

export ROBINSON_PlusPlus.Meta.LineWFMpPrf (
  tagMp lencMp ax_lineWF_mp_eq prf_lineWF_mp_bwd
  tagDotM lencDotM paso6_backbone_mp
  prf_tagDotM_eq prf_lencDotM_eq pcc_tagDotM pcc_lencDotM
  pcc_lineWF_tracked_mp_imp
)

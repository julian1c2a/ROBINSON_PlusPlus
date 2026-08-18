/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.InAxiomsCodePrf

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
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFThyPrf

/-!
## META — NIVEL D real (B.3c): `lineWF` PUNTEADO, caso `thy` (tag 15)

Segundo caso cerrado de `pcc_lineWF_tracked` (tras `eqrefl`), y el **estructuralmente distinto**:
su condición no es una igualdad `=eq` sino la **pertenencia** `In (carc #0) axiomsCodeT`. Por eso
consume el `In`‑reflect de `Meta/InAxiomsCodePrf.lean` en lugar de `pcc_eq_tracked`.

**Esquema ESTRICTO** (plan A, igual que `eqrefl`): `ax_lineWF_thy` es hoy

  `∀. (nthc #0 1 = 15̇) ⇒ (lineWF #0 ⇔ ((lenc #0 = 2̇) ∧ In (carc #0) axiomsCodeT))`

La cláusula canónica `lenc = 2̇` (la línea `⟨concl, 15⟩` tiene dos componentes) **fuerza la cota**
`1 < lenc t` de la reflexión punteada, que con el esquema laxo no era derivable.

**El truco que evita re‑hacer el `In`‑reflect.** `pcc_In_axiomsCodeT_tracked` pide un puente
`hbr : Prov(⌜yc = ẏ⌝)` como hipótesis **`Prf` cerrada**. Instanciarlo con `yc = carcT ṫ` obligaría
a tener el puente `Prov(carcT ṫ = (carc t)˙)` fuera de contexto — pero ése depende de `lineWF t`
(es `pcc_eval_carc` + la estructura `cons` de la línea), que sólo está en el contexto. La salida:
instanciarlo con **`yc = (carc t)˙`**, para el que el puente es la **reflexividad interna**
(`prf_provFromCode_eqCodeFn_refl`, incondicional), y hacer el encaje `(carc t)˙ → carcT ṫ`
**después**, con un único Leibniz interno en el hueco 1 del átomo `In`
(`prf_substfc_inFormCode_hole1`), ya dentro del contexto donde `lineWF t` está disponible.
-/

/-! ### Invariancia `substtc` del código de `axiomsCodeT`

`termCode axiomsCodeT` aparece **estáticamente** dentro del código punteado `inDotT`, luego su
invariancia bajo `substtc` es imprescindible para evaluarlo. ⚠️ **No sale por el atajo
`substtc_inv_termCode_of_tc`**: éste pide el puente `tcFn a =eq termCode a`, y para
`a = axiomsCodeT` ese puente es **falso** — `axiomsCodeT` es opaco y `prf_axiomsCodeT_eq` sólo lo
ancla a `listFormCodeM axioms` a nivel OBJETO, mientras que `termCode axiomsCodeT` y
`termCode (listFormCodeM axioms)` son códigos meta distintos (de hecho, provablemente distintos).

Se prueba en cambio **estructuralmente**: `axiomsCodeT = .func "axiomsCodeT" []`, así que su código
es `funcc ⌜"axiomsCodeT"⌝ nil`, un árbol cerrado sin ningún `varc` ⟹ `substtc` es la identidad por
las ecuaciones `ax_substtc_func` / `ax_substtsc_nil`. -/

/-- **`termCode axiomsCodeT` es `substtc`‑invariante** (código cerrado, sin huecos). -/
theorem substtc_inv_termCode_axiomsCodeT (W : Term) :
    Prf (substtc zero W (termCode axiomsCodeT) =eq termCode axiomsCodeT) := by
  show Prf (substtc zero W (funcc (strCode "axiomsCodeT") nil)
    =eq funcc (strCode "axiomsCodeT") nil)
  exact prf_eq_trans (prf_substtc_func zero W (strCode "axiomsCodeT") nil)
    (prf_congr_bin2 (prf_substtsc_nil zero W))

/-! ### Los componentes del bicondicional `ax_lineWF_thy` (ESTRICTO), sobre la línea abstracta `#0` -/

/-- Antecedente de etiqueta del caso `thy`: `nthc #0 1 = 15̇`. -/
def tagThy : Formula := nthc (.var 0) (succ zero) =eq numeralM 15

/-- Cláusula canónica de longitud (plan A): `lenc #0 = 2̇`. -/
def lencThy : Formula := lenc (.var 0) =eq numeralM 2

/-- Condición estructural del caso `thy`: `In (carc #0) axiomsCodeT`. **No es un `=eq`** — es la
    pertenencia, y de ahí que este caso consuma el `In`‑reflect. -/
def inThy : Formula := In (carc (.var 0)) axiomsCodeT

/-- El axioma‑accesor estricto, reexpresado con sus componentes (definicional). -/
theorem ax_lineWF_thy_eq :
    ax_lineWF_thy
      = Formula.forall (Formula.impl tagThy (lwfVar ⇔ Formula.and lencThy inThy)) := rfl

/-! ### Paso 6a — dirección `⇐` del bicondicional, currificada bajo el tag -/

/-- **Dirección `⇐` del bicondicional `ax_lineWF_thy` estricto, currificada bajo el tag.** -/
theorem prf_lineWF_thy_bwd :
    Prf (Formula.forall (Formula.impl tagThy
      (Formula.impl (Formula.and lencThy inThy) lwfVar))) := by
  refine Prf.gen _ ?_
  refine prf_deduction ?_
  refine deduction_aux ?_ (Formula.and lencThy inThy) [tagThy] rfl
  have hax : PrfH [Formula.and lencThy inThy, tagThy]
      (Formula.impl tagThy (lwfVar ⇔ Formula.and lencThy inThy)) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms])) (.var 0)
    have hid : Prf (Formula.impl tagThy (lwfVar ⇔ Formula.and lencThy inThy)) := by
      simpa [ax_lineWF_thy, tagThy, lencThy, inThy, lwfVar, iff, lineWF, carc, lenc, nthc, In,
        axiomsCodeT, numeralM, succ, zero, cons, nil, substFormula, substTerm, substTerms,
        FOL.substTerm_liftTerm] using hh
    exact prf_to_prfH hid _
  have hiff : PrfH [Formula.and lencThy inThy, tagThy]
      (lwfVar ⇔ Formula.and lencThy inThy) :=
    PrfH.mp _ _ _ hax (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  have hmpr : PrfH [Formula.and lencThy inThy, tagThy]
      (Formula.impl (Formula.and lencThy inThy) lwfVar) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hiff
  exact PrfH.mp _ _ _ hmpr (PrfH.hyp _ _ (List.Mem.head _))

/-! ### Paso 6b — el bicondicional TRANSPORTADO al nivel del código, instanciado en `tcFn t` -/

/-- Código del antecedente de etiqueta, punteado en la línea `t`. -/
def tagDotT (t : Term) : Term := substfc zero (tcFn t) (formCode tagThy)

/-- Código de la cláusula canónica de longitud, punteado en la línea `t`. -/
def lencDotT (t : Term) : Term := substfc zero (tcFn t) (formCode lencThy)

/-- Código de la condición de pertenencia, punteado en la línea `t`. -/
def inDotT (t : Term) : Term := substfc zero (tcFn t) (formCode inThy)

/-- **Columna vertebral del paso 6, caso `thy`**: el bicondicional (dirección `⇐`) transportado al
    nivel del código y punteado en `t`. Misma plantilla que `paso6_backbone` (`eqrefl`). -/
theorem paso6_backbone_thy (t : Term) :
    Prf (provFromCode
      (implc (tagDotT t) (implc (andc (lencDotT t) (inDotT t)) (lwfDot t)))) := by
  have h := pcc_thm_inst _ prf_lineWF_thy_bwd (tcFn t)
  refine prf_mp (prf_provCode_congr ?_) h
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode tagThy)
      (formCode (Formula.impl (Formula.and lencThy inThy) lwfVar))) ?_
  refine prf_congr_implc (prf_refl _) ?_
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode (Formula.and lencThy inThy))
      (formCode lwfVar)) ?_
  exact prf_congr_implc
    (prf_substfc_and zero (tcFn t) (formCode lencThy) (formCode inThy))
    (prf_refl _)

/-! ### Paso 6c — los códigos punteados, EVALUADOS a forma rastreada -/

/-- **`TAG_dot` evaluado** (caso `thy`, tag 15). -/
theorem prf_tagDotT_eq (t : Term) :
    Prf (tagDotT t =eq
      eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM 15))) := by
  unfold tagDotT tagThy
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeral 15) (tcFn t))
  refine prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _) ?_
  exact prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeral 1) (tcFn t))

/-- **`LENC_dot` evaluado** (longitud canónica `2̇` del caso `thy`). -/
theorem prf_lencDotT_eq (t : Term) :
    Prf (lencDotT t =eq eqCodeFn (lencT (tcFn t)) (termCode (numeralM 2))) := by
  unfold lencDotT lencThy
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeral 2) (tcFn t))
  exact prf_eq_trans (prf_substtc_lencT zero (tcFn t) (varc (numeral 0)))
    (prf_congr_lencT (prf_substtc_varc0 (tcFn t)))

/-- **`IN_dot` evaluado**: `substfc 0 ṫ ⌜In (carc #0) axiomsCodeT⌝ = ⌜In (carc ṫ) axiomsCodeT~⌝`.
    El hueco `⌜v₀⌝` (bajo `carcT`) recibe `ṫ`; el 2º argumento es el código cerrado
    `termCode axiomsCodeT`, invariante por `substtc_inv_termCode_axiomsCodeT`. -/
theorem prf_inDotT_eq (t : Term) :
    Prf (inDotT t =eq inFormCodeFn (carcT (tcFn t)) (termCode axiomsCodeT)) := by
  show Prf (substfc zero (tcFn t) (atomc (strCode in_sym)
      (cons (carcT (varc (numeral 0))) (cons (termCode axiomsCodeT) nil)))
    =eq atomc (strCode in_sym) (cons (carcT (tcFn t)) (cons (termCode axiomsCodeT) nil)))
  refine prf_eq_trans (prf_substfc_atom zero (tcFn t) (strCode in_sym) _) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero (tcFn t) _ _) ?_
  refine prf_eq_trans (prf_congr_cons_head ?_) (prf_congr_cons_tail ?_)
  · exact prf_eq_trans (prf_substtc_carcT zero (tcFn t) _)
      (prf_congr_carcT (prf_substtc_varc0 (tcFn t)))
  · refine prf_eq_trans (prf_substtsc_cons zero (tcFn t) _ _) ?_
    exact prf_eq_trans (prf_congr_cons_head (substtc_inv_termCode_axiomsCodeT (tcFn t)))
      (prf_congr_cons_tail (prf_substtsc_nil zero (tcFn t)))

/-! ### Paso 6d — PRODUCCIÓN de los punteados -/

/-- **`Prov(TAG_dot t)`** (caso `thy`), bajo la cota `1 < lenc t` y la igualdad de etiqueta. -/
theorem pcc_tagDotT (t : Term) :
    Prf (lt (succ zero) (lenc t) ⇒
      ((nthc t (succ zero) =eq numeralM 15) ⇒ provFromCode (tagDotT t))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM 15)
    [lt (succ zero) (lenc t)] rfl)
  have hbound : PrfH [nthc t (succ zero) =eq numeralM 15, lt (succ zero) (lenc t)]
      (lt (succ zero) (lenc t)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htag : PrfH [nthc t (succ zero) =eq numeralM 15, lt (succ zero) (lenc t)]
      (nthc t (succ zero) =eq numeralM 15) := PrfH.hyp _ _ (List.Mem.head _)
  have hev : PrfH [nthc t (succ zero) =eq numeralM 15, lt (succ zero) (lenc t)]
      (provFromCode (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero)))
        (tcFn (nthc t (succ zero))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (succ zero)) _) hbound
  have hcodeq : PrfH [nthc t (succ zero) =eq numeralM 15, lt (succ zero) (lenc t)]
      (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero))) (tcFn (nthc t (succ zero)))
        =eq eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM 15))) :=
    PrfH_congr_eqCodeFn
      (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) (prf_to_prfH (prf_tc_numeral 1) _))
      (PrfH_eq_trans (PrfH_congr_tcFn htag) (prf_to_prfH (prf_tc_numeral 15) _))
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_tagDotT_eq t))) _)
    (PrfH_provCode_congr hcodeq hev)

/-- **`Prov(LENC_dot t)`** a partir de la igualdad de longitud externa `lenc t = 2̇`. -/
theorem pcc_lencDotT (t : Term) :
    Prf ((lenc t =eq numeralM 2) ⇒ provFromCode (lencDotT t)) := by
  refine prf_deduction ?_
  have hev : PrfH [lenc t =eq numeralM 2]
      (provFromCode (eqCodeFn (lencT (tcFn t)) (tcFn (lenc t)))) :=
    prf_to_prfH (pcc_eval_lenc t) _
  have hval : PrfH [lenc t =eq numeralM 2] (tcFn (lenc t) =eq termCode (numeralM 2)) :=
    PrfH_eq_trans (PrfH_congr_tcFn (prfH_hyp_self _)) (prf_to_prfH (prf_tc_numeral 2) _)
  have hev2 : PrfH [lenc t =eq numeralM 2]
      (provFromCode (eqCodeFn (lencT (tcFn t)) (termCode (numeralM 2)))) :=
    PrfH_provCode_congr (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) hval) hev
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_lencDotT_eq t))) _) hev2

/-- **`Prov(IN_dot t)`** — el corazón del caso `thy`.

    De `In (carc t) axiomsCodeT` sale, por el `In`‑reflect (`pcc_In_axiomsCodeT_tracked`
    instanciado en `yc = (carc t)˙`, cuyo puente es la reflexividad interna), el código
    `⌜In (carc t)˙ axiomsCodeT~⌝`; y de `lineWF t` sale, por `pcc_eval_carc` + la estructura `cons`
    de la línea, el puente `Prov(carcT ṫ = (carc t)˙)`, que un Leibniz interno usa para cambiar
    `(carc t)˙` por `carcT ṫ` en el hueco 1 del átomo `In`. -/
theorem pcc_inDotT (t : Term) :
    Prf (lineWF t ⇒ (In (carc t) axiomsCodeT ⇒ provFromCode (inDotT t))) := by
  refine prf_deduction (deduction_aux ?_ (In (carc t) axiomsCodeT) [lineWF t] rfl)
  let Γ : List Formula := [In (carc t) axiomsCodeT, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hin : PrfH Γ (In (carc t) axiomsCodeT) := PrfH.hyp _ _ (List.Mem.head _)
  -- (1) `In`-reflect con `yc = (carc t)˙`: el puente es la reflexividad interna (incondicional)
  have hrefl : PrfH Γ (provFromCode (inFormCodeFn (tcFn (carc t)) (termCode axiomsCodeT))) :=
    PrfH.mp _ _ _
      (prf_to_prfH (pcc_In_axiomsCodeT_tracked (tcFn (carc t)) (carc t)
        (substtc_inv_tcFn _) (prf_provFromCode_eqCodeFn_refl (tcFn (carc t)))) _) hin
  -- (2) puente de evaluación `Prov(carcT ṫ = (carc t)˙)` (necesita la estructura `cons`)
  have hcons := PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_cons t) _) hlw
  have hcarc0 := prf_to_prfH (pcc_eval_carc (carc t) (cdrc t)) Γ
  have hcarc : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (tcFn (carc t)))) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
        (prf_to_prfH (prf_refl _) _)) hcarc0
  have hCinv : ∀ W, Prf (substtc zero W (carcT (tcFn t)) =eq carcT (tcFn t)) := fun W =>
    prf_eq_trans (prf_substtc_carcT zero W (tcFn t))
      (prf_congr_carcT (substtc_inv_tcFn t W))
  have hsym : PrfH Γ (provFromCode (eqc (tcFn (carc t)) (carcT (tcFn t)))) :=
    PrfH_eq_symm_code (carcT (tcFn t)) (tcFn (carc t)) hCinv hcarc
  -- (3) Leibniz interno en el hueco 1 del átomo `In`: `(carc t)˙ → carcT ṫ`
  let Ac : Term := inFormCodeFn (varc (numeral 0)) (termCode axiomsCodeT)
  have h1 : PrfH Γ (provFromCode (substfc zero (tcFn (carc t)) Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm
      (prf_substfc_inFormCode_hole1 (tcFn (carc t)) (termCode axiomsCodeT)
        substtc_inv_termCode_axiomsCodeT))) _) hrefl
  have h2 : PrfH Γ (provFromCode (substfc zero (carcT (tcFn t)) Ac)) :=
    PrfH_leibniz_apply Ac (tcFn (carc t)) (carcT (tcFn t)) hsym h1
  have h3 : PrfH Γ (provFromCode (inFormCodeFn (carcT (tcFn t)) (termCode axiomsCodeT))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (prf_substfc_inFormCode_hole1 (carcT (tcFn t)) (termCode axiomsCodeT)
        substtc_inv_termCode_axiomsCodeT)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_inDotT_eq t))) _) h3

/-! ### Paso 6g — reflector POR RAMA del caso `thy`, **sin hipótesis de cota** -/

/-- **Reflector por rama, caso `thy`** (accesor estricto, dirección `⇒` descargada): asumido sólo
    el tag `nthc t 1 = 15̇` (que el `or_elim` de `prf_lineWF_inv` provee en este disyunto),
    `lineWF t` refleja su código punteado. Espejo exacto de `pcc_lineWF_tracked_eqrefl_imp`. -/
theorem pcc_lineWF_tracked_thy_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 15) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM 15) [lineWF t] rfl)
  let Γ : List Formula := [nthc t (succ zero) =eq numeralM 15, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH Γ (nthc t (succ zero) =eq numeralM 15) := PrfH.hyp _ _ (List.Mem.head _)
  -- accesor ESTRICTO instanciado en `t`, dirección directa (`iff.mp` = c2)
  have hacc : Prf (Formula.impl (nthc t (succ zero) =eq numeralM 15)
      (lineWF t ⇔ Formula.and (lenc t =eq numeralM 2) (In (carc t) axiomsCodeT))) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms])) t
    simpa [ax_lineWF_thy, iff, lineWF, carc, lenc, nthc, In, axiomsCodeT, numeralM, succ, zero,
      cons, nil, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] using hh
  have hiff : PrfH Γ (lineWF t ⇔ Formula.and (lenc t =eq numeralM 2)
      (In (carc t) axiomsCodeT)) :=
    PrfH.mp _ _ _ (prf_to_prfH hacc _) htagH
  have hand : PrfH Γ (Formula.and (lenc t =eq numeralM 2) (In (carc t) axiomsCodeT)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hiff) hlw
  have hlencH : PrfH Γ (lenc t =eq numeralM 2) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have hinH : PrfH Γ (In (carc t) axiomsCodeT) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  -- cota DERIVADA de la longitud canónica (`thy` sólo necesita `1 < lenc t`)
  have hb1 : PrfH Γ (lt (succ zero) (lenc t)) :=
    PrfH_lt_subst2 (PrfH_eq_symm hlencH)
      (prf_to_prfH (prf_lt_numeralM (a := 1) (b := 2) (by omega)) _)
  -- los tres punteados producidos en el contexto
  have hTag : PrfH Γ (provFromCode (tagDotT t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_tagDotT t) _) hb1) htagH
  have hLenc : PrfH Γ (provFromCode (lencDotT t)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lencDotT t) _) hlencH
  have hIn : PrfH Γ (provFromCode (inDotT t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_inDotT t) _) hlw) hinH
  -- `∧`‑intro interno + MP interno ×2 + `lwfDot = lineWFCodeFn`
  have hAnd : PrfH Γ (provFromCode (andc (lencDotT t) (inDotT t))) :=
    PrfH_and_intro_code (lencDotT t) (inDotT t) hLenc hIn
  have hImp : PrfH Γ (provFromCode (implc (andc (lencDotT t) (inDotT t)) (lwfDot t))) :=
    PrfH_mp_code_apply (prf_to_prfH (paso6_backbone_thy t) _) hTag
  have hLwf : PrfH Γ (provFromCode (lwfDot t)) := PrfH_mp_code_apply hImp hAnd
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_lwfDot_eq t)) _) hLwf

end ROBINSON_PlusPlus.Meta.LineWFThyPrf

export ROBINSON_PlusPlus.Meta.LineWFThyPrf (
  substtc_inv_termCode_axiomsCodeT
  tagThy lencThy inThy ax_lineWF_thy_eq prf_lineWF_thy_bwd
  tagDotT lencDotT inDotT paso6_backbone_thy
  prf_tagDotT_eq prf_lencDotT_eq prf_inDotT_eq
  pcc_tagDotT pcc_lencDotT pcc_inDotT
  pcc_lineWF_tracked_thy_imp
)

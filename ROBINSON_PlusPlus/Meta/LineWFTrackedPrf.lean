/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

/-!
## META — NIVEL D real (B.3c de `PLAN-NEGVERIFIER.md`): `lineWF` PUNTEADO, caso `eqrefl`

**Objetivo del módulo (B.3c).** `pcc_lineWF_tracked (t) : Prf (lineWF t ⇒ provFromCode
(lineWFCodeFn (tcFn t)))` — la reflexión *punteada* del átomo `lineWF` que consume `hC_dot`
(y con ella D3). El plan (diseño §16) son **21 casos de etiqueta**; este módulo cierra el
**caso piloto `eqrefl` (tag 12)**, cuya producción libre de muro
(`prf_provFromCode_eqCodeFn_refl`) ya existe, para validar el patrón y medir el coste real
por tag antes del batch.

**Esqueleto del caso (pasos 1–6).**
1. `prf_lineWF_inv t` da `⋁_{k≤20} (lineTag t =eq k̇)` → `PrfH_or_elim` de 21 ramas.
2. En la rama `k`, el bicondicional‑accesor `ax_lineWF_<k>` reduce `lineWF t` a `carc t =eq expr_k`.
3. Reflejar ese `=eq` con `pcc_eq_tracked` (libre de muro).
6. **Transporte codificado del bicondicional** — la pieza densa, *común a los 21 casos*
   (sólo cambian el axioma y `expr_k`). Es lo que construye este módulo.

**Columna vertebral del paso 6** (`prf_lineWF_eqrefl_bwd` + `paso6_backbone`): reflejar el
axioma con `pcc_thm_inst` (testigo `tcFn t`) produce el bicondicional codificado con forma
`substfc zero (tcFn t) (formCode …)` — **la misma forma que `hI_dot`/`bddCarcDot` ya dominan**
(`inDotAt φ p = substfc zero (tcFn p) (formCode …)`), y la maquinaria de tracking de accesores
existe (`pcc_eval_carc_nthc`). ⟹ el paso 6 **no** está bloqueado por puentes inexistentes; es
composición densa.

⚠️ **El encaje forma‑`substfc` / forma‑`tcFn` NO va por `pcc_eq_tracked` directo** (sería
Tarski) sino por **evaluación provable** (`pcc_eval_nthc` / `pcc_eval_carc_nthc`, que operan
DENTRO de `Prov` bajo cota) — que es justo lo que resuelven los `pcc_eval_*`.
-/

/-! ### Los tres componentes del bicondicional `ax_lineWF_eqrefl`, sobre la línea abstracta `#0` -/

/-- Antecedente de etiqueta del caso `eqrefl`: `nthc #0 1 = 12̇`. -/
def tagEqrefl : Formula := nthc (.var 0) (succ zero) =eq numeralM 12

/-- Condición estructural del caso `eqrefl`: `carc #0 = eqc (nthc #0 2) (nthc #0 2)`. -/
def eqEqrefl : Formula :=
  carc (.var 0) =eq eqc (nthc (.var 0) (numeralM 2)) (nthc (.var 0) (numeralM 2))

/-- La conclusión del bicondicional: `lineWF #0`. -/
def lwfVar : Formula := lineWF (.var 0)

/-- El axioma‑accesor, reexpresado con los tres componentes (definicional). -/
theorem ax_lineWF_eqrefl_eq :
    ax_lineWF_eqrefl = Formula.forall (Formula.impl tagEqrefl (lwfVar ⇔ eqEqrefl)) := rfl

/-! ### Paso 6a — dirección `⇐` del bicondicional, currificada bajo el tag

De `ax_lineWF_eqrefl : ∀. (TAG ⇒ (LWF ⇔ EQ))` sale `∀. (TAG ⇒ (EQ ⇒ LWF))`: se instancia en
`#0` (sustitución identidad), se descargan las dos hipótesis con el teorema de deducción y se
toma la segunda componente del `⇔` con `Prf₀.c3` (`iff.mpr` interno). -/

/-- **Dirección `⇐` del bicondicional `ax_lineWF_eqrefl`, currificada bajo el tag.** -/
theorem prf_lineWF_eqrefl_bwd :
    Prf (Formula.forall (Formula.impl tagEqrefl (Formula.impl eqEqrefl lwfVar))) := by
  refine Prf.gen _ ?_
  refine prf_deduction ?_
  refine deduction_aux ?_ eqEqrefl [tagEqrefl] rfl
  -- ctx `[EQ, TAG]` ⊢ `LWF`
  have hax : PrfH [eqEqrefl, tagEqrefl] (Formula.impl tagEqrefl (lwfVar ⇔ eqEqrefl)) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms])) (.var 0)
    have hid : Prf (Formula.impl tagEqrefl (lwfVar ⇔ eqEqrefl)) := by
      simpa [ax_lineWF_eqrefl, tagEqrefl, eqEqrefl, lwfVar, iff, lineWF, carc, nthc, eqc,
        numeralM, succ, zero, cons, nil, substFormula, substTerm, substTerms,
        FOL.substTerm_liftTerm] using hh
    exact prf_to_prfH hid _
  -- MP con el tag (2ª hipótesis del contexto) ⇒ el bicondicional
  have hiff : PrfH [eqEqrefl, tagEqrefl] (lwfVar ⇔ eqEqrefl) :=
    PrfH.mp _ _ _ hax (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  -- `c3` = 2ª componente del `⇔` = la dirección `EQ ⇒ LWF`
  have hmpr : PrfH [eqEqrefl, tagEqrefl] (Formula.impl eqEqrefl lwfVar) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hiff
  -- MP con la condición estructural (1ª hipótesis del contexto)
  exact PrfH.mp _ _ _ hmpr (PrfH.hyp _ _ (List.Mem.head _))

/-! ### Paso 6b — el bicondicional TRANSPORTADO al nivel del código, instanciado en `tcFn t`

`pcc_thm_inst` internaliza el teorema universal anterior en el código‑testigo `tcFn t`
(abierto), y `prf_substfc_impl` distribuye el `substfc` sobre los dos `implc`. -/

/-- Código del antecedente de etiqueta, punteado en la línea `t`. -/
def tagDot (t : Term) : Term := substfc zero (tcFn t) (formCode tagEqrefl)

/-- Código de la condición estructural, punteado en la línea `t`. -/
def eqDot (t : Term) : Term := substfc zero (tcFn t) (formCode eqEqrefl)

/-- Código de `lineWF`, punteado en la línea `t`. -/
def lwfDot (t : Term) : Term := substfc zero (tcFn t) (formCode lwfVar)

/-- **COLUMNA VERTEBRAL DEL PASO 6**: el bicondicional (dirección `⇐`) transportado al nivel
    del código y punteado en `t`:

    `Prov(⌜TAG_dot t ⇒ (EQ_dot t ⇒ LWF_dot t)⌝)`

    Es la plantilla `pcc_bddDot_imp_inDot`, **común a los 21 casos de etiqueta**: sólo cambian
    el axioma‑accesor y la `expr_k` de la condición estructural. -/
theorem paso6_backbone (t : Term) :
    Prf (provFromCode (implc (tagDot t) (implc (eqDot t) (lwfDot t)))) := by
  have h := pcc_thm_inst _ prf_lineWF_eqrefl_bwd (tcFn t)
  refine prf_mp (prf_provCode_congr ?_) h
  -- distribuye el `substfc` sobre los dos `implc`
  exact prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode tagEqrefl)
      (formCode (Formula.impl eqEqrefl lwfVar)))
    (prf_congr_implc (prf_refl _)
      (prf_substfc_impl zero (tcFn t) (formCode eqEqrefl) (formCode lwfVar)))

/-! ### Paso 6c — los códigos punteados, EVALUADOS

`tagDot`/`eqDot` son `substfc`‑aplicaciones sin reducir. Aquí se calculan a la forma
*rastreada* (`nthcT (tcFn t) …`) que consumen `pcc_eval_nthc` / `pcc_eval_carc_nthc`. Es pura
distribución de `substfc`/`substtc` sobre los constructores de código, con el hueco `⌜v₀⌝`
recibiendo `tcFn t` (`prf_substtc_varc0`) y los subcódigos cerrados invariantes. -/

/-- `termCode a` es `substtc`‑invariante cuando `a` está **rastreado** (`tcFn a =eq termCode a`):
    el código de un código es cerrado. Generaliza `substtc_inv_termCode_formCode`. -/
theorem substtc_inv_termCode_of_tc {a : Term} (htc : Prf (tcFn a =eq termCode a)) :
    ∀ W, Prf (substtc zero W (termCode a) =eq termCode a) := fun W =>
  prf_eq_trans (prf_congr_substtc3 (prf_eq_symm htc))
    (prf_eq_trans (prf_substtc_tcFn W a) htc)

/-- **`TAG_dot` evaluado**: `substfc 0 (tcFn t) ⌜nthc #0 1 = 12̇⌝ = ⌜nthc(ṫ,1̇) = 12̇⌝`.
    El hueco `⌜v₀⌝` recibe `tcFn t`; los numerales `1̇`/`12̇` son cerrados (`prf_tc_numeral`). -/
theorem prf_tagDot_eq (t : Term) :
    Prf (tagDot t =eq
      eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM 12))) := by
  unfold tagDot tagEqrefl
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (substtc_inv_termCode_of_tc (prf_tc_numeral 12) (tcFn t))
  refine prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _) ?_
  exact prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
    (substtc_inv_termCode_of_tc (prf_tc_numeral 1) (tcFn t))

/-! #### El código de `eqc`

A diferencia de `carc`/`nthc` (que son `.func`, con constructor `carcT`/`nthcT`), `eqc a b` es un
**`cons`‑árbol** (`⟨4, a, b⟩`), luego su código es un árbol de `consT`. Se le da constructor
object propio, `eqcT`, con su congruencia y su distribución de `substtc`. -/

/-- Constructor object del código de `eqc a b` desde los códigos `a`, `b` de sus argumentos. -/
def eqcT (a b : Term) : Term :=
  consT (termCode (numeralM 4)) (consT a (consT b (termCode nil)))

/-- Puente definicional con `termCode`. -/
theorem eqcT_termCode (a b : Term) : eqcT (termCode a) (termCode b) = termCode (eqc a b) := rfl

/-- Congruencia de `eqcT` en ambos argumentos. -/
theorem prf_congr_eqcT {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (eqcT a b =eq eqcT a' b') := by
  unfold eqcT
  exact prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- `substtc` distribuye sobre `eqcT` (los subcódigos `4̇` y `⌜nil⌝` son cerrados). -/
theorem prf_substtc_eqcT (W a b : Term) :
    Prf (substtc zero W (eqcT a b) =eq eqcT (substtc zero W a) (substtc zero W b)) := by
  unfold eqcT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_of_tc (prf_tc_numeral 4) W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (prf_refl _) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _) (substtc_inv_termCode_of_tc prf_tc_zero W)

/-- **`EQ_dot` evaluado**: `substfc 0 (tcFn t) ⌜carc #0 = eqc (nthc #0 2) (nthc #0 2)⌝`
    `= ⌜carc(ṫ) = eqc(nthc(ṫ,2̇), nthc(ṫ,2̇))⌝`. Misma distribución que `TAG_dot`, un nivel
    más profunda (el `eqc` anidado). -/
theorem prf_eqDot_eq (t : Term) :
    Prf (eqDot t =eq eqCodeFn (carcT (tcFn t))
      (eqcT (nthcT (tcFn t) (termCode (numeralM 2)))
            (nthcT (tcFn t) (termCode (numeralM 2))))) := by
  unfold eqDot eqEqrefl
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ ?_
  · exact prf_eq_trans (prf_substtc_carcT zero (tcFn t) _)
      (prf_congr_carcT (prf_substtc_varc0 (tcFn t)))
  · refine prf_eq_trans (prf_substtc_eqcT (tcFn t) _ _) ?_
    refine prf_congr_eqcT ?_ ?_ <;>
      exact prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _)
        (prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
          (substtc_inv_termCode_of_tc (prf_tc_numeral 2) (tcFn t)))

end ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

export ROBINSON_PlusPlus.Meta.LineWFTrackedPrf (
  tagEqrefl eqEqrefl lwfVar ax_lineWF_eqrefl_eq prf_lineWF_eqrefl_bwd
  tagDot eqDot lwfDot paso6_backbone
)

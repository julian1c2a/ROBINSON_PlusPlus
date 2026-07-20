/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.EvalBoundedPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.D3InDotPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
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
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf

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

/-! ### Los componentes del bicondicional `ax_lineWF_eqrefl` (ESTRICTO), sobre la línea abstracta `#0`

Tras el plan (A) — esquema estricto — el `⇔` tiene RHS `lencEqrefl ∧ eqEqrefl`: la cláusula
canónica de longitud (`lenc #0 = 3̇`, que fuerza las cotas de sub‑índice) **y** la condición
estructural. -/

/-- Antecedente de etiqueta del caso `eqrefl`: `nthc #0 1 = 12̇`. -/
def tagEqrefl : Formula := nthc (.var 0) (succ zero) =eq numeralM 12

/-- Cláusula canónica de longitud (plan A): `lenc #0 = 3̇`. -/
def lencEqrefl : Formula := lenc (.var 0) =eq numeralM 3

/-- Condición estructural del caso `eqrefl`: `carc #0 = eqc (nthc #0 2) (nthc #0 2)`. -/
def eqEqrefl : Formula :=
  carc (.var 0) =eq eqc (nthc (.var 0) (numeralM 2)) (nthc (.var 0) (numeralM 2))

/-- La conclusión del bicondicional: `lineWF #0`. -/
def lwfVar : Formula := lineWF (.var 0)

/-- El axioma‑accesor estricto, reexpresado con sus componentes (definicional). -/
theorem ax_lineWF_eqrefl_eq :
    ax_lineWF_eqrefl
      = Formula.forall (Formula.impl tagEqrefl (lwfVar ⇔ Formula.and lencEqrefl eqEqrefl)) := rfl

/-! ### Paso 6a — dirección `⇐` del bicondicional, currificada bajo el tag

De `ax_lineWF_eqrefl : ∀. (TAG ⇒ (LWF ⇔ (LENC ∧ EQ)))` sale `∀. (TAG ⇒ ((LENC ∧ EQ) ⇒ LWF))`:
se instancia en `#0`, se descargan las dos hipótesis con deducción y se toma la 2ª componente del
`⇔` con `Prf₀.c3` (`iff.mpr` interno). -/

/-- **Dirección `⇐` del bicondicional `ax_lineWF_eqrefl` estricto, currificada bajo el tag.** -/
theorem prf_lineWF_eqrefl_bwd :
    Prf (Formula.forall (Formula.impl tagEqrefl
      (Formula.impl (Formula.and lencEqrefl eqEqrefl) lwfVar))) := by
  refine Prf.gen _ ?_
  refine prf_deduction ?_
  refine deduction_aux ?_ (Formula.and lencEqrefl eqEqrefl) [tagEqrefl] rfl
  -- ctx `[LENC ∧ EQ, TAG]` ⊢ `LWF`
  have hax : PrfH [Formula.and lencEqrefl eqEqrefl, tagEqrefl]
      (Formula.impl tagEqrefl (lwfVar ⇔ Formula.and lencEqrefl eqEqrefl)) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms])) (.var 0)
    have hid : Prf (Formula.impl tagEqrefl (lwfVar ⇔ Formula.and lencEqrefl eqEqrefl)) := by
      simpa [ax_lineWF_eqrefl, tagEqrefl, lencEqrefl, eqEqrefl, lwfVar, iff, lineWF, carc, lenc,
        nthc, eqc, numeralM, succ, zero, cons, nil, substFormula, substTerm, substTerms,
        FOL.substTerm_liftTerm] using hh
    exact prf_to_prfH hid _
  -- MP con el tag (2ª hipótesis del contexto) ⇒ el bicondicional
  have hiff : PrfH [Formula.and lencEqrefl eqEqrefl, tagEqrefl]
      (lwfVar ⇔ Formula.and lencEqrefl eqEqrefl) :=
    PrfH.mp _ _ _ hax (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  -- `c3` = 2ª componente del `⇔` = la dirección `(LENC ∧ EQ) ⇒ LWF`
  have hmpr : PrfH [Formula.and lencEqrefl eqEqrefl, tagEqrefl]
      (Formula.impl (Formula.and lencEqrefl eqEqrefl) lwfVar) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hiff
  -- MP con `LENC ∧ EQ` (1ª hipótesis del contexto)
  exact PrfH.mp _ _ _ hmpr (PrfH.hyp _ _ (List.Mem.head _))

/-! ### Paso 6b — el bicondicional TRANSPORTADO al nivel del código, instanciado en `tcFn t`

`pcc_thm_inst` internaliza el teorema universal anterior en el código‑testigo `tcFn t`
(abierto), y `prf_substfc_impl` distribuye el `substfc` sobre los dos `implc`. -/

/-- Código del antecedente de etiqueta, punteado en la línea `t`. -/
def tagDot (t : Term) : Term := substfc zero (tcFn t) (formCode tagEqrefl)

/-- Código de la cláusula canónica de longitud, punteado en la línea `t`. -/
def lencDot (t : Term) : Term := substfc zero (tcFn t) (formCode lencEqrefl)

/-- Código de la condición estructural, punteado en la línea `t`. -/
def eqDot (t : Term) : Term := substfc zero (tcFn t) (formCode eqEqrefl)

/-- Código de `lineWF`, punteado en la línea `t`. -/
def lwfDot (t : Term) : Term := substfc zero (tcFn t) (formCode lwfVar)

/-- **COLUMNA VERTEBRAL DEL PASO 6** (esquema estricto): el bicondicional (dirección `⇐`)
    transportado al nivel del código y punteado en `t`:

    `Prov(⌜TAG_dot t ⇒ ((LENC_dot t ∧ EQ_dot t) ⇒ LWF_dot t)⌝)`

    Es la plantilla común a los 21 casos de etiqueta: sólo cambian el axioma‑accesor y `expr_k`. -/
theorem paso6_backbone (t : Term) :
    Prf (provFromCode
      (implc (tagDot t) (implc (andc (lencDot t) (eqDot t)) (lwfDot t)))) := by
  have h := pcc_thm_inst _ prf_lineWF_eqrefl_bwd (tcFn t)
  refine prf_mp (prf_provCode_congr ?_) h
  -- distribuye el `substfc` sobre `implc`, el `andc` interno y el `implc` interno
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode tagEqrefl)
      (formCode (Formula.impl (Formula.and lencEqrefl eqEqrefl) lwfVar))) ?_
  refine prf_congr_implc (prf_refl _) ?_
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode (Formula.and lencEqrefl eqEqrefl))
      (formCode lwfVar)) ?_
  exact prf_congr_implc
    (prf_substfc_and zero (tcFn t) (formCode lencEqrefl) (formCode eqEqrefl))
    (prf_refl _)

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

/-! ### Paso 6d — PRODUCCIÓN de los punteados: `Prov(TAG_dot t)` y `Prov(EQ_dot t)`

Aquí entra la **evaluación provable**: `pcc_eval_nthc` calcula `nthc(ṫ,ı̇)` *dentro de `Prov`* bajo
la cota `i < lenc t`, y la hipótesis de la rama (la igualdad `=eq` del paso 5) se transporta al
código con la congruencia de `tcFn` (`PrfH_congr_tcFn`) + el puente de numerales
(`prf_tc_numeral`).

⚠️ **Esto NO es `pcc_eq_tracked` aplicado al átomo** (eso sería Tarski: el código absorbería la
forma sintáctica). La igualdad `=eq` se usa sólo para reescribir el **valor** `(nthc t 1)˙` dentro
de un `Prov` que la evaluación ya produjo.

Las cotas (`1 < lenc t`, `2 < lenc t`) van como **hipótesis explícitas**, igual que `chainOk`/cota
en `pcc_eval_carc_nthc`: se descargan aguas arriba, desde `lineWF t`. -/

/-- **Ecuación `tc` del árbol `eqc`**: `tcFn (eqc a b) = eqcT (tcFn a) (tcFn b)`. Es `prf_tc_cons'`
    tres veces (el árbol `⟨4,a,b⟩`), con `4̇` y `nil` descargados por `prf_tc_numeral`/`prf_tc_zero`. -/
theorem prf_tc_eqc (a b : Term) :
    Prf (tcFn (eqc a b) =eq eqcT (tcFn a) (tcFn b)) := by
  unfold eqc eqcT
  refine prf_eq_trans (prf_tc_cons' _ _) ?_
  refine prf_congr_consT (prf_tc_numeral 4) ?_
  refine prf_eq_trans (prf_tc_cons' _ _) ?_
  refine prf_congr_consT (prf_refl _) ?_
  refine prf_eq_trans (prf_tc_cons' _ _) ?_
  exact prf_congr_consT (prf_refl _) prf_tc_zero

/-- **Congruencia DIAGONAL de `eqcT` DENTRO de `Prov`**: de `Prov(⌜X = Y⌝)` sale
    `Prov(⌜eqc(X,X) = eqc(Y,Y)⌝)`. Mismo patrón que `pcc_congr_carcT_code_imp`, con el contexto
    de código llevando **dos huecos** `⌜v₀⌝` — ambos reciben el mismo testigo al sustituir, que es
    justo lo que pide `eqrefl` (`t ≐ t`, el mismo término a los dos lados). -/
theorem pcc_congr_eqcT_diag_code_imp (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (eqcT X X) (eqcT Y Y))) := by
  let Ac : Term := eqc (eqcT X X) (eqcT (varc (numeral 0)) (varc (numeral 0)))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc (eqcT X X) (eqcT t t)) := by
    intro t
    refine prf_eq_trans (prf_substfc_eq zero t (eqcT X X)
      (eqcT (varc (numeral 0)) (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_eqcT t X X) (prf_congr_eqcT (hX t) (hX t))
    · exact prf_eq_trans (prf_substtc_eqcT t (varc (numeral 0)) (varc (numeral 0)))
        (prf_congr_eqcT (prf_substtc_varc0 t) (prf_substtc_varc0 t))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (eqcT X X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **`Prov(TAG_dot t)`**: bajo la cota `1 < lenc t`, la igualdad de etiqueta `nthc t 1 = 12̇`
    produce el código punteado del antecedente de tag, DENTRO de `Prov`. -/
theorem pcc_tagDot (t : Term) :
    Prf (lt (succ zero) (lenc t) ⇒
      ((nthc t (succ zero) =eq numeralM 12) ⇒ provFromCode (tagDot t))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM 12)
    [lt (succ zero) (lenc t)] rfl)
  have hbound : PrfH [nthc t (succ zero) =eq numeralM 12, lt (succ zero) (lenc t)]
      (lt (succ zero) (lenc t)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htag : PrfH [nthc t (succ zero) =eq numeralM 12, lt (succ zero) (lenc t)]
      (nthc t (succ zero) =eq numeralM 12) := PrfH.hyp _ _ (List.Mem.head _)
  -- evaluación provable de `nthc` bajo la cota
  have hev : PrfH [nthc t (succ zero) =eq numeralM 12, lt (succ zero) (lenc t)]
      (provFromCode (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero)))
        (tcFn (nthc t (succ zero))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (succ zero)) _) hbound
  -- reescritura del VALOR con la igualdad de la rama (congruencia de `tcFn`)
  have hcodeq : PrfH [nthc t (succ zero) =eq numeralM 12, lt (succ zero) (lenc t)]
      (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero))) (tcFn (nthc t (succ zero)))
        =eq eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM 12))) :=
    PrfH_congr_eqCodeFn
      (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) (prf_to_prfH (prf_tc_numeral 1) _))
      (PrfH_eq_trans (PrfH_congr_tcFn htag) (prf_to_prfH (prf_tc_numeral 12) _))
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_tagDot_eq t))) _)
    (PrfH_provCode_congr hcodeq hev)

/-- **`Prov(EQ_dot t)`**: bajo `lineWF t` (que da la estructura `cons` de la línea) y la cota
    `2 < lenc t`, la condición estructural del caso `eqrefl` produce su código punteado DENTRO de
    `Prov`.

    Cadena: `pcc_eval_carc` evalúa `carc(ṫ)` (usando que la línea es un `cons`), `pcc_eval_nthc`
    evalúa `nthc(ṫ,2̇)`, la hipótesis `=eq` reescribe el valor vía `prf_tc_eqc`, y el encaje final
    es la congruencia diagonal `pcc_congr_eqcT_diag_code_imp` + Leibniz interno. -/
theorem pcc_eqDot (t : Term) :
    Prf (lineWF t ⇒ (lt (numeralM 2) (lenc t) ⇒
      ((carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2))) ⇒
        provFromCode (eqDot t)))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)))
    [lt (numeralM 2) (lenc t), lineWF t] rfl)
    (lt (numeralM 2) (lenc t)) [lineWF t] rfl)
  -- Γ = [EQ, cota, lineWF t]
  have hlw : PrfH [carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)),
      lt (numeralM 2) (lenc t), lineWF t] (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hbound : PrfH [carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)),
      lt (numeralM 2) (lenc t), lineWF t] (lt (numeralM 2) (lenc t)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hEQ : PrfH [carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)),
      lt (numeralM 2) (lenc t), lineWF t]
      (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  -- abreviaturas: `V` = valor rastreado de `nthc t 2`; `N` = su forma EVALUADA
  let V : Term := tcFn (nthc t (numeralM 2))
  let N : Term := nthcT (tcFn t) (termCode (numeralM 2))
  have hNinv : ∀ W, Prf (substtc zero W N =eq N) :=
    substtc_inv_nthcT (substtc_inv_tcFn t)
      (substtc_inv_termCode_of_tc (prf_tc_numeral 2))
  -- (1) la línea es un `cons` (reflejo de `ax_lineWF_cons`)
  have hcons := PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_cons t) _) hlw
  -- (2) evaluación provable de `carc`, transportada de `cons (carc t) (cdrc t)` a `t`
  have hcarc0 := prf_to_prfH (pcc_eval_carc (carc t) (cdrc t))
    [carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)),
     lt (numeralM 2) (lenc t), lineWF t]
  have hcarc : PrfH _ (provFromCode (eqc (carcT (tcFn t)) (tcFn (carc t)))) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
        (prf_to_prfH (prf_refl _) _)) hcarc0
  -- (3) la hipótesis `=eq` reescribe el VALOR: `(carc t)˙ = eqcT(V,V)`
  have hEQtc : PrfH _ (tcFn (carc t) =eq eqcT V V) :=
    PrfH_eq_trans (PrfH_congr_tcFn hEQ) (prf_to_prfH (prf_tc_eqc _ _) _)
  have hcarc2 : PrfH _ (provFromCode (eqc (carcT (tcFn t)) (eqcT V V))) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) hEQtc) hcarc
  -- (4) evaluación provable de `nthc` bajo la cota, normalizada a `N`
  have hevN0 := PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (numeralM 2)) _) hbound
  have hevN : PrfH _ (provFromCode (eqc N V)) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn
        (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _)
          (prf_to_prfH (prf_tc_numeral 2) _))
        (prf_to_prfH (prf_refl _) _)) hevN0
  -- (5) simetría interna + congruencia diagonal: `Prov(eqcT(V,V) = eqcT(N,N))`
  have hdiag : PrfH _ (provFromCode (eqc (eqcT V V) (eqcT N N))) :=
    PrfH.mp _ _ _
      (prf_to_prfH (pcc_congr_eqcT_diag_code_imp V N (substtc_inv_tcFn _)) _)
      (PrfH_eq_symm_code N V hNinv hevN)
  -- (6) transitividad interna (Leibniz con el hueco en la 2ª posición)
  have hCinv : ∀ W, Prf (substtc zero W (carcT (tcFn t)) =eq carcT (tcFn t)) := fun W =>
    prf_eq_trans (prf_substtc_carcT zero W (tcFn t))
      (prf_congr_carcT (substtc_inv_tcFn t W))
  have hcompA : ∀ w : Term,
      Prf (substfc zero w (eqc (carcT (tcFn t)) (varc (numeral 0)))
        =eq eqc (carcT (tcFn t)) w) := fun w =>
    prf_eq_trans (prf_substfc_eq zero w (carcT (tcFn t)) (varc (numeral 0)))
      (prf_congr_eqCodeFn (hCinv w) (prf_substtc_varc0 w))
  have hfin : PrfH _ (provFromCode (eqc (carcT (tcFn t)) (eqcT N N))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcompA (eqcT N N))) _)
      (PrfH_leibniz_apply (eqc (carcT (tcFn t)) (varc (numeral 0))) (eqcT V V) (eqcT N N)
        hdiag
        (PrfH.mp _ _ _
          (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcompA (eqcT V V)))) _) hcarc2))
  -- (7) de vuelta a la forma `substfc` del código punteado
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_eqDot_eq t))) _) hfin

/-! ### Paso 6d bis — el punteado de LONGITUD `LENC_dot` (cláusula canónica del plan A)

`lencDot t` se evalúa a la forma rastreada `lencT (tcFn t)`, y se **produce** con `pcc_eval_lenc`
(incondicional) reescribiendo el valor `(lenc t)˙ = 3̇` con la igualdad externa `lenc t = 3̇` (que
sale de la dirección `⇒` del accesor estricto). -/

/-- **`LENC_dot` evaluado**: `substfc 0 (tcFn t) ⌜lenc #0 = 3̇⌝ = ⌜lencT ṫ = 3̇⌝`. -/
theorem prf_lencDot_eq (t : Term) :
    Prf (lencDot t =eq eqCodeFn (lencT (tcFn t)) (termCode (numeralM 3))) := by
  unfold lencDot lencEqrefl
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (substtc_inv_termCode_of_tc (prf_tc_numeral 3) (tcFn t))
  exact prf_eq_trans (prf_substtc_lencT zero (tcFn t) (varc (numeral 0)))
    (prf_congr_lencT (prf_substtc_varc0 (tcFn t)))

/-- **`Prov(LENC_dot t)`** a partir de la igualdad de longitud externa `lenc t = 3̇`. -/
theorem pcc_lencDot (t : Term) :
    Prf ((lenc t =eq numeralM 3) ⇒ provFromCode (lencDot t)) := by
  refine prf_deduction ?_
  have hev : PrfH [lenc t =eq numeralM 3]
      (provFromCode (eqCodeFn (lencT (tcFn t)) (tcFn (lenc t)))) :=
    prf_to_prfH (pcc_eval_lenc t) _
  have hval : PrfH [lenc t =eq numeralM 3] (tcFn (lenc t) =eq termCode (numeralM 3)) :=
    PrfH_eq_trans (PrfH_congr_tcFn (prfH_hyp_self _)) (prf_to_prfH (prf_tc_numeral 3) _)
  have hev2 : PrfH [lenc t =eq numeralM 3]
      (provFromCode (eqCodeFn (lencT (tcFn t)) (termCode (numeralM 3)))) :=
    PrfH_provCode_congr (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) hval) hev
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_lencDot_eq t))) _) hev2

/-- Orden estricto entre numerales `numeralM` (vía `numeralM_eq` + `prf_gnum_lt`). -/
theorem prf_lt_numeralM {a b : Nat} (h : a < b) : Prf (lt (numeralM a) (numeralM b)) := by
  rw [numeralM_eq, numeralM_eq]; exact prf_gnum_lt h

/-! ### Paso 6e — `lwfDot t` es el código que pide la reflexión punteada

`lwfDot t = substfc 0 (tcFn t) ⌜lineWF #0⌝` y `lineWFCodeFn (tcFn t)` coinciden: es el mismo
`substfc` sobre el átomo unario, con el hueco `⌜v₀⌝` recibiendo `tcFn t`. -/

/-- `lwfDot t =eq lineWFCodeFn (tcFn t)`. -/
theorem prf_lwfDot_eq (t : Term) :
    Prf (lwfDot t =eq lineWFCodeFn (tcFn t)) := by
  show Prf (substfc zero (tcFn t) (atomc (strCode "lineWF") (cons (varc (numeral 0)) nil))
    =eq atomc (strCode "lineWF") (cons (tcFn t) nil))
  refine prf_eq_trans (prf_substfc_atom zero (tcFn t) (strCode "lineWF")
    (cons (varc (numeral 0)) nil)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero (tcFn t) (varc (numeral 0)) nil) ?_
  exact prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 (tcFn t)))
    (prf_congr_cons_tail (prf_substtsc_nil zero (tcFn t)))

/-! ### Paso 6f — MP interno ×2: de la columna vertebral + los punteados a `Prov(lineWF)`

Con `paso6_backbone` (`Prov(⌜TAG_dot ⇒ (EQ_dot ⇒ LWF_dot)⌝)`) y los dos punteados producidos
(`pcc_tagDot`, `pcc_eqDot`), dos aplicaciones de `pcc_mp_code_apply` (MP interno a nivel de
código) dan `Prov(⌜LWF_dot t⌝)` = `provFromCode (lineWFCodeFn (tcFn t))` — que es exactamente la
reflexión punteada del átomo `lineWF` en el caso `eqrefl`. -/

/-- **CASO `eqrefl` de `pcc_lineWF_tracked`** (paso 6 completo salvo la inversión de tag).
    Bajo la etiqueta `nthc t 1 = 12̇` y la buena‑formación estricta (`lineWF t` + la longitud
    canónica `lenc t = 3̇` + la condición `carc t = eqc (nthc t 2)(nthc t 2)`), la línea refleja su
    código punteado. Las **cotas ya NO son hipótesis**: se derivan de `lenc t = 3̇`. -/
theorem pcc_lineWF_tracked_eqrefl (t : Term)
    (hlw : Prf (lineWF t))
    (htag : Prf (nthc t (succ zero) =eq numeralM 12))
    (hlenc : Prf (lenc t =eq numeralM 3))
    (heq : Prf (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)))) :
    Prf (provFromCode (lineWFCodeFn (tcFn t))) := by
  -- cotas de sub‑índice, DERIVADAS de la longitud canónica
  have hb1 : Prf (lt (succ zero) (lenc t)) :=
    prf_lt_subst2 (prf_eq_symm hlenc) (prf_lt_numeralM (a := 1) (b := 3) (by omega))
  have hb2 : Prf (lt (numeralM 2) (lenc t)) :=
    prf_lt_subst2 (prf_eq_symm hlenc) (prf_lt_numeralM (a := 2) (b := 3) (by omega))
  -- los tres punteados
  have hTag : Prf (provFromCode (tagDot t)) := prf_mp (prf_mp (pcc_tagDot t) hb1) htag
  have hLenc : Prf (provFromCode (lencDot t)) := prf_mp (pcc_lencDot t) hlenc
  have hEq : Prf (provFromCode (eqDot t)) := prf_mp (prf_mp (prf_mp (pcc_eqDot t) hlw) hb2) heq
  -- `∧`‑intro interno + MP interno ×2 sobre la columna vertebral
  have hAnd : Prf (provFromCode (andc (lencDot t) (eqDot t))) := pcc_and_intro_code hLenc hEq
  have hImp : Prf (provFromCode (implc (andc (lencDot t) (eqDot t)) (lwfDot t))) :=
    pcc_mp_code_apply (paso6_backbone t) hTag
  have hLwf : Prf (provFromCode (lwfDot t)) := pcc_mp_code_apply hImp hAnd
  exact prf_mp (prf_provCode_congr (prf_lwfDot_eq t)) hLwf

/-! ### Paso 6g — (c) para `eqrefl`: reflector POR RAMA, **sin hipótesis de cota**

Del accesor ESTRICTO `ax_lineWF_eqrefl` en la dirección `⇒` (`iff.mp` = `Prf₀.c2`): bajo `lineWF t`
y el tag `nthc t 1 = 12̇`, el RHS `(lenc t = 3̇) ∧ (carc t = eqc (nthc t 2)(nthc t 2))` **se deriva
entero**. Su primer conjunto da la longitud canónica ⇒ las cotas; el segundo, la condición
estructural. **Ya no hay hipótesis de cota** (el plan A las cerró de raíz). Es el reflector que el
`or_elim` ×21 invocará en el disyunto `eqrefl`. -/

/-- **Reflector por rama, caso `eqrefl`** (accesor estricto, dirección `⇒` descargada): asumido sólo
    el tag `nthc t 1 = 12̇` (que el `or_elim` de `prf_lineWF_inv` provee en este disyunto), `lineWF t`
    refleja su código punteado. **Sin** hipótesis de cota ni de condición estructural: todo se deriva
    del RHS estricto `(lenc t = 3̇) ∧ EQ`. -/
theorem pcc_lineWF_tracked_eqrefl_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 12) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM 12) [lineWF t] rfl)
  -- Γ = [tag, lineWF t]
  let Γ : List Formula := [nthc t (succ zero) =eq numeralM 12, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH Γ (nthc t (succ zero) =eq numeralM 12) := PrfH.hyp _ _ (List.Mem.head _)
  -- accesor ESTRICTO instanciado en `t`, dirección directa (`iff.mp` = c2)
  have hacc : Prf (Formula.impl (nthc t (succ zero) =eq numeralM 12)
      (lineWF t ⇔ Formula.and (lenc t =eq numeralM 3)
        (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2))))) := by
    have hh := prf_spec (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms])) t
    simpa [ax_lineWF_eqrefl, iff, lineWF, carc, lenc, nthc, eqc, numeralM, succ, zero, cons, nil,
      substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] using hh
  have hiff : PrfH Γ (lineWF t ⇔ Formula.and (lenc t =eq numeralM 3)
      (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hacc _) htagH
  -- del RHS estricto: longitud canónica + condición estructural
  have hand : PrfH Γ (Formula.and (lenc t =eq numeralM 3)
      (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2)))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hiff) hlw
  have hlencH : PrfH Γ (lenc t =eq numeralM 3) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have heqH : PrfH Γ (carc t =eq eqc (nthc t (numeralM 2)) (nthc t (numeralM 2))) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  -- cotas DERIVADAS de la longitud canónica (en `PrfH`)
  have hb1 : PrfH Γ (lt (succ zero) (lenc t)) :=
    PrfH_lt_subst2 (PrfH_eq_symm hlencH)
      (prf_to_prfH (prf_lt_numeralM (a := 1) (b := 3) (by omega)) _)
  have hb2 : PrfH Γ (lt (numeralM 2) (lenc t)) :=
    PrfH_lt_subst2 (PrfH_eq_symm hlencH)
      (prf_to_prfH (prf_lt_numeralM (a := 2) (b := 3) (by omega)) _)
  -- los tres punteados producidos en el contexto
  have hTag : PrfH Γ (provFromCode (tagDot t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_tagDot t) _) hb1) htagH
  have hLenc : PrfH Γ (provFromCode (lencDot t)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lencDot t) _) hlencH
  have hEq : PrfH Γ (provFromCode (eqDot t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_eqDot t) _) hlw) hb2) heqH
  -- `∧`‑intro interno + MP interno ×2 + `lwfDot = lineWFCodeFn`
  have hAnd : PrfH Γ (provFromCode (andc (lencDot t) (eqDot t))) :=
    PrfH_and_intro_code (lencDot t) (eqDot t) hLenc hEq
  have hImp : PrfH Γ (provFromCode (implc (andc (lencDot t) (eqDot t)) (lwfDot t))) :=
    PrfH_mp_code_apply (prf_to_prfH (paso6_backbone t) _) hTag
  have hLwf : PrfH Γ (provFromCode (lwfDot t)) := PrfH_mp_code_apply hImp hAnd
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_lwfDot_eq t)) _) hLwf

end ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

export ROBINSON_PlusPlus.Meta.LineWFTrackedPrf (
  tagEqrefl lencEqrefl eqEqrefl lwfVar ax_lineWF_eqrefl_eq prf_lineWF_eqrefl_bwd
  tagDot lencDot eqDot lwfDot paso6_backbone
  substtc_inv_termCode_of_tc eqcT eqcT_termCode prf_congr_eqcT prf_substtc_eqcT
  prf_tagDot_eq prf_eqDot_eq prf_tc_eqc pcc_congr_eqcT_diag_code_imp
  prf_lencDot_eq pcc_lencDot prf_lt_numeralM
  pcc_tagDot pcc_eqDot prf_lwfDot_eq pcc_lineWF_tracked_eqrefl
  pcc_lineWF_tracked_eqrefl_imp
)

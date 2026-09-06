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

namespace ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

/-!
## META — NIVEL D real (B.3c): **CHASIS GENÉRICO** de la reflexión punteada de `lineWF`

Tras cerrar a mano los tres casos estructuralmente distintos (`eqrefl` = condición `=eq`,
`thy` = condición `In`, `mp` = sin condición), los **18 tags restantes** son todos del mismo molde:

  `∀. (nthc #0 1 = k̇) ⇒ (lineWF #0 ⇔ ((lenc #0 = ṅ) ∧ (carc #0 = E(nthc #0 i…))))`

variando sólo `k`, `n` y el árbol `E`. Este módulo **factoriza todo lo que no depende de `E`** para
que cada tag cueste sólo su parte estructural.

### Qué es genérico (aquí) y qué queda por tag

| pieza | genérico | por tag |
|---|---|---|
| dirección `⇐` del `⇔` currificada bajo el tag | ✅ `schema_bwd` | — |
| columna vertebral codificada (`pcc_thm_inst` + `substfc`) | ✅ `schema_backbone` | — |
| punteado del **tag** (`prf_tagD_eq`, `pcc_tagD`) | ✅ | — |
| punteado de la **longitud** (`prf_lencD_eq`, `pcc_lencD`) | ✅ | — |
| cotas de sub‑índice desde la longitud canónica | ✅ `prf_lt_of_lenc_eq` | — |
| ensamblaje final (`∧`‑intro + MP interno ×2) | ✅ `pcc_lineWF_tracked_of_schema` | — |
| puentes de evaluación `carc`/`nthc` dentro de `Prov` | ✅ `pcc_carcD_bridge`, `pcc_nthcD_bridge` | — |
| invariancias `substtc` de los accesores rastreados | ✅ `substtc_inv_{carcT,nthcT}_tcFn` | — |
| **reflejar `carc t = E(nthc t i…)` al código** | — | **todo** |

Es decir, por tag queda exactamente una cosa: el **reflector de su condición**, `hcond`, que debe
(1) evaluar `condD C t` a forma rastreada (distribución de `substfc`/`substtc` sobre el árbol `E`) y
(2) producirlo dentro de `Prov` componiendo los dos puentes con la congruencia interna de `E`. Es
corto porque **todos** los constructores de código (`implc`, `andc`, `orc`, `eqc`, `forallc`, `exc`,
…) son `cons`‑árboles, pero **no está factorizado**: depende de la forma de `E`.

⚠️ **Precondición**: los 21 esquemas deben estar en forma ESTRICTA uniforme (cláusula canónica
`lenc = ṅ` como primer conjunto). Se completó en el lote previo.
-/

/-! ### Numerales `numeralM` con exponente VARIABLE

El chasis cuantifica sobre `k`/`n : Nat`, así que necesita los puentes de numeral con índice
**abierto**. ⚠️ `numeralM k` y `Godel.numeral k` **no son defeq** para `k` variable
(`numeralM_eq` se prueba por inducción, no por `rfl`); con literales reducen, pero aquí no.
De ahí que cada puente tenga que reescribir explícitamente con `numeralM_eq`. -/

-- ⚠️ `substTerm_numeralM` y `liftTerm_numeralM` **ya existen** en `Minimal/Axioms.lean`; no se
-- reintroducen aquí (duplicarlos hacía ambiguo el nombre en los módulos cliente).

/-- Puente `tc` del numeral con índice abierto. -/
theorem prf_tc_numeralM (k : Nat) : Prf (tcFn (numeralM k) =eq termCode (numeralM k)) := by
  rw [numeralM_eq]; exact prf_tc_numeral k

/-- El código de un numeral (índice abierto) es `substtc`‑invariante. -/
theorem substtc_inv_termCode_numeralM (k : Nat) (W : Term) :
    Prf (substtc zero W (termCode (numeralM k)) =eq termCode (numeralM k)) :=
  LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeralM k) W

/-! ### Las dos cláusulas genéricas (tag y longitud) sobre la línea abstracta `#0` -/

/-- Antecedente de etiqueta genérico: `nthc #0 1 = k̇`. -/
def tagF (k : Nat) : Formula := nthc (.var 0) (succ zero) =eq numeralM k

/-- Cláusula canónica de longitud genérica: `lenc #0 = ṅ`. -/
def lencF (n : Nat) : Formula := lenc (.var 0) =eq numeralM n

@[simp] theorem substFormula_tagF (k : Nat) (t : Term) :
    substFormula 0 t (tagF k) = (nthc t (succ zero) =eq numeralM k) := by
  simp only [tagF, nthc, succ, zero, substFormula, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_liftTerm, if_true]

@[simp] theorem substFormula_lencF (n : Nat) (t : Term) :
    substFormula 0 t (lencF n) = (lenc t =eq numeralM n) := by
  simp only [lencF, lenc, substFormula, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_liftTerm, if_true]

@[simp] theorem substFormula_lwfVar (t : Term) : substFormula 0 t lwfVar = lineWF t := by
  simp only [lwfVar, lineWF, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]

/-! ### Los códigos punteados genéricos -/

/-- Código punteado del antecedente de etiqueta. -/
def tagD (k : Nat) (t : Term) : Term := substfc zero (tcFn t) (formCode (tagF k))

/-- Código punteado de la cláusula canónica de longitud. -/
def lencD (n : Nat) (t : Term) : Term := substfc zero (tcFn t) (formCode (lencF n))

/-- Código punteado de la condición estructural `C` (la parte que varía por tag). -/
def condD (C : Formula) (t : Term) : Term := substfc zero (tcFn t) (formCode C)

/-- **`TAG_dot` evaluado**, genérico en `k`. -/
theorem prf_tagD_eq (k : Nat) (t : Term) :
    Prf (tagD k t =eq
      eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM k))) := by
  unfold tagD tagF
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (substtc_inv_termCode_numeralM k (tcFn t))
  refine prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _) ?_
  exact prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc (prf_tc_numeral 1) (tcFn t))

/-- **`LENC_dot` evaluado**, genérico en `n`. -/
theorem prf_lencD_eq (n : Nat) (t : Term) :
    Prf (lencD n t =eq eqCodeFn (lencT (tcFn t)) (termCode (numeralM n))) := by
  unfold lencD lencF
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (substtc_inv_termCode_numeralM n (tcFn t))
  exact prf_eq_trans (prf_substtc_lencT zero (tcFn t) (varc (numeral 0)))
    (prf_congr_lencT (prf_substtc_varc0 (tcFn t)))

/-- **`Prov(TAG_dot t)`**, genérico en `k`. -/
theorem pcc_tagD (k : Nat) (t : Term) :
    Prf (lt (succ zero) (lenc t) ⇒
      ((nthc t (succ zero) =eq numeralM k) ⇒ provFromCode (tagD k t))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM k)
    [lt (succ zero) (lenc t)] rfl)
  have hbound : PrfH [nthc t (succ zero) =eq numeralM k, lt (succ zero) (lenc t)]
      (lt (succ zero) (lenc t)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htag : PrfH [nthc t (succ zero) =eq numeralM k, lt (succ zero) (lenc t)]
      (nthc t (succ zero) =eq numeralM k) := PrfH.hyp _ _ (List.Mem.head _)
  have hev : PrfH [nthc t (succ zero) =eq numeralM k, lt (succ zero) (lenc t)]
      (provFromCode (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero)))
        (tcFn (nthc t (succ zero))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (succ zero)) _) hbound
  have hcodeq : PrfH [nthc t (succ zero) =eq numeralM k, lt (succ zero) (lenc t)]
      (eqCodeFn (nthcT (tcFn t) (tcFn (succ zero))) (tcFn (nthc t (succ zero)))
        =eq eqCodeFn (nthcT (tcFn t) (termCode (succ zero))) (termCode (numeralM k))) :=
    PrfH_congr_eqCodeFn
      (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) (prf_to_prfH (prf_tc_numeral 1) _))
      (PrfH_eq_trans (PrfH_congr_tcFn htag) (prf_to_prfH (prf_tc_numeralM k) _))
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_tagD_eq k t))) _)
    (PrfH_provCode_congr hcodeq hev)

/-- **`Prov(LENC_dot t)`**, genérico en `n`. -/
theorem pcc_lencD (n : Nat) (t : Term) :
    Prf ((lenc t =eq numeralM n) ⇒ provFromCode (lencD n t)) := by
  refine prf_deduction ?_
  have hev : PrfH [lenc t =eq numeralM n]
      (provFromCode (eqCodeFn (lencT (tcFn t)) (tcFn (lenc t)))) :=
    prf_to_prfH (pcc_eval_lenc t) _
  have hval : PrfH [lenc t =eq numeralM n] (tcFn (lenc t) =eq termCode (numeralM n)) :=
    PrfH_eq_trans (PrfH_congr_tcFn (prfH_hyp_self _)) (prf_to_prfH (prf_tc_numeralM n) _)
  have hev2 : PrfH [lenc t =eq numeralM n]
      (provFromCode (eqCodeFn (lencT (tcFn t)) (termCode (numeralM n)))) :=
    PrfH_provCode_congr (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) hval) hev
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_lencD_eq n t))) _) hev2

/-! ### Puentes de evaluación genéricos (`carc` y `nthc` DENTRO de `Prov`)

Los dos ladrillos que toda condición estructural necesita, factorizados: llevan el accesor
*rastreado* (`carcT ṫ`, `nthcT ṫ ı̇`) al *valor* punteado (`(carc t)˙`, `(nthc t ı)˙`) dentro de
`Prov`. Con ellos, la parte propia de cada tag se reduce a la congruencia del árbol `E`. -/

/-- `carcT ṫ` es `substtc`‑invariante. -/
theorem substtc_inv_carcT_tcFn (t : Term) :
    ∀ W, Prf (substtc zero W (carcT (tcFn t)) =eq carcT (tcFn t)) := fun W =>
  prf_eq_trans (prf_substtc_carcT zero W (tcFn t))
    (prf_congr_carcT (substtc_inv_tcFn t W))

/-- `nthcT ṫ ı̇` es `substtc`‑invariante. -/
theorem substtc_inv_nthcT_tcFn (t : Term) (i : Nat) :
    ∀ W, Prf (substtc zero W (nthcT (tcFn t) (termCode (numeralM i)))
      =eq nthcT (tcFn t) (termCode (numeralM i))) :=
  substtc_inv_nthcT (substtc_inv_tcFn t) (substtc_inv_termCode_numeralM i)

/-- **Puente `carc`**: bajo `lineWF t` (que da la estructura `cons` de la línea),
    `Prov(⌜carcT ṫ = (carc t)˙⌝)`. -/
theorem pcc_carcD_bridge (t : Term) :
    Prf (lineWF t ⇒ provFromCode (eqc (carcT (tcFn t)) (tcFn (carc t)))) := by
  refine prf_deduction ?_
  have hcons := PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_cons t) _) (prfH_hyp_self (lineWF t))
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc t) (cdrc t)) _)

/-- **Puente `nthc`**: bajo la cota `i < lenc t`, `Prov(⌜nthcT ṫ ı̇ = (nthc t ı)˙⌝)`. -/
theorem pcc_nthcD_bridge (t : Term) (i : Nat) :
    Prf (lt (numeralM i) (lenc t) ⇒
      provFromCode (eqc (nthcT (tcFn t) (termCode (numeralM i)))
        (tcFn (nthc t (numeralM i))))) := by
  refine prf_deduction ?_
  have hev := PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (numeralM i)) _)
    (prfH_hyp_self (lt (numeralM i) (lenc t)))
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn
      (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) (prf_to_prfH (prf_tc_numeralM i) _))
      (prf_to_prfH (prf_refl _) _)) hev

/-! ### Cotas de sub‑índice, derivadas de la longitud canónica

Es lo que compró el plan (A): con `lenc t = ṅ` en la mano, toda cota `i < lenc t` con `i < n` es
inmediata. Las dos versiones (cerrada y en contexto) porque el ensamblaje trabaja en `PrfH`. -/

/-- Cota de sub‑índice desde la longitud canónica. -/
theorem prf_lt_of_lenc_eq {t : Term} {i n : Nat} (hlt : i < n)
    (h : Prf (lenc t =eq numeralM n)) : Prf (lt (numeralM i) (lenc t)) :=
  prf_lt_subst2 (prf_eq_symm h) (prf_lt_numeralM hlt)

/-- Cota de sub‑índice desde la longitud canónica, en contexto. -/
theorem PrfH_lt_of_lenc_eq {Γ : List Formula} {t : Term} {i n : Nat} (hlt : i < n)
    (h : PrfH Γ (lenc t =eq numeralM n)) : PrfH Γ (lt (numeralM i) (lenc t)) :=
  BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm h) (prf_to_prfH (prf_lt_numeralM hlt) _)

/-! ### Dirección `⇐` del bicondicional y columna vertebral, genéricas -/

/-- **Dirección `⇐` currificada bajo el tag**, genérica en `k`, `n` y la condición `C`. -/
theorem schema_bwd (k n : Nat) (C : Formula)
    (hC : substFormula 0 (.var 0) C = C)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ Formula.and (lencF n) C)))) :
    Prf (Formula.forall (Formula.impl (tagF k)
      (Formula.impl (Formula.and (lencF n) C) lwfVar))) := by
  refine Prf.gen _ ?_
  refine prf_deduction ?_
  refine deduction_aux ?_ (Formula.and (lencF n) C) [tagF k] rfl
  have hspec : Prf (Formula.impl (tagF k) (lwfVar ⇔ Formula.and (lencF n) C)) := by
    have hh := prf_spec hax (.var 0)
    -- ⚠️ NO se pone `numeralM` en el conjunto: desplegarlo impide que `substTerm_numeralM`
    -- dispare, y el `substTerm 0 #0 (numeralM ·)` se queda sin reducir.
    simpa [tagF, lencF, lwfVar, iff, lineWF, lenc, nthc, succ, zero, cons, nil,
      substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, substTerm_numeralM,
      hC] using hh
  have hiff : PrfH [Formula.and (lencF n) C, tagF k] (lwfVar ⇔ Formula.and (lencF n) C) :=
    PrfH.mp _ _ _ (prf_to_prfH hspec _) (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hiff)
    (PrfH.hyp _ _ (List.Mem.head _))

/-- **Columna vertebral codificada**, genérica: el bicondicional (dirección `⇐`) transportado al
    nivel del código y punteado en `t`. Es la plantilla común a los 21 tags. -/
theorem schema_backbone (k n : Nat) (C : Formula)
    (hbwd : Prf (Formula.forall (Formula.impl (tagF k)
      (Formula.impl (Formula.and (lencF n) C) lwfVar)))) (t : Term) :
    Prf (provFromCode
      (implc (tagD k t) (implc (andc (lencD n t) (condD C t)) (lwfDot t)))) := by
  have h := pcc_thm_inst _ hbwd (tcFn t) (prf_hasWit_tcFn (liftTerm 0 t))
  refine prf_mp (prf_provCode_congr ?_) h
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode (tagF k))
      (formCode (Formula.impl (Formula.and (lencF n) C) lwfVar))) ?_
  refine prf_congr_implc (prf_refl _) ?_
  refine prf_eq_trans
    (prf_substfc_impl zero (tcFn t) (formCode (Formula.and (lencF n) C)) (formCode lwfVar)) ?_
  exact prf_congr_implc
    (prf_substfc_and zero (tcFn t) (formCode (lencF n)) (formCode C)) (prf_refl _)

/-! ### ENSAMBLAJE FINAL genérico

Todo lo anterior, compuesto. Lo único que cada tag debe aportar es `hcond`: el reflector de su
condición estructural, que puede consumir `lineWF t` y la longitud canónica (de donde saca las
cotas que necesite). -/

/-- **Reflector por rama, GENÉRICO.** Dado el esquema estricto del tag `k` (longitud canónica `n`,
    condición `C`) y el reflector `hcond` de esa condición, la línea refleja su código punteado bajo
    la sola hipótesis del tag. Instanciar esto es lo que cierra cada uno de los 18 tags.

    `hC : substFormula 0 #0 C = C` es la única obligación «administrativa»: para `C` ABIERTA
    arbitraria, instanciar el `∀` en `#0` **no** es la identidad (De Bruijn *decrementa* los índices
    superiores), así que el chasis no puede abrir el binder sin saberlo. Toda condición real de los
    21 tags menciona sólo `#0`, luego cada tag la descarga con `rfl`. -/
theorem pcc_lineWF_tracked_of_schema {k n : Nat} {C : Formula} (t : Term)
    (hC : substFormula 0 (.var 0) C = C)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ Formula.and (lencF n) C))))
    (hcond : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t C ⇒ provFromCode (condD C t)))))
    (h1n : 1 < n) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM k) [lineWF t] rfl)
  let Γ : List Formula := [nthc t (succ zero) =eq numeralM k, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH Γ (nthc t (succ zero) =eq numeralM k) := PrfH.hyp _ _ (List.Mem.head _)
  -- el esquema instanciado en `t`, dirección directa (`iff.mp` = c2)
  have hacc : Prf (Formula.impl (nthc t (succ zero) =eq numeralM k)
      (lineWF t ⇔ Formula.and (lenc t =eq numeralM n) (substFormula 0 t C))) := by
    have hh := prf_spec hax t
    simpa [iff, substFormula, substFormula_tagF, substFormula_lencF, substFormula_lwfVar] using hh
  have hiff : PrfH Γ (lineWF t ⇔ Formula.and (lenc t =eq numeralM n) (substFormula 0 t C)) :=
    PrfH.mp _ _ _ (prf_to_prfH hacc _) htagH
  have hand : PrfH Γ (Formula.and (lenc t =eq numeralM n) (substFormula 0 t C)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hiff) hlw
  have hlencH : PrfH Γ (lenc t =eq numeralM n) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have hcondH : PrfH Γ (substFormula 0 t C) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  -- cota del tag (`1 < lenc t`), derivada de la longitud canónica
  have hb1 : PrfH Γ (lt (succ zero) (lenc t)) := by
    have := PrfH_lt_of_lenc_eq (i := 1) (n := n) h1n hlencH
    simpa [numeralM, succ, zero] using this
  -- los tres punteados
  have hTag : PrfH Γ (provFromCode (tagD k t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_tagD k t) _) hb1) htagH
  have hLenc : PrfH Γ (provFromCode (lencD n t)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lencD n t) _) hlencH
  have hCond : PrfH Γ (provFromCode (condD C t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hcond _) hlw) hlencH) hcondH
  -- `∧`‑intro interno + MP interno ×2 + `lwfDot = lineWFCodeFn`
  have hAnd : PrfH Γ (provFromCode (andc (lencD n t) (condD C t))) :=
    PrfH_and_intro_code (lencD n t) (condD C t) hLenc hCond
  have hImp : PrfH Γ (provFromCode (implc (andc (lencD n t) (condD C t)) (lwfDot t))) :=
    PrfH_mp_code_apply (prf_to_prfH (schema_backbone k n C (schema_bwd k n C hC hax) t) _) hTag
  have hLwf : PrfH Γ (provFromCode (lwfDot t)) := PrfH_mp_code_apply hImp hAnd
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_lwfDot_eq t)) _) hLwf

end ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

export ROBINSON_PlusPlus.Meta.LineWFSchemaPrf (
  prf_tc_numeralM substtc_inv_termCode_numeralM
  tagF lencF substFormula_tagF substFormula_lencF substFormula_lwfVar
  tagD lencD condD prf_tagD_eq prf_lencD_eq pcc_tagD pcc_lencD
  substtc_inv_carcT_tcFn substtc_inv_nthcT_tcFn pcc_carcD_bridge pcc_nthcD_bridge
  prf_lt_of_lenc_eq PrfH_lt_of_lenc_eq
  schema_bwd schema_backbone pcc_lineWF_tracked_of_schema
)

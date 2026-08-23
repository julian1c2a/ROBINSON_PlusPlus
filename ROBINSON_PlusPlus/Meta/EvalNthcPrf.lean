/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalRunFnPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.EvalNthcPrf

/-!
## META — NIVEL D real (§35, arranque): evaluación ACOTADA de `nthc`

Para `hI_dot` vía `boundedCarcIn` (`∃i<lenc p. carc(nthc p i) = ⌜φ⌝`) hace falta puentear el término
simbólico `nthc(ṗ, ı̇)` con el valor `(nthc p i)˙`. A diferencia de `+` (total), `nthc` es **parcial**
(sólo definido sobre `cons`/índices en rango), así que la evaluación es **acotada** (`i < lenc p`):

```text
⊢ (i < lenc p) → Prov( ⌜ nthc(ṗ, ı̇) = (nthc p i)˙ ⌝ )
```

Se prueba por inducción de listas sobre `p` con análisis de casos sobre `i` (`0`/`σj`), reflejando las
dos **ecuaciones codificadas** de `nthc`:

* `ax_nthc_zero` (`forall_2`): `pcc_nthc_zero_code` (vía `pcc_axiom_inst2`) — **hecho aquí**.
* `ax_nthc_succ` (`forall_3`): `pcc_nthc_succ_code` (vía `pcc_axiom_inst3`, §MpCodePrf) — pendiente.

**Este módulo entrega la ecuación `zero`.** El `succ` (`substfc` triple) y la inducción acotada quedan
como siguiente ladrillo. Nota: `nthc` es total sobre índices en rango, así que **no** tiene la
partialidad de `carc` (esa se resuelve con `chainOk` → la línea es `cons`).
-/

/-- Constructor de código del término `nthc x y`: `⟨1, ⌜nthc⌝, [x, y]⟩`. -/
def nthcT (x y : Term) : Term := funcc (strCode "nthc") (cons x (cons y nil))

/-- Congruencia de `nthcT` en ambos argumentos. -/
theorem prf_congr_nthcT {x x' y y' : Term} (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (nthcT x y =eq nthcT x' y') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_congr_cons_head hy)))

/-- `substtc` atraviesa `nthcT` (funcc de 2 argumentos). -/
theorem prf_substtc_nthcT (v W x y : Term) :
    Prf (substtc v W (nthcT x y) =eq nthcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "nthc") x y

/-- **Ecuación `zero` de `nthc` CODIFICADA**: `⊢ Prov(⌜nthc(cons ḣ ṫ, ⌜0⌝) = ḣ⌝)`.
    De `pcc_axiom_inst2` de `ax_nthc_zero` (testigos `tcFn h`, `tcFn t`), computando el doble
    `substfc` sobre el código explícito (patrón `pcc_ax5_computed`). -/
theorem pcc_nthc_zero_code (h t : Term) :
    Prf (provFromCode (eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) (termCode zero)) (tcFn h))) := by
  let W1 : Term := liftc zero (tcFn h)
  let T : Term := tcFn t
  let BODY : Formula := nthc (cons (.var 1) (.var 0)) zero =eq (.var 1)
  have hin : Prf (substfc (succ zero) W1 (formCode BODY)
      =eq eqCodeFn (nthcT (consT W1 (varc (numeral 0))) (termCode zero)) W1) :=
    prf_substfc_arith_open 1 W1 BODY
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (nthcT (consT W1 (varc (numeral 0))) (termCode zero)) W1
      =eq eqCodeFn (nthcT (consT (tcFn h) (varc (numeral 0))) (termCode zero)) (tcFn h)) :=
    prf_congr_eqCodeFn
      (prf_congr_nthcT (prf_congr_consT hA (prf_refl _)) (prf_refl _)) hA
  have hout : Prf (substfc zero T
      (eqCodeFn (nthcT (consT (tcFn h) (varc (numeral 0))) (termCode zero)) (tcFn h))
      =eq eqCodeFn (nthcT (consT (tcFn h) T) (termCode zero)) (tcFn h)) := by
    refine prf_eq_trans (prf_substfc_eq zero T _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn T h)
    refine prf_eq_trans
      (prf_substtc_nthcT zero T (consT (tcFn h) (varc (numeral 0))) (termCode zero)) ?_
    refine prf_congr_nthcT ?_ (prf_substtc_termCode_nil T)
    refine prf_eq_trans (prf_substtc_consT zero T (tcFn h) (varc (numeral 0))) ?_
    exact prf_congr_consT (prf_substtc_tcFn T h) (prf_substtc_varc0 T)
  have hchain : Prf (substfc zero T (substfc (succ zero) W1 (formCode BODY))
      =eq eqCodeFn (nthcT (consT (tcFn h) T) (termCode zero)) (tcFn h)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 BODY (show ax_nthc_zero ∈ axioms by simp [axioms]) (tcFn h) T)

/-- **Ecuación `succ` de `nthc` CODIFICADA**:
    `⊢ Prov(⌜nthc(cons ḣ ṫ, σ ı̇) = nthc(ṫ, ı̇)⌝)`.
    De `pcc_axiom_inst3` de `ax_nthc_succ` (`forall_3`, testigos `tcFn h`, `tcFn t`, `tcFn i`),
    computando el `substfc` **triple** sobre el código explícito: el interno (nivel 2) por
    `prf_substfc_arith_open`, el de nivel 1 con testigo levantado (`liftc 0 (tcFn t)`, normalizado por
    (A) e invariancia `substtc`‑nivel‑1 de `tcFn h`), y el externo (nivel 0). -/
theorem pcc_nthc_succ_code (h t i : Term) :
    Prf (provFromCode (eqCodeFn
      (nthcT (consT (tcFn h) (tcFn t)) (succcT (tcFn i)))
      (nthcT (tcFn t) (tcFn i)))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn h))
  let W1 : Term := liftc zero (tcFn t)
  let W0 : Term := tcFn i
  let BODY : Formula := nthc (cons (.var 2) (.var 1)) (succ (.var 0)) =eq nthc (.var 1) (.var 0)
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode BODY)
      =eq eqCodeFn (nthcT (consT W2 (varc (numeral 1))) (succcT (varc (numeral 0))))
                   (nthcT (varc (numeral 1)) (varc (numeral 0)))) :=
    prf_substfc_arith_open 2 W2 BODY
  have hA2 : Prf (W2 =eq tcFn h) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn h)) (prf_liftc_tcFn h)
  have hnorm : Prf (eqCodeFn (nthcT (consT W2 (varc (numeral 1))) (succcT (varc (numeral 0))))
                             (nthcT (varc (numeral 1)) (varc (numeral 0)))
      =eq eqCodeFn (nthcT (consT (tcFn h) (varc (numeral 1))) (succcT (varc (numeral 0))))
                   (nthcT (varc (numeral 1)) (varc (numeral 0)))) :=
    prf_congr_eqCodeFn
      (prf_congr_nthcT (prf_congr_consT hA2 (prf_refl _)) (prf_refl _)) (prf_refl _)
  have hmid : Prf (substfc (succ zero) W1
      (eqCodeFn (nthcT (consT (tcFn h) (varc (numeral 1))) (succcT (varc (numeral 0))))
                (nthcT (varc (numeral 1)) (varc (numeral 0))))
      =eq eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) (succcT (varc (numeral 0))))
                   (nthcT (tcFn t) (varc (numeral 0)))) := by
    have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn t) :=
      prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
        (prf_liftc_tcFn t)
    have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
      prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
    have hh : Prf (substtc (succ zero) W1 (tcFn h) =eq tcFn h) := prf_substtc_tcFn_at 1 W1 h
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_nthcT (succ zero) W1 (consT (tcFn h) (varc (numeral 1)))
        (succcT (varc (numeral 0)))) ?_
      refine prf_congr_nthcT ?_ ?_
      · exact prf_eq_trans (prf_substtc_consT (succ zero) W1 (tcFn h) (varc (numeral 1)))
          (prf_congr_consT hh hv1)
      · exact prf_eq_trans (prf_substtc_succcT (succ zero) W1 (varc (numeral 0)))
          (prf_congr_succcT hv0)
    · refine prf_eq_trans (prf_substtc_nthcT (succ zero) W1 (varc (numeral 1)) (varc (numeral 0))) ?_
      exact prf_congr_nthcT hv1 hv0
  have hout : Prf (substfc zero W0
      (eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) (succcT (varc (numeral 0))))
                (nthcT (tcFn t) (varc (numeral 0))))
      =eq eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) (succcT (tcFn i)))
                   (nthcT (tcFn t) (tcFn i))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_nthcT zero W0 (consT (tcFn h) (tcFn t))
        (succcT (varc (numeral 0)))) ?_
      refine prf_congr_nthcT ?_ ?_
      · exact prf_eq_trans (prf_substtc_consT zero W0 (tcFn h) (tcFn t))
          (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_tcFn W0 t))
      · exact prf_eq_trans (prf_substtc_succcT zero W0 (varc (numeral 0)))
          (prf_congr_succcT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_nthcT zero W0 (tcFn t) (varc (numeral 0))) ?_
      exact prf_congr_nthcT (prf_substtc_tcFn W0 t) (prf_substtc_varc0 W0)
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (substfc (succ (succ zero)) W2
      (formCode BODY)))
      =eq eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) (succcT (tcFn i)))
                   (nthcT (tcFn t) (tcFn i))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 BODY (show ax_nthc_succ ∈ axioms by simp [axioms]) (tcFn h) (tcFn t) (tcFn i))

/-! ### La inducción ACOTADA de `nthc` (`∀p∀i. i<lenc p ⇒ Prov(⌜nthc(ṗ,ı̇) = (nthc p i)˙⌝)`)

Mismo esqueleto que `prf_nthc_runFn` (`RunFnBoundedPrf`): predicado con `∀i` **interno** (la HI se usa
en `pred i`), `step` con confinación `qconf` + `PrfH_spec`, y `case-split` de `i` con
`prf_zero_or_eq_succ_pred`. La diferencia: el consecuente es `provFromCode (evalNthcCode p i)`, así
que las igualdades de código se transportan **dentro de `Prov`** (Leibniz sobre `provFormulaC'`,
patrón `pcc_lt_tracked`) reflejando `pcc_nthc_zero_code`/`pcc_nthc_succ_code`. -/

/-- Código de la evaluación acotada de `nthc`: `nthc(ṗ,ı̇) = (nthc p i)˙`. -/
noncomputable def evalNthcCode (p i : Term) : Term :=
  eqCodeFn (nthcT (tcFn p) (tcFn i)) (tcFn (nthc p i))

theorem substTerm_evalNthcCode (v : Nat) (s p i : Term) :
    substTerm v s (evalNthcCode p i) = evalNthcCode (substTerm v s p) (substTerm v s i) := by
  simp only [evalNthcCode, eqCodeFn, nthcT, funcc, tcFn, nthc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem liftTerm_evalNthcCode (k : Nat) (p i : Term) :
    liftTerm k (evalNthcCode p i) = evalNthcCode (liftTerm k p) (liftTerm k i) := by
  simp only [evalNthcCode, eqCodeFn, nthcT, funcc, tcFn, nthc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- Predicado inductivo: `Ψ(p) = ∀i. (i < lenc p ⇒ provFromCode (evalNthcCode p i))`
    (lista `p` = `#1` bajo el `∀i`; `i` = `#0`). -/
noncomputable def nthcEvalPred : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 1)))
    (provFromCode (evalNthcCode (.var 1) (.var 0))))

/-- Caso base: `p = nil` (vacuo, `i < lenc nil = 0`). -/
theorem nthcEvalPred_base : Prf (substFormula 0 nil nthcEvalPred) := by
  refine Prf.gen _ ?_
  simp only [nthcEvalPred, substFormula_provFromCode_open, substTerm_evalNthcCode,
    substFormula, substTerm, substTerms, lt, lenc, nil, zero, Nat.reduceEqDiff,
    reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
      (BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) (prfH_hyp_self _)))

/-- Transporte de `provFromCode` por igualdad de código bajo contexto (Leibniz sobre
    `provFormulaC'`). -/
theorem PrfH_provCode_congr {Γ : List Formula} {C₁ C₂ : Term}
    (h : PrfH Γ (C₁ =eq C₂)) (hp : PrfH Γ (provFromCode C₁)) : PrfH Γ (provFromCode C₂) :=
  PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.leibniz provFormulaC' C₁ C₂)) h) hp

/-- Congruencia de `nthcT` en `PrfH`. -/
theorem PrfH_congr_nthcT {Γ : List Formula} {x x' y y' : Term}
    (hx : PrfH Γ (x =eq x')) (hy : PrfH Γ (y =eq y')) :
    PrfH Γ (nthcT x y =eq nthcT x' y') := by
  unfold nthcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head
    (PrfH_eq_trans (PrfH_congr_cons_head hx) (PrfH_congr_cons_tail (PrfH_congr_cons_head hy)))))

/-! ### El sustituto de `pcc_dot_cons` (antes `prf_tc_cons'`, retirado)` en esta capa

Aquí el transporte del `cons` dotado NO tiene la forma del molde de `EvalListPrf`
(`pcc_rw_dot_cons_un`), por tres razones:

* los sitios viven dentro de **`PrfH`** (con contexto de hipótesis), no en `Prf` pelado ⇒ hace falta
  la forma IMPLICACIÓN, `pcc_rw_imp`;
* `nthcT` es **binario**, y el hueco va en su primer argumento;
* el `cons` es **una de tres ranuras** que la prueba original reescribía a la vez. Las otras dos van
  por `prf_tc_zero` / `prf_tc_succ'`, que **siguen vivos** ⇒ se separan: primero las sanas a nivel de
  código, y sólo el `cons` por dentro de `Prov`.
-/

/-- **Molde de repatriación para la capa `nthc`.** Cambia `cons(ḣ,ṫ)` por `(cons h t)˙` **dentro de
    `Prov`**, bajo el contexto `⌜nthc(·, IDX) = RHS⌝`, y **dentro de `PrfH`**.

    Sustituye al viejo transporte por `pcc_dot_cons` (antes `prf_tc_cons'`, retirado)`, que era de CÓDIGO; éste es INTERNO. -/
theorem pcc_rw_dot_cons_nthc {Γ : List Formula} (h t IDX RHS : Term)
    (hI : ∀ W : Term, Prf (substtc zero W IDX =eq IDX))
    (hR : ∀ W : Term, Prf (substtc zero W RHS =eq RHS))
    (hbase : PrfH Γ (provFromCode (eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) IDX) RHS))) :
    PrfH Γ (provFromCode (eqCodeFn (nthcT (tcFn (cons h t)) IDX) RHS)) := by
  refine PrfH.mp _ _ _ (prf_to_prfH
    (pcc_rw_imp (fun s => eqCodeFn (nthcT s IDX) RHS) ?_ _ _ (pcc_dot_cons h t)) _) hbase
  intro s
  refine prf_eq_trans (prf_substfc_eq zero s (nthcT (varc (numeral 0)) IDX) RHS) ?_
  exact prf_congr_eqCodeFn
    (prf_eq_trans (prf_substtc_nthcT zero s (varc (numeral 0)) IDX)
      (prf_congr_nthcT (prf_substtc_varc0 s) (hI s)))
    (hR s)

/-- `nthcT X Y` es `substtc`‑invariante si `X`, `Y` lo son. -/
theorem substtc_inv_nthcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (nthcT X Y) =eq nthcT X Y) :=
  fun W => prf_eq_trans (prf_substtc_nthcT zero W X Y) (prf_congr_nthcT (hX W) (hY W))

/-- **Paso `cons`** de la inducción acotada: análisis de casos `i = 0 / σ(pred i)`
    (`prf_zero_or_eq_succ_pred`), reflejando `pcc_nthc_zero_code` (base) y `pcc_nthc_succ_code` + HI
    (`pcc_eq_trans_code_imp`) en el caso sucesor, transportando por igualdad de código bajo contexto
    (`PrfH_provCode_congr`). Confinación `qconf` + `PrfH_spec` (la HI es `∀i`), como `prf_nthc_runFn`. -/
theorem nthcEvalPred_step :
    Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 nthcEvalPred)
      (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nthcEvalPred)))))) := by
  refine Prf.gen _ (Prf.gen _ ?_)
  simp only [nthcEvalPred, liftFormula_provFromCode_open, substFormula_provFromCode_open,
    liftTerm_evalNthcCode, substTerm_evalNthcCode, liftFormula, liftTerm, liftTerms,
    substFormula, substTerm, substTerms, lt, lenc, cons, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (lenc (cons (.var 2) (.var 1)))) _ rfl)
  let P0 : Formula := Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 2)))
    (provFromCode (evalNthcCode (.var 2) (.var 0))))
  let A0 : Formula := lt (.var 0) (lenc (cons (.var 2) (.var 1)))
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?_ ?_
  · -- i = 0
    have hz : PrfH [Formula.eq (.var 0) zero, A0, P0] (Formula.eq (.var 0) zero) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hbase : PrfH [Formula.eq (.var 0) zero, A0, P0]
        (provFromCode (eqCodeFn (nthcT (consT (tcFn (.var 2)) (tcFn (.var 1))) (termCode zero))
          (tcFn (.var 2)))) := prf_to_prfH (pcc_nthc_zero_code (.var 2) (.var 1)) _
    -- el `cons` va por DENTRO de `Prov` (`pcc_dot_cons`); las otras dos ranuras siguen
    -- siendo reescrituras de CÓDIGO, que `prf_tc_zero` y `prf_tc_succ'` cubren y siguen vivas
    refine pcc_rw_dot_cons_nthc (.var 2) (.var 1) _ _
      (substtc_inv_tcFn _) (substtc_inv_tcFn _) ?_
    refine PrfH_provCode_congr ?_ hbase
    refine PrfH_congr_eqCodeFn (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) ?_) ?_
    · exact PrfH_eq_trans (prf_to_prfH (prf_eq_symm prf_tc_zero) _)
        (PrfH_congr_tcFn (PrfH_eq_symm hz))
    · exact PrfH_eq_symm (PrfH_eq_trans (PrfH_congr_tcFn (PrfH_eq_congr_nthc2 hz))
        (prf_to_prfH (prf_congr_tcFn (prf_nthc_zero (.var 2) (.var 1))) _))
  · -- i = σ(pred i)
    have hs : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0]
        (Formula.eq (.var 0) (succ (pred (.var 0)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hlt : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0] A0 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hP : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0] P0 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have ihj := PrfH_spec hP (pred (.var 0))
    simp only [P0, liftFormula_provFromCode_open, substFormula_provFromCode_open,
      substTerm_evalNthcCode, liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms,
      lt, lenc, pred, cons, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
      Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm,
      FOL.substTerm_liftLift] at ihj
    have hltJ : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0]
        (lt (pred (.var 0)) (lenc (.var 1))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (.var 1))) _)
        (BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH (prf_lenc_cons (.var 2) (.var 1)) _)
          (BoundedInPrf.PrfH_lt_subst1 hs hlt))
    have ihEval := PrfH.mp _ _ _ ihj hltJ
    let X : Term := nthcT (consT (tcFn (.var 2)) (tcFn (.var 1))) (succcT (tcFn (pred (.var 0))))
    let Y : Term := nthcT (tcFn (.var 1)) (tcFn (pred (.var 0)))
    let Z : Term := tcFn (nthc (.var 1) (pred (.var 0)))
    have hX : ∀ W, Prf (substtc zero W X =eq X) :=
      substtc_inv_nthcT (substtc_inv_consT (substtc_inv_tcFn (.var 2)) (substtc_inv_tcFn (.var 1)))
        (substtc_inv_succcT (substtc_inv_tcFn (pred (.var 0))))
    have hXZ : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0]
        (provFromCode (eqc X Z)) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_trans_code_imp X Y Z hX
        (pcc_nthc_succ_code (.var 2) (.var 1) (pred (.var 0)))) _) ihEval
    refine pcc_rw_dot_cons_nthc (.var 2) (.var 1) _ _
      (substtc_inv_tcFn _) (substtc_inv_tcFn _) ?_
    refine PrfH_provCode_congr ?_ hXZ
    refine PrfH_congr_eqCodeFn (PrfH_congr_nthcT (prf_to_prfH (prf_refl _) _) ?_) ?_
    · exact PrfH_eq_trans (prf_to_prfH (prf_eq_symm (prf_tc_succ' (pred (.var 0)))) _)
        (PrfH_congr_tcFn (PrfH_eq_symm hs))
    · exact PrfH_eq_symm (PrfH_eq_trans (PrfH_congr_tcFn (PrfH_eq_congr_nthc2 hs))
        (prf_to_prfH (prf_congr_tcFn (prf_nthc_succ (.var 2) (.var 1) (pred (.var 0)))) _))

/-- **EVALUACIÓN ACOTADA DE `nthc`**: `⊢ (i < lenc p) ⇒ Prov(⌜nthc(ṗ,ı̇) = (nthc p i)˙⌝)`, para
    `p`, `i` **arbitrarios**. Inducción de listas (`nthcEvalPred_base`/`_step`) + `prf_spec`. -/
theorem pcc_eval_nthc (p i : Term) :
    Prf ((lt i (lenc p)) ⇒ provFromCode (evalNthcCode p i)) := by
  have key : Prf (Formula.forall nthcEvalPred) :=
    prf_list_induction nthcEvalPred nthcEvalPred_base nthcEvalPred_step
  have hi := prf_spec (prf_spec key p) i
  simpa only [nthcEvalPred, substFormula_provFromCode_open, substTerm_evalNthcCode,
    substFormula, substTerm, substTerms, lt, lenc, nil, zero, Nat.reduceAdd, Nat.reduceGT,
    Nat.reduceSub, Nat.reduceEqDiff, reduceIte, if_true, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift] using hi

end ROBINSON_PlusPlus.Meta.EvalNthcPrf

export ROBINSON_PlusPlus.Meta.EvalNthcPrf (
  nthcT prf_congr_nthcT prf_substtc_nthcT pcc_nthc_zero_code pcc_nthc_succ_code
  evalNthcCode substTerm_evalNthcCode liftTerm_evalNthcCode nthcEvalPred nthcEvalPred_base
  PrfH_provCode_congr PrfH_congr_nthcT
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.NatMulPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.EvalMulPrf

/-!
## META — **evaluación provable del PRODUCTO**: `⊢ Prov(⌈ ẋ · ỳ = (x·y)˙ ⌉)`

**Segundo peldaño de la escalera (a.2)** (`PLAN-FRENTE-A.md`). Espejo exacto de
`Meta/EvalArithPrf.lean`, que hace `+`, con `prf_nat_induction` como cierre.

**La diferencia estructural con `+`:** `ax9_mul_succ` da `x·σy = (x·y) + x`, cuyo lado derecho es un
`add`, **no un `succ`**. Por eso el paso inductivo necesita dos piezas que `+` no tenía:

* **`pcc_congr_addcT1_code_imp`** — congruencia de `addcT` en el PRIMER argumento, para meter la HI;
* **`pcc_eq_subst2_code_imp`** — sustitución en el SEGUNDO argumento de `=` con la igualdad
  **cerrada**, que es lo que permite encadenar con **`pcc_eval_add`** (cuya igualdad viene cerrada
  mientras la de la HI está en contexto).

O sea: **este peldaño CONSUME el anterior.** La cadena del paso es
`HI → (ẋ·ỳ)+ẋ = (x·y)˙+ẋ → ẋ·σỳ = (x·y)˙+ẋ → ẋ·σỳ = (x·y+x)˙`.
-/


/-! ### Constructor de código del término `x · y` -/

/-- Código object del término `x · y`: `⟨1, ⌜·⌝, [x, y]⟩`. -/
def mulcT (x y : Term) : Term := funcc (strCode mul_sym) (cons x (cons y nil))

theorem mulcT_termCode (a b : Term) : mulcT (termCode a) (termCode b) = termCode (mul a b) := rfl

/-- `mulcT X Y` tiene testigo si lo tienen sus dos argumentos (escalera de aridad, §28). -/
theorem prf_hasWit_mulcT {X Y : Term} (hX : Prf (hasWit X)) (hY : Prf (hasWit Y)) :
    Prf (hasWit (mulcT X Y)) :=
  prf_hasWit_funcc2 (strCode mul_sym) X Y hX hY

theorem prf_congr_mulcT {x x' y y' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (mulcT x y =eq mulcT x' y') := by
  unfold mulcT funcc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head hx) (prf_congr_cons_tail (prf_congr_cons_head hy)))))

/-- `substtc` atraviesa `mulcT` (es `prf_substtc_funcc2`). -/
theorem prf_substtc_mulcT (v W x y : Term) :
    Prf (substtc v W (mulcT x y) =eq mulcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode mul_sym) x y

theorem substtc_inv_mulcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (mulcT X Y) =eq mulcT X Y) :=
  fun W => prf_eq_trans (prf_substtc_mulcT zero W X Y) (prf_congr_mulcT (hX W) (hY W))

/-- El enunciado: `ȧ · ḃ = (a·b)˙`. -/
def evalMulCode (a b : Term) : Term :=
  eqCodeFn (mulcT (tcFn a) (tcFn b)) (tcFn (mul a b))

/-! ### Instancias codificadas de `ax8` y `ax9` -/

theorem pcc_ax8_inst (w : Term) (hw : Prf (hasWit (liftTerm 0 w))) :
    Prf (provFromCode (substfc zero w (formCode (mul (.var 0) zero =eq zero)))) :=
  pcc_axiom_inst _ (show ax8_mul_zero ∈ axioms by simp [axioms]) w hw

theorem pcc_ax9_inst (w₁ w₂ : Term)
    (hw₁ : Prf (hasWit (liftTerm 0 w₁))) (hw₂ : Prf (hasWit (liftTerm 0 w₂))) :
    Prf (provFromCode (substfc zero w₂ (substfc (succ zero) (liftc zero w₁)
      (formCode (mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1)))))) :=
  pcc_axiom_inst2 _ (show ax9_mul_succ ∈ axioms by simp [axioms]) w₁ w₂ hw₁ hw₂

/-! ### BASE: `b = 0` -/

theorem pcc_ax8_computed (a : Term) :
    Prf (provFromCode (eqCodeFn (mulcT (tcFn a) (termCode zero)) (termCode zero))) :=
  prf_mp
    (prf_provCode_congr
      (prf_substfc_arith_open 0 (tcFn a) (mul (.var 0) zero =eq zero)))
    (pcc_ax8_inst (tcFn a) (prf_hasWit_tcFn (liftTerm 0 a)))

theorem pcc_eval_mul_zero (a : Term) : Prf (provFromCode (evalMulCode a zero)) := by
  have hz : Prf (termCode zero =eq tcFn zero) := prf_eq_symm prf_tc_zero
  have ha : Prf (termCode zero =eq tcFn (mul a zero)) :=
    prf_eq_symm (prf_eq_trans (prf_congr_tcFn (prf_mul_zero a)) prf_tc_zero)
  exact prf_mp
    (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_mulcT (prf_refl (tcFn a)) hz) ha))
    (pcc_ax8_computed a)

/-! ### La instancia de `ax9`, computada -/

theorem pcc_ax9_computed (a b : Term) :
    Prf (provFromCode
      (eqCodeFn (mulcT (tcFn a) (succcT (tcFn b)))
                (addcT (mulcT (tcFn a) (tcFn b)) (tcFn a)))) := by
  let W1 : Term := liftc zero (tcFn a)
  let B : Term := tcFn b
  have hin : Prf (substfc (succ zero) W1
      (formCode (mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1)))
      =eq eqCodeFn (mulcT W1 (succcT (varc (numeral 0))))
                   (addcT (mulcT W1 (varc (numeral 0))) W1)) :=
    prf_substfc_arith_open 1 W1
      (mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1))
  have hA : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  have hnorm : Prf (eqCodeFn (mulcT W1 (succcT (varc (numeral 0))))
                             (addcT (mulcT W1 (varc (numeral 0))) W1)
      =eq eqCodeFn (mulcT (tcFn a) (succcT (varc (numeral 0))))
                   (addcT (mulcT (tcFn a) (varc (numeral 0))) (tcFn a))) :=
    prf_congr_eqCodeFn
      (prf_congr_mulcT hA (prf_refl _))
      (prf_congr_addcT (prf_congr_mulcT hA (prf_refl _)) hA)
  have hout : Prf (substfc zero B
      (eqCodeFn (mulcT (tcFn a) (succcT (varc (numeral 0))))
                (addcT (mulcT (tcFn a) (varc (numeral 0))) (tcFn a)))
      =eq eqCodeFn (mulcT (tcFn a) (succcT B)) (addcT (mulcT (tcFn a) B) (tcFn a))) := by
    refine prf_eq_trans
      (prf_substfc_eq zero B (mulcT (tcFn a) (succcT (varc (numeral 0))))
        (addcT (mulcT (tcFn a) (varc (numeral 0))) (tcFn a))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_mulcT zero B (tcFn a) (succcT (varc (numeral 0)))) ?_
      refine prf_congr_mulcT (prf_substtc_tcFn B a) ?_
      exact prf_eq_trans (prf_substtc_succcT zero B (varc (numeral 0)))
        (prf_congr_succcT (prf_substtc_varc0 B))
    · refine prf_eq_trans (prf_substtc_addcT zero B (mulcT (tcFn a) (varc (numeral 0))) (tcFn a)) ?_
      refine prf_congr_addcT ?_ (prf_substtc_tcFn B a)
      exact prf_eq_trans (prf_substtc_mulcT zero B (tcFn a) (varc (numeral 0)))
        (prf_congr_mulcT (prf_substtc_tcFn B a) (prf_substtc_varc0 B))
  have hchain : Prf (substfc zero B (substfc (succ zero) W1
      (formCode (mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1))))
      =eq eqCodeFn (mulcT (tcFn a) (succcT B)) (addcT (mulcT (tcFn a) B) (tcFn a))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_ax9_inst (tcFn a) B (prf_hasWit_tcFn (liftTerm 0 a)) (prf_hasWit_tcFn (liftTerm 0 b)))

/-! ### Las dos congruencias nuevas dentro de `Prov` -/

/-- **Congruencia de `addcT` en el PRIMER argumento**, en forma implicación.
    Espejo de `pcc_congr_succ_code_imp` con contexto `Ac := (X+A = v₀+A)`. -/
theorem pcc_congr_addcT1_code_imp (X Y A : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hA : ∀ W, Prf (substtc zero W A =eq A))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) (hwA : Prf (hasWit A)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (addcT X A) (addcT Y A))) := by
  let Ac : Term := eqc (addcT X A) (addcT (varc (numeral 0)) A)
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc (addcT X A) (addcT t A)) := by
    intro t
    refine prf_eq_trans (prf_substfc_eq zero t (addcT X A) (addcT (varc (numeral 0)) A)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_addcT zero t X A) (prf_congr_addcT (hX t) (hA t))
    · exact prf_eq_trans (prf_substtc_addcT zero t (varc (numeral 0)) A)
        (prf_congr_addcT (prf_substtc_varc0 t) (hA t))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (addcT X A))
  have himp : Prf (provFromCode (eqc X Y) ⇒ provFromCode (substfc zero Y Ac)) :=
    pcc_leibniz_apply_imp Ac X Y
      (prf_hasWitF_eq2 (addcT X A) (addcT (varc (numeral 0)) A)
        (prf_hasWit_addcT hwX hwA)
        (prf_hasWit_addcT (prf_hasWit_varc (numeral 0)) hwA)) hwX hwY hAX
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (prfH_hyp_self _))

/-- **Sustitución en el SEGUNDO argumento de `=`**, con la igualdad CERRADA:
    de `Prov(⌜Z=W⌝)` sale `Prov(⌜X=Z⌝) ⇒ Prov(⌜X=W⌝)`. Es lo que permite encadenar con
    `pcc_eval_add`, cuya igualdad viene cerrada mientras la otra está en contexto. -/
theorem pcc_eq_subst2_code_imp (X Z W : Term) (hX : ∀ V, Prf (substtc zero V X =eq X))
    (hwX : Prf (hasWit X)) (hwZ : Prf (hasWit Z)) (hwW : Prf (hasWit W))
    (hZW : Prf (provFromCode (eqc Z W))) :
    Prf (provFromCode (eqc X Z) ⇒ provFromCode (eqc X W)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hI : Prf (provFromCode (implc (substfc zero Z Ac) (substfc zero W Ac))) :=
    pcc_mp_code_apply (pcc_leibniz_code Ac Z W
      (prf_hasWitF_eq2 X (varc (numeral 0)) hwX (prf_hasWit_varc (numeral 0))) hwZ hwW) hZW
  have himp : Prf (provFromCode (substfc zero Z Ac) ⇒ provFromCode (substfc zero W Ac)) :=
    prf_mp (pcc_mp_code_open _ _) hI
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp W)) _)
    (PrfH.mp _ _ _ (prf_to_prfH himp _)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp Z))) _)
        (prfH_hyp_self _)))

/-! ### PASO INDUCTIVO de `·` -/

theorem pcc_eval_mul_succ_imp (a b : Term) :
    Prf (provFromCode (evalMulCode a b) ⇒ provFromCode (evalMulCode a (succ b))) := by
  have hinvA : ∀ W, Prf (substtc zero W (tcFn a) =eq tcFn a) := substtc_inv_tcFn a
  have hinvMB : ∀ W, Prf (substtc zero W (mulcT (tcFn a) (tcFn b)) =eq mulcT (tcFn a) (tcFn b)) :=
    substtc_inv_mulcT (substtc_inv_tcFn a) (substtc_inv_tcFn b)
  have hinvMS : ∀ W, Prf (substtc zero W (mulcT (tcFn a) (succcT (tcFn b)))
      =eq mulcT (tcFn a) (succcT (tcFn b))) :=
    substtc_inv_mulcT (substtc_inv_tcFn a) (substtc_inv_succcT (substtc_inv_tcFn b))
  -- (1) HI ⇒ `Prov(⌜(ȧ·ḃ)+ȧ = (a·b)˙+ȧ⌝)`
  have h1 : Prf (provFromCode (eqc (mulcT (tcFn a) (tcFn b)) (tcFn (mul a b)))
      ⇒ provFromCode (eqc (addcT (mulcT (tcFn a) (tcFn b)) (tcFn a))
                          (addcT (tcFn (mul a b)) (tcFn a)))) :=
    pcc_congr_addcT1_code_imp _ _ _ hinvMB hinvA
      (prf_hasWit_mulcT (prf_hasWit_tcFn a) (prf_hasWit_tcFn b))
      (prf_hasWit_tcFn (mul a b)) (prf_hasWit_tcFn a)
  -- (2) `ax9` + transitividad ⇒ `Prov(⌜ȧ·σḃ = (a·b)˙+ȧ⌝)`
  have h2 : Prf (provFromCode (eqc (addcT (mulcT (tcFn a) (tcFn b)) (tcFn a))
                                   (addcT (tcFn (mul a b)) (tcFn a)))
      ⇒ provFromCode (eqc (mulcT (tcFn a) (succcT (tcFn b)))
                          (addcT (tcFn (mul a b)) (tcFn a)))) :=
    pcc_eq_trans_code_imp _ _ _ hinvMS
      (prf_hasWit_mulcT (prf_hasWit_tcFn a) (prf_hasWit_succcT (prf_hasWit_tcFn b)))
      (prf_hasWit_addcT (prf_hasWit_mulcT (prf_hasWit_tcFn a) (prf_hasWit_tcFn b))
        (prf_hasWit_tcFn a))
      (prf_hasWit_addcT (prf_hasWit_tcFn (mul a b)) (prf_hasWit_tcFn a))
      (pcc_ax9_computed a b)
  -- (3) encadenar con `pcc_eval_add` ⇒ `Prov(⌜ȧ·σḃ = (a·b+a)˙⌝)`
  have h3 : Prf (provFromCode (eqc (mulcT (tcFn a) (succcT (tcFn b)))
                                   (addcT (tcFn (mul a b)) (tcFn a)))
      ⇒ provFromCode (eqc (mulcT (tcFn a) (succcT (tcFn b)))
                          (tcFn (add (mul a b) a)))) :=
    pcc_eq_subst2_code_imp _ _ _ hinvMS
      (prf_hasWit_mulcT (prf_hasWit_tcFn a) (prf_hasWit_succcT (prf_hasWit_tcFn b)))
      (prf_hasWit_addcT (prf_hasWit_tcFn (mul a b)) (prf_hasWit_tcFn a))
      (prf_hasWit_tcFn (add (mul a b) a))
      (pcc_eval_add (mul a b) a)
  -- (4) transporte final de códigos
  have hcode : Prf (eqc (mulcT (tcFn a) (succcT (tcFn b))) (tcFn (add (mul a b) a))
      =eq evalMulCode a (succ b)) :=
    prf_congr_eqCodeFn
      (prf_congr_mulcT (prf_refl (tcFn a)) (prf_eq_symm (prf_tc_succ' b)))
      (prf_eq_symm (prf_congr_tcFn (prf_mul_succ a b)))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcode) _)
    (PrfH.mp _ _ _ (prf_to_prfH h3 _)
      (PrfH.mp _ _ _ (prf_to_prfH h2 _)
        (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))))

/-! ### Inducción object -/

theorem substTerm_evalMulCode (v : Nat) (s X Y : Term) :
    substTerm v s (evalMulCode X Y)
      = evalMulCode (substTerm v s X) (substTerm v s Y) := by
  simp only [evalMulCode, eqCodeFn, mulcT, funcc, tcFn, mul, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem liftTerm_evalMulCode (k : Nat) (X Y : Term) :
    liftTerm k (evalMulCode X Y) = evalMulCode (liftTerm k X) (liftTerm k Y) := by
  simp only [evalMulCode, eqCodeFn, mulcT, funcc, tcFn, mul, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

def evalMulPred (a : Term) : Formula := provFromCode (evalMulCode (liftTerm 0 a) (.var 0))

theorem substFormula_evalMulPred (a b : Term) :
    substFormula 0 b (evalMulPred a) = provFromCode (evalMulCode a b) := by
  simp only [evalMulPred, substFormula_provFromCode_open, substTerm_evalMulCode, substTerm,
    reduceIte, FOL.substTerm_liftTerm]

theorem step_evalMulPred (a : Term) :
    substFormula 0 (succ (.var 0)) (liftFormula 1 (provFromCode (evalMulCode (liftTerm 0 a) (.var 0))))
      = provFromCode (evalMulCode (liftTerm 0 a) (succ (.var 0))) := by
  rw [liftFormula_provFromCode_open, liftTerm_evalMulCode, substFormula_provFromCode_open,
    substTerm_evalMulCode, ← FOL.liftTerm_comm_zero a 0, FOL.substTerm_liftTerm]
  simp only [liftTerm, substTerm, Nat.zero_lt_one, reduceIte, Nat.lt_irrefl, if_true]

/-- **EVALUACIÓN PROVABLE DE `·` (∀ object)**. -/
theorem prf_eval_mul_all (a : Term) : Prf (Formula.forall (evalMulPred a)) := by
  refine prf_nat_induction (evalMulPred a) ?base ?step
  · rw [substFormula_evalMulPred]
    exact pcc_eval_mul_zero a
  · refine Prf.gen _ ?_
    show Prf (Formula.impl (provFromCode (evalMulCode (liftTerm 0 a) (.var 0)))
      (substFormula 0 (succ (.var 0))
        (liftFormula 1 (provFromCode (evalMulCode (liftTerm 0 a) (.var 0))))))
    rw [step_evalMulPred]
    exact pcc_eval_mul_succ_imp (liftTerm 0 a) (.var 0)

/-- **`pcc_eval_mul`** — `⊢ Prov(⌜ȧ · ḃ = (a·b)˙⌝)` para `a`, `b` arbitrarios. -/
theorem pcc_eval_mul (a b : Term) : Prf (provFromCode (evalMulCode a b)) := by
  have h := prf_spec (prf_eval_mul_all a) b
  rwa [substFormula_evalMulPred] at h





end ROBINSON_PlusPlus.Meta.EvalMulPrf

export ROBINSON_PlusPlus.Meta.EvalMulPrf (
  mulcT mulcT_termCode prf_congr_mulcT prf_substtc_mulcT substtc_inv_mulcT
  evalMulCode pcc_ax8_inst pcc_ax9_inst pcc_ax8_computed pcc_eval_mul_zero
  pcc_ax9_computed pcc_congr_addcT1_code_imp pcc_eq_subst2_code_imp
  pcc_eval_mul_succ_imp
  substTerm_evalMulCode liftTerm_evalMulCode evalMulPred
  substFormula_evalMulPred step_evalMulPred prf_eval_mul_all pcc_eval_mul
  -- ADR-020: la guarda de los constructores dotados (escalera de aridad, §28)
  prf_hasWit_mulcT
)

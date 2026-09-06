/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.ExIntroCodePrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.ExIntroCodePrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace ROBINSON_PlusPlus.Meta.EvalLtPrf

/-!
## META — NIVEL D real (§29): reflexión del átomo `<`

`<` **no es primitivo**: `ax13_lt_def` lo define como `n < m ⇔ ∃k. n + σk = m`. Reflejarlo al nivel
de código es por tanto **`∃`‑intro + `=eq` + evaluación provable de `+`** (§18), las tres piezas ya
construidas:

* la dirección `⇐` de `ax13` es un **teorema object** cerrado `ltBwd`
  (`∀n∀m. (∃k. n+σk=m) ⇒ n<m`);
* se **codifica en forma rastreada** (`tcFn`) instanciándolo con `pcc_thm_inst2` y computando el
  doble `substfc` con `prf_substfc_arith_open` (sin `termCode`, sin muro de Tarski);
* de un testigo `Prov(⌜ȧ + σK = ḃ⌝)` (evaluación provable de `+`), el **`∃`‑intro codificado**
  (`pcc_exIntro_code'`) da `Prov(⌜∃k. ȧ + σk = ḃ⌝)`, y el **MP interno** (`pcc_mp_code_apply`)
  concluye `Prov(⌜ȧ < ḃ⌝)`.

El resultado es `pcc_lt_intro`: la regla de introducción de `<` **reflejada** para códigos `tcFn`.
-/

/-! ### Congruencias de código auxiliares -/

theorem prf_congr_implc {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (implc a b =eq implc a' b') := by
  unfold implc
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))

theorem prf_congr_exc {a a' : Term} (h : Prf (a =eq a')) : Prf (exc a =eq exc a') := by
  unfold exc
  exact prf_congr_cons_tail (prf_congr_cons_head h)

/-! ### `substtc` a nivel arbitrario deja invariante el código de un numeral

`prf_substtc_tcFn` (§23) sólo cubre el nivel `0`. El `substfc` externo bajo el `∃`‑binder de `ax13`
actúa a nivel `1` (`prf_substfc_ex` lo incrementa), así que necesitamos la invariancia de `tcFn a`
bajo `substtc (numeral k)` para `k` arbitrario. Mismo esquema que §23 (inducción interna), con el
nivel parametrizado. -/

/-- Base a nivel `k`: `substtc ⌜k⌝ W (tcFn 0) =eq tcFn 0`. -/
theorem prf_substtc_tcFn_zero_at (k : Nat) (W : Term) :
    Prf (substtc (numeral k) W (tcFn zero) =eq tcFn zero) :=
  prf_eq_trans (prf_congr_substtc3 prf_tc_zero)
    (prf_eq_trans (prf_substtc_arith_open k W zero) (prf_eq_symm prf_tc_zero))

/-- Paso a nivel `k`: `substtc ⌜k⌝` atraviesa `tcFn (σx) = succc (tcFn x)` y baja a la HI. -/
theorem prf_substtc_tcFn_succ_imp_at (k : Nat) (W x : Term) :
    Prf ((substtc (numeral k) W (tcFn x) =eq tcFn x)
      ⇒ (substtc (numeral k) W (tcFn (succ x)) =eq tcFn (succ x))) := by
  refine prf_deduction ?_
  have ih : PrfH [substtc (numeral k) W (tcFn x) =eq tcFn x]
      (substtc (numeral k) W (tcFn x) =eq tcFn x) := prfH_hyp_self _
  have hsucc : Prf (tcFn (succ x) =eq funcc (strCode succ_sym) (cons (tcFn x) nil)) :=
    prf_tc_succ x
  refine PrfH_eq_trans (PrfH_congr_substtc3 (prf_to_prfH hsucc _)) ?_
  refine PrfH_eq_trans
    (prf_to_prfH (prf_substtc_func (numeral k) W (strCode succ_sym) (cons (tcFn x) nil)) _) ?_
  refine PrfH_eq_trans (PrfH_congr_funcc2 ?_) (prf_to_prfH (prf_eq_symm hsucc) _)
  refine PrfH_eq_trans (prf_to_prfH (prf_substtsc_cons (numeral k) W (tcFn x) nil) _) ?_
  exact PrfH_eq_trans (PrfH_congr_cons_head ih)
    (PrfH_congr_cons_tail (prf_to_prfH (prf_substtsc_nil (numeral k) W) _))

/-- Predicado inductivo a nivel `k` (testigo `W` externo, liftado bajo el `∀`). -/
def substtcTcPredAt (k : Nat) (W : Term) : Formula :=
  Formula.eq (substtc (numeral k) (liftTerm 0 W) (tcFn (.var 0))) (tcFn (.var 0))

theorem prf_substtc_tcFn_all_at (k : Nat) (W : Term) :
    Prf (Formula.forall (substtcTcPredAt k W)) := by
  refine prf_nat_induction (substtcTcPredAt k W) ?base ?step
  · simpa only [substtcTcPredAt, substFormula, substTerm, substTerms, substtc, tcFn, zero,
      substTerm_numeral, reduceIte, if_true, FOL.substTerm_liftTerm]
      using prf_substtc_tcFn_zero_at k W
  · refine Prf.gen _ ?_
    simpa only [substtcTcPredAt, liftFormula, liftTerm, liftTerms, substFormula, substTerm,
      substTerms, substtc, tcFn, zero, succ, liftTerm_numeral, substTerm_numeral, Nat.reduceAdd,
      Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, norm11]
      using prf_substtc_tcFn_succ_imp_at k (liftTerm 0 W) (.var 0)

/-- **`substtc ⌜k⌝ W (tcFn a) =eq tcFn a`** a nivel `k` arbitrario (instancia del ∀). -/
theorem prf_substtc_tcFn_at (k : Nat) (W a : Term) :
    Prf (substtc (numeral k) W (tcFn a) =eq tcFn a) := by
  have h := prf_spec (prf_substtc_tcFn_all_at k W) a
  simpa only [substtcTcPredAt, substFormula, substTerm, substTerms, substtc, tcFn, zero,
    substTerm_numeral, reduceIte, if_true, FOL.substTerm_liftTerm] using h

/-! ### Código del átomo `<` y cuerpo del existencial -/

/-- Código object del átomo `A < B` desde los códigos `A`, `B` (tag 3, símbolo `<`). -/
def ltCodeFn (A B : Term) : Term := atom2CodeFn lt_sym A B

/-- Puente definicional con `formCode` (por definición de `formCode` sobre `.atom`). -/
theorem ltCodeFn_termCode (a b : Term) :
    ltCodeFn (termCode a) (termCode b) = formCode (lt a b) := rfl

/-- El «cuerpo `∃`» del código rastreado, abierto en `⌜v₀⌝` (la `k` del existencial):
    código de `A + σ(v₀) = B`. -/
def exBodyc (A B : Term) : Term :=
  eqCodeFn (addcT A (succcT (varc (numeral 0)))) B

/-- Cuerpo de `ltBwd` (dirección `⇐` de `ax13`): `(∃k. n+σk=m) ⇒ n<m` con `n=#1`, `m=#0`. -/
def phiLtBwd : Formula :=
  Formula.impl
    (Formula.ex (add (.var 2) (succ (.var 0)) =eq (.var 1)))
    (lt (.var 1) (.var 0))

/-- **Teorema object** `∀n∀m. (∃k. n+σk=m) ⇒ n<m` (la dirección `⇐` de `ax13_lt_def`,
    generalizada). Prueba por deducción + `∃`‑elim + `PrfH_lt_intro`. -/
theorem ltBwd : Prf (forall_2 phiLtBwd) := by
  refine Prf.gen _ (Prf.gen _ ?_)
  refine prf_deduction ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  refine PrfH_lt_intro (.var 2) (.var 1) (.var 0) ?_
  exact PrfH.hyp _ _ (List.Mem.head _)

/-! ### La implicación `⇐` de `ax13`, CODIFICADA en forma rastreada

`substCodeF 1 w phiLtBwd` computa por `rfl` a
`implc (exc (eqCodeFn (addcT (liftc 0 w) (succcT ⌜v₀⌝)) ⌜v₁⌝)) (atom2CodeFn "<" w ⌜v₀⌝)`.
El `substfc` externo (testigo `tcFn b`) más la normalización de los `liftc` con (A) dan el código
rastreado de `(∃k. ȧ + σk = ḃ) ⇒ ȧ < ḃ`. -/

theorem pcc_ltBwd_computed (a b : Term) :
    Prf (provFromCode
      (implc (exc (exBodyc (tcFn a) (tcFn b))) (ltCodeFn (tcFn a) (tcFn b)))) := by
  let A : Term := tcFn a
  let B : Term := tcFn b
  let W : Term := liftc zero A
  have h0 : Prf (provFromCode
      (substfc zero B (substfc (succ zero) W (formCode phiLtBwd)))) :=
    pcc_thm_inst2 phiLtBwd ltBwd A B
      (prf_hasWit_tcFn (liftTerm 0 a)) (prf_hasWit_tcFn (liftTerm 0 b))
  -- (1) `substfc` INTERNO (nivel 1) sobre `formCode phiLtBwd` (computa por `rfl` a substCodeF)
  have hin : Prf (substfc (succ zero) W (formCode phiLtBwd)
      =eq implc (exc (eqCodeFn (addcT (liftc zero W) (succcT (varc (numeral 0))))
                              (varc (numeral 1))))
                (atom2CodeFn lt_sym W (varc (numeral 0)))) :=
    prf_substfc_arith_open 1 W phiLtBwd
  -- (2) normaliza los `liftc` con (A): `W → A`, `liftc 0 W → A`
  have hWA : Prf (W =eq A) := prf_liftc_tcFn a
  have hWWA : Prf (liftc zero W =eq A) := prf_eq_trans (prf_congr_liftc hWA) hWA
  have hnorm : Prf (implc (exc (eqCodeFn (addcT (liftc zero W) (succcT (varc (numeral 0))))
                                         (varc (numeral 1))))
                          (atom2CodeFn lt_sym W (varc (numeral 0)))
      =eq implc (exc (eqCodeFn (addcT A (succcT (varc (numeral 0)))) (varc (numeral 1))))
                (ltCodeFn A (varc (numeral 0)))) :=
    prf_congr_implc
      (prf_congr_exc (prf_congr_eqCodeFn (prf_congr_addcT hWWA (prf_refl _)) (prf_refl _)))
      (prf_congr_atom2CodeFn hWA (prf_refl _))
  -- (3) `substfc` EXTERNO (nivel 0, testigo `B`)
  have hout : Prf (substfc zero B
      (implc (exc (eqCodeFn (addcT A (succcT (varc (numeral 0)))) (varc (numeral 1))))
             (ltCodeFn A (varc (numeral 0))))
      =eq implc (exc (exBodyc A B)) (ltCodeFn A B)) := by
    refine prf_eq_trans (prf_substfc_impl zero B _ _) ?_
    refine prf_congr_implc ?_ ?_
    · -- lado ∃:  substfc 0 B (exc …) = exc (substfc 1 (liftc 0 B) …)
      refine prf_eq_trans (prf_substfc_ex zero B _) ?_
      refine prf_congr_exc ?_
      refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero B) _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · -- addcT A (σ⌜v₀⌝): A invariante a nivel 1, ⌜v₀⌝ (0 < 1) intacto
        refine prf_eq_trans (prf_substtc_addcT (succ zero) (liftc zero B) A
          (succcT (varc (numeral 0)))) ?_
        refine prf_congr_addcT ?_ ?_
        · exact prf_substtc_tcFn_at 1 (liftc zero B) a
        · refine prf_eq_trans (prf_substtc_succcT (succ zero) (liftc zero B)
            (varc (numeral 0))) ?_
          refine prf_congr_succcT ?_
          exact prf_mp (prf_substtc_var_lt (succ zero) (liftc zero B) (numeral 0))
            (prf_zero_lt_succ zero)
      · -- ⌜v₁⌝ (1 = 1) recibe el testigo:  liftc 0 B → B
        refine prf_eq_trans
          (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero B) (numeral 1)) (prf_refl _)) ?_
        exact prf_liftc_tcFn b
    · -- lado `<`:  substfc 0 B (ltCodeFn A ⌜v₀⌝) = ltCodeFn A B
      have hts : Prf (substtsc zero B (cons A (cons (varc (numeral 0)) nil))
          =eq cons A (cons B nil)) :=
        prf_eq_trans (prf_substtsc_cons zero B A (cons (varc (numeral 0)) nil))
          (prf_eq_trans (prf_congr_cons_head (prf_substtc_tcFn B a))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons zero B (varc (numeral 0)) nil)
                (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 B))
                  (prf_congr_cons_tail (prf_substtsc_nil zero B))))))
      refine prf_eq_trans (prf_substfc_atom zero B (strCode lt_sym)
        (cons A (cons (varc (numeral 0)) nil))) ?_
      show Prf (atomc (strCode lt_sym) (substtsc zero B (cons A (cons (varc (numeral 0)) nil)))
        =eq atomc (strCode lt_sym) (cons A (cons B nil)))
      unfold atomc
      exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head hts))
  have hchain : Prf (substfc zero B (substfc (succ zero) W (formCode phiLtBwd))
      =eq implc (exc (exBodyc A B)) (ltCodeFn A B)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain) h0

/-! ### `exBodyc` cerrado y su cómputo bajo `substfc` -/

/-- `exBodyc A B` es cerrado a todo nivel si `A`, `B` lo son. -/
theorem liftTerm_exBodyc (A B : Term)
    (hA : ∀ c, liftTerm c A = A) (hB : ∀ c, liftTerm c B = B) :
    ∀ c, liftTerm c (exBodyc A B) = exBodyc A B := by
  intro c
  simp only [exBodyc, eqCodeFn, addcT, succcT, varc, funcc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode, hA c, hB c]

/-- `substfc zero K (exBodyc A B) =eq eqCodeFn (addcT A (σK)) B` (`⌜v₀⌝` recibe el testigo `K`). -/
theorem prf_substfc_exBodyc (A B K : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B)) :
    Prf (substfc zero K (exBodyc A B) =eq eqCodeFn (addcT A (succcT K)) B) := by
  refine prf_eq_trans (prf_substfc_eq zero K _ _) ?_
  refine prf_congr_eqCodeFn ?_ (hB K)
  refine prf_eq_trans (prf_substtc_addcT zero K A (succcT (varc (numeral 0)))) ?_
  refine prf_congr_addcT (hA K) ?_
  exact prf_eq_trans (prf_substtc_succcT zero K (varc (numeral 0)))
    (prf_congr_succcT (prf_substtc_varc0 K))

/-! ### La regla de introducción de `<` REFLEJADA -/

/-- **Reflexión de `<`** (regla de introducción): dado un testigo `K` y la evaluación provable
    `Prov(⌜ȧ + σK = ḃ⌝)`, con `a`, `b` cerrados, se obtiene `Prov(⌜ȧ < ḃ⌝)`.

    Es el `∃`‑intro codificado (testigo `K`) sobre `exBodyc`, seguido del MP interno con la
    implicación `⇐` de `ax13` codificada (`pcc_ltBwd_computed`). -/
theorem pcc_lt_intro (a b K : Term)
    (ha : ∀ c, liftTerm c a = a) (hb : ∀ c, liftTerm c b = b)
    (h : Prf (provFromCode (eqCodeFn (addcT (tcFn a) (succcT K)) (tcFn b))))
    (hwK : Prf (hasWit (liftTerm 0 K))) :
    Prf (provFromCode (ltCodeFn (tcFn a) (tcFn b))) := by
  have hAcl : ∀ c, liftTerm c (tcFn a) = tcFn a := fun c => by
    simp only [tcFn, liftTerm, liftTerms, ha c]
  have hBcl : ∀ c, liftTerm c (tcFn b) = tcFn b := fun c => by
    simp only [tcFn, liftTerm, liftTerms, hb c]
  have hbodycl : ∀ c, liftTerm c (exBodyc (tcFn a) (tcFn b)) = exBodyc (tcFn a) (tcFn b) :=
    liftTerm_exBodyc (tcFn a) (tcFn b) hAcl hBcl
  have hsub : Prf (provFromCode (substfc zero K (exBodyc (tcFn a) (tcFn b)))) :=
    prf_mp (prf_provCode_congr (prf_eq_symm
      (prf_substfc_exBodyc (tcFn a) (tcFn b) K (substtc_inv_tcFn a) (substtc_inv_tcFn b)))) h
  have hex : Prf (provFromCode (exc (exBodyc (tcFn a) (tcFn b)))) :=
    prf_mp (pcc_exIntro_code' (exBodyc (tcFn a) (tcFn b)) K hbodycl
      (prf_hasWitF_eq2 (addcT (tcFn a) (succcT (varc (numeral 0)))) (tcFn b)
        (prf_hasWit_addcT (prf_hasWit_tcFn a)
          (prf_hasWit_succcT (prf_hasWit_varc (numeral 0))))
        (prf_hasWit_tcFn b))
      hwK) hsub
  exact pcc_mp_code_apply (pcc_ltBwd_computed a b) hex

end ROBINSON_PlusPlus.Meta.EvalLtPrf

export ROBINSON_PlusPlus.Meta.EvalLtPrf (
  ltCodeFn ltCodeFn_termCode exBodyc phiLtBwd ltBwd
  prf_congr_implc prf_congr_exc
  prf_substtc_tcFn_zero_at prf_substtc_tcFn_succ_imp_at prf_substtc_tcFn_all_at prf_substtc_tcFn_at
  pcc_ltBwd_computed liftTerm_exBodyc prf_substfc_exBodyc pcc_lt_intro
)

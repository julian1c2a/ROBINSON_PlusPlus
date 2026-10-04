import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf

/-!
# `Meta/SubstfcCodePrf.lean` — el caso BINARIO y el caso BOTTOM de `substfc`

Promovido de `sondeos/SubstfcPlanos.lean` (rama **B3**, 2026‑09‑04). Cierra el paso 2 para
los constructores `implc`/`andc`/`orc` y para `botc`, con la ETIQUETA abstracta — que es lo
que permite hacerlos en UN lema en vez de tres.

## De 39 declaraciones del sondeo, aquí viven 17

El resto **no** entra, y por tres razones distintas — cada una medida:

* **18 ya estaban en producción**, y 13 de ellas llegaron en los dos DESCENSOS previos de
  esta misma rama: `binK` y su kit a `Meta/CodeCtorKit.lean`, y el KIT TERNARIO
  (`funcc3` + la imagen dotada `substfcT`) a `Meta/EvalArithPrf.lean`.
* **4 se retiran por MUERTAS**: `paso2_caso_bin`, `_impl`, `_and`, `_or`.
* 17 quedan aquí.

## ⚠️ Por qué se retiran esos cuatro — «la moneda de la inducción OBJETO»

`paso2_caso_bin` y sus tres instancias **no tienen ni un consumidor de código**. Medido: sus
únicas apariciones fuera del sondeo son **prosa en comentarios** (`EnsamblajeMedida:937,1198`,
`EvalSubstfcPrf:6687`, `HasWitFReal:6694`), y `_impl`/`_and`/`_or` no aparecen en ningún sitio.

La razón es la lección registrada del proyecto: el ensamblaje real (`EvalSubstfcPrf:7037`)
**no los llama**, sino que escribe `paso2_caso_bin_imp`, el mismo caso reprobado en `PrfH Γ`
como **IMPLICACIÓN** — porque dentro de la inducción la HI llega como **hipótesis**, no como
`Prf` cerrada. Y esa reprueba **no usa** `paso2_caso_bin`: es independiente.

Promoverlos sería meter cuatro constantes que nadie puede consumir. Mismo criterio con el que
se retiraron los seis `CRIT_*` en B2.

⚠️ **Sí entra `paso2_caso_bottom`**, que sí tiene consumidores: el caso `botc` no induce, así
que no sufre el problema de la moneda.

## ⛔ La línea que no se cruza

`substfcT` —que llegó a producción en el descenso 2— es una **DEFINICIÓN**, y `substfcT_termCode`
un puente `:= rfl`. Postular la ecuación de recursión de la imagen dotada como axioma **OBJETO**
(`ax_tc_substfc`) hace la teoría **INCONSISTENTE**; la derivación está guardada en el proyecto.
Este módulo consume la definición y **no postula nada**.

## Citas

A producción se cita **por nombre, nunca por número de línea** (ver la política en
`Meta/EvalLiftcPrf.lean`): dos auditorías mecánicas midieron que las citas de línea del frente
eran falsas a las pocas horas de escribirse.
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

namespace ROBINSON_PlusPlus.Meta.SubstfcCodePrf

/-! ## §3 · Congruencia INTERNA de `substfcT` en el 3er argumento (patrón §4 de `Paso2CasoForall`) -/

theorem pcc_congr_substfcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwB : Prf (hasWit B) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) := by
  let Ac : Term := eqc (substfcT A B X) (substfcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A B X) (substfcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A B X)
      (substfcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B X)
        (prf_congr_substfcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
        (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (substfcT A B X) (substfcT A B (varc (numeral 0)))
        (prf_hasWit_funcc3 (strCode "substfc") A B X hwA hwB hwX)
        (prf_hasWit_funcc3 (strCode "substfc") A B (varc (numeral 0)) hwA hwB
          (prf_hasWit_varc (numeral 0)))) hwX hwY)

/-! ## §4 · El código de la ecuación interna (idéntico a `Paso2CasoForall` §6) -/

def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

theorem substTerm_evalSubstfcCode (k : Nat) (u v s f : Term) :
    substTerm k u (evalSubstfcCode v s f)
      = evalSubstfcCode (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem liftTerm_evalSubstfcCode (k : Nat) (v s f : Term) :
    liftTerm k (evalSubstfcCode v s f)
      = evalSubstfcCode (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-! ## §5 · CASO `bottom` — constructor NULARIO, axioma `forall_2`. El más barato de todos. -/

def AXBOT_BODY : Formula := substfc (.var 1) (.var 0) botc =eq botc

theorem AXBOT_BODY_ok : ax_substfc_bottom = forall_2 AXBOT_BODY := rfl

/-- La instancia INTERNA del axioma `ax_substfc_bottom`, DOTADA (patrón `pcc_substfc_forall_dot`). -/
theorem pcc_substfc_bottom_dot (v s : Term) :
    Prf (provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (numeral 1) W1 (formCode AXBOT_BODY)
      =eq eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_substfc_arith_open 1 W1 AXBOT_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)
      =eq eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_congr_eqCodeFn (prf_congr_substfcT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0 (eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2))
        (nulT 2))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_nulT 2 W0)
    refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
    exact prf_congr_substfcT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
      (prf_substtc_nulT 2 W0)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (formCode AXBOT_BODY))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 AXBOT_BODY (show ax_substfc_bottom ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (prf_hasWit_tcFn (liftTerm 0 v)) (prf_hasWit_tcFn (liftTerm 0 s)))

/-- **CASO `bottom` DE `pcc_eval_substfc`, CERRADO.** Sin hipótesis: constructor nulario. -/
theorem paso2_caso_bottom (v s : Term) :
    Prf (provFromCode (evalSubstfcCode v s botc)) := by
  unfold evalSubstfcCode
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn botc))
      =eq substfcT (tcFn v) (tcFn s) (tcFn botc)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)
  have iB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (nulT 2))
      =eq substfcT (tcFn v) (tcFn s) (nulT 2)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_nulT 2)
  -- (1) `tcFn botc ↦ nulT 2` bajo el 3er argumento de `substfcT`, DENTRO de `Prov`
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn botc))
      (substfcT (tcFn v) (tcFn s) (nulT 2)))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn botc) (nulT 2)
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)) (pcc_dot_nul_symm 2)
  -- (2) la instancia interna del axioma
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) :=
    pcc_substfc_bottom_dot v s
  -- (3) `nulT 2 ↦ tcFn botc` (el KIT, dirección directa)
  have h3 : Prf (provFromCode (eqc (nulT 2) (tcFn botc))) := pcc_dot_nul 2
  -- (4) la ecuación OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h4 : Prf (provFromCode (eqc (tcFn botc) (tcFn (substfc v s botc)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_bottom v s)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn botc))
  exact pcc_eq_trans_code _ _ _ iA (by hw_auto) (by hw_auto) (by hw_auto) h1
    (pcc_eq_trans_code _ _ _ iB (by hw_auto) (by hw_auto) (by hw_auto) h2
      (pcc_eq_trans_code _ _ _ (substtc_inv_nulT 2) (by hw_auto) (by hw_auto) (by hw_auto)
        h3 h4))

/-! ## §6 · CASO BINARIO — `impl`, `and`, `or` en UN SOLO lema.

Los tres axiomas son **literalmente la misma fórmula** salvo el tag (`5`, `7`, `8`), que en
el código es un `numeralM k` CERRADO. Se factoriza tomando el tag como un `Term` abstracto `T`
con la hipótesis de clausura `hT`; el único punto donde `T` bloquea la reducción definicional
es la hoja `substCodeT 3 W3 T`, y ahí basta `substCodeT_closed`. -/

def binct (T a b : Term) : Term := cons T (cons a (cons b nil))

theorem binct_implc (a b : Term) : binct (numeralM 5) a b = implc a b := rfl
theorem binct_andc (a b : Term) : binct (numeralM 7) a b = andc a b := rfl
theorem binct_orc (a b : Term) : binct (numeralM 8) a b = orc a b := rfl

def AXBIN_BODY (T : Term) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

theorem AXBIN_impl : ax_substfc_impl = forall_4 (AXBIN_BODY (numeralM 5)) := rfl
theorem AXBIN_and : ax_substfc_and = forall_4 (AXBIN_BODY (numeralM 7)) := rfl
theorem AXBIN_or : ax_substfc_or = forall_4 (AXBIN_BODY (numeralM 8)) := rfl

/-- **La instancia INTERNA del axioma binario, DOTADA**, genérica en la etiqueta `T`.
    Un solo lema para `impl`, `and` y `or`. -/
theorem pcc_substfc_bin_dot (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (hmem : forall_4 (AXBIN_BODY T) ∈ axioms) (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
      (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  -- normalizaciones de los testigos levantados
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  -- (0) la instancia bruta, con la hoja del tag SIN evaluar
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXBIN_BODY T))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 (AXBIN_BODY T)
  rw [hkc] at hin0
  -- (1) nivel 3 : `W3 ↦ v̇`
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
        (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _)))
  -- (2) nivel 2 : `#2 ↦ ṡ`
  have k2v : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have k2s : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hs2
  have k21 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1))
      (prf_gnum_lt (show (1 : Nat) < 2 by omega))
  have k20 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 2 by omega))
  have hmid2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k20)
  -- (3) nivel 1 : `#1 ↦ ȧ`
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k10)
  -- (4) nivel 0 : `#0 ↦ ḃ`
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXBIN_BODY T)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 (AXBIN_BODY T) hmem (tcFn v) (tcFn s) (tcFn a) (tcFn b)
      (prf_hasWit_tcFn (liftTerm 0 v)) (prf_hasWit_tcFn (liftTerm 0 s))
      (prf_hasWit_tcFn (liftTerm 0 a)) (prf_hasWit_tcFn (liftTerm 0 b)))

end ROBINSON_PlusPlus.Meta.SubstfcCodePrf

/-! ## AI-GUIDE §17 · bloque `export`

    Criterio de B2b: **sale a la raíz lo que OTRO módulo consume, no lo que existe.** -/

export ROBINSON_PlusPlus.Meta.SubstfcCodePrf (
  evalSubstfcCode liftTerm_evalSubstfcCode substTerm_evalSubstfcCode
  pcc_congr_substfcT_arg3_code
  binct AXBIN_BODY pcc_substfc_bin_dot
  AXBOT_BODY pcc_substfc_bottom_dot paso2_caso_bottom
)

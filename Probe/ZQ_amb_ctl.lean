/-
# `Probe/B3B_substtc_modulo.lean` — B3.B: el MODULO propuesto para `sondeos/EvalSubsttc.lean`

**Destino propuesto**: `ROBINSON_PlusPlus/Meta/EvalSubsttcPrf.lean`
**Namespace**   : `ROBINSON_PlusPlus.Meta.EvalSubsttcPrf`
**Fuente**      : `sondeos/EvalSubsttc.lean` (md5 `7cfc61a8f12477b3dae118a136d5b904`,
                  1905 lineas, 156 declaraciones), que compila VERDE hoy (exit 0).

## De 156 declaraciones a 74

| bloque                                                              |  n |
|---------------------------------------------------------------------|---:|
| DUPLICADOS de produccion (65 identicos + 3 identicos salvo defeq)     | 68 |
| §13 + `PredHyp` (MUERTOS: `EvalPredPrf.pcc_eval_pred'` es mas fuerte) |  9 |
| trio primado `pcc_eval_*'` (redundante al caer `PredHyp`)             |  3 |
| MUERTOS nuevos sin consumidor de codigo (3 «planos» + 1 puente `rfl`) |  4 |
| **CONTENIDO DEL MODULO**                                              | **74** |
| ...de los cuales COLISIONES renombradas (14 de las 17 medidas)         | 14 |

⚠️ Los 3 «planos» retirados (`refl_caso_funcc` / `refl_lista_cons` / `refl_caso_varc`
   del sondeo) son EXACTAMENTE el patron `SubstfcPlanos`: el ensamblaje real usa la
   version `_imp` (moneda OBJETO) y la `varc` usa `refl_caso_varc_at` directamente.
   En `LiftcCodePrf` sus homonimos SI tienen consumidor (`refl_termCode`/`refl_termsCode`,
   la reflexion del ARBOL CONCRETO), que aqui no existe.

## Imports

Los 35 `import` de abajo son los modulos que DECLARAN algun simbolo usado; ninguno es
el barrel. Medido: la clausura transitiva los reduce a DOS (`EvalLiftcPrf` +
`EvalPredPrf`) — los 29 restantes son documentales, que es el estilo de la casa
(`EvalLiftcPrf` lista 20, `SubstfcCodePrf` 19). Validado en las dos formas: con
`import ROBINSON_PlusPlus.Meta` (exit 0) y con esta lista concreta (exit 0).

## Footprint

3 axiomas de Lean (`propext`, `Classical.choice`, `Quot.sound`) +
`Representability2Prf.prf_axiomsCodeT_eq`, SANCIONADO y ya en la linea base.
O sea el «net-0 = CUATRO axiomas» del frente. CERO axiomas nuevos, CERO `sorry`.
-/
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.EvalNthcPrf
import ROBINSON_PlusPlus.Meta.EvalPredPrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NatMulPrf
import ROBINSON_PlusPlus.Meta.NatOrderPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.EvalPredPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.EvalSubsttcPrf

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))

def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))

theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl

theorem substtscT_termCode (v s t : Term) :
    substtscT (termCode v) (termCode s) (termCode t) = termCode (substtsc v s t) := rfl

theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht

theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht

theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z

theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z

theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z) (prf_congr_substtcT (hX W) (hY W) (hZ W))

theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z) (prf_congr_substtscT (hX W) (hY W) (hZ W))

def SUBSTTSC_NIL_BODY : Formula := substtsc (.var 1) (.var 0) nil =eq nil

theorem SUBSTTSC_NIL_BODY_ok : ax_substtsc_nil = forall_2 SUBSTTSC_NIL_BODY := rfl

theorem pcc_substtsc_nil_code (v s : Term) :
    Prf (provFromCode (eqCodeFn
      (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (succ zero) W1 (formCode SUBSTTSC_NIL_BODY)
      =eq eqCodeFn (substtscT W1 (varc (numeral 0)) (termCode nil)) (termCode nil)) :=
    prf_substfc_arith_open 1 W1 SUBSTTSC_NIL_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substtscT W1 (varc (numeral 0)) (termCode nil)) (termCode nil)
      =eq eqCodeFn (substtscT (tcFn v) (varc (numeral 0)) (termCode nil)) (termCode nil)) :=
    prf_congr_eqCodeFn (prf_congr_substtscT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0
        (eqCodeFn (substtscT (tcFn v) (varc (numeral 0)) (termCode nil)) (termCode nil))
      =eq eqCodeFn (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_termCode_zero 0 W0)
    exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
      (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
        (prf_substtc_termCode_zero 0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode SUBSTTSC_NIL_BODY))
      =eq eqCodeFn (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 SUBSTTSC_NIL_BODY (show ax_substtsc_nil ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s))

def SUBSTTC_FUNC_BODY : Formula :=
  substtc (.var 3) (.var 2) (funcc (.var 1) (.var 0))
    =eq funcc (.var 1) (substtsc (.var 3) (.var 2) (.var 0))

theorem SUBSTTC_FUNC_BODY_ok : ax_substtc_func = forall_4 SUBSTTC_FUNC_BODY := rfl

theorem pcc_substtc_func_code (v s p b : Term) :
    Prf (provFromCode (eqCodeFn
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn p)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTC_FUNC_BODY)
      =eq eqCodeFn
        (substtcT W3 (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 SUBSTTC_FUNC_BODY
  have hA3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn v)))
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v))
  have hnorm : Prf (eqCodeFn
        (substtcT W3 (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substtcT (tcFn v) (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_substtcT hA3 (prf_refl _) (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _)))
  -- nivel 2 : `varc 2̄ ↦ ṡ`
  have hA2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have g2v2 : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hA2
  have g2v1 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1)) (prf_gnum_lt (by omega))
  have g2v0 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0)) (prf_gnum_lt (by omega))
  have g2tv : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have hL2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substtcT (tcFn v) (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substtcT g2tv g2v2 ?_
      exact prf_eq_trans (prf_substtc_funccT_at 2 W2 _ _) (prf_congr_funccT g2v1 g2v0)
    · refine prf_eq_trans (prf_substtc_funccT_at 2 W2 _ _) ?_
      refine prf_congr_funccT g2v1 ?_
      exact prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _)
        (prf_congr_substtscT g2tv g2v2 g2v0)
  -- nivel 1 : `varc 1̄ ↦ ṗ`
  have hA1 : Prf (W1 =eq tcFn p) := prf_liftc_tcFn p
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn p) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have g1ts : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have hL1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (varc (numeral 0))))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtcT g1tv g1ts ?_
      exact prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) (prf_congr_funccT g1v1 g1v0)
    · refine prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) ?_
      refine prf_congr_funccT g1v1 ?_
      exact prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _)
        (prf_congr_substtscT g1tv g1ts g1v0)
  -- nivel 0 : `varc 0̄ ↦ ḃ`
  have hL0 : Prf (substfc zero W0 (eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (varc (numeral 0))))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
      refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _)
        (prf_congr_funccT (prf_substtc_tcFn W0 p) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _) ?_
      refine prf_congr_funccT (prf_substtc_tcFn W0 p) ?_
      exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
        (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
          (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2
          (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTC_FUNC_BODY))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm))))
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 hL2))
        (prf_eq_trans (prf_congr_substfc_arg3 hL1) hL0))
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 SUBSTTC_FUNC_BODY (show ax_substtc_func ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn p) (tcFn b))

def SUBSTTSC_CONS_BODY : Formula :=
  substtsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
    =eq cons (substtc (.var 3) (.var 2) (.var 1)) (substtsc (.var 3) (.var 2) (.var 0))

theorem SUBSTTSC_CONS_BODY_ok : ax_substtsc_cons = forall_4 SUBSTTSC_CONS_BODY := rfl

theorem pcc_substtsc_cons_code (v s h t : Term) :
    Prf (provFromCode (eqCodeFn
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn h)
  let W0 : Term := tcFn t
  have hin : Prf (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTSC_CONS_BODY)
      =eq eqCodeFn
        (substtscT W3 (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 SUBSTTSC_CONS_BODY
  have hA3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn v)))
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v))
  have hnorm : Prf (eqCodeFn
        (substtscT W3 (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substtscT (tcFn v) (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _))
      (prf_congr_consT (prf_congr_substtcT hA3 (prf_refl _) (prf_refl _))
        (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _)))
  have hA2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have g2v2 : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hA2
  have g2v1 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1)) (prf_gnum_lt (by omega))
  have g2v0 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0)) (prf_gnum_lt (by omega))
  have g2tv : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have hL2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substtscT (tcFn v) (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substtscT g2tv g2v2 ?_
      exact prf_eq_trans (prf_substtc_consT (numeral 2) W2 _ _) (prf_congr_consT g2v1 g2v0)
    · refine prf_eq_trans (prf_substtc_consT (numeral 2) W2 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT (numeral 2) W2 _ _ _)
          (prf_congr_substtcT g2tv g2v2 g2v1)
      · exact prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _)
          (prf_congr_substtscT g2tv g2v2 g2v0)
  have hA1 : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn h) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have g1ts : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have hL1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtscT g1tv g1ts ?_
      exact prf_eq_trans (prf_substtc_consT (numeral 1) W1 _ _) (prf_congr_consT g1v1 g1v0)
    · refine prf_eq_trans (prf_substtc_consT (numeral 1) W1 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _)
          (prf_congr_substtcT g1tv g1ts g1v1)
      · exact prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _)
          (prf_congr_substtscT g1tv g1ts g1v0)
  have hL0 : Prf (substfc zero W0 (eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (tcFn t)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _) ?_
      refine prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_consT zero W0 _ _)
        (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_consT zero W0 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _)
          (prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
            (prf_substtc_tcFn W0 h))
      · exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
          (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
            (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2
          (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTSC_CONS_BODY))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (tcFn t)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm))))
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 hL2))
        (prf_eq_trans (prf_congr_substfc_arg3 hL1) hL0))
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 SUBSTTSC_CONS_BODY (show ax_substtsc_cons ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn h) (tcFn t))

def SUBSTTC_VAR_EQ_BODY : Formula :=
  Formula.impl ((.var 2) =eq (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq (.var 1))

def SUBSTTC_VAR_GT_BODY : Formula :=
  Formula.impl (lt (.var 2) (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (pred (.var 0)))

def SUBSTTC_VAR_LT_BODY : Formula :=
  Formula.impl (lt (.var 0) (.var 2))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (.var 0))

theorem SUBSTTC_VAR_EQ_BODY_ok : ax_substtc_var_eq = forall_3 SUBSTTC_VAR_EQ_BODY := rfl

theorem SUBSTTC_VAR_GT_BODY_ok : ax_substtc_var_gt = forall_3 SUBSTTC_VAR_GT_BODY := rfl

theorem SUBSTTC_VAR_LT_BODY_ok : ax_substtc_var_lt = forall_3 SUBSTTC_VAR_LT_BODY := rfl

theorem pcc_substtc_var_eq_code (v s n : Term) :
    Prf (provFromCode (implc (eqCodeFn (tcFn v) (tcFn n))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s)))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_EQ_BODY)
      =eq implc (eqCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_EQ_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (eqCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))
      =eq implc (eqCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))) :=
    prf_congr_implc (prf_congr_eqCodeFn hA2 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (eqCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varc (numeral 1))))
      =eq implc (eqCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0)))) (tcFn s))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _)
        (prf_congr_eqCodeFn g1tv g1v0)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ g1v1
      refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtcT g1tv g1v1 ?_
      exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (eqCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0)))) (tcFn s)))
      =eq implc (eqCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_eq zero W0 _ _)
        (prf_congr_eqCodeFn (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn W0 s)
      refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
      refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_EQ_BODY)))
      =eq implc (eqCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_EQ_BODY (show ax_substtc_var_eq ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

theorem pcc_substtc_var_gt_code (v s n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn v) (tcFn n))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (varcT (predcT (tcFn n)))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_GT_BODY)
      =eq implc (ltCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_GT_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (ltCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn hA2 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (ltCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varcT (predcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' (numeral 1) W1 _ _)
        (prf_congr_atom2CodeFn g1tv g1v0)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
        refine prf_congr_substtcT g1tv g1v1 ?_
        exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
      · refine prf_eq_trans (prf_substtc_varcT_at 1 W1 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_predcT (numeral 1) W1 _) (prf_congr_predcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (ltCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
            (varcT (predcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
              (varcT (predcT (tcFn n))))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _)
        (prf_congr_atom2CodeFn (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
        refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
        exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
      · refine prf_eq_trans (prf_substtc_varcT_at 0 W0 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_predcT zero W0 _)
          (prf_congr_predcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_GT_BODY)))
      =eq implc (ltCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
              (varcT (predcT (tcFn n))))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_GT_BODY (show ax_substtc_var_gt ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

theorem pcc_substtc_var_lt_code (v s n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn n) (tcFn v))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_LT_BODY)
      =eq implc (ltCodeFn (varc (numeral 0)) W2)
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_LT_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (ltCodeFn (varc (numeral 0)) W2)
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn (prf_refl _) hA2)
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (ltCodeFn (varc (numeral 0)) (tcFn v))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' (numeral 1) W1 _ _)
        (prf_congr_atom2CodeFn g1v0 g1tv)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
        refine prf_congr_substtcT g1tv g1v1 ?_
        exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
      · exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (ltCodeFn (varc (numeral 0)) (tcFn v))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
            (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn n) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _)
        (prf_congr_atom2CodeFn (prf_substtc_varc0 W0) (prf_substtc_tcFn W0 v))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
        refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
        exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
      · exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _)
          (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_LT_BODY)))
      =eq implc (ltCodeFn (tcFn n) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_LT_BODY (show ax_substtc_var_lt ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

/-- El objetivo, con `v`, `s`, `X` **ABSTRACTOS**. -/
def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))

/-- Su companera sobre LISTAS de codigos de termino. -/
def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))

/-- CONTROL NEGATIVO: no es una reflexividad disfrazada. -/
example (v s X : Term) : True := by
  fail_if_success
    exact (rfl : substtcT (tcFn v) (tcFn s) (tcFn X) = tcFn (substtc v s X))
  trivial

theorem pcc_congr_substtcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtcT A B X) (substtcT A B Y))) := by
  let Ac : Term := eqc (substtcT A B X) (substtcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substtcT A B X) (substtcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substtcT A B X)
      (substtcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substtcT zero w A B X)
        (prf_congr_substtcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substtcT zero w A B (varc (numeral 0)))
        (prf_congr_substtcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substtcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substtscT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtscT A B X) (substtscT A B Y))) := by
  let Ac : Term := eqc (substtscT A B X) (substtscT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term,
      Prf (substfc zero w Ac =eq eqc (substtscT A B X) (substtscT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substtscT A B X)
      (substtscT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substtscT zero w A B X)
        (prf_congr_substtscT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substtscT zero w A B (varc (numeral 0)))
        (prf_congr_substtscT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substtscT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem invA (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (tcFn X))
      =eq substtcT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)

theorem invAs (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (tcFn X))
      =eq substtscT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil_substtc (v s : Term) : Prf (targetSubsttsc v s nil) := by
  unfold targetSubsttsc
  refine prf_mp (prf_provCode_congr (prf_congr_eqCodeFn ?_ ?_)) (pcc_substtsc_nil_code v s)
  · exact prf_congr_substtscT (prf_refl _) (prf_refl _) (prf_eq_symm prf_tc_zero)
  · exact prf_eq_trans (prf_eq_symm prf_tc_zero)
      (prf_congr_tcFn (prf_eq_symm (prf_substtsc_nil v s)))

/-- Rama `v < n` (clausula `ax_substtc_var_gt`). **La UNICA que necesita `pred` dotado.** -/
theorem br_lt (v s n : Term) :
    Prf (Formula.impl (lt v n)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [lt v n] (lt v n) := prfH_hyp_self _
  have hdotg : PrfH [lt v n] (provFromCode (ltCodeFn (tcFn v) (tcFn n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked v n) _) hg
  have e1 : PrfH [lt v n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (predcT (tcFn n))))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_gt_code v s n) _) hdotg
  have hpd : PrfH [lt v n] (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) :=
    prf_to_prfH (pcc_eval_pred' n) _
  have e2 : PrfH [lt v n] (provFromCode (eqc
      (varcT (predcT (tcFn n))) (varcT (tcFn (pred n))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code 0 (predcT (tcFn n)) (tcFn (pred n))
      (substtc_inv_predcT (substtc_inv_tcFn n))) _) hpd
  have e3 : PrfH [lt v n] (provFromCode (eqc (varcT (tcFn (pred n))) (tcFn (varc (pred n))))) :=
    prf_to_prfH (pcc_dot_un 0 (pred n)) _
  have hchain : PrfH [lt v n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn (varc (pred n))))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
        (substtc_inv_unT (substtc_inv_tcFn n))) e1
      (PrfH_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_predcT (substtc_inv_tcFn n))) e2 e3)
  have hobj : PrfH [lt v n] (substtc v s (varc n) =eq varc (pred n)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_gt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- Rama `v ≐ n` (clausula `ax_substtc_var_eq`). CERRADA, sin hipotesis. -/
theorem br_eq (v s n : Term) :
    Prf (Formula.impl (v =eq n)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [v =eq n] (v =eq n) := prfH_hyp_self _
  have hdotg : PrfH [v =eq n] (provFromCode (eqCodeFn (tcFn v) (tcFn n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked v n) _) hg
  have e1 : PrfH [v =eq n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_eq_code v s n) _) hdotg
  have hobj : PrfH [v =eq n] (substtc v s (varc n) =eq s) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_eq v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    e1

/-- Rama `n < v` (clausula `ax_substtc_var_lt`). CERRADA, sin hipotesis. -/
theorem br_gt (v s n : Term) :
    Prf (Formula.impl (lt n v)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [lt n v] (lt n v) := prfH_hyp_self _
  have hdotg : PrfH [lt n v] (provFromCode (ltCodeFn (tcFn n) (tcFn v))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked n v) _) hg
  have e1 : PrfH [lt n v] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_lt_code v s n) _) hdotg
  have e2 : PrfH [lt n v] (provFromCode (eqc (varcT (tcFn n)) (tcFn (varc n)))) :=
    prf_to_prfH (pcc_dot_un 0 n) _
  have hchain : PrfH [lt n v] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn (varc n)))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
        (substtc_inv_unT (substtc_inv_tcFn n))) e1 e2
  have hobj : PrfH [lt n v] (substtc v s (varc n) =eq varc n) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_lt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- **(1) BASE `varc`, con la TRICOTOMIA ya eliminada.** Unica hipotesis: `pred` dotado. -/
theorem refl_caso_varc_at (v s n : Term) :
    Prf (targetSubsttc v s (varc n)) := by
  unfold targetSubsttc
  have s0 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (varc n)))
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))))) :=
    prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (varc n)) (varcT (tcFn n))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (varc n)))
      (pcc_dot_un_symm 0 n)
  have hmain : Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
      (tcFn (substtc v s (varc n))))) :=
    prf_or_elim (prf_lt_trichotomy v n) (br_lt v s n)
      (prf_or_elim_imp (br_eq v s n) (br_gt v s n))
  exact pcc_eq_trans_code _ _ _ (invA v s (varc n)) s0 hmain

theorem liftF_targetSubsttc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubsttc v s X)
      = targetSubsttc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubsttc, liftFormula_provFromCode_open, eqc, substtcT, funcc, tcFn, substtc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem liftF_targetSubsttsc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubsttsc v s X)
      = targetSubsttsc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubsttsc, liftFormula_provFromCode_open, eqc, substtscT, funcc, tcFn, substtsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substF_targetSubsttc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubsttc v s X)
      = targetSubsttc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubsttc, substFormula_provFromCode_open, eqc, substtcT, funcc, tcFn, substtc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

theorem substF_targetSubsttsc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubsttsc v s X)
      = targetSubsttsc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubsttsc, substFormula_provFromCode_open, eqc, substtscT, funcc, tcFn, substtsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

theorem substF_hole_tc (v s u : Term) :
    substFormula 0 u (targetSubsttc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttc v s u := by
  rw [substF_targetSubsttc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_tsc (v s u : Term) :
    substFormula 0 u (targetSubsttsc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttsc v s u := by
  rw [substF_targetSubsttsc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_targetSubsttc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubsttc v s X)) : PrfH Γ (targetSubsttc v s X') :=
  (substF_hole_tc v s X') ▸
    PrfH_leibniz_subst (A := targetSubsttc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_tc v s X) ▸ ha)

theorem PrfH_congr_targetSubsttsc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubsttsc v s X)) : PrfH Γ (targetSubsttsc v s X') :=
  (substF_hole_tsc v s X') ▸
    PrfH_leibniz_subst (A := targetSubsttsc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_tsc v s X) ▸ ha)

theorem refl_shapeUn_imp_substtc (v s X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc (nthc X (numeralM 1)))) := prfH_hyp_self _
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc_at v s (nthc X (numeralM 1))) _)

theorem refl_caso_funcc_imp_substtc (v s p b : Term) :
    Prf (Formula.impl (targetSubsttsc v s b) (targetSubsttc v s (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetSubsttsc v s b] (targetSubsttsc v s b) := prfH_hyp_self _
  have hY : ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      =eq substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (invAs v s b)
  have s1 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (funcc p b))) (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) :=
    prf_to_prfH (pcc_substtc_func_code v s p b) _
  have s3 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      (funccT (tcFn p) (tcFn (substtsc v s b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (substtscT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtsc v s b))
      (substtc_inv_tcFn p) (invAs v s b)) _) hb
  have s4 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (substtsc v s b))) (tcFn (funcc p (substtsc v s b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (substtsc v s b)) _
  have hchain : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (tcFn (funcc p (substtsc v s b))))) :=
    PrfH_eq_trans_code _ _ _ (invA v s (funcc p b)) s1
      (PrfH_eq_trans_code _ _ _ hY s2 (PrfH_eq_trans_code _ _ _ hZ s3 s4))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtc_func v s p b))))) _) hchain

theorem refl_shapeBin_imp_substtc (v s X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetSubsttsc v s (nthc X (numeralM 2))))
      (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetSubsttsc v s b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hbb : PrfH [H] (targetSubsttsc v s b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetSubsttc v s (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp_substtc v s p b) _) hbb
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hs) hfb

theorem refl_lista_cons_imp_substtc (v s h t : Term) :
    Prf (Formula.impl (land (targetSubsttc v s h) (targetSubsttsc v s t))
      (targetSubsttsc v s (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetSubsttc v s h) (targetSubsttsc v s t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetSubsttc v s h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetSubsttsc v s t) := PrfH_and_elim_right hh0
  have hY : ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      =eq substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (invA v s h) (invAs v s t)
  have hU : ∀ W, Prf (substtc zero W (consT (tcFn (substtc v s h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (substtc v s h)) (invAs v s t)
  have s1 : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substtscT_arg3_code (tcFn v) (tcFn s) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons h t))) (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    prf_to_prfH (pcc_substtsc_cons_code v s h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (substtcT (tcFn v) (tcFn s) (tcFn h))
      (tcFn (substtc v s h)) (invAs v s t) (invA v s h)) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (substtc v s h))
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))
      (substtc_inv_tcFn (substtc v s h)) (invAs v s t)) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    prf_to_prfH (pcc_dot_cons (substtc v s h) (substtsc v s t)) _
  have hchain : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    PrfH_eq_trans_code _ _ _ (invAs v s (cons h t)) s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 (PrfH_eq_trans_code _ _ _ hU s4 s5)))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtsc_cons v s h t))))) _) hchain

def CONJ (w v s X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (targetSubsttc v s X))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (targetSubsttsc v s X))

theorem liftF_CONJ (k : Nat) (w v s X : Term) :
    liftFormula k (CONJ w v s X)
      = CONJ (liftTerm k w) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [CONJ, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetSubsttc, liftF_targetSubsttsc]

theorem substF_CONJ (k : Nat) (u w v s X : Term) :
    substFormula k u (CONJ w v s X)
      = CONJ (substTerm k u w) (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [CONJ, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetSubsttc, substF_targetSubsttsc]

/-- `#3` es el CODIGO sobre el que se induce; `#2` el testigo, `#1` = `v`, `#0` = `s`. -/
def PHIbodySubsttc : Formula := CONJ (.var 2) (.var 1) (.var 0) (.var 3)

def PHIsubsttc : Formula := Formula.forall (Formula.forall (Formula.forall PHIbodySubsttc))

theorem hPHIsubsttc1 : liftFormula 1 PHIsubsttc = PHIsubsttc := by
  simp only [PHIsubsttc, PHIbodySubsttc, liftFormula, liftF_CONJ, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHIsubsttc_at (t : Term) :
    substFormula 0 t PHIsubsttc
      = Formula.forall (Formula.forall (Formula.forall
          (CONJ (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHIsubsttc, PHIbodySubsttc, substFormula, substF_CONJ, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHIsubsttc_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
        (CONJ (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHIsubsttc_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
        (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHIsubsttc_spec3 (t w v s : Term) :
    substFormula 0 s (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = CONJ w v s t := by
  simp only [substF_CONJ, substTerm, FOL.substTerm_liftTerm, if_true]

/-- Instanciacion de las DOS mitades a `w`, `v`, `s` concretos. -/
theorem PHIsubsttc_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHIsubsttc)) :
    PrfH Γ (CONJ w v s t) := by
  rw [PHIsubsttc_at] at h
  have h1 := PrfH_spec h w
  rw [PHIsubsttc_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHIsubsttc_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHIsubsttc_spec3] at h3

theorem psi_substtc_l1 : liftFormula 0 (PSI PHIsubsttc)
    = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHIsubsttc) := by
  simp only [PSI, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHIsubsttc1]

theorem psi_substtc_l2 : liftFormula 0 (liftFormula 0 (PSI PHIsubsttc))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) PHIsubsttc) := by
  rw [psi_substtc_l1]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHIsubsttc1]

theorem psi_substtc_l3 : liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIsubsttc)))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) PHIsubsttc) := by
  rw [psi_substtc_l2]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHIsubsttc1]

def PSIsubsttc3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIsubsttc)))

theorem PSIsubsttc_inst {Γ : List Formula} (hpsi : PrfH Γ PSIsubsttc3) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z PHIsubsttc)) := by
  unfold PSIsubsttc3 at hpsi
  rw [psi_substtc_l3] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) PHIsubsttc)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z PHIsubsttc) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

theorem PHIsubsttc_step : Prf (Formula.forall (Formula.impl (PSI PHIsubsttc) PHIsubsttc)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIsubsttc] (Formula.forall (Formula.forall PHIbodySubsttc)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIbodySubsttc) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIbodySubsttc ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSIsubsttc3] PHIbodySubsttc
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (isTC1 (.var 2) (.var 3)) [PSIsubsttc3] rfl
    have hh : PrfH [isTC1 (.var 2) (.var 3), PSIsubsttc3] (isTC1 (.var 2) (.var 3)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwf : PrfH [isTC1 (.var 2) (.var 3), PSIsubsttc3] (wfAll1 (.var 2)) :=
      PrfH_and_elim_left hh
    have hin : PrfH [isTC1 (.var 2) (.var 3), PSIsubsttc3] (In (.var 3) (.var 2)) :=
      PrfH_and_elim_right hh
    have hitc : PrfH [isTC1 (.var 2) (.var 3), PSIsubsttc3]
        (isTermCodeE1 (.var 2) (.var 3)) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH (prf_isTermCodeE1_of_In (.var 2) (.var 3)) _) hin) hwf
    refine PrfH_or_elim hitc ?varc ?func
    case varc =>
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp_substtc (.var 1) (.var 0) (.var 3)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    case func =>
      have hb : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSIsubsttc3]
          (land (shapeBin (.var 3) 1) (argsIn (.var 2) (nthc (.var 3) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hwf' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSIsubsttc3] (wfAll1 (.var 2)) :=
        PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      have hpsi' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSIsubsttc3] PSIsubsttc3 :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hshape := PrfH_and_elim_left hb
      have hargs := PrfH_and_elim_right hb
      have h1 : Prf (lt (nthc (.var 3) (numeralM 2)) (cons (nthc (.var 3) (numeralM 2)) nil)) :=
        prf_cantor_mono_left _ _
      have h2 : Prf (lt (cons (nthc (.var 3) (numeralM 2)) nil)
          (cons (nthc (.var 3) (numeralM 1)) (cons (nthc (.var 3) (numeralM 2)) nil))) :=
        prf_cantor_mono_right _ _
      have h3 : Prf (lt (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil))
          (cons (numeralM 1) (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil)))) :=
        prf_cantor_mono_right _ _
      have h12 : Prf (lt (nthc (.var 3) (numeralM 2))
          (cons (nthc (.var 3) (numeralM 1)) (cons (nthc (.var 3) (numeralM 2)) nil))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
      have h123 : Prf (lt (nthc (.var 3) (numeralM 2))
          (cons (numeralM 1) (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil)))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
      have hltb := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
      have hphi := PrfH.mp _ _ _ (PSIsubsttc_inst hpsi' (nthc (.var 3) (numeralM 2))) hltb
      have huse := PHIsubsttc_use (nthc (.var 3) (numeralM 2)) (.var 2) (.var 1) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp_substtc (.var 1) (.var 0) (.var 3)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) [PSIsubsttc3] rfl
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 3) nil,
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSIsubsttc3]
          (Formula.eq (.var 3) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm heq)
        (prf_to_prfH (refl_lista_nil_substtc (.var 1) (.var 0)) _)
    case consc =>
      have hcons : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSIsubsttc3]
          (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh' : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSIsubsttc3]
          (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSIsubsttc3] PSIsubsttc3 :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hwf := PrfH_and_elim_left hh'
      have hargs := PrfH_and_elim_right hh'
      -- (a) la CABEZA esta en el testigo y es MENOR
      have hlenX := PrfH_eq_trans (PrfH_congr_lenc hcons)
        (prf_to_prfH (prf_lenc_cons (carc (.var 3)) (cdrc (.var 3))) _)
      have hzlt := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hlenX) (prf_to_prfH (prf_zero_lt_succ (lenc (cdrc (.var 3)))) _)
      have hin0 := PrfH.mp _ _ _ (PrfH_inst_argsIn (.var 2) (.var 3) zero hargs) hzlt
      have hnth0 := PrfH_eq_trans (PrfH_congr_nthc_lst zero hcons)
        (prf_to_prfH (prf_nthc_zero (carc (.var 3)) (cdrc (.var 3))) _)
      have hinhd := PrfH_congr_In_left hnth0 hin0
      have hlthd := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_left (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_hd := PHIsubsttc_use (carc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSIsubsttc_inst hpsi (carc (.var 3))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      -- (b) la COLA hereda `argsIn` y es MENOR
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 2) (carc (.var 3)) (cdrc (.var 3))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_tl := PHIsubsttc_use (cdrc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSIsubsttc_inst hpsi (cdrc (.var 3))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp_substtc (.var 1) (.var 0)
          (carc (.var 3)) (cdrc (.var 3))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hcons) hres

theorem PHIsubsttc_all (t : Term) : Prf (substFormula 0 t PHIsubsttc) :=
  prf_strong_induction PHIsubsttc hPHIsubsttc1 PHIsubsttc_step t

theorem DESCENSO_imp_substtc (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PHIsubsttc_use t w v s (prf_to_prfH (PHIsubsttc_all t) []))) rfl

theorem DESCENSO_lista_imp_substtc (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_right (PHIsubsttc_use t w v s (prf_to_prfH (PHIsubsttc_all t) []))) rfl

/-- **`pcc_eval_substtc`** — el objetivo del encargo, con `v`, `s`, `t` **ABSTRACTOS**
    y el testigo `w` como GUARDA (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  prf_mp (DESCENSO_imp_substtc w v s t) h

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem pcc_eval_substtsc (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  prf_mp (DESCENSO_lista_imp_substtc w v s t) (prf_and_intro hwf hargs)

theorem pcc_eval_substtc_hasWit (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetSubsttc]
  exact PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_imp_substtc (.var 0) (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t)) _)
    (prfH_hyp_self _)
def PHI_CTL_dummy : Formula := PHIsubsttc
abbrev PHI : Formula := PHIsubsttc
abbrev refl_lista_nil : Prop := True
end ROBINSON_PlusPlus.Meta.EvalSubsttcPrf

section ZQ_CTL
open ROBINSON_PlusPlus.Meta.EvalSubsttcPrf
open ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf
#check @PHI
#check @refl_lista_nil
end ZQ_CTL

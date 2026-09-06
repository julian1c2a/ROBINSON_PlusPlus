import ROBINSON_PlusPlus.Meta.EvalPredPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
import ROBINSON_PlusPlus.Meta.D3InDotPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.PropCodePrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
/-!
# `Meta/EvalSubsttcPrf.lean` — la EVALUACIÓN PROVABLE de `substtc` / `substtsc`

**El resultado**, con `v`, `s`, `t` **ABSTRACTOS** y el testigo `w` como guarda:

    pcc_eval_substtc      (w v s t) (h : Prf (isTC1 w t)) :
        Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t))))
    pcc_eval_substtsc     (w v s t) (hwf …) (hargs …) :  la gemela sobre LISTAS
    pcc_eval_substtc_hasWit (v s t) : Prf (hasWit t ⇒ targetSubsttc v s t)

Sigue el patrón cerrado de `Meta/EvalLiftcPrf.lean` (`pcc_eval_liftc`): UNA inducción fuerte
con conclusión CONJUNTIVA sobre los dos sorts (término / lista de términos), con el testigo,
`v` y `s` cuantificados DENTRO del predicado (lo exige `liftFormula 1 Φ = Φ`).

## PROMOCIÓN B3.2 (2026-09-07) — qué se quedó fuera, y por qué

Este módulo viene de `sondeos/EvalSubsttc.lean` (154 declaraciones). Medido contra producción:

* **83 declaraciones BORRADAS**, no movidas. 66 eran duplicados exactos que producción ya
  tenía; el resto son instancias de genéricos que ya subieron (`psi_lift_form3`/`PSI_inst3`
  de `StrongInductionPrf`), tres muertas sin ningún consumidor, y **el §13 entero**.
* ⭐ **El §13 sobraba por completo** (8 declaraciones para descargar una hipótesis `PredHyp`):
  producción prueba `pcc_eval_pred'` **SIN guarda** (`Meta/EvalPredPrf.lean:200`), que es
  estrictamente más fuerte que la forma guardada que este frente necesita. La hipótesis ya no
  existe como tal: se descarga en `prf_pred_dot_guarded`, tres líneas.
* ⚠️ **13 nombres RENOMBRADOS antes de mover.** `PHI`, `PHIbody`, `PHI_at`, `PHI_use`,
  `PHI_step`, `PHI_all`, `DESCENSO_imp`, `DESCENSO_lista_imp` y los cinco `refl_*_imp`
  chocaban con los HOMÓNIMOS de `EvalLiftcPrf`/`LiftcCodePrf` — **mismo nombre, enunciado
  distinto** (allí sobre `targetLift`, aquí sobre `targetSubsttc`). Dos de ellos, `PHI` y
  `PHIbody`, tienen además la **misma firma** (`def … : Formula`) y sólo se distinguen por el
  cuerpo: ningún comparador de enunciados los separa, y borrarlos como «duplicados» habría
  cambiado el predicado de la inducción en silencio. El riesgo real no era este módulo —
  dentro gana el local— sino un consumidor aguas abajo con los dos `export` visibles: dos
  candidatos y Lean elige por elaboración, **sin avisar**.

⚠️ Las ecuaciones de recursión de `substtcT`/`substtscT` **no se postulan**: son DEFINICIONES,
y los puentes con `termCode` son `rfl`. Postularlas como axioma OBJETO haría la teoría
INCONSISTENTE (ADR-016).
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.PropCodePrf
open ROBINSON_PlusPlus.Meta.NatMulPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.EvalPredPrf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.EvalSubsttcPrf

/-! ############################################################################
    ## §1 · CONSTRUCTORES DE CODIGO (DEFINICIONES; ninguna ecuacion suya se postula)
    ############################################################################ -/

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s t : Term) :
    substtscT (termCode v) (termCode s) (termCode t) = termCode (substtsc v s t) := rfl
theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-! ## §2 · Fontaneria basica: congruencias e invariancias -/

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
/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados (copia de Paso2 §2) -/

/-! ## §3 · `pcc_axiom_inst4` — ⛔ **BORRADA: hoy vive en PRODUCCIÓN**

    Cuando se escribió este sondeo, `pcc_thm_inst4`/`pcc_axiom_inst4` no existían y había que
    reproducirlas aquí. Hoy están en `Meta/MpCodePrf.lean` (:302, :378) y **enmendadas por
    ADR-020**, con sus cuatro guardas `hasWit`. ⛔ ADR-019: no se deja duplicado, se consume el
    de producción — que además es el único que compila bajo la enmienda. -/

/-! ############################################################################
    ## §4 · LAS SEIS ECUACIONES DE `substtc`/`substtsc`, DOTADAS
    ############################################################################ -/

/-! ### (a) `ax_substtsc_nil` (`forall_2`) -/

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
      (tcFn v) (tcFn s) (by hw_auto) (by hw_auto))

/-! ### (b) `ax_substtc_func` (`forall_4`) -/

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
      (tcFn v) (tcFn s) (tcFn p) (tcFn b) (by hw_auto) (by hw_auto) (by hw_auto) (by hw_auto))

/-! ### (c) `ax_substtsc_cons` (`forall_4`) -/

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
      (tcFn v) (tcFn s) (tcFn h) (tcFn t) (by hw_auto) (by hw_auto) (by hw_auto) (by hw_auto))

/-! ### (d) las TRES clausulas guardadas de `varc` (`forall_3`) -/

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
      (tcFn v) (tcFn s) (tcFn n) (by hw_auto) (by hw_auto) (by hw_auto))

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
      (tcFn v) (tcFn s) (tcFn n) (by hw_auto) (by hw_auto) (by hw_auto))

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
      (tcFn v) (tcFn s) (tcFn n) (by hw_auto) (by hw_auto) (by hw_auto))

/-! ############################################################################
    ## §5 · EL OBJETIVO y las CONGRUENCIAS INTERNAS
    ############################################################################ -/

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
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwB : Prf (hasWit B) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
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
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (by hw_auto) hwX hwY)

theorem pcc_congr_substtscT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwB : Prf (hasWit B) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
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
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (by hw_auto) hwX hwY)

/-! ############################################################################
    ## §6 · LAS CLAUSULAS ESTRUCTURALES (`funcc`, `nil`, `cons`) — CERRADAS
    ############################################################################ -/

theorem invA (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (tcFn X))
      =eq substtcT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)
theorem invAs (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (tcFn X))
      =eq substtscT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_substtc_lista_nil (v s : Term) : Prf (targetSubsttsc v s nil) := by
  unfold targetSubsttsc
  refine prf_mp (prf_provCode_congr (prf_congr_eqCodeFn ?_ ?_)) (pcc_substtsc_nil_code v s)
  · exact prf_congr_substtscT (prf_refl _) (prf_refl _) (prf_eq_symm prf_tc_zero)
  · exact prf_eq_trans (prf_eq_symm prf_tc_zero)
      (prf_congr_tcFn (prf_eq_symm (prf_substtsc_nil v s)))

/-! ############################################################################
    ## §7 · LA CLAUSULA `varc`: LA TRICOTOMIA, REFLEJADA DENTRO DE `Prov`
    ############################################################################

    Las tres clausulas de `substtc _ _ (varc n)` estan guardadas por `v ≐ n` / `v < n` / `n < v`
    con `v` **ABSTRACTO**. La tricotomia se elimina a nivel **OBJETO** (`prf_lt_trichotomy` +
    `Prf₀.j3`), y cada guarda se **refleja** dentro de `Prov`:
    * `<` por `pcc_lt_tracked` (produccion, argumentos ABIERTOS);
    * `=` por reflexividad codificada + Leibniz (`pcc_eq_tracked`, aqui abajo).

    ⚠️ ***NO hace falta un or-elim INTERNO*** (`pcc_or_elim_code`): la disyuncion se elimina
    FUERA de `Prov`, porque la conclusion `targetSubsttc` es la MISMA en las tres ramas. -/

/- ⛔ **RETIRADA 2026‑08‑31 — `pcc_eq_tracked` YA EXISTE EN PRODUCCIÓN.**

   Aquí había una copia local del reflector del átomo `=`. El agente que la escribió la
   declaró como pieza nueva; el verificador adversarial lo refutó y yo lo confirmé:
   está en `ROBINSON_PlusPlus/Meta/Sigma1AtomPrf.lean:246`, con enunciado **idéntico**
   (`Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))`) y ya consumida en
   `Meta/InAxiomsCodePrf.lean:220`.

   La copia local la **SOMBREABA** — la trampa registrada de «misma definición en dos
   namespaces». Este fichero abre `Sigma1AtomPrf` en la línea 17, así que el uso de
   más abajo resuelve solo a la de producción. -/

/-- Rama `v < n` (clausula `ax_substtc_var_gt`). **La UNICA que necesita `pred` dotado.** -/
theorem br_lt (v s n : Term)
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
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
    PrfH.mp _ _ _ (prf_to_prfH hPred _) hg
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
        (substtc_inv_unT (substtc_inv_predcT (substtc_inv_tcFn n))) e2 e3 (by hw_auto) (by hw_auto) (by hw_auto)) (by hw_auto) (by hw_auto) (by hw_auto)
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
        (substtc_inv_unT (substtc_inv_tcFn n))) e1 e2 (by hw_auto) (by hw_auto) (by hw_auto)
  have hobj : PrfH [lt n v] (substtc v s (varc n) =eq varc n) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_lt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- **(1) BASE `varc`, con la TRICOTOMIA ya eliminada.** Unica hipotesis: `pred` dotado. -/
theorem refl_caso_varc_at (v s n : Term)
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
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
    prf_or_elim (prf_lt_trichotomy v n) (br_lt v s n hPred)
      (prf_or_elim_imp (br_eq v s n) (br_gt v s n))
  exact pcc_eq_trans_code _ _ _ (invA v s (varc n)) (by hw_auto) (by hw_auto) (by hw_auto) s0 hmain

/-! ############################################################################
    ## §8 · EL TESTIGO Y SU FONTANERIA — copia LITERAL de `sondeos/DescensoLiftc.lean`
       §B/§C/§D.1-§D.3 (es INDEPENDIENTE del objetivo: habla solo de codigos de TERMINO)
    ############################################################################ -/

/-! ### D.1 · `⊢ Y ≐ nil ∨ consOk Y` para `Y` ARBITRARIO -/

/-! ### D.2 · `argsIn` se hereda a la COLA -/

/-! ### D.3 · Del testigo al NODO -/

/-! ############################################################################
    ## §9 · `liftFormula`/`substFormula` atraviesan los dos objetivos
    ############################################################################ -/

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

/-! ## §10 · Las clausulas en forma IMPLICACION (la moneda de la induccion OBJETO) -/

/-- ⭐ **La que fue la única hipótesis externa del frente, DESCARGADA en tres líneas.**

El sondeo la arrastraba como una `PredHyp` abstracta (`∀ v n, ⊢ v < n ⇒ Prov(⌜τ(ṅ) = (τn)˙⌝)`)
y gastaba una sección entera —ocho declaraciones, con `ax26_pred_succ` instanciada dentro de
`Prov` y una eliminación de ∃ objeto— en probarla. Sobra toda: producción tiene
`pcc_eval_pred'` **sin guarda ninguna** (`Meta/EvalPredPrf.lean:200`), que es estrictamente
más fuerte. Lo único que hace falta es debilitarla añadiendo la guarda que el punto de uso
lleva de todos modos. -/
theorem prf_pred_dot_guarded (v n : Term) :
    Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n))))) :=
  prf_deduction (prf_to_prfH (pcc_eval_pred' n) [lt v n])

theorem refl_substtc_shapeUn_imp (v s X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc (nthc X (numeralM 1)))) := prfH_hyp_self _
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc_at v s (nthc X (numeralM 1)) (prf_pred_dot_guarded v (nthc X (numeralM 1)))) _)

theorem refl_substtc_caso_funcc_imp (v s p b : Term) :
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
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 s4 (by hw_auto) (by hw_auto) (by hw_auto)) (by hw_auto) (by hw_auto) (by hw_auto)) (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtc_func v s p b))))) _) hchain

theorem refl_substtc_shapeBin_imp (v s X : Term) :
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
    PrfH.mp _ _ _ (prf_to_prfH (refl_substtc_caso_funcc_imp v s p b) _) hbb
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hs) hfb

theorem refl_substtc_lista_cons_imp (v s h t : Term) :
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
        (PrfH_eq_trans_code _ _ _ hZ s3
          (PrfH_eq_trans_code _ _ _ hU s4 s5 (by hw_auto) (by hw_auto) (by hw_auto)) (by hw_auto) (by hw_auto) (by hw_auto)) (by hw_auto) (by hw_auto) (by hw_auto)) (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtsc_cons v s h t))))) _) hchain

/-! ############################################################################
    ## §11 · EL PREDICADO DE LA INDUCCION FUERTE — las DOS mitades y los DOS
       parametros `v`/`s`, todos CUANTIFICADOS DENTRO (lo exige `liftFormula 1 Φ = Φ`)
    ############################################################################ -/

def CONJsubsttc (w v s X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (targetSubsttc v s X))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (targetSubsttsc v s X))

theorem liftF_CONJsubsttc (k : Nat) (w v s X : Term) :
    liftFormula k (CONJsubsttc w v s X)
      = CONJsubsttc (liftTerm k w) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [CONJsubsttc, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetSubsttc, liftF_targetSubsttsc]

theorem substF_CONJsubsttc (k : Nat) (u w v s X : Term) :
    substFormula k u (CONJsubsttc w v s X)
      = CONJsubsttc (substTerm k u w) (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [CONJsubsttc, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetSubsttc, substF_targetSubsttsc]

/-- `#3` es el CODIGO sobre el que se induce; `#2` el testigo, `#1` = `v`, `#0` = `s`. -/
def PHIsubsttcBody : Formula := CONJsubsttc (.var 2) (.var 1) (.var 0) (.var 3)
def PHIsubsttc : Formula := Formula.forall (Formula.forall (Formula.forall PHIsubsttcBody))

theorem hPHIsubsttc1 : liftFormula 1 PHIsubsttc = PHIsubsttc := by
  simp only [PHIsubsttc, PHIsubsttcBody, liftFormula, liftF_CONJsubsttc, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHIsubsttc_at (t : Term) :
    substFormula 0 t PHIsubsttc
      = Formula.forall (Formula.forall (Formula.forall
          (CONJsubsttc (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHIsubsttc, PHIsubsttcBody, substFormula, substF_CONJsubsttc, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHIsubsttc_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
        (CONJsubsttc (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (CONJsubsttc (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_CONJsubsttc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHIsubsttc_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
        (CONJsubsttc (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (CONJsubsttc (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_CONJsubsttc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHIsubsttc_spec3 (t w v s : Term) :
    substFormula 0 s (CONJsubsttc (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = CONJsubsttc w v s t := by
  simp only [substF_CONJsubsttc, substTerm, FOL.substTerm_liftTerm, if_true]

/-- Instanciacion de las DOS mitades a `w`, `v`, `s` concretos. -/
theorem PHIsubsttc_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHIsubsttc)) :
    PrfH Γ (CONJsubsttc w v s t) := by
  rw [PHIsubsttc_at] at h
  have h1 := PrfH_spec h w
  rw [PHIsubsttc_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHIsubsttc_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHIsubsttc_spec3] at h3

def PSIsubsttc3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIsubsttc)))

/-! ### El PASO de la induccion fuerte -/

theorem PHIsubsttc_step : Prf (Formula.forall (Formula.impl (PSI PHIsubsttc) PHIsubsttc)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIsubsttc] (Formula.forall (Formula.forall PHIsubsttcBody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIsubsttcBody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIsubsttcBody ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSIsubsttc3] PHIsubsttcBody
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
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_substtc_shapeUn_imp (.var 1) (.var 0) (.var 3)) _)
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
      have hphi := PrfH.mp _ _ _ (PSI_inst3 PHIsubsttc hPHIsubsttc1 hpsi' (nthc (.var 3) (numeralM 2))) hltb
      have huse := PHIsubsttc_use (nthc (.var 3) (numeralM 2)) (.var 2) (.var 1) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_substtc_shapeBin_imp (.var 1) (.var 0) (.var 3)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) [PSIsubsttc3] rfl
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 3) nil,
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSIsubsttc3]
          (Formula.eq (.var 3) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm heq)
        (prf_to_prfH (refl_substtc_lista_nil (.var 1) (.var 0)) _)
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
        (PrfH.mp _ _ _ (PSI_inst3 PHIsubsttc hPHIsubsttc1 hpsi (carc (.var 3))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      -- (b) la COLA hereda `argsIn` y es MENOR
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 2) (carc (.var 3)) (cdrc (.var 3))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_tl := PHIsubsttc_use (cdrc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst3 PHIsubsttc hPHIsubsttc1 hpsi (cdrc (.var 3))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_substtc_lista_cons_imp (.var 1) (.var 0)
          (carc (.var 3)) (cdrc (.var 3))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hcons) hres

/-! ### §12 · EL DESCENSO y `pcc_eval_substtc` -/

theorem PHIsubsttc_all (t : Term) : Prf (substFormula 0 t PHIsubsttc) :=
  prf_strong_induction PHIsubsttc hPHIsubsttc1 (PHIsubsttc_step) t

theorem DESCENSO_substtc_imp (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PHIsubsttc_use t w v s (prf_to_prfH (PHIsubsttc_all t) []))) rfl

theorem DESCENSO_substtc_lista_imp (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_right (PHIsubsttc_use t w v s (prf_to_prfH (PHIsubsttc_all t) []))) rfl

/-- **`pcc_eval_substtc`** — el objetivo del frente, con `v`, `s`, `t` **ABSTRACTOS** y el
    testigo `w` como GUARDA (igual que `pcc_eval_liftc`), y **sin ninguna hipótesis externa**:
    la que había (`PredHyp`) la descarga `prf_pred_dot_guarded` desde `pcc_eval_pred'`. -/
theorem pcc_eval_substtc (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  prf_mp (DESCENSO_substtc_imp w v s t) h

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem pcc_eval_substtsc (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  prf_mp (DESCENSO_substtc_lista_imp w v s t) (prf_and_intro hwf hargs)

theorem pcc_eval_substtc_hasWit (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetSubsttc]
  exact PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_substtc_imp (.var 0) (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t)) _)
    (prfH_hyp_self _)
end ROBINSON_PlusPlus.Meta.EvalSubsttcPrf

/-! ## `export` POR CONSUMO (§17)

No es una lista por existencia: los 46 nombres de abajo son los que **de hecho** referencian
los assets aguas abajo del frente —`sondeos/EvalSubstfcPrf.lean` (B3.4) y
`sondeos/HasWitFReal.lean`— medidos por grep sobre las 71 declaraciones del módulo. Las 25
restantes (la fontanería de la inducción: `PHIsubsttc*`, `PSIsubsttc3`, `CONJsubsttc`, los
`refl_substtc_*`, `br_*_at`, …) se quedan dentro del namespace hasta que alguien las pida. -/
export ROBINSON_PlusPlus.Meta.EvalSubsttcPrf (
  substtcT substtscT substtcT_termCode substtscT_termCode eqc_eq_eqCodeFn
  prf_congr_substtcT prf_congr_substtscT
  prf_substtc_substtcT prf_substtc_substtscT
  substtc_inv_substtcT substtc_inv_substtscT
  pcc_congr_substtcT_arg3_code pcc_congr_substtscT_arg3_code
  SUBSTTSC_NIL_BODY  SUBSTTSC_NIL_BODY_ok  pcc_substtsc_nil_code
  SUBSTTC_FUNC_BODY  SUBSTTC_FUNC_BODY_ok  pcc_substtc_func_code
  SUBSTTSC_CONS_BODY SUBSTTSC_CONS_BODY_ok pcc_substtsc_cons_code
  SUBSTTC_VAR_EQ_BODY SUBSTTC_VAR_EQ_BODY_ok pcc_substtc_var_eq_code
  SUBSTTC_VAR_GT_BODY SUBSTTC_VAR_GT_BODY_ok pcc_substtc_var_gt_code
  SUBSTTC_VAR_LT_BODY SUBSTTC_VAR_LT_BODY_ok pcc_substtc_var_lt_code
  invA invAs br_lt br_eq br_gt refl_caso_varc_at
  targetSubsttc targetSubsttsc
  liftF_targetSubsttc liftF_targetSubsttsc substF_targetSubsttc substF_targetSubsttsc
  PrfH_congr_targetSubsttc PrfH_congr_targetSubsttsc substF_hole_tc substF_hole_tsc
  pcc_eval_substtc pcc_eval_substtsc pcc_eval_substtc_hasWit
)

/-! ## FOOTPRINT — la única auditoría que vale (`#print axioms`, no los `import`) -/

#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtc
#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtsc
#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtc_hasWit
#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.prf_pred_dot_guarded
#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.PHIsubsttc_step
#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_substtc_func_code
#print axioms ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_substtc_var_lt_code

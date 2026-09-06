/-
# `pcc_eval_substtc` — la evaluacion PROVABLE de `substtc` / `substtsc`.

Sigue el patron cerrado de `sondeos/DescensoLiftc.lean` (`pcc_eval_liftc`): UNA induccion
fuerte con conclusion CONJUNTIVA sobre los dos sorts (termino / lista de terminos).

Fichero AUTOCONTENIDO: `import ROBINSON_PlusPlus.Meta` y copia literal de lo que hace falta.

    lake env lean Probe/SF_substtc.lean
-/
import ROBINSON_PlusPlus.Meta

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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace SFsubsttc

/-! ############################################################################
    ## §1 · CONSTRUCTORES DE CODIGO (DEFINICIONES; ninguna ecuacion suya se postula)
    ############################################################################ -/

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
/-- `varc x = cons 0 (cons x nil)` ⇒ su imagen punteada es el `unT 0` del KIT. -/
def varcT (X : Term) : Term := unT 0 X
/-- `funcc a b = cons 1 (cons a (cons b nil))` ⇒ su imagen punteada es `binT 1`. -/
def funccT (X Y : Term) : Term := binT 1 X Y
/-- Imagen punteada de `pred` (identica en forma a `succcT`). -/
def predcT (x : Term) : Term := funcc (strCode pred_sym) (cons x nil)

theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s t : Term) :
    substtscT (termCode v) (termCode s) (termCode t) = termCode (substtsc v s t) := rfl
theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl
theorem predcT_termCode (x : Term) : predcT (termCode x) = termCode (pred x) := rfl

theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-! ## §2 · Fontaneria basica: congruencias e invariancias -/

/-- Congruencia ternaria sobre `funcc` (injerto de `sondeos/Paso2CasoForall.lean:74`). -/
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-- `substtc` sobre un `funcc` de **tres** argumentos. -/
theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy
theorem prf_congr_predcT {x y : Term} (h : Prf (x =eq y)) : Prf (predcT x =eq predcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z
theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z
theorem prf_substtc_predcT (v W x : Term) :
    Prf (substtc v W (predcT x) =eq predcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode pred_sym) x

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
theorem substtc_inv_predcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (predcT X) =eq predcT X) := fun W =>
  prf_eq_trans (prf_substtc_predcT zero W X) (prf_congr_predcT (hX W))

/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados (copia de Paso2 §2) -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) := by
  unfold binT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a)) :=
  prf_substtc_unT_at 0 v W a
theorem prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binT_at 1 v W a b

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

/-- `substfc` atraviesa un atomo binario de codigo (copia de `DescensoLiftc:251`). -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

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

/-- Congruencia interna en la CABEZA de `consT` (copia de `DescensoLiftc:508`). -/
theorem pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwB : Prf (hasWit B) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) := by
  let Ac : Term := eqc (consT X B) (consT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT X B) (consT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT X B) (consT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w X B) (prf_congr_consT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
        (prf_congr_consT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (by hw_auto) hwX hwY)

/-- Congruencia interna en la COLA de `consT`. -/
theorem pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) := by
  let Ac : Term := eqc (consT A X) (consT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT A X) (consT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT A X) (consT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w A X) (prf_congr_consT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
        (prf_congr_consT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT A X))
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

/-- **(2) PASO `funcc`** — el unico salto: pide la companera sobre la LISTA de argumentos. -/
theorem refl_caso_funcc (v s X p b : Term) (hX : Prf (X =eq funcc p b))
    (hb : Prf (targetSubsttsc v s b)) : Prf (targetSubsttc v s X) := by
  unfold targetSubsttc
  unfold targetSubsttsc at hb
  have hplain : Prf (substtc v s X =eq funcc p (substtsc v s b)) :=
    prf_eq_trans (prf_congr_substtc3 hX) (prf_substtc_func v s p b)
  have hY : ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      =eq substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (invAs v s b)
  have s1 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (funcc p b))) (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) :=
    pcc_substtc_func_code v s p b
  have s3 : Prf (provFromCode (eqc
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      (funccT (tcFn p) (tcFn (substtsc v s b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))
      (tcFn (substtsc v s b)) (substtc_inv_tcFn p) (invAs v s b)) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (substtsc v s b)))
      (tcFn (funcc p (substtsc v s b))))) := pcc_dot_bin 1 p (substtsc v s b)
  have hchain : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (tcFn (funcc p (substtsc v s b))))) :=
    pcc_eq_trans_code _ _ _ (invA v s (funcc p b)) (by hw_auto) (by hw_auto) (by hw_auto) s1
      (pcc_eq_trans_code _ _ _ hY (by hw_auto) (by hw_auto) (by hw_auto) s2 (pcc_eq_trans_code _ _ _ hZ (by hw_auto) (by hw_auto) (by hw_auto) s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_substtcT (prf_refl _) (prf_refl _) (prf_congr_tcFn (prf_eq_symm hX)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil (v s : Term) : Prf (targetSubsttsc v s nil) := by
  unfold targetSubsttsc
  refine prf_mp (prf_provCode_congr (prf_congr_eqCodeFn ?_ ?_)) (pcc_substtsc_nil_code v s)
  · exact prf_congr_substtscT (prf_refl _) (prf_refl _) (prf_eq_symm prf_tc_zero)
  · exact prf_eq_trans (prf_eq_symm prf_tc_zero)
      (prf_congr_tcFn (prf_eq_symm (prf_substtsc_nil v s)))

/-- **(4) PASO de la LISTA (`cons`)** — pide la companera sobre la cabeza y sobre la cola. -/
theorem refl_lista_cons (v s h t : Term) (hh : Prf (targetSubsttc v s h))
    (ht : Prf (targetSubsttsc v s t)) : Prf (targetSubsttsc v s (cons h t)) := by
  unfold targetSubsttc at hh
  unfold targetSubsttsc at ht ⊢
  have hplain : Prf (substtsc v s (cons h t)
      =eq cons (substtc v s h) (substtsc v s t)) := prf_substtsc_cons v s h t
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
  have s1 : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_substtscT_arg3_code (tcFn v) (tcFn s) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons h t))) (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) := pcc_substtsc_cons_code v s h t
  have s3 : Prf (provFromCode (eqc
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (substtscT (tcFn v) (tcFn s) (tcFn t))
      (substtcT (tcFn v) (tcFn s) (tcFn h)) (tcFn (substtc v s h))
      (invAs v s t) (invA v s h)) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (substtc v s h))
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))
      (substtc_inv_tcFn (substtc v s h)) (invAs v s t)) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    pcc_dot_cons (substtc v s h) (substtsc v s t)
  have hchain : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    pcc_eq_trans_code _ _ _ (invAs v s (cons h t)) (by hw_auto) (by hw_auto) (by hw_auto) s1
      (pcc_eq_trans_code _ _ _ hY (by hw_auto) (by hw_auto) (by hw_auto) s2
        (pcc_eq_trans_code _ _ _ hZ (by hw_auto) (by hw_auto) (by hw_auto) s3 (pcc_eq_trans_code _ _ _ hU (by hw_auto) (by hw_auto) (by hw_auto) s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

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

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

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

/-- La forma que consume la induccion: la guarda llega como ecuacion PLANA `X ≐ varc n`. -/
theorem refl_caso_varc (v s X n : Term) (hX : Prf (X =eq varc n))
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (targetSubsttc v s X) := by
  unfold targetSubsttc
  have h := refl_caso_varc_at v s n hPred
  unfold targetSubsttc at h
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_substtcT (prf_refl _) (prf_refl _) (prf_congr_tcFn (prf_eq_symm hX)))
    (prf_congr_tcFn (prf_eq_symm (prf_congr_substtc3 hX))))) h

/-! ############################################################################
    ## §8 · EL TESTIGO Y SU FONTANERIA — copia LITERAL de `sondeos/DescensoLiftc.lean`
       §B/§C/§D.1-§D.3 (es INDEPENDIENTE del objetivo: habla solo de codigos de TERMINO)
    ############################################################################ -/

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

theorem shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

theorem PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 a)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc a) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (lenc a)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 a) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc a i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (nthc a i)) Γ)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAll1, wfAll1Body, substFormula, substF_isTermCodeE1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) := by
  simp only [isTC1, land, In, substFormula, substF_wfAll1, substTerm, substTerms]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

theorem PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)

theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s
    simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)

theorem PrfH_inst_argsIn {Γ : List Formula} (wT Y i : Term) (h : PrfH Γ (argsIn wT Y)) :
    PrfH Γ (Formula.impl (lt i (lenc Y)) (In (nthc Y i) wT)) := by
  have hi := PrfH_spec h i
  simpa only [argsInBody, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hi

theorem PrfH_inst_wfAll1 {Γ : List Formula} (w i : Term) (h : PrfH Γ (wfAll1 w)) :
    PrfH Γ (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i))) := by
  have hi := PrfH_spec h i
  simpa only [wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody, lor, land,
    lt, lenc, nthc, In, cons, nil, zero, substFormula, substTerm, substTerms,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_lift_comm_zero, substTerm_numeralM, if_true] using hi

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j1 A B)) h
theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j2 A B)) h

/-! ### D.1 · `⊢ Y ≐ nil ∨ consOk Y` para `Y` ARBITRARIO -/

def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

theorem nilOrCons_at (Y : Term) :
    substFormula 0 Y nilOrCons = lor (Formula.eq Y nil) (consOk Y) := by
  simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, substFormula, substTerm,
    substTerms, if_true]

theorem prf_nil_or_cons_all : Prf (Formula.forall nilOrCons) := by
  refine prf_list_induction nilOrCons ?base ?step
  · rw [nilOrCons_at]
    exact prf_orL (prf_refl nil)
  · refine Prf.gen _ (Prf.gen _ ?_)
    have hR : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nilOrCons))
        = lor (Formula.eq (cons (.var 1) (.var 0)) nil) (consOk (cons (.var 1) (.var 0))) := by
      simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, liftFormula, substFormula,
        liftTerm, liftTerms, substTerm, substTerms, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        reduceIte, if_true]
    rw [hR]
    exact prf_mp (Prf.incl (Prf₀.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-! ### D.2 · `argsIn` se hereda a la COLA -/

theorem prf_argsIn_tail (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (argsIn w tl)) := by
  refine prf_mp (Prf.qconf (argsIn w (cons hd tl)) (argsInBody w tl)) (Prf.gen _ ?_)
  rw [liftF_argsIn]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc tl)))
    [argsIn (liftTerm 0 w) (liftTerm 0 (cons hd tl))] rfl)
  show PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
    (In (nthc (liftTerm 0 tl) (.var 0)) (liftTerm 0 w))
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (lt (.var 0) (lenc (liftTerm 0 tl))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt' : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (lt (succ (.var 0)) (lenc (cons (liftTerm 0 hd) (liftTerm 0 tl)))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_cons (liftTerm 0 hd) (liftTerm 0 tl))) _)
      (PrfH.mp _ _ _ (prf_to_prfH
        (prf_succ_lt_succ_of_lt (.var 0) (lenc (liftTerm 0 tl))) _) hlt)
  have hin : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (In (nthc (cons (liftTerm 0 hd) (liftTerm 0 tl)) (succ (.var 0))) (liftTerm 0 w)) :=
    PrfH.mp _ _ _ (PrfH_inst_argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))
      (succ (.var 0)) hargs) hlt'
  exact PrfH_congr_In_left
    (prf_to_prfH (prf_nthc_succ (liftTerm 0 hd) (liftTerm 0 tl) (.var 0)) _) hin

/-! ### D.3 · Del testigo al NODO -/

theorem prf_isTermCodeE1_of_boundedIn (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAll1, liftF_isTermCodeE1]
  refine deduction_aux ?_ (wfAll1 (liftTerm 0 w)) _ rfl
  have hwf : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (liftTerm 0 w))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) hwf) hlt
  exact PrfH_congr_isTermCodeE1 heq hitc

theorem prf_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (prf_isTermCodeE1_of_boundedIn w c)

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

/-- La UNICA hipotesis externa del frente: la evaluacion DOTADA de `pred`, en su forma
    GUARDADA (la mas debil que sirve). Otro agente la esta construyendo. -/
def PredHyp : Prop := ∀ v n : Term,
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))

theorem refl_shapeUn_imp (hP : PredHyp) (v s X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc (nthc X (numeralM 1)))) := prfH_hyp_self _
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc_at v s (nthc X (numeralM 1)) (hP v (nthc X (numeralM 1)))) _)

theorem refl_caso_funcc_imp (v s p b : Term) :
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

theorem refl_shapeBin_imp (v s X : Term) :
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
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp v s p b) _) hbb
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hs) hfb

theorem refl_lista_cons_imp (v s h t : Term) :
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
def PHIbody : Formula := CONJ (.var 2) (.var 1) (.var 0) (.var 3)
def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

theorem hPHI1 : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_CONJ, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHI_at (t : Term) :
    substFormula 0 t PHI
      = Formula.forall (Formula.forall (Formula.forall
          (CONJ (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI, PHIbody, substFormula, substF_CONJ, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
        (CONJ (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHI_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
        (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHI_spec3 (t w v s : Term) :
    substFormula 0 s (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = CONJ w v s t := by
  simp only [substF_CONJ, substTerm, FOL.substTerm_liftTerm, if_true]

/-- Instanciacion de las DOS mitades a `w`, `v`, `s` concretos. -/
theorem PHI_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (CONJ w v s t) := by
  rw [PHI_at] at h
  have h1 := PrfH_spec h w
  rw [PHI_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHI_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHI_spec3] at h3

theorem psi_l1 : liftFormula 0 (PSI PHI)
    = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHI) := by
  simp only [PSI, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI1]

theorem psi_l2 : liftFormula 0 (liftFormula 0 (PSI PHI))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) PHI) := by
  rw [psi_l1]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI1]

theorem psi_l3 : liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) PHI) := by
  rw [psi_l2]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI1]

def PSI3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))

theorem PSI_inst {Γ : List Formula} (hpsi : PrfH Γ PSI3) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z PHI)) := by
  unfold PSI3 at hpsi
  rw [psi_l3] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) PHI)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z PHI) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-! ### El PASO de la induccion fuerte -/

theorem PHI_step (hP : PredHyp) : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] (Formula.forall (Formula.forall PHIbody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIbody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSI3] PHIbody
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (isTC1 (.var 2) (.var 3)) [PSI3] rfl
    have hh : PrfH [isTC1 (.var 2) (.var 3), PSI3] (isTC1 (.var 2) (.var 3)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwf : PrfH [isTC1 (.var 2) (.var 3), PSI3] (wfAll1 (.var 2)) :=
      PrfH_and_elim_left hh
    have hin : PrfH [isTC1 (.var 2) (.var 3), PSI3] (In (.var 3) (.var 2)) :=
      PrfH_and_elim_right hh
    have hitc : PrfH [isTC1 (.var 2) (.var 3), PSI3]
        (isTermCodeE1 (.var 2) (.var 3)) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH (prf_isTermCodeE1_of_In (.var 2) (.var 3)) _) hin) hwf
    refine PrfH_or_elim hitc ?varc ?func
    case varc =>
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp hP (.var 1) (.var 0) (.var 3)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    case func =>
      have hb : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3]
          (land (shapeBin (.var 3) 1) (argsIn (.var 2) (nthc (.var 3) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hwf' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3] (wfAll1 (.var 2)) :=
        PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      have hpsi' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3] PSI3 :=
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
      have hphi := PrfH.mp _ _ _ (PSI_inst hpsi' (nthc (.var 3) (numeralM 2))) hltb
      have huse := PHI_use (nthc (.var 3) (numeralM 2)) (.var 2) (.var 1) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp (.var 1) (.var 0) (.var 3)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) [PSI3] rfl
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 3) nil,
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (Formula.eq (.var 3) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm heq)
        (prf_to_prfH (refl_lista_nil (.var 1) (.var 0)) _)
    case consc =>
      have hcons : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh' : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3] PSI3 :=
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
      have huse_hd := PHI_use (carc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (carc (.var 3))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      -- (b) la COLA hereda `argsIn` y es MENOR
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 2) (carc (.var 3)) (cdrc (.var 3))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_tl := PHI_use (cdrc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (cdrc (.var 3))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp (.var 1) (.var 0)
          (carc (.var 3)) (cdrc (.var 3))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hcons) hres

/-! ### §12 · EL DESCENSO y `pcc_eval_substtc` -/

theorem PHI_all (hP : PredHyp) (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI1 (PHI_step hP) t

theorem DESCENSO_imp (hP : PredHyp) (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PHI_use t w v s (prf_to_prfH (PHI_all hP t) []))) rfl

theorem DESCENSO_lista_imp (hP : PredHyp) (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_right (PHI_use t w v s (prf_to_prfH (PHI_all hP t) []))) rfl

/-- **`pcc_eval_substtc`** — el objetivo del encargo, con `v`, `s`, `t` **ABSTRACTOS**
    y el testigo `w` como GUARDA (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc (hP : PredHyp) (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  prf_mp (DESCENSO_imp hP w v s t) h

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem pcc_eval_substtsc (hP : PredHyp) (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  prf_mp (DESCENSO_lista_imp hP w v s t) (prf_and_intro hwf hargs)

/-- La forma que de verdad llega rio abajo: el testigo viene de un `∃`. -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

theorem pcc_eval_substtc_hasWit (hP : PredHyp) (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetSubsttc]
  exact PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_imp hP (.var 0) (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t)) _)
    (prfH_hyp_self _)

/-! ############################################################################
    ## §13 · LA HIPOTESIS `PredHyp` SE DESCARGA — `pred` DOTADO bajo la guarda `v < n`.

    `v < n` da (por `ax13`) un testigo `k` con `v + σk = n`, o sea **`n` es un SUCESOR**
    (`prf_add_succ_t`). Y para un sucesor, `pred` dotado sale de **`ax26_pred_succ`
    instanciado DENTRO de `Prov`** (`pcc_axiom_inst`), sin induccion ninguna.
    ############################################################################ -/

def AX26_BODY : Formula := pred (succ (.var 0)) =eq (.var 0)

theorem AX26_BODY_ok : ax26_pred_succ = Formula.forall AX26_BODY := rfl

/-- **`ax26_pred_succ` DOTADA**: `⊢ Prov(⌜ pred(σ(ṁ)) = ṁ ⌝)`, con `m` **ABSTRACTO**. -/
theorem pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) := by
  have hin : Prf (substfc zero (tcFn m) (formCode AX26_BODY)
      =eq eqCodeFn (predcT (succcT (tcFn m))) (tcFn m)) :=
    prf_substfc_arith_open 0 (tcFn m) AX26_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst AX26_BODY (show ax26_pred_succ ∈ axioms by simp [axioms]) (tcFn m) (by hw_auto))

theorem PrfH_congr_pred {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (pred a =eq pred b) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 a)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred a) (pred s) := by
    intro s
    simp only [f, pred, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (pred a)) Γ)

theorem PrfH_congr_predcT {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (predcT a =eq predcT b) := by
  let f : Formula := Formula.eq (predcT (liftTerm 0 a)) (predcT (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (predcT a) (predcT s) := by
    intro s
    simp only [f, predcT, funcc, cons, nil, zero, succ, substFormula, substTerm, substTerms,
      substTerm_strCode, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (predcT a)) Γ)

theorem PrfH_pred_dot_of_succ {Γ : List Formula} (n m : Term) (h : PrfH Γ (n =eq succ m)) :
    PrfH Γ (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := by
  have e1 : PrfH Γ (predcT (tcFn n) =eq predcT (succcT (tcFn m))) :=
    PrfH_congr_predcT (PrfH_eq_trans (PrfH_congr_tcFn h) (prf_to_prfH (prf_tc_succ' m) _))
  have hpn : PrfH Γ (pred n =eq m) :=
    PrfH_eq_trans (PrfH_congr_pred h) (prf_to_prfH (prf_pred_succ m) _)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_eq_symm e1) (PrfH_congr_tcFn (PrfH_eq_symm hpn)))
    (prf_to_prfH (pcc_pred_succ_code m) _)

theorem liftT_predcode (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) := by
  simp only [eqc, predcT, funcc, tcFn, pred, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode]

/-- **`PredHyp` DESCARGADA.** -/
theorem predHyp : PredHyp := by
  intro v n
  refine prf_deduction ?_
  have hiff : PrfH [lt v n]
      (Formula.ex (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_lt_iff v n)) _) (prfH_hyp_self _)
  refine PrfH_ex_elim hiff ?_
  rw [liftFormula_provFromCode_open, liftT_predcode]
  have hh : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsucc : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (liftTerm 0 n =eq succ (add (liftTerm 0 v) (.var 0))) :=
    PrfH_eq_trans (PrfH_eq_symm hh)
      (prf_to_prfH (prf_add_succ_t (liftTerm 0 v) (.var 0)) _)
  exact PrfH_pred_dot_of_succ (liftTerm 0 n) (add (liftTerm 0 v) (.var 0)) hsucc

/-! ### §14 · EL TEOREMA, YA SIN NINGUNA HIPOTESIS EXTERNA -/

/-- **`pcc_eval_substtc`** — SIN hipotesis: la evaluacion PROVABLE de `substtc` con
    `v`, `s`, `t` **ABSTRACTOS**, guardada por el testigo `w` (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc' (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  pcc_eval_substtc predHyp w v s t h

/-- Su gemela sobre LISTAS de codigos de termino, SIN hipotesis. -/
theorem pcc_eval_substtsc' (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  pcc_eval_substtsc predHyp w v s t hwf hargs

/-- La forma con el testigo CUANTIFICADO (la que llega rio abajo), SIN hipotesis. -/
theorem pcc_eval_substtc_hasWit' (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) :=
  pcc_eval_substtc_hasWit predHyp v s t

end SFsubsttc

#print axioms SFsubsttc.prf_isTermCodeE1_of_In
#print axioms SFsubsttc.pcc_pred_succ_code
#print axioms SFsubsttc.predHyp
#print axioms SFsubsttc.pcc_eval_substtc'
#print axioms SFsubsttc.pcc_eval_substtsc'
#print axioms SFsubsttc.pcc_eval_substtc_hasWit'
#print axioms SFsubsttc.refl_shapeUn_imp
#print axioms SFsubsttc.refl_shapeBin_imp
#print axioms SFsubsttc.refl_lista_cons_imp
#print axioms SFsubsttc.PHI_step
#print axioms SFsubsttc.pcc_eval_substtc
#print axioms SFsubsttc.pcc_eval_substtsc
#print axioms SFsubsttc.pcc_eval_substtc_hasWit
#print axioms SFsubsttc.pcc_substtsc_nil_code
#print axioms SFsubsttc.pcc_substtc_func_code
#print axioms SFsubsttc.pcc_substtsc_cons_code
#print axioms SFsubsttc.pcc_substtc_var_eq_code
#print axioms SFsubsttc.pcc_substtc_var_gt_code
#print axioms SFsubsttc.pcc_substtc_var_lt_code
#print axioms SFsubsttc.refl_caso_funcc
#print axioms SFsubsttc.refl_lista_nil
#print axioms SFsubsttc.refl_lista_cons
#print axioms SFsubsttc.br_lt
#print axioms SFsubsttc.br_eq
#print axioms SFsubsttc.br_gt
#print axioms SFsubsttc.refl_caso_varc

-- ENUNCIADOS EXACTOS (para el informe)
#check @SFsubsttc.pcc_eval_substtc'
#check @SFsubsttc.pcc_eval_substtsc'
#check @SFsubsttc.pcc_eval_substtc_hasWit'
#check @SFsubsttc.predHyp
#check @SFsubsttc.pcc_substtc_func_code
#check @SFsubsttc.refl_caso_varc_at

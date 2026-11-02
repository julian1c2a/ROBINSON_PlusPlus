/-
# `Probe/B3_substtc_conexion.lean` — ANGULO (C) de la rama B3: ¿CONECTA
  `sondeos/EvalSubsttc.lean` con el vocabulario que YA esta en produccion?

Fichero de SONDEO. No integra nada. Todo lo que afirma esta COMPILADO aqui.

Medido sobre `sondeos/EvalSubsttc.lean` de 1905 lineas, md5 7cfc61a8f12477b3dae118a136d5b904
(156 declaraciones; 83 nombres coinciden con produccion, 73 no).

  * §0  copia LITERAL de las 30 definiciones del sondeo (para poder enunciar lo demas).
  * §A  15 PUENTES `:= rfl` — el vocabulario redefinido ES el de produccion.
  * §B  51 lemas del sondeo CERRADOS con la constante de produccion, tal cual.
        §A+§B = los 66 DUPLICADOS REALES que NO hay que promover.
  * §C  16 `example` con `fail_if_success` que cubren los 17 nombres restantes:
        mismo NOMBRE, enunciado DISTINTO (son los homonimos de la familia `liftc`).
  * §D  el `PSI_inst` del sondeo NO es el de produccion; se prueba aqui el GENERAL
        (`PSI_inst3`) que hay que BAJAR a `Meta/StrongInductionPrf.lean` (ADR-019).
  * §E  la copia de `pcc_eq_tracked` que sobrevive en `sondeos/EvalSubstfcPrf.lean`.
  * §F  ADR-019 al reves: `PrfH_congr_predcT` del sondeo SUBSUME a
        `EvalPredPrf.prf_congr_predcT`; hay que BAJARLA, no dejarla arriba.
  * §G  tres nombres que `CodeWitnessPrf` declara pero NO exporta.
  * §H  cuando rompen los 17 homonimos y cuando no (medido, no supuesto).

VEREDICTO: promocion MECANICA en el vocabulario (66/156 se borran), pero NO mecanica en
el ensamblaje: 17 nombres piden renombre y hay dos lemas que van a OTROS modulos (§D, §F).
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace B3conx

/-! ## §0 · COPIA LITERAL de las DEFINICIONES del sondeo (para enunciar §A-§D) -/

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

def SUBSTTSC_NIL_BODY : Formula := substtsc (.var 1) (.var 0) nil =eq nil

def SUBSTTC_FUNC_BODY : Formula :=
  substtc (.var 3) (.var 2) (funcc (.var 1) (.var 0))
    =eq funcc (.var 1) (substtsc (.var 3) (.var 2) (.var 0))

def SUBSTTSC_CONS_BODY : Formula :=
  substtsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
    =eq cons (substtc (.var 3) (.var 2) (.var 1)) (substtsc (.var 3) (.var 2) (.var 0))

def SUBSTTC_VAR_EQ_BODY : Formula :=
  Formula.impl ((.var 2) =eq (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq (.var 1))

def SUBSTTC_VAR_GT_BODY : Formula :=
  Formula.impl (lt (.var 2) (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (pred (.var 0)))

def SUBSTTC_VAR_LT_BODY : Formula :=
  Formula.impl (lt (.var 0) (.var 2))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (.var 0))

def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))
/-- Su companera sobre LISTAS de codigos de termino. -/

def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))


def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

def CONJ (w v s X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (targetSubsttc v s X))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (targetSubsttsc v s X))

def PHIbody : Formula := CONJ (.var 2) (.var 1) (.var 0) (.var 3)

def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

def PSI3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))

def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

def AX26_BODY : Formula := pred (succ (.var 0)) =eq (.var 0)

def PredHyp : Prop := ∀ v n : Term,
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))

/-! ############################################################################
    ## §A · PUENTES `:= rfl` — las 15 definiciones redefinidas SON las de produccion
    ############################################################################ -/

theorem br_varcT : @varcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT := rfl
theorem br_funccT : @funccT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT := rfl
theorem br_predcT : @predcT = @ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT := rfl
theorem br_shapeUn : @shapeUn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn := rfl
theorem br_shapeBin : @shapeBin = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin := rfl
theorem br_argsInBody : @argsInBody = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody := rfl
theorem br_argsIn : @argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn := rfl
theorem br_isTermCodeE1 : @isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 := rfl
theorem br_consOk : @consOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.consOk := rfl
theorem br_wfAll1Body : @wfAll1Body = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body := rfl
theorem br_wfAll1 : @wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1 := rfl
theorem br_isTC1 : @isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 := rfl
theorem br_hasWit : @hasWit = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit := rfl
theorem br_nilOrCons : @nilOrCons = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons := rfl
theorem br_AX26_BODY : @AX26_BODY = @ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY := rfl

/-! ############################################################################
    ## §B · 51 lemas del sondeo, CERRADOS con la constante de produccion TAL CUAL
    ############################################################################ -/

theorem chk_varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x)
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT_termCode ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT_termCode <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT_termCode <;> assumption)

theorem chk_funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y)
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT_termCode ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT_termCode <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT_termCode <;> assumption)

theorem chk_predcT_termCode (x : Term) : predcT (termCode x) = termCode (pred x)
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT_termCode ..
    | (apply ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT_termCode <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT_termCode <;> assumption)

theorem chk_prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X')
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_varcT ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_varcT <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_varcT <;> assumption)

theorem chk_prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y')
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_funccT ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_funccT <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_funccT <;> assumption)

theorem chk_prf_congr_predcT {x y : Term} (h : Prf (x =eq y)) : Prf (predcT x =eq predcT y)
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_congr_predcT ..
    | (apply ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_congr_predcT <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_congr_predcT <;> assumption)

theorem chk_prf_substtc_predcT (v W x : Term) :
    Prf (substtc v W (predcT x) =eq predcT (substtc v W x))
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_substtc_predcT ..
    | (apply ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_substtc_predcT <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_substtc_predcT <;> assumption)

theorem chk_substtc_inv_predcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (predcT X) =eq predcT X)
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalPredPrf.substtc_inv_predcT ..
    | (apply ROBINSON_PlusPlus.Meta.EvalPredPrf.substtc_inv_predcT <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalPredPrf.substtc_inv_predcT <;> assumption)

theorem chk_prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t)
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed <;> assumption)

theorem chk_prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM <;> assumption)

theorem chk_prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero)
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero <;> assumption)

theorem chk_prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_unT_at ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_unT_at <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_unT_at <;> assumption)

theorem chk_prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at <;> assumption)

theorem chk_prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_varcT_at ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_varcT_at <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_varcT_at <;> assumption)

theorem chk_prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_funccT_at ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_funccT_at <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_funccT_at <;> assumption)

theorem chk_pcc_thm_inst4 (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
          (formCode φ))))))
  := by first
    | exact ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 ..
    | (apply ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 <;> assumption)

theorem chk_pcc_axiom_inst4 (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
          (formCode φ))))))
  := by first
    | exact ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 ..
    | (apply ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 <;> assumption)

theorem chk_prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn <;> assumption)

theorem chk_prf_substfc_ltCodeFn_p (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_ltCodeFn' ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_ltCodeFn' <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_ltCodeFn' <;> assumption)

theorem chk_pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code <;> assumption)

theorem chk_pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg2_code ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg2_code <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg2_code <;> assumption)

theorem chk_prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp <;> assumption)

theorem chk_shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeUn0_es_varc ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeUn0_es_varc <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeUn0_es_varc <;> assumption)

theorem chk_shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeBin1_es_funcc ..
    | (apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeBin1_es_funcc <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeBin1_es_funcc <;> assumption)

theorem chk_impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT <;> assumption)

theorem chk_prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_cdrc_cons ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_cdrc_cons <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_cdrc_cons <;> assumption)

theorem chk_prf_consOk_cons (a b : Term) : Prf (consOk (cons a b))
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_consOk_cons ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_consOk_cons <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_consOk_cons <;> assumption)

theorem chk_PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_lenc ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_lenc <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_lenc <;> assumption)

theorem chk_PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_nthc_lst ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_nthc_lst <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_nthc_lst <;> assumption)

theorem chk_PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_In_left ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_In_left <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_In_left <;> assumption)

theorem chk_liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_argsIn ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_argsIn <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_argsIn <;> assumption)

theorem chk_substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_argsIn ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_argsIn <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_argsIn <;> assumption)

theorem chk_substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_isTermCodeE1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_isTermCodeE1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_isTermCodeE1 <;> assumption)

theorem chk_liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_isTermCodeE1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_isTermCodeE1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_isTermCodeE1 <;> assumption)

theorem chk_liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_wfAll1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_wfAll1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_wfAll1 <;> assumption)

theorem chk_substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_wfAll1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_wfAll1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_wfAll1 <;> assumption)

theorem chk_substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTC1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTC1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTC1 <;> assumption)

theorem chk_liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTC1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTC1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTC1 <;> assumption)

theorem chk_PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_argsIn ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_argsIn <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_argsIn <;> assumption)

theorem chk_PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_isTermCodeE1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_isTermCodeE1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_isTermCodeE1 <;> assumption)

theorem chk_PrfH_inst_argsIn {Γ : List Formula} (wT Y i : Term) (h : PrfH Γ (argsIn wT Y)) :
    PrfH Γ (Formula.impl (lt i (lenc Y)) (In (nthc Y i) wT))
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_argsIn ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_argsIn <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_argsIn <;> assumption)

theorem chk_PrfH_inst_wfAll1 {Γ : List Formula} (w i : Term) (h : PrfH Γ (wfAll1 w)) :
    PrfH Γ (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_wfAll1 ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_wfAll1 <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_wfAll1 <;> assumption)

theorem chk_prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orL ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orL <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orL <;> assumption)

theorem chk_prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B)
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orR ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orR <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orR <;> assumption)

theorem chk_nilOrCons_at (Y : Term) :
    substFormula 0 Y nilOrCons = lor (Formula.eq Y nil) (consOk Y)
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons_at ..
    | (apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons_at <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons_at <;> assumption)

theorem chk_prf_nil_or_cons_all : Prf (Formula.forall nilOrCons)
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons_all ..
    | (apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons_all <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons_all <;> assumption)

theorem chk_prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y))
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons ..
    | (apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons <;> assumption)

theorem chk_prf_argsIn_tail (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (argsIn w tl))
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail <;> assumption)

theorem chk_prf_isTermCodeE1_of_boundedIn (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn <;> assumption)

theorem chk_prf_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c)))
  := by first
    | exact ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In ..
    | (apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In <;> assumption)

theorem chk_AX26_BODY_ok : ax26_pred_succ = Formula.forall AX26_BODY
  := by first
    | exact ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY_ok ..
    | (apply ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY_ok <;> assumption)
    | (intros; apply ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY_ok <;> assumption)

/-! ############################################################################
    ## §C · CONTROLES NEGATIVOS — 17 nombres compartidos que NO son la misma cosa
    ############################################################################ -/

/-- NEGATIVO: `PHIbody` / `PHI` son HOMONIMOS, no copias: el `Φ` del sondeo es el de
    `substtc` (`CONJ w v s X`, tres `∀`) y el de produccion el de `liftc` (un `∀`). -/
example : True := by
  fail_if_success (have : @PHIbody = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIbody := rfl)
  fail_if_success (have : @PHI = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI := rfl)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc` NO sirve para el enunciado del sondeo. -/
example (v s X p b : Term) (hX : Prf (X =eq funcc p b)) (hb : Prf (targetSubsttsc v s b)) : True := by
  fail_if_success (have : Prf (targetSubsttc v s X) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil` NO sirve para el enunciado del sondeo. -/
example (v s : Term) : True := by
  fail_if_success (have : Prf (targetSubsttsc v s nil) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons` NO sirve para el enunciado del sondeo. -/
example (v s h t : Term) (hh : Prf (targetSubsttc v s h)) (ht : Prf (targetSubsttsc v s t)) : True := by
  fail_if_success (have : Prf (targetSubsttsc v s (cons h t)) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc` NO sirve para el enunciado del sondeo. -/
example (v s X n : Term) (hX : Prf (X =eq varc n)) (hPred : Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) : True := by
  fail_if_success (have : Prf (targetSubsttc v s X) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp` NO sirve para el enunciado del sondeo. -/
example (hP : PredHyp) (v s X : Term) : True := by
  fail_if_success (have : Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X)) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp` NO sirve para el enunciado del sondeo. -/
example (v s p b : Term) : True := by
  fail_if_success (have : Prf (Formula.impl (targetSubsttsc v s b) (targetSubsttc v s (funcc p b))) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp` NO sirve para el enunciado del sondeo. -/
example (v s X : Term) : True := by
  fail_if_success (have : Prf (Formula.impl (land (shapeBin X 1) (targetSubsttsc v s (nthc X (numeralM 2)))) (targetSubsttc v s X)) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp` NO sirve para el enunciado del sondeo. -/
example (v s h t : Term) : True := by
  fail_if_success (have : Prf (Formula.impl (land (targetSubsttc v s h) (targetSubsttsc v s t)) (targetSubsttsc v s (cons h t))) := by apply ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_at` NO sirve para el enunciado del sondeo. -/
example (t : Term) : True := by
  fail_if_success (have : substFormula 0 t PHI = Formula.forall (Formula.forall (Formula.forall (CONJ (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_at <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_use` NO sirve para el enunciado del sondeo. -/
example {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) : True := by
  fail_if_success (have : PrfH Γ (CONJ w v s t) := by apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_use <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst` NO sirve para el enunciado del sondeo. -/
example {Γ : List Formula} (hpsi : PrfH Γ PSI3) (z : Term) : True := by
  fail_if_success (have : PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z PHI)) := by apply ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step` NO sirve para el enunciado del sondeo. -/
example (hP : PredHyp) : True := by
  fail_if_success (have : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all` NO sirve para el enunciado del sondeo. -/
example (hP : PredHyp) (t : Term) : True := by
  fail_if_success (have : Prf (substFormula 0 t PHI) := by apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp` NO sirve para el enunciado del sondeo. -/
example (hP : PredHyp) (w v s t : Term) : True := by
  fail_if_success (have : Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) := by apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp <;> assumption)
  trivial

/-- NEGATIVO: `ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp` NO sirve para el enunciado del sondeo. -/
example (hP : PredHyp) (w v s t : Term) : True := by
  fail_if_success (have : Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) := by apply ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp <;> assumption)
  trivial

/-! ############################################################################
    ## §D · ADR-019 · `PSI_inst`: el del sondeo NO es el de produccion

    `Meta/StrongInductionPrf.lean` exporta `PSI_inst` **generico en `Φ`**, pero para UN
    solo levantamiento: de `PrfH Γ (liftFormula 0 (PSI Φ))` saca `lt z #1 ⇒ Φ(z)`.
    El sondeo necesita el de **TRES** levantamientos (su `Φ` lleva tres `∀`: w, v, s):
    de `PSI3 = liftFormula 0 ^[3] (PSI PHI)` saca `lt z #3 ⇒ PHI(z)`. Ninguno subsume
    al otro: el de produccion es mas general en `Φ`, el del sondeo en el numero de lifts.

    Lo que sigue prueba que la generalizacion SI existe y es mecanica. Va a
    `Meta/StrongInductionPrf.lean` (junto a `psi_lift_form`), NO al modulo nuevo:
    `EvalSubsttcPrf` lo importaria, y un corolario aguas arriba es el CICLO de imports.
    ############################################################################ -/

theorem psi_lift_form2 (F : Formula) (hF : liftFormula 1 F = F) :
    liftFormula 0 (liftFormula 0 (PSI F))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) F) := by
  rw [ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form F hF]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hF]

theorem psi_lift_form3 (F : Formula) (hF : liftFormula 1 F = F) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI F)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) F) := by
  rw [psi_lift_form2 F hF]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hF]

/-- **El general que falta**: `PSI_inst` con TRES levantamientos, generico en `Φ`. -/
theorem PSI_inst3 (F : Formula) (hF : liftFormula 1 F = F) {G : List Formula}
    (hpsi : PrfH G (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI F))))) (z : Term) :
    PrfH G (Formula.impl (lt z (.var 3)) (substFormula 0 z F)) := by
  rw [psi_lift_form3 F hF] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) F)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z F) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-- Y el `PSI_inst` del sondeo es su corolario INMEDIATO. `hPHI1` entra como hipotesis
    para no arrastrar aqui la cadena `liftF_CONJ` del sondeo. -/
theorem chk_PSI_inst_es_corolario (hPHI1 : liftFormula 1 PHI = PHI)
    {G : List Formula} (hpsi : PrfH G PSI3) (z : Term) :
    PrfH G (Formula.impl (lt z (.var 3)) (substFormula 0 z PHI)) :=
  PSI_inst3 PHI hPHI1 hpsi z

/-! ############################################################################
    ## §E · La copia de `pcc_eq_tracked` que SOBREVIVE en `sondeos/EvalSubstfcPrf.lean`

    ⚠️ CORRECCION DE ENCARGO: `sondeos/EvalSubsttc.lean` **ya NO** declara `pcc_eq_tracked`
    (retirada 2026-08-31; en su sitio hay un comentario). La copia que SOMBREA a
    `Meta/Sigma1AtomPrf.lean` esta viva en `sondeos/EvalSubstfcPrf.lean`, dentro de la
    copia literal del sondeo. Su enunciado se cierra con el de produccion:
    ############################################################################ -/

theorem chk_pcc_eq_tracked_dup (a b : Term) :
    Prf ((a =eq b) ⇒ provFromCode (eqCodeFn (tcFn a) (tcFn b))) :=
  ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.pcc_eq_tracked a b

/-! ############################################################################
    ## §F · ADR-019 · SUBSUNCION AL REVES: `PrfH_congr_predcT` ⊐ `prf_congr_predcT`

    El sondeo declara la congruencia de `predcT` en forma **Γ-parametrica** (`PrfH`).
    Produccion tiene solo la META (`Meta/EvalPredPrf.lean`, `prf_congr_predcT`, exportada).
    La del sondeo es ESTRICTAMENTE mas general: con `prfH_nil_to_prf` sale la de produccion.

    Consecuencia operativa (ADR-019): NO se puede dejar `PrfH_congr_predcT` en el modulo
    nuevo y reescribir `prf_congr_predcT` como corolario suyo — `EvalSubsttcPrf` importa
    `EvalPredPrf`, seria un CICLO. Hay que BAJAR la general a `Meta/EvalPredPrf.lean`
    (con `PrfH_congr_pred` y `PrfH_pred_dot_of_succ`, que la consumen) y anadirla a su
    bloque `export`. Lo mismo vale para `AX26_BODY`/`pcc_pred_succ_code`, que ya estan alli.
    ############################################################################ -/

/-- Copia LITERAL del sondeo (`EvalSubsttc`, §11). -/
theorem PrfH_congr_predcT {G : List Formula} {a b : Term} (h : PrfH G (a =eq b)) :
    PrfH G (predcT a =eq predcT b) := by
  let f : Formula := Formula.eq (predcT (liftTerm 0 a)) (predcT (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (predcT a) (predcT s) := by
    intro s
    simp only [f, predcT, funcc, cons, nil, zero, succ, substFormula, substTerm, substTerms,
      substTerm_strCode, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (predcT a)) G)

/-- La de PRODUCCION sale de la del SONDEO. (El tipo es el suyo, comprobado justo debajo.) -/
theorem chk_subsume_prf_congr_predcT {x y : Term} (h : Prf (x =eq y)) :
    Prf (predcT x =eq predcT y) :=
  prfH_nil_to_prf (PrfH_congr_predcT (prf_to_prfH h [])) rfl

/-- Y ese es EXACTAMENTE el tipo de `EvalPredPrf.prf_congr_predcT`. -/
theorem chk_tipo_de_prf_congr_predcT :
    ∀ {x y : Term}, Prf (x =eq y) → Prf (predcT x =eq predcT y) :=
  @ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_congr_predcT

end B3conx

#print axioms B3conx.PSI_inst3
#print axioms B3conx.chk_pcc_eq_tracked_dup
#print axioms B3conx.chk_prf_isTermCodeE1_of_In
#print axioms B3conx.chk_subsume_prf_congr_predcT

/-! ############################################################################
    ## §G · TRES nombres que produccion DECLARA pero NO exporta

    `Meta/CodeWitnessPrf.lean` exporta 50 nombres (42 por `SinWTs`, 8 por `ENS`). Tres de
    los que el sondeo redefine y §A/§B prueban IDENTICOS quedan FUERA de ese bloque:
    `prf_cdrc_cons`, `wfAll1Body` y `PrfH_congr_isTermCodeE1`. Al promover hay que
    cualificarlos por `SinWTs.` o anadirlos al `export` — si no, el modulo nuevo se los
    vuelve a copiar y vuelven los duplicados.
    ############################################################################ -/

section G
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-- Los TRES no resuelven a secas: no estan en el `export`. -/
example : True := by
  fail_if_success (have := @prf_cdrc_cons)
  fail_if_success (have := @wfAll1Body)
  fail_if_success (have := @PrfH_congr_isTermCodeE1)
  trivial

/-- Control POSITIVO: sus vecinos de `SinWTs`/`ENS` SI resuelven a secas. -/
example : True := by
  have _h1 := @consOk
  have _h2 := @isTC1
  have _h3 := @PrfH_congr_argsIn
  have _h4 := @hasWit
  trivial

/-- Y por el camino largo los TRES existen y son los del sondeo. -/
example : True := by
  have _h1 := @SinWTs.prf_cdrc_cons
  have _h2 := @SinWTs.wfAll1Body
  have _h3 := @SinWTs.PrfH_congr_isTermCodeE1
  trivial

end G

/-! ############################################################################
    ## §H · LOS 17 HOMONIMOS: cuando rompen y cuando no

    Medido, no supuesto:
    * Declarar un homonimo DENTRO del namespace del modulo nuevo con `LiftcCodePrf`
      abierto NO rompe: el nombre del namespace actual gana (H.1).
    * Dos namespaces ABIERTOS con el mismo nombre y tipos DISTINTOS tampoco: Lean
      desambigua por tipo (H.2).
    * Dos namespaces abiertos con el mismo nombre y **el MISMO tipo** es
      **`Ambiguous term`, ERROR DURO** (H.3). Ese es el caso de `PHI` y `PHIbody`,
      ambos `Formula`.

    CONSECUENCIA para el bloque `export` de `Meta/EvalSubsttcPrf.lean`:
    `EvalLiftcPrf` NO exporta `PHI`/`PHIbody` (ni `PHI_at`/`PHI_use`/`PHI_step`/`PHI_all`/
    `DESCENSO_imp`/`DESCENSO_lista_imp`), asi que el modulo nuevo tampoco debe exportarlos.
    `LiftcCodePrf` SI exporta los ocho `refl_*`; el nuevo puede declararlos igual, pero
    exportarlos deja dos `refl_lista_nil` en la raiz — se desambiguan por tipo, pero un
    `refine`/`exact` con metavariables lo nota. Sufijo `_stc` y no exportarlos.
    ############################################################################ -/

namespace H1
open ROBINSON_PlusPlus.Meta.LiftcCodePrf
/-- H.1 — homonimo local con `LiftcCodePrf` abierto: el local GANA, sin error. -/
theorem refl_lista_nil (v : Term) : Prf (v =eq v) := prf_refl v
theorem h1_usa_el_local (v : Term) : Prf (v =eq v) := refl_lista_nil v
theorem h1_usa_el_de_produccion : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil
end H1

section H2
open H1 ROBINSON_PlusPlus.Meta.LiftcCodePrf
/-- H.2 — dos namespaces abiertos, mismo nombre, TIPOS distintos: desambigua por tipo. -/
example : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) := refl_lista_nil
example (v : Term) : Prf (v =eq v) := refl_lista_nil v
end H2

section H3
open B3conx ROBINSON_PlusPlus.Meta.EvalLiftcPrf
/-- H.3 — mismo nombre y MISMO tipo (`Formula`): `Ambiguous term`, error duro. -/
example : True := by
  fail_if_success (have _h : Formula := PHI)
  fail_if_success (have _h : Formula := PHIbody)
  trivial
end H3

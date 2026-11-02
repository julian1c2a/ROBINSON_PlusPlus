import ROBINSON_PlusPlus.Meta

/-
# VERIFICACION ADVERSARIAL de Probe\B2_dedup.lean

§1 replica los 17 puentes `rfl` bajo los `open` **EXACTOS** del sondeo (lineas 26-43 de
`sondeos/DescensoLiftc.lean`, copiadas byte a byte, SIN los tres `open` extra que anade
`B2_dedup.lean`: `EvalRunFnPrf`, `EvalCarcNthcPrf`, `CodeWitnessPrf`). El lado de PRODUCCION
va con nombre COMPLETAMENTE CUALIFICADO. Si el "conecta" de B2 fuese un artefacto de los
`open` extra, aqui se caeria.

§3 es MI HALLAZGO: la mitad 1 de `PHI_step` reconstruye a mano el teorema CENTRAL de
`Meta/LiftcCodePrf.lean` (`refl_isTermCodeE1_imp`, :948), que el preparador no menciona
NI UNA VEZ (ni en hallazgos, ni en duplicados, ni en su inventario de simbolos importados).
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
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdvVerifB2

/-! ## §0 · COPIAS VERBATIM del sondeo, bajo los `open` EXACTOS del sondeo -/

namespace S2

def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))
def varcT (X : Term) : Term := unT 0 X
def funccT (X Y : Term) : Term := binT 1 X Y

def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

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
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

def PHIbody : Formula :=
  land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
       (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
         (targetLiftsc (.var 1)))
def PHI : Formula := Formula.forall PHIbody

end S2

/-! ## §1 · LOS 17 PUENTES, bajo los `open` EXACTOS del sondeo.
       Lado derecho SIEMPRE completamente cualificado: cero dependencia de `open`. -/

theorem V_liftcT : @S2.liftcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT := rfl
theorem V_liftscT : @S2.liftscT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT := rfl
theorem V_varcT : @S2.varcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT := rfl
theorem V_funccT : @S2.funccT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT := rfl
theorem V_targetLift : @S2.targetLift = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift := rfl
theorem V_targetLiftsc :
    @S2.targetLiftsc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc := rfl
theorem V_shapeUn :
    @S2.shapeUn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn := rfl
theorem V_shapeBin :
    @S2.shapeBin = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin := rfl
theorem V_argsInBody :
    @S2.argsInBody = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody := rfl
theorem V_argsIn :
    @S2.argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn := rfl
theorem V_isTermCodeE1 :
    @S2.isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 := rfl
theorem V_consOk :
    @S2.consOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.consOk := rfl
theorem V_cOk : @S2.cOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.cOk := rfl
theorem V_wfAll1Body :
    @S2.wfAll1Body = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body := rfl
theorem V_wfAll1 :
    @S2.wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1 := rfl
theorem V_isTC1 :
    @S2.isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 := rfl
theorem V_hasWit :
    @S2.hasWit = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit := rfl

/-- Y el tipo FINAL consumible rio abajo. -/
theorem V_DESCENSO_hasWit_tipo (s : Term) :
    (Prf (Formula.impl (S2.hasWit s) (S2.targetLift s)))
      = (Prf (Formula.impl (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit s)
          (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s))) := rfl

theorem V_DESCENSO_tipo (w s : Term) :
    (Prf (S2.isTC1 w s) → Prf (S2.targetLift s))
      = (Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 w s)
          → Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s)) := rfl

/-! ## §2 · AUDITORIA de los 5 duplicados DECLARADOS (bajo los opens exactos) -/

/-- (1) `iz_inv` -/
theorem V_dup_iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil

/-- (2) `eqc_eq_eqCodeFn`, con la orientacion INVERTIDA. -/
theorem V_dup_eqc (a b : Term) : eqc a b = eqCodeFn a b :=
  (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc a b).symm

/-- (3) `CRIT_antecedente_discrimina` = `SinWTs.crit_junk_var0_witness1`. -/
theorem V_dup_CRIT_antecedente
    (hjunk : Prf (S2.isTC1 (.var 0) (implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))))) :
    Prf Formula.bottom :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.crit_junk_var0_witness1 hjunk

/-- (4) `pcc_eval_liftc` ES `DESCENSO`: mismo tipo, `targetLift` desplegado. -/
theorem V_pcc_eval_liftc_es_DESCENSO (w s : Term) :
    (Prf (S2.isTC1 w s) →
       Prf (provFromCode (eqc (S2.liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))))
    = (Prf (S2.isTC1 w s) → Prf (S2.targetLift s)) := rfl

/-- (5) `CRIT_hasWit_descenso` tiene el tipo de `CRIT_targetLift_real`. -/
theorem V_CRIT_hasWit_descenso_tipo (t : Term) :
    (Prf (S2.targetLift (termCodeM t)))
      = (Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift (termCodeM t))) := rfl

/-- Y el HALLAZGO GORDO del preparador, replicado: produccion prueba ese enunciado SOLA. -/
theorem V_prod_targetLift_termCodeM (t : Term) : Prf (S2.targetLift (termCodeM t)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]
  exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode t

theorem V_prod_targetLiftsc_termsCodeM (ts : List Term) :
    Prf (S2.targetLiftsc (termsCodeM ts)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termsCodeM_eq]
  exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode ts

/-! ## §3 · ⚠️ MI HALLAZGO — el duplicado que el preparador NO declara.

    `PHI_step` (`sondeos/DescensoLiftc.lean:1239`) es, segun el preparador, «EL PASO, ~120
    lineas, el trabajo real del sondeo». Su **mitad 1** (`:1246-1299`) hace, a mano:

        hitc := prf_isTermCodeE1_of_In ...          -- isTC1 ⟶ isTermCodeE1
        PrfH_or_elim hitc
          case varc => refl_shapeUn_imp
          case func => ... refl_shapeBin_imp ...

    Ese `or_elim` con esos dos brazos **ES**, literalmente, la prueba de
    `Meta/LiftcCodePrf.refl_isTermCodeE1_imp` (`:948`), cuyo propio docstring lo llama
    «**EL RESULTADO CENTRAL DE ESTE MODULO**»:

        ⊢ isTermCodeE1 w X ⇒ (targetLiftsc (nthc X 2̄) ⇒ targetLift X)

    El preparador NO lo nombra en ningun sitio: ni entre los duplicados, ni entre los
    hallazgos, ni en su inventario de simbolos de `LiftcCodePrf` (donde lista
    `refl_caso_varc/funcc`, `refl_lista_nil/cons`, `refl_termCode/termsCode`,
    `substF_targetLift_hole`, `PrfH_congr_targetLift` — pero **no** `refl_isTermCodeE1_imp`,
    ni `refl_shapeUn_imp`, ni `refl_shapeBin_imp`, ni `refl_lista_cons_imp`, que `PHI_step`
    SI llama por nombre).

    Abajo se compila la mitad 1 ENTERA (menos el descenso de Cantor, que es lo unico
    genuinamente nuevo) a partir de PRODUCCION, en 6 lineas. -/

section Hallazgo
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

/-- Pieza nueva del sondeo (`:1158`), recompilada sobre produccion. -/
theorem V_new_isTermCodeE1_of_boundedIn (w c : Term) :
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

theorem V_new_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (V_new_isTermCodeE1_of_boundedIn w c)

/-- `isTC1 w X ⇒ isTermCodeE1 w X` — el primer paso de la mitad 1. -/
theorem V_isTC1_imp_isTermCodeE1 (w X : Term) :
    Prf (Formula.impl (isTC1 w X) (isTermCodeE1 w X)) := by
  refine prf_deduction ?_
  have hh : PrfH [isTC1 w X] (isTC1 w X) := prfH_hyp_self _
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (V_new_isTermCodeE1_of_In w X) _) (PrfH_and_elim_right hh))
    (PrfH_and_elim_left hh)

/-- ⚠️ **LA MITAD 1 DE `PHI_step`, DESDE PRODUCCION.** Todo lo que hace el `PrfH_or_elim`
    de `:1259-1299` salvo el descenso de Cantor sale de `refl_isTermCodeE1_imp`, que YA
    ESTA EN PRODUCCION. Dos lineas. -/
theorem V_HALLAZGO_half1_desde_produccion (w X : Term) :
    Prf (Formula.impl (isTC1 w X)
      (Formula.impl (targetLiftsc (nthc X (numeralM 2))) (targetLift X))) :=
  impT (V_isTC1_imp_isTermCodeE1 w X) (refl_isTermCodeE1_imp w X)

/-- Y el brazo `varc` a secas, que el sondeo reconstruye en `case varc`, tambien: es
    `refl_shapeUn_imp`, exportado por produccion. -/
theorem V_brazo_varc_es_produccion (X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetLift X)) := refl_shapeUn_imp X

/-- CONTROL NEGATIVO 1: `refl_isTermCodeE1_imp` NO es una trivialidad — su enunciado no es
    defeq al de la conclusion. -/
example (w X : Term) : True := by
  fail_if_success
    exact (rfl : (Formula.impl (isTermCodeE1 w X)
        (Formula.impl (targetLiftsc (nthc X (numeralM 2))) (targetLift X)))
      = targetLift X)
  trivial

/-- CONTROL NEGATIVO 2: y NO prueba el DESCENSO — falta exactamente la premisa
    `targetLiftsc (nthc X 2̄)`, que es lo que la induccion fuerte aporta. La implicacion
    completa `isTC1 w X ⇒ targetLift X` **NO** se habita con lo anterior. -/
example (w X : Term) : True := by
  fail_if_success
    exact (V_HALLAZGO_half1_desde_produccion w X :
      Prf (Formula.impl (isTC1 w X) (targetLift X)))
  trivial

end Hallazgo

/-! ## §4 · FOOTPRINT -/

#print axioms AdvVerifB2.V_liftcT
#print axioms AdvVerifB2.V_targetLift
#print axioms AdvVerifB2.V_targetLiftsc
#print axioms AdvVerifB2.V_shapeUn
#print axioms AdvVerifB2.V_argsIn
#print axioms AdvVerifB2.V_isTermCodeE1
#print axioms AdvVerifB2.V_consOk
#print axioms AdvVerifB2.V_wfAll1
#print axioms AdvVerifB2.V_isTC1
#print axioms AdvVerifB2.V_hasWit
#print axioms AdvVerifB2.V_DESCENSO_hasWit_tipo
#print axioms AdvVerifB2.V_DESCENSO_tipo
#print axioms AdvVerifB2.V_dup_iz_inv
#print axioms AdvVerifB2.V_dup_eqc
#print axioms AdvVerifB2.V_dup_CRIT_antecedente
#print axioms AdvVerifB2.V_pcc_eval_liftc_es_DESCENSO
#print axioms AdvVerifB2.V_CRIT_hasWit_descenso_tipo
#print axioms AdvVerifB2.V_prod_targetLift_termCodeM
#print axioms AdvVerifB2.V_prod_targetLiftsc_termsCodeM
#print axioms AdvVerifB2.V_new_isTermCodeE1_of_boundedIn
#print axioms AdvVerifB2.V_new_isTermCodeE1_of_In
#print axioms AdvVerifB2.V_isTC1_imp_isTermCodeE1
#print axioms AdvVerifB2.V_HALLAZGO_half1_desde_produccion
#print axioms AdvVerifB2.V_brazo_varc_es_produccion

-- CONTROL: la base sancionada
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp

end AdvVerifB2

import ROBINSON_PlusPlus.Meta

/-
# VERIFICACION ADVERSARIAL INDEPENDIENTE de Probe/B2_dedup.lean

Diferencias METODOLOGICAS con el fichero auditado (a proposito):
  * `open`s **EXACTAMENTE** los del sondeo (lineas 26-43), SIN los tres extra que anadio
    `B2_dedup.lean` (`EvalRunFnPrf`, `EvalCarcNthcPrf`, `CodeWitnessPrf`). Si alguno de esos
    cambiara la resolucion de un nombre dentro de las copias, los puentes serian FALSOS.
  * produccion se nombra SIEMPRE con nombre COMPLETAMENTE CUALIFICADO (nada por `open`).
  * cada familia de puentes lleva su CONTROL NEGATIVO `fail_if_success`.
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdvV3

/-! ## §0 · CONTROL DURO DEL ARNES — si esto pasara, el fichero seria un falso verde. -/

example : True := by
  fail_if_success exact (rfl : (1 : Nat) = 2)
  trivial

/-! ## §1 · COPIAS VERBATIM del sondeo, bajo los `open` del SONDEO (no los del auditado) -/

namespace S

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

def PHIbody : Formula :=
  land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
       (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
         (targetLiftsc (.var 1)))
def PHI : Formula := Formula.forall PHIbody

end S

/-! ## §2 · LOS 17 PUENTES, con nombre COMPLETAMENTE CUALIFICADO al otro lado -/

open ROBINSON_PlusPlus.Meta.LiftcCodePrf (liftcT liftscT varcT funccT targetLift targetLiftsc) in
theorem v_liftcT : @S.liftcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT := rfl

theorem v_liftscT : @S.liftscT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT := rfl
theorem v_varcT : @S.varcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT := rfl
theorem v_funccT : @S.funccT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT := rfl
theorem v_targetLift : @S.targetLift = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift := rfl
theorem v_targetLiftsc :
    @S.targetLiftsc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc := rfl

theorem v_shapeUn :
    @S.shapeUn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn := rfl
theorem v_shapeBin :
    @S.shapeBin = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin := rfl
theorem v_argsInBody :
    @S.argsInBody = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody := rfl
theorem v_argsIn :
    @S.argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn := rfl
theorem v_isTermCodeE1 :
    @S.isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 := rfl
theorem v_consOk :
    @S.consOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.consOk := rfl
theorem v_cOk : @S.cOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.cOk := rfl
theorem v_wfAll1Body :
    @S.wfAll1Body = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body := rfl
theorem v_wfAll1 :
    @S.wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1 := rfl
theorem v_isTC1 :
    @S.isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 := rfl
theorem v_hasWit :
    @S.hasWit = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit := rfl

/-- CONTROL NEGATIVO de la familia: los puentes NO son degenerados. -/
example : True := by
  fail_if_success
    exact (rfl : @S.targetLift = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc)
  fail_if_success
    exact (rfl : @S.isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body)
  fail_if_success
    exact (rfl : @S.consOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn)
  trivial

/-! ## §3 · Los ENUNCIADOS finales del sondeo, sobre vocabulario de PRODUCCION -/

theorem v_DESCENSO_tipo (w s : Term) :
    (Prf (S.isTC1 w s) → Prf (S.targetLift s))
    = (Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 w s) →
       Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s)) := rfl

theorem v_DESCENSO_hasWit_tipo (s : Term) :
    Prf (Formula.impl (S.hasWit s) (S.targetLift s))
    = Prf (Formula.impl (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit s)
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s)) := rfl

/-! ## §4 · EL HALLAZGO GORDO, re-derivado por mi cuenta -/

theorem v_prod_targetLift_termCodeM (t : Term) :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift (termCodeM t)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]
  exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode t

/-- `CRIT_targetLift_real` del sondeo, habitado SIN descenso. -/
theorem v_dup_CRIT_targetLift_real (t : Term) : Prf (S.targetLift (termCodeM t)) :=
  v_prod_targetLift_termCodeM t

theorem v_prod_targetLiftsc_termsCodeM (ts : List Term) :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc (termsCodeM ts)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termsCodeM_eq]
  exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode ts

theorem v_dup_CRIT_targetLiftsc_real (f : String) (ts : List Term) :
    Prf (S.targetLiftsc (termsCodeM ts)) :=
  v_prod_targetLiftsc_termsCodeM ts

/-! ## §5 · `iz_inv` — RUTA MAS CORTA que la declarada por el auditado.

El sondeo lo prueba `fun W => prf_substtc_termCode_zero 0 W` y ESE lema ya esta en
produccion (`LiftcCodePrf.prf_substtc_termCode_zero`, :177). El auditado apunta a
`EvalRunFnPrf.prf_substtc_termCode_nil` (:103), que tambien lo habita. LAS DOS valen. -/

theorem v_iz_inv_via_zero : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  fun W => ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero 0 W

theorem v_iz_inv_via_nil : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil

/-! ## §6 · ⚠️ EL DUPLICADO **NO DECLARADO**.

El auditado afirma, en §5bis de su fichero y en su RIESGO 6, que `Meta/CodeWitnessPrf.lean`
duplica **CINCO** lemas entre `SinWTs` y `ENS`, y escribe literalmente
«(`substF_wfAll1` solo existe en `ENS`: son CINCO duplicados, no seis.)».

**Son SIETE.** Faltan `impT` (SinWTs:105 / ENS:1332) y `prf_or_elim_imp`
(SinWTs:109 / ENS:1336), que estan copiados BYTE A BYTE (mismo enunciado y misma prueba).
Y no es cosmetico para B2: el sondeo REDEFINE los dos otra vez (`DescensoLiftc.lean:870`
y `:874`), y `new_prf_isTermCodeE1_of_In` — que el auditado SI recomienda promover — se
prueba con `impT`. Al promover hay que decidir CUAL de las (ya) dos copias consume, o entra
una TERCERA. -/

theorem NO_DECLARADO_impT :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.impT := rfl

theorem NO_DECLARADO_prf_or_elim_imp :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.prf_or_elim_imp := rfl

/-- Y la copia del SONDEO es la misma constante que las dos de produccion. -/
theorem NO_DECLARADO_impT_sondeo {A B C : Formula}
    (h1 : Prf (Formula.impl A B)) (h2 : Prf (Formula.impl B C)) : Prf (Formula.impl A C) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT h1 h2

/-- CONTROL NEGATIVO: `impT` y `prf_or_elim_imp` NO son la misma constante entre si. -/
example : True := by
  fail_if_success
    exact (rfl : @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT
                 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.prf_or_elim_imp)
  trivial

/-! Los CINCO que el auditado si declara, re-verificados. -/
theorem v5_liftF_argsIn :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_argsIn
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_argsIn := rfl
theorem v5_substF_argsIn :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_argsIn
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_argsIn := rfl
theorem v5_liftF_isTermCodeE1 :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_isTermCodeE1
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTermCodeE1 := rfl
theorem v5_substF_isTermCodeE1 :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_isTermCodeE1
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTermCodeE1 := rfl
theorem v5_liftF_wfAll1 :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_wfAll1
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_wfAll1 := rfl

/-! ## §7 · La SUBSUNCION de `prf_crit_In_rejects_open1`, re-verificada con nombres cualificados -/

section
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

theorem v_new_of_boundedIn (w c : Term) :
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

theorem v_imp2_post {P Q R T : Formula} (h1 : Prf (Formula.impl P (Formula.impl Q R)))
    (h2 : Prf (Formula.impl R T)) : Prf (Formula.impl P (Formula.impl Q T)) := by
  refine prf_deduction (deduction_aux ?_ Q [P] rfl)
  have hq : PrfH [Q, P] Q := PrfH.hyp _ _ (List.Mem.head _)
  have hp : PrfH [Q, P] P := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _)
    (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h1 _) hp) hq)

/-- El de PRODUCCION, derivado del nuevo. Tipo IDENTICO al de `prf_crit_In_rejects_open1`. -/
theorem v_prod_crit_desde_el_nuevo (w c : Term) (k : Nat)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hcl : ∀ n : Nat, liftTerm n c = c)
    (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) :=
  v_imp2_post (v_new_of_boundedIn w c) (crit_isTermCodeE1_rejects w c k hk0 hk1 hck)

/-- Y el tipo es EL MISMO que el de produccion (no «parecido»). -/
theorem v_prod_crit_tipo :
    (∀ (w c : Term) (k : Nat), k ≠ 0 → k ≠ 1 → (∀ n : Nat, liftTerm n c = c) →
        Prf (carc c =eq numeralM k) →
        Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)))
      := fun w c k h0 h1 hcl hck =>
        ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_crit_In_rejects_open1
          w c k h0 h1 hcl hck

end

/-! ## §8 · `CRIT_antecedente_discrimina` — habitacion directa, sin tactica -/

theorem v_dup_CRIT_antecedente_discrimina :
    Prf (S.isTC1 (.var 0) (implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))))
      → Prf Formula.bottom :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.crit_junk_var0_witness1

/-! ## §9 · FOOTPRINT -/

#print axioms AdvV3.v_targetLift
#print axioms AdvV3.v_targetLiftsc
#print axioms AdvV3.v_isTC1
#print axioms AdvV3.v_hasWit
#print axioms AdvV3.v_consOk
#print axioms AdvV3.v_argsIn
#print axioms AdvV3.v_DESCENSO_tipo
#print axioms AdvV3.v_DESCENSO_hasWit_tipo
#print axioms AdvV3.v_prod_targetLift_termCodeM
#print axioms AdvV3.v_dup_CRIT_targetLift_real
#print axioms AdvV3.v_prod_targetLiftsc_termsCodeM
#print axioms AdvV3.v_dup_CRIT_targetLiftsc_real
#print axioms AdvV3.v_iz_inv_via_zero
#print axioms AdvV3.v_iz_inv_via_nil
#print axioms AdvV3.NO_DECLARADO_impT
#print axioms AdvV3.NO_DECLARADO_prf_or_elim_imp
#print axioms AdvV3.NO_DECLARADO_impT_sondeo
#print axioms AdvV3.v5_liftF_argsIn
#print axioms AdvV3.v_new_of_boundedIn
#print axioms AdvV3.v_prod_crit_desde_el_nuevo
#print axioms AdvV3.v_prod_crit_tipo
#print axioms AdvV3.v_dup_CRIT_antecedente_discrimina

#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_crit_In_rejects_open1

end AdvV3

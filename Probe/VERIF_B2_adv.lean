import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf

/-!
# VERIFICACION ADVERSARIAL de `Probe/B2_conexion.lean`

Nada aqui se toma prestado del fichero del preparador: todos los puentes se re-escriben
CUALIFICADOS A TOPE, para que ningun `open` pueda hacer que un lado resuelva al otro.
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## §V0 · CONTROL POSITIVO/NEGATIVO DEL METODO `rfl`

Antes de creerme ningun `:= rfl`, compruebo que en ESTE fichero un `rfl` FALSO falla. -/

example : True := by
  fail_if_success
    exact (rfl : ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1
      = ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn)
  trivial

/-! ## §V1 · LOS DUPLICADOS DECLARADOS, RE-VERIFICADOS CUALIFICADOS A TOPE -/

namespace VSondeo
/-- `sondeos/DescensoLiftc.lean:56` (transcrito de nuevo desde el fichero, no del preparador). -/
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
/-- `sondeos/DescensoLiftc.lean:57` -/
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))
/-- `sondeos/DescensoLiftc.lean:79` -/
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))
/-- `sondeos/DescensoLiftc.lean:535` -/
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))
/-- `sondeos/DescensoLiftc.lean:899` -/
def isTC1 (w c : Term) : Formula :=
  land (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1 w) (In c w)
/-- `sondeos/DescensoLiftc.lean:1386` -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))
end VSondeo

theorem V_targetLift (s : Term) :
    VSondeo.targetLift s = ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s := rfl
theorem V_targetLiftsc (b : Term) :
    VSondeo.targetLiftsc b = ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc b := rfl
theorem V_isTC1 (w c : Term) :
    VSondeo.isTC1 w c = ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 w c := rfl
/-- **El TERCER duplicado que declara el preparador**, re-probado sin `open`. -/
theorem V_hasWit (c : Term) :
    VSondeo.hasWit c = ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit c := rfl

/-- CONTROL: `ENS.hasWit` y `SinWTs.isTC1` son constantes DISTINTAS, luego `V_hasWit`
    no es un `rfl` trivial de algo consigo mismo. -/
example : True := by
  fail_if_success
    exact (rfl : ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit
      = fun c => ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 (.var 0) c)
  trivial

/-! ### `iz_inv` — el puente del preparador (`BRIDGE_iz_inv`) es una TAUTOLOGIA VACIA
    (`f = f := rfl`). Aqui va el puente que SI mide algo: el enunciado LITERAL del sondeo
    (`sondeos/DescensoLiftc.lean:538`) descargado con la constante de PRODUCCION. -/
theorem V_iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil

/-- Y al reves: la de produccion sale del termino con que el sondeo prueba `iz_inv`. -/
theorem V_iz_inv_conv (W : Term) :
    Prf (substtc zero W (termCode nil) =eq termCode nil) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero 0 W

/-! ### `eqc_eq_eqCodeFn` — orientacion invertida, confirmada. -/
theorem V_eqc (a b : Term) : eqc a b = eqCodeFn a b :=
  (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc a b).symm

/-! ## §V2 · HALLAZGO 1 — `psi_lift_form` NO es trabajo nuevo: es un COROLARIO de dos
    lemas de PRODUCCION (`psi_lift_eq_subst` + `psi_at`), y en forma GENERICA. -/

theorem V_psi_lift_form_generic (Phi : Formula) (hPhi : liftFormula 1 Phi = Phi) :
    liftFormula 0 (PSI Phi) = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) Phi) := by
  rw [psi_lift_eq_subst Phi hPhi, psi_at]
  simp only [liftTerm, Nat.reduceLT, reduceIte, Nat.reduceAdd]

/-! ## §V3 · HALLAZGO 2 — `substF_targetLift` (nuevo) SUBSUME a `substF_targetLift_hole`
    (produccion, `LiftcCodePrf:790`): el de produccion es su instancia `v:=0`, `s:=#0`. -/

open ROBINSON_PlusPlus.Meta.LiftcCodePrf (targetLift targetLiftsc liftcT liftscT)

theorem V_substF_targetLift (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- El lema de PRODUCCION, re-probado como INSTANCIA del nuevo. Queda redundante al promover. -/
theorem V_hole_es_instancia (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t := by
  have h := V_substF_targetLift 0 t (.var 0)
  simpa only [targetLift, substTerm, if_true] using h

example (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole t

/-! ## §V4 · `PrfH_congr_targetLiftsc` — la Leibniz que FALTA. Control: la gemela SI existe. -/

example {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLift s)) : PrfH Γ (targetLift s') :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift h ha

/-! ## §V5 · `refl_isTermCodeE1_imp` — el «RESULTADO CENTRAL» de `LiftcCodePrf`.
    Su premisa `targetLiftsc (nthc X 2̄)` es la CONCLUSION del descenso, no su insumo:
    aqui se comprueba que su enunciado NO menciona `argsIn` ni `isTC1` en la premisa util. -/

#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp

/-! ## §V6 · FOOTPRINT -/

#print axioms V_targetLift
#print axioms V_isTC1
#print axioms V_hasWit
#print axioms V_iz_inv
#print axioms V_eqc
#print axioms V_psi_lift_form_generic
#print axioms V_hole_es_instancia

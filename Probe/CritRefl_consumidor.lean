/-
# VERIFICACION ADVERSARIAL de `Probe/Refl_consumidor.lean`.

Tres tests que el fichero auditado NO compila:

* T1/T2 — la afirmacion ESTRUCTURAL central («el ∀ anidado se consume PLANAMENTE, sin
  dotar») estaba ARGUMENTADA, no compilada. Aqui se compila: el ∀ INTERIOR (`argsIn`) y el
  EXTERIOR (`wfAll1`) se eliminan con `Prfᵢ.q1` a nivel objeto, CERO `substfc`, CERO
  `provFromCode`.
* T3 — el «RESULTADO CENTRAL» (`refl_isTermCodeE1_imp`) pide `targetLiftsc (nthc X 2̄)`
  INCONDICIONALMENTE, tambien en la rama `varc`. Aqui se compila que en esa rama el
  argumento cae sobre `nthc nil 0`, para el que NO hay axioma.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.NumListPrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace CritRefl

/-! ## §1 · COPIAS LITERALES del predicado sin-`wTs` (`Probe/CritLift_sinwts.lean:109-145`) -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

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

/-! ## §2 · T1 — EL ∀ ANIDADO **INTERIOR** SE CONSUME PLANAMENTE

    `argsIn w Y` es el `∀` acotado que, en la cara punteada, seria un `bdAllCode` DENTRO de
    otro. Aqui se elimina con la instanciacion objeto `Prfᵢ.q1`: el resultado es una formula
    LIBRE DE CUANTIFICADOR, y no aparece ni `substfc` ni `provFromCode` en ningun punto. -/

theorem CRIT_argsIn_elim (w Y i : Term) :
    Prf (Formula.impl (argsIn w Y) (Formula.impl (lt i (lenc Y)) (In (nthc Y i) w))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc Y)) [argsIn w Y] rfl)
  have hlt : PrfH [lt i (lenc Y), argsIn w Y] (lt i (lenc Y)) := PrfH.hyp _ _ (List.Mem.head _)
  have hall : PrfH [lt i (lenc Y), argsIn w Y] (argsIn w Y) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (argsInBody w Y)
      = Formula.impl (lt i (lenc Y)) (In (nthc Y i) w) := by
    simp only [argsInBody, lt, In, lenc, nthc, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (lenc Y), argsIn w Y] _
    (Prfᵢ.q1 (argsInBody w Y) i)) hall
  rw [hsubst] at h0
  exact PrfH.mp _ _ _ h0 hlt

/-! ## §3 · T2 — EL ∀ **EXTERIOR** SE CONSUME PLANAMENTE, y entrega el predicado con el
       `∀` anidado INTACTO. Tampoco aqui hay dotado de ninguna clase. -/

theorem CRIT_wfAll1_elim (w i : Term) :
    Prf (Formula.impl (wfAll1 w) (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc w)) [wfAll1 w] rfl)
  have hlt : PrfH [lt i (lenc w), wfAll1 w] (lt i (lenc w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hall : PrfH [lt i (lenc w), wfAll1 w] (wfAll1 w) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (wfAll1Body w)
      = Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i)) := by
    simp only [wfAll1Body, lt, lenc, nthc, substFormula, substF_isTermCodeE1,
      substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (lenc w), wfAll1 w] _
    (Prfᵢ.q1 (wfAll1Body w) i)) hall
  rw [hsubst] at h0
  exact PrfH.mp _ _ _ h0 hlt

/-! ### T2' · la COMPOSICION completa, tambien plana: de `isTC1` al predicado del nodo -/

theorem CRIT_isTC1_to_node (w i : Term) :
    Prf (Formula.impl (isTC1 w i) (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i)))) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (CRIT_wfAll1_elim w i) _)
    (PrfH_and_elim_left (prfH_hyp_self (isTC1 w i)))

/-! ## §4 · T3 — EL PREMISO DEL «RESULTADO CENTRAL» CAE SOBRE UN TERMINO OPACO EN LA RAMA `varc`

    `refl_isTermCodeE1_imp (w X) : isTermCodeE1 w X ⇒ (targetLiftsc (nthc X 2̄) ⇒ targetLift X)`
    pide `targetLiftsc (nthc X 2̄)` INCONDICIONALMENTE — tambien cuando `X` es un `varc`, donde
    la lista de argumentos NO EXISTE. Y en esa rama `nthc X 2̄` se reduce a `nthc nil 0`, para el
    que NO hay axioma (`ax_nthc_zero`/`ax_nthc_succ` solo disparan sobre `cons`). -/

theorem CRIT_varc_arg_opaco (n : Term) :
    Prf (nthc (varc n) (numeralM 2) =eq nthc nil zero) :=
  prf_eq_trans (prf_nthc_succ zero (cons n nil) (succ zero)) (prf_nthc_succ n nil zero)

/-- Y `nil` NO es un `cons`: es `zero`. Ninguna ecuacion de `nthc` aplica ya. -/
theorem CRIT_nil_es_zero : nil = zero := rfl

end CritRefl

#print axioms CritRefl.CRIT_argsIn_elim
#print axioms CritRefl.CRIT_wfAll1_elim
#print axioms CritRefl.CRIT_isTC1_to_node
#print axioms CritRefl.CRIT_varc_arg_opaco
#print axioms CritRefl.substF_isTermCodeE1

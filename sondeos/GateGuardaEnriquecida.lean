/-
# MEDIDA del residuo aguas abajo: ¿pasa el GATE de `prf_strong_induction` el predicado
# de `pcc_eval_substfc` ENRIQUECIDO con la guarda `hasWit s`?

Auditoria independiente. Copias LITERALES:
  * de `sondeos/ClausuraLiftSinWTs.lean`: argsInBody/argsIn/shapeUn/shapeBin/isTermCodeE1/
    wfAll1Body/wfAll1/isTC1/hasWit y liftF_argsIn/liftF_isTermCodeE1/liftF_wfAll1/liftF_isTC1.
  * de `sondeos/Paso2CasoForall.lean`: substfcT/evalSubstfcCode/liftTerm_evalSubstfcCode/
    substTerm_evalSubstfcCode y `Paso2Ind.PHI`.

    lake env lean Probe/GateEnriquecido.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace GateEnr

/-! ## §1 · COPIAS LITERALES del predicado sin-`wTs` (ClausuraLiftSinWTs.lean:109-145) -/

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

/-- «`c` TIENE testigo» — testigo CUANTIFICADO (ClausuraLiftSinWTs.lean:1389). -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

/-! ### Fontaneria De Bruijn (copias literales, ClausuraLiftSinWTs.lean:540-570, 1380-1386) -/

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

/-- **NUEVO** (no existe en `sondeos/`): `liftFormula` atraviesa `hasWit`. -/
theorem liftF_hasWit (k : Nat) (c : Term) :
    liftFormula k (hasWit c) = hasWit (liftTerm k c) := by
  simp only [hasWit, liftFormula, liftF_isTC1, liftTerm, Nat.zero_lt_succ, reduceIte,
    ← FOL.liftTerm_comm_zero]

/-! ## §2 · COPIAS LITERALES del consumidor (Paso2CasoForall.lean:84, 476-489, 689) -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

theorem liftTerm_evalSubstfcCode (k : Nat) (v s f : Term) :
    liftTerm k (evalSubstfcCode v s f)
      = evalSubstfcCode (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem substTerm_evalSubstfcCode (k : Nat) (u v s f : Term) :
    substTerm k u (evalSubstfcCode v s f)
      = evalSubstfcCode (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

/-- El `Φ` ACTUAL del consumidor, copia literal de `Paso2Ind.PHI`. SIN guarda. -/
def PHI_actual : Formula :=
  Formula.forall (Formula.forall (provFromCode (evalSubstfcCode (.var 1) (.var 0) (.var 2))))

/-! ## §3 · EL PREDICADO ENRIQUECIDO — la guarda `hasWit s` va DENTRO, sobre el `s` (`#0`) -/

def PHI_guarded : Formula :=
  Formula.forall (Formula.forall (Formula.impl (hasWit (.var 0))
    (provFromCode (evalSubstfcCode (.var 1) (.var 0) (.var 2)))))

/-- **EL GATE, SUPERADO.** `liftFormula 1 Φ = Φ` para el predicado ENRIQUECIDO:
    `prf_strong_induction` lo ADMITE. No hace falta binder nuevo (la guarda es un `∃`
    interno), luego el numero de binders exteriores NO cambia. -/
theorem PHI_guarded_lift : liftFormula 1 PHI_guarded = PHI_guarded := by
  simp only [PHI_guarded, liftFormula, liftF_hasWit, liftFormula_provFromCode_open,
    liftTerm_evalSubstfcCode, liftTerm, Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

/-! ### `substFormula` a traves de la guarda (copias + una pieza nueva) -/

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

/-- **NUEVO**: `substFormula` atraviesa `hasWit`. -/
theorem substF_hasWit (v : Nat) (s c : Term) :
    substFormula v s (hasWit c) = hasWit (substTerm v s c) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [hasWit, substFormula, substF_isTC1, substTerm, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero]

/-- Y la instancia en un codigo `t` sigue siendo la ecuacion que se quiere, con la guarda. -/
theorem PHI_guarded_at (t : Term) :
    substFormula 0 t PHI_guarded
      = Formula.forall (Formula.forall (Formula.impl (hasWit (.var 0))
          (provFromCode (evalSubstfcCode (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI_guarded, substFormula, substFormula_provFromCode_open, substF_hasWit,
    substTerm_evalSubstfcCode, substTerm, substTerms, liftTerm, liftTerms,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceGT, reduceIte,
    if_true]

/-- CONTROL: el `Φ` enriquecido NO es el actual (la guarda no es decorativa sintacticamente). -/
example : True := by
  fail_if_success exact (rfl : PHI_guarded = PHI_actual)
  trivial

/-- El gate del `Φ` ACTUAL, para comparar (copia de `Paso2Ind.PHI_lift`). -/
theorem PHI_actual_lift : liftFormula 1 PHI_actual = PHI_actual := by
  simp only [PHI_actual, liftFormula, liftFormula_provFromCode_open, liftTerm_evalSubstfcCode,
    liftTerm, Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

end GateEnr

#print axioms GateEnr.liftF_hasWit
#print axioms GateEnr.substF_hasWit
#print axioms GateEnr.PHI_guarded_lift
#print axioms GateEnr.PHI_guarded_at
#print axioms GateEnr.PHI_actual_lift
#check @GateEnr.PHI_guarded_lift
#check @GateEnr.PHI_guarded_at

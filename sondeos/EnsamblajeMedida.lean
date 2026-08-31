/- # ENS_medida — EL INVENTARIO DE ACOPLES del ensamblaje de `pcc_eval_substfc`.

   MEDICION, no construccion. Cada punto verificado por Lean, no de palabra.
   CERO axiomas de Lean, cero `sorry`, cero `axiom`.

   Contenido:
     §1  FAMILIA A  — el reconocedor FUSIONADO-POSICIONAL (`isTC1`/`hasWit`), el que
                      consumen `pcc_eval_substtc'` y los casos `∀`/`∃`.
     §2  FAMILIA B  — el reconocedor PARTIDO en tres (`isFCB3`), el unico que reconoce
                      codigos de FORMULA y el unico con no-vacuidad probada.
     §3  PUENTES `rfl` — cuales coinciden definicionalmente y cuales NO.
     §4  EL CENSO DE GUARDAS — la guarda EXACTA de cada uno de los ocho casos.
     §5  EL GATE — `liftFormula 1 Φ = Φ` para los predicados candidatos.
     §6  LOS LIFTS — cuantos binders soporta el kit de produccion.
     §7  EL PUENTE DE TESTIGOS — enunciado exacto de lo que falta.
     §8  UN CASO CERRADO DENTRO DEL ESQUEMA REAL.
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
-- Solo silencia HINTS de `simp only` con argumentos de mas (los `simp only` se
-- copiaron literalmente de los sondeos). No afecta a ningun chequeo de correccion.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ############################################################################
    # §1 · FAMILIA A — el reconocedor FUSIONADO-POSICIONAL.
    #
    # Copiado LITERALMENTE de `sondeos/Paso2Guardado.lean` §1 (namespace `SinWTs`),
    # que es el mismo texto que `sondeos/EvalSubsttc.lean` y `sondeos/DescensoLiftc.lean`.
    # UNA sola lista testigo `w`; la lista de argumentos se maneja POSICIONALMENTE
    # (`argsIn`), no con una segunda lista `wTs`.
    ############################################################################ -/

section S_FamA
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.SubstArith
open FOL

namespace FamA

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def funcOkT1 (wT X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (argsIn wT (nthc X (numeralM 2)))

def isTermCodeB1 (wT X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT1 wT X))

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

def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

/-! ### Naturalidad (copiada literalmente; hace falta para el GATE del §5) -/

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero]

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    substTerm, substTerms, nthc, cons, nil, zero, substTerm_numeralM]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    liftTerm, liftTerms, nthc, cons, nil, zero, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

theorem substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAll1, wfAll1Body, substFormula, substF_isTermCodeE1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero]

theorem substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) := by
  simp only [isTC1, land, In, substFormula, substF_wfAll1, substTerms]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerms]

theorem liftF_hasWit (k : Nat) (c : Term) :
    liftFormula k (hasWit c) = hasWit (liftTerm k c) := by
  simp only [hasWit, liftFormula, liftF_isTC1, liftTerm,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

theorem substF_hasWit (v : Nat) (s c : Term) :
    substFormula v s (hasWit c) = hasWit (substTerm v s c) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [hasWit, substFormula, substF_isTC1, substTerm, hz, hz2,
    if_false, FOL.substTerm_lift_comm_zero]

/-! ### El objetivo y su codigo (copiado de `sondeos/SubstfcPlanos.lean` §0/§4) -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

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

/-- El objetivo del encargo, con nombre corto. -/
def TGT (v s f : Term) : Formula := provFromCode (evalSubstfcCode v s f)

theorem liftF_TGT (k : Nat) (v s f : Term) :
    liftFormula k (TGT v s f) = TGT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [TGT, liftFormula_provFromCode_open, liftTerm_evalSubstfcCode]

theorem substF_TGT (k : Nat) (u v s f : Term) :
    substFormula k u (TGT v s f)
      = TGT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [TGT, substFormula_provFromCode_open, substTerm_evalSubstfcCode]

end FamA
end S_FamA

/-! ############################################################################
    # §2 · FAMILIA B — el reconocedor PARTIDO EN TRES.
    #
    # Copiado LITERALMENTE de `sondeos/ParticionTresPredicados.lean` (§1, §1580-1810)
    # y `sondeos/DiscriminaEcuacional.lean` §4 (las formas ECUACIONALES).
    # TRES listas testigo empaquetadas en un solo `p`, con accesores META.
    ############################################################################ -/

section S_FamB
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.SubstArith
open FOL

set_option linter.unusedVariables false

namespace FamB

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

/-- tag 1 (`funcc`): casilla 2 **en `wTs`** — LA SEGUNDA LISTA. -/
def funcOkT (wTs X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) wTs)

def isTermCodeB (wT wTs X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT wTs X))

def isTermsCodeB (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))

def nulOkF (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 2)) (Formula.eq (lenc X) (numeralM 1))

def unOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

def binOkF (wA wB X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) wA) (In (nthc X (numeralM 2)) wB))

def strBinOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

def isFormCodeB (wF wT wTs X : Term) : Formula :=
  lorAll (cOk X (nulOkF X))
    [ cOk X (strBinOkF wTs X 3)
    , cOk X (binOkF wT wT X 4)
    , cOk X (binOkF wF wF X 5)
    , cOk X (unOkF  wF X 6)
    , cOk X (binOkF wF wF X 7)
    , cOk X (binOkF wF wF X 8)
    , cOk X (unOkF  wF X 9) ]

def bndFF  (aF  : Term → Term) (p : Term) : Term := lenc (aF p)
def bndTgen  (aT  : Term → Term) (p : Term) : Term := lenc (aT p)
def bndTsgen (aTs : Term → Term) (p : Term) : Term := lenc (aTs p)

def wfAllF (aF aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndFF aF p)))
    (isFormCodeB (liftTerm 0 (aF p)) (liftTerm 0 (aT p)) (liftTerm 0 (aTs p))
      (nthc (liftTerm 0 (aF p)) (.var 0))))

def wfAllTgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTgen aT p)))
    (isTermCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aT p)) (.var 0))))

def wfAllTsgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTsgen aTs p)))
    (isTermsCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aTs p)) (.var 0))))

def acF  : Term → Term := carc
def acT  : Term → Term := fun p => carc (cdrc p)
def acTs : Term → Term := fun p => cdrc (cdrc p)

def tripleOk (p : Term) : Formula :=
  land (wfAllF acF acT acTs p)
       (land (wfAllTgen acT acTs p) (wfAllTsgen acT acTs p))

/-- El testigo completo: `c` es codigo de FORMULA con testigo `p`. -/
def isFCB3 (p c : Term) : Formula := land (tripleOk p) (In c (acF p))

/-! ### Las formas ECUACIONALES (de `sondeos/DiscriminaEcuacional.lean` §4) -/

def shapeNul (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) nil)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def isTermCodeE (wT wTs X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (In (nthc X (numeralM 2)) wTs))

def isFormCodeE (wF wT wTs X : Term) : Formula :=
  lorAll (shapeNul X 2)
    [ land (shapeBin X 3) (In (nthc X (numeralM 2)) wTs)
    , land (shapeBin X 4) (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))
    , land (shapeBin X 5) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeUn  X 6) (In (nthc X (numeralM 1)) wF)
    , land (shapeBin X 7) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeBin X 8) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeUn  X 9) (In (nthc X (numeralM 1)) wF) ]

end FamB
end S_FamB

/-! ############################################################################
    # §3 · LOS PUENTES `rfl` — que coincide DEFINICIONALMENTE y que NO.
    #
    # Trampa registrada: «misma definicion en dos namespaces = DOS CONSTANTES».
    # Aqui se comprueba con `rfl` compilado (positivo) o con `fail_if_success`
    # (negativo, y entonces es un obstaculo REAL al ensamblaje).
    ############################################################################ -/

section S_Puentes
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open FOL

namespace Puentes

/-! ### §3.a · LO QUE **SI** COINCIDE (net-0, `rfl`) -/

/-- El envoltorio `cons` es LITERALMENTE el mismo en las dos familias. -/
theorem br_consOk : FamA.consOk = FamB.consOk := rfl
theorem br_cOk    : FamA.cOk    = FamB.cOk    := rfl
theorem br_varOkT : FamA.varOkT = FamB.varOkT := rfl

/-- **Las formas ECUACIONALES coinciden**: `FamA.shapeUn/shapeBin` (de `SinWTs`,
    `sondeos/Paso2Guardado.lean:133`) son LA MISMA definicion que las de
    `sondeos/DiscriminaEcuacional.lean:3371`. -/
theorem br_shapeUn  : FamA.shapeUn  = FamB.shapeUn  := rfl
theorem br_shapeBin : FamA.shapeBin = FamB.shapeBin := rfl

/-- `shapeUn X 0` ES el codigo `varc`, y `shapeBin X 1` ES el codigo `funcc`
    (lema `shapeUn0_es_varc` de `sondeos/DescensoLiftc.lean:682`, revalidado aqui). -/
theorem br_shapeUn0_varc (X : Term) :
    FamA.shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem br_shapeBin1_funcc (X : Term) :
    FamA.shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

/-! ### §3.b · LO QUE **NO** COINCIDE — los dos reconocedores ESTAN DESCONECTADOS -/

/-- **NEGATIVO 1.** `FamA.funcOkT1` (posicional, `argsIn`) NO es `FamB.funcOkT`
    (segunda lista testigo `wTs`), ni siquiera identificando las dos listas. -/
example : True := by
  fail_if_success
    exact (rfl : (fun (w X : Term) => FamA.funcOkT1 w X)
                 = (fun (w X : Term) => FamB.funcOkT w X))
  trivial

/-- **NEGATIVO 2.** El reconocedor de TERMINO de la familia A no es el de la familia B. -/
example : True := by
  fail_if_success
    exact (rfl : (fun (w X : Term) => FamA.isTermCodeB1 w X)
                 = (fun (w X : Term) => FamB.isTermCodeB w w X))
  trivial

/-- **NEGATIVO 3 — EL QUE MANDA.** La forma ECUACIONAL de la familia A
    (`isTermCodeE1`, la que consume `pcc_eval_substtc'` a traves de `wfAll1`)
    NO es la forma ecuacional de la familia B (`isTermCodeE`). Difieren
    EXACTAMENTE en el segundo disyunto: `argsIn wT (nthc X 2̄)` frente a
    `In (nthc X 2̄) wTs`. -/
example : True := by
  fail_if_success
    exact (rfl : (fun (w X : Term) => FamA.isTermCodeE1 w X)
                 = (fun (w X : Term) => FamB.isTermCodeE w w X))
  trivial

/-- **NEGATIVO 4.** Y por tanto la buena-formacion de la mitad de TERMINOS del
    paquete triple NO es la buena-formacion de la familia A sobre esa misma lista. -/
example : True := by
  fail_if_success
    exact (rfl : (fun (p : Term) => FamB.wfAllTgen FamB.acT FamB.acTs p)
                 = (fun (p : Term) => FamA.wfAll1 (FamB.acT p)))
  trivial

/-- **CONTROL POSITIVO del negativo 3**: la diferencia es SOLO ese disyunto.
    Si se sustituye `argsIn wT Y` por `In Y wTs`, las dos definiciones coinciden. -/
theorem br_isTermCodeE_forma (wT wTs X : Term) :
    FamB.isTermCodeE wT wTs X
      = lor (FamA.shapeUn X 0)
            (land (FamA.shapeBin X 1) (In (nthc X (numeralM 2)) wTs)) := rfl

theorem br_isTermCodeE1_forma (wT X : Term) :
    FamA.isTermCodeE1 wT X
      = lor (FamA.shapeUn X 0)
            (land (FamA.shapeBin X 1) (FamA.argsIn wT (nthc X (numeralM 2)))) := rfl

end Puentes
end S_Puentes

/-! ############################################################################
    # §4 · EL CENSO DE GUARDAS — la guarda EXACTA de cada uno de los OCHO casos.
    #
    # Cada `def` de abajo es el TIPO LITERAL del caso correspondiente tal y como
    # esta (o NO esta) en los sondeos. Compilan todos, luego las formas son
    # bien-tipadas y se pueden diffear contra el `#check` del sondeo.
    #
    #  tag  ctor     sondeo                          GUARDA
    #  ---  -------  ------------------------------  ---------------------------
    #   2   botc     SubstfcPlanos.paso2_caso_bottom NINGUNA
    #   5   implc    SubstfcPlanos.paso2_caso_impl   NINGUNA (HI x2)
    #   7   andc     SubstfcPlanos.paso2_caso_and    NINGUNA (HI x2)
    #   8   orc      SubstfcPlanos.paso2_caso_or     NINGUNA (HI x2)
    #   6   forallc  SubstfcEx.paso2_caso_forall_g   hasWit s   (SUSTITUYENDO)
    #   9   exc      SubstfcEx.paso2_caso_ex_guarded hasWit s   (SUSTITUYENDO)
    #   4   eqc      ***NO EXISTE ENSAMBLADO***      isTC1 w a / isTC1 w b  (SUBCODIGOS)
    #   3   atomc    ***NO EXISTE ENSAMBLADO***      wfAll1 w + argsIn w ts (SUBCODIGO)
    ############################################################################ -/

section S_Censo
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open FOL FamA

namespace Censo

def unc (m : Nat) (a : Term) : Term := cons (numeralM m) (cons a nil)
def bnc (m : Nat) (a b : Term) : Term := cons (numeralM m) (cons a (cons b nil))

/-- Codigo objeto de `substtc` / `substtsc` (los que consumen `eqc` y `atomc`). -/
def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s t : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons t nil)))

/-! ### GRUPO I — SIN GUARDA (4 constructores: `botc`, `implc`, `andc`, `orc`) -/

/-- tag 2. `SubstfcPlanos.paso2_caso_bottom`. -/
def CASO_bottom : Prop := ∀ v s : Term, Prf (TGT v s botc)

/-- tags 5/7/8, genericos en el tag. `SubstfcPlanos.paso2_caso_bin` ya instanciado. -/
def CASO_bin (m : Nat) : Prop :=
  ∀ v s a b : Term, Prf (TGT v s a) → Prf (TGT v s b) → Prf (TGT v s (bnc m a b))

/-! ### GRUPO II — GUARDA `hasWit s` sobre el **SUSTITUYENDO** (2 ctores: `∀`, `∃`) -/

/-- tags 6/9, genericos en el tag. `SubstfcEx.paso2_caso_un_guarded` ya instanciado. -/
def CASO_un (m : Nat) : Prop :=
  ∀ v s f : Term,
    Prf (Formula.impl (hasWit (liftc zero s)) (TGT (succ v) (liftc zero s) f)) →
    Prf (Formula.impl (hasWit s) (TGT v s (unc m f)))

/-! ### GRUPO III — GUARDA `isTC1 w ·` sobre los **SUBCODIGOS DEL SUSTITUIDO**.
       ⚠️ **NINGUNO DE LOS DOS ESTA ENSAMBLADO.** Lo que hay es el INGREDIENTE. -/

/-- El ingrediente que SI existe: `SFsubsttc.pcc_eval_substtc'`. -/
def ING_substtc : Prop :=
  ∀ w v s t : Term, Prf (isTC1 w t) →
    Prf (provFromCode (eqCodeFn (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t))))

/-- El ingrediente que SI existe: `SFsubsttc.pcc_eval_substtsc'`. -/
def ING_substtsc : Prop :=
  ∀ w v s t : Term, Prf (wfAll1 w) → Prf (argsIn w t) →
    Prf (provFromCode (eqCodeFn (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))))

/-- tag 4, **POR ENSAMBLAR**. La guarda cae sobre los DOS subcodigos de TERMINO. -/
def CASO_eq : Prop :=
  ∀ w v s a b : Term, Prf (isTC1 w a) → Prf (isTC1 w b) → Prf (TGT v s (eqc a b))

/-- tag 3, **POR ENSAMBLAR**. La guarda cae sobre la LISTA de argumentos. -/
def CASO_atom : Prop :=
  ∀ w v s p ts : Term, Prf (wfAll1 w) → Prf (argsIn w ts) → Prf (TGT v s (atomc p ts))

/-! ### §4.a · ¿SON COMPATIBLES LAS TRES FORMAS DE GUARDA?
       **SI, y se unifican** — las tres viven en la MISMA familia A y se derivan
       todas de `isTC1`. Se comprueba aqui por `rfl` compilado. -/

/-- `hasWit` (grupo II) ES `isTC1` (grupo III) con el testigo existencializado.
    No son «dos guardas distintas»: es la misma, abierta y cerrada. -/
theorem unif_hasWit_es_isTC1 (c : Term) :
    hasWit c = Formula.ex (isTC1 (.var 0) (liftTerm 0 c)) := rfl

/-- `wfAll1` (grupo III, mitad de listas) ES la mitad izquierda de `isTC1`. -/
theorem unif_wfAll1_es_mitad (w c : Term) : isTC1 w c = land (wfAll1 w) (In c w) := rfl

/-- La guarda UNIFICADA que sirve para los tres grupos a la vez: un solo testigo `w`
    bien formado, mas las pertenencias que cada caso necesita. -/
def GuardaUnica (w s : Term) : Formula := land (wfAll1 w) (In s w)

theorem unif_guarda_unica (w s : Term) : GuardaUnica w s = isTC1 w s := rfl

/-- Y por tanto **la guarda del grupo II se DERIVA de la unica** (ex-intro). -/
theorem unif_II_desde_unica (w s : Term)
    (h : Prf (GuardaUnica w s)) : Prf (hasWit s) := by
  have hsub : substFormula 0 w (isTC1 (.var 0) (liftTerm 0 s)) = isTC1 w s := by
    simp only [substF_isTC1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact prf_ex_intro (A := isTC1 (.var 0) (liftTerm 0 s)) w (hsub ▸ h)

end Censo
end S_Censo

/-! ############################################################################
    # §5 · EL GATE — `liftFormula 1 Φ = Φ`, lo que exige `prf_strong_induction`.
    #
    # Tres candidatos:
    #   Φ1 = el que YA existe (`P2G.PHI_guarded`): guarda SOLO sobre el sustituyendo.
    #        PASA el gate — pero **no sirve**: no lleva testigo del codigo sobre el
    #        que se induce, luego el paso inductivo no puede hacer el analisis de casos.
    #   Φ2 = Φ1 + el testigo TRIPLE `isFCB3 p #3` sobre el codigo de FORMULA.
    #        Es el predicado que el ensamblaje necesita de verdad.
    #   Φ3 = idem con el testigo existencializado (sin binder para `p`).
    ############################################################################ -/

section S_Gate
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.SubstArith ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open FOL

namespace Gate

open FamA

/-! ### §5.a · NATURALIDAD DE LA FAMILIA B (nueva: no existia; hace falta para el gate) -/

theorem liftF_isTermCodeB (k : Nat) (wT wTs X : Term) :
    liftFormula k (FamB.isTermCodeB wT wTs X)
      = FamB.isTermCodeB (liftTerm k wT) (liftTerm k wTs) (liftTerm k X) := by
  simp only [FamB.isTermCodeB, FamB.cOk, FamB.consOk, FamB.varOkT, FamB.funcOkT,
    lor, land, In, carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM]

theorem liftF_isTermsCodeB (k : Nat) (wT wTs X : Term) :
    liftFormula k (FamB.isTermsCodeB wT wTs X)
      = FamB.isTermsCodeB (liftTerm k wT) (liftTerm k wTs) (liftTerm k X) := by
  simp only [FamB.isTermsCodeB, FamB.cOk, FamB.consOk, lor, land, In, carc, cdrc,
    cons, nil, zero, liftFormula, liftTerm, liftTerms]

theorem liftF_isFormCodeB (k : Nat) (wF wT wTs X : Term) :
    liftFormula k (FamB.isFormCodeB wF wT wTs X)
      = FamB.isFormCodeB (liftTerm k wF) (liftTerm k wT) (liftTerm k wTs) (liftTerm k X) := by
  simp only [FamB.isFormCodeB, FamB.lorAll, FamB.cOk, FamB.consOk, FamB.nulOkF, FamB.unOkF,
    FamB.binOkF, FamB.strBinOkF, lor, land, In, carc, cdrc, lenc, nthc, cons, nil, zero,
    liftFormula, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftT_acF  (k : Nat) (p : Term) : liftTerm k (FamB.acF p)  = FamB.acF  (liftTerm k p) := by
  simp only [FamB.acF, carc, liftTerm, liftTerms]
theorem liftT_acT  (k : Nat) (p : Term) : liftTerm k (FamB.acT p)  = FamB.acT  (liftTerm k p) := by
  simp only [FamB.acT, carc, cdrc, liftTerm, liftTerms]
theorem liftT_acTs (k : Nat) (p : Term) : liftTerm k (FamB.acTs p) = FamB.acTs (liftTerm k p) := by
  simp only [FamB.acTs, cdrc, liftTerm, liftTerms]

theorem liftF_wfAllF (k : Nat) (p : Term) :
    liftFormula k (FamB.wfAllF FamB.acF FamB.acT FamB.acTs p)
      = FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm k p) := by
  simp only [FamB.wfAllF, FamB.bndFF, liftFormula, liftF_isFormCodeB, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero,
    liftT_acF, liftT_acT, liftT_acTs]

theorem liftF_wfAllTgen (k : Nat) (p : Term) :
    liftFormula k (FamB.wfAllTgen FamB.acT FamB.acTs p)
      = FamB.wfAllTgen FamB.acT FamB.acTs (liftTerm k p) := by
  simp only [FamB.wfAllTgen, FamB.bndTgen, liftFormula, liftF_isTermCodeB, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero,
    liftT_acT, liftT_acTs]

theorem liftF_wfAllTsgen (k : Nat) (p : Term) :
    liftFormula k (FamB.wfAllTsgen FamB.acT FamB.acTs p)
      = FamB.wfAllTsgen FamB.acT FamB.acTs (liftTerm k p) := by
  simp only [FamB.wfAllTsgen, FamB.bndTsgen, liftFormula, liftF_isTermsCodeB, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero,
    liftT_acT, liftT_acTs]

theorem liftF_tripleOk (k : Nat) (p : Term) :
    liftFormula k (FamB.tripleOk p) = FamB.tripleOk (liftTerm k p) := by
  simp only [FamB.tripleOk, land, liftFormula, liftF_wfAllF, liftF_wfAllTgen, liftF_wfAllTsgen]

theorem liftF_isFCB3 (k : Nat) (p c : Term) :
    liftFormula k (FamB.isFCB3 p c) = FamB.isFCB3 (liftTerm k p) (liftTerm k c) := by
  simp only [FamB.isFCB3, land, In, liftFormula, liftF_tripleOk, liftT_acF, liftTerm, liftTerms]

/-! ### §5.b · Φ1 — EL QUE YA EXISTE. Pasa el gate, y **no basta**. -/

/-- `P2G.PHI_guarded`, copiado literalmente. `#2` = codigo, `#1` = v, `#0` = s. -/
def PHI1 : Formula :=
  Formula.forall (Formula.forall (Formula.impl (hasWit (.var 0)) (TGT (.var 1) (.var 0) (.var 2))))

/-- **GATE DE Φ1: PASA.** (Reproduce `P2G.PHI_guarded_lift`.) -/
theorem PHI1_lift : liftFormula 1 PHI1 = PHI1 := by
  simp only [PHI1, liftFormula, liftF_hasWit, liftF_TGT, liftTerm,
    Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

/-! ### §5.c · Φ2 — EL QUE HACE FALTA. `#3` = codigo, `#2` = p, `#1` = v, `#0` = s. -/

def PHI2body : Formula :=
  Formula.impl (FamB.isFCB3 (.var 2) (.var 3))
    (Formula.impl (hasWit (.var 0)) (TGT (.var 1) (.var 0) (.var 3)))

def PHI2 : Formula := Formula.forall (Formula.forall (Formula.forall PHI2body))

/-- **★ GATE DE Φ2: PASA.** El predicado triple-conjuntivo con el testigo de FORMULA
    dentro es admisible por `prf_strong_induction`. Tres binders — exactamente los
    mismos que `SFsubsttc.PHI` (`sondeos/EvalSubsttc.lean:1537`). -/
theorem PHI2_lift : liftFormula 1 PHI2 = PHI2 := by
  simp only [PHI2, PHI2body, liftFormula, liftF_isFCB3, liftF_hasWit, liftF_TGT, liftTerm,
    Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

/-! ### §5.d · Φ3 — con el testigo EXISTENCIALIZADO (sin binder exterior para `p`),
       al modo de `sondeos/GateGuardaEnriquecida.lean`. Tambien pasa. -/

def hasFWit (c : Term) : Formula := Formula.ex (FamB.isFCB3 (.var 0) (liftTerm 0 c))

theorem liftF_hasFWit (k : Nat) (c : Term) :
    liftFormula k (hasFWit c) = hasFWit (liftTerm k c) := by
  simp only [hasFWit, liftFormula, liftF_isFCB3, liftTerm,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

def PHI3 : Formula :=
  Formula.forall (Formula.forall (Formula.impl (hasFWit (.var 2))
    (Formula.impl (hasWit (.var 0)) (TGT (.var 1) (.var 0) (.var 2)))))

/-- **GATE DE Φ3: PASA.** Dos binders solamente: el testigo `p` no anade binder
    exterior porque es un `ex` INTERNO. -/
theorem PHI3_lift : liftFormula 1 PHI3 = PHI3 := by
  simp only [PHI3, liftFormula, liftF_hasFWit, liftF_hasWit, liftF_TGT, liftTerm,
    Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

end Gate
end S_Gate

/-! ############################################################################
    # §6 · LOS LIFTS — cuantos binders soporta el kit de produccion, MEDIDO.
    #
    # `sondeos/EvalSubsttc.lean` usa `FOL.substTerm_liftTerm`, `FOL.substTerm_liftLift`
    # y `SubstArith.substTerm_liftLiftLift` para TRES binders. Aqui se comprueba que
    # el predicado Φ2 (§5.c) tiene EXACTAMENTE tres binders y que por tanto **no hace
    # falta ninguna pieza nueva**: las tres especializaciones compilan.
    #
    # INVENTARIO DE PRODUCCION (`ROBINSON_PlusPlus/Meta/SubstArith.lean`):
    #   1 binder  : FOL.substTerm_liftTerm                ✅ FOL/Theorems/Eq.lean:6
    #   2 binders : FOL.substTerm_liftLift                ✅ FOL/Theorems/Eq.lean:121
    #   3 binders : SubstArith.substTerm_liftLiftLift     ✅ SubstArith.lean:72  (+ substTerms_)
    #   4 binders : SubstArith.substTerm_liftLiftLiftLift ✅ SubstArith.lean:97  (+ substTerms_)
    #   5 binders : **NO EXISTE** (grep en `ROBINSON_PlusPlus/` y en `FOL/`: 0 hits)
    ############################################################################ -/

section S_Lifts
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.SubstArith ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open FOL FamA Gate

namespace Lifts

/-! ### §6.a · Naturalidad `subst` de la familia B (espejo del §5.a) -/

theorem substF_isTermCodeB (v : Nat) (u wT wTs X : Term) :
    substFormula v u (FamB.isTermCodeB wT wTs X)
      = FamB.isTermCodeB (substTerm v u wT) (substTerm v u wTs) (substTerm v u X) := by
  simp only [FamB.isTermCodeB, FamB.cOk, FamB.consOk, FamB.varOkT, FamB.funcOkT,
    lor, land, In, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

theorem substF_isTermsCodeB (v : Nat) (u wT wTs X : Term) :
    substFormula v u (FamB.isTermsCodeB wT wTs X)
      = FamB.isTermsCodeB (substTerm v u wT) (substTerm v u wTs) (substTerm v u X) := by
  simp only [FamB.isTermsCodeB, FamB.cOk, FamB.consOk, lor, land, In, carc, cdrc,
    cons, nil, zero, substFormula, substTerm, substTerms]

theorem substF_isFormCodeB (v : Nat) (u wF wT wTs X : Term) :
    substFormula v u (FamB.isFormCodeB wF wT wTs X)
      = FamB.isFormCodeB (substTerm v u wF) (substTerm v u wT) (substTerm v u wTs)
          (substTerm v u X) := by
  simp only [FamB.isFormCodeB, FamB.lorAll, FamB.cOk, FamB.consOk, FamB.nulOkF, FamB.unOkF,
    FamB.binOkF, FamB.strBinOkF, lor, land, In, carc, cdrc, lenc, nthc, cons, nil, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM]

theorem substT_acF (v : Nat) (u p : Term) :
    substTerm v u (FamB.acF p) = FamB.acF (substTerm v u p) := by
  simp only [FamB.acF, carc, substTerm, substTerms]
theorem substT_acT (v : Nat) (u p : Term) :
    substTerm v u (FamB.acT p) = FamB.acT (substTerm v u p) := by
  simp only [FamB.acT, carc, cdrc, substTerm, substTerms]
theorem substT_acTs (v : Nat) (u p : Term) :
    substTerm v u (FamB.acTs p) = FamB.acTs (substTerm v u p) := by
  simp only [FamB.acTs, cdrc, substTerm, substTerms]

theorem substF_wfAllF (v : Nat) (u p : Term) :
    substFormula v u (FamB.wfAllF FamB.acF FamB.acT FamB.acTs p)
      = FamB.wfAllF FamB.acF FamB.acT FamB.acTs (substTerm v u p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [FamB.wfAllF, FamB.bndFF, substFormula, substF_isFormCodeB, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero, substT_acF, substT_acT, substT_acTs]

theorem substF_wfAllTgen (v : Nat) (u p : Term) :
    substFormula v u (FamB.wfAllTgen FamB.acT FamB.acTs p)
      = FamB.wfAllTgen FamB.acT FamB.acTs (substTerm v u p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [FamB.wfAllTgen, FamB.bndTgen, substFormula, substF_isTermCodeB, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero, substT_acT, substT_acTs]

theorem substF_wfAllTsgen (v : Nat) (u p : Term) :
    substFormula v u (FamB.wfAllTsgen FamB.acT FamB.acTs p)
      = FamB.wfAllTsgen FamB.acT FamB.acTs (substTerm v u p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [FamB.wfAllTsgen, FamB.bndTsgen, substFormula, substF_isTermsCodeB, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero, substT_acT, substT_acTs]

theorem substF_tripleOk (v : Nat) (u p : Term) :
    substFormula v u (FamB.tripleOk p) = FamB.tripleOk (substTerm v u p) := by
  simp only [FamB.tripleOk, land, substFormula, substF_wfAllF, substF_wfAllTgen,
    substF_wfAllTsgen]

theorem substF_isFCB3 (v : Nat) (u p c : Term) :
    substFormula v u (FamB.isFCB3 p c) = FamB.isFCB3 (substTerm v u p) (substTerm v u c) := by
  simp only [FamB.isFCB3, land, In, substFormula, substF_tripleOk, substT_acF,
    substTerm, substTerms]

/-! ### §6.b · LAS TRES ESPECIALIZACIONES DE Φ2 — cada una consume exactamente un
       lema de cancelacion de lifts, y los tres EXISTEN en produccion. -/

theorem PHI2_at (t : Term) :
    substFormula 0 t PHI2
      = Formula.forall (Formula.forall (Formula.forall
          (Formula.impl (FamB.isFCB3 (.var 2) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))
            (Formula.impl (hasWit (.var 0))
              (TGT (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))))) := by
  simp only [PHI2, PHI2body, substFormula, substF_isFCB3, substF_hasWit, substF_TGT,
    substTerm, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

/-- Especializacion del PRIMER binder (`p`). **Consume `substTerm_liftLiftLift`.** -/
theorem PHI2_spec1 (t p : Term) :
    substFormula 0 p (Formula.forall (Formula.forall
        (Formula.impl (FamB.isFCB3 (.var 2) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))
          (Formula.impl (hasWit (.var 0))
            (TGT (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))))
      = Formula.forall (Formula.forall
          (Formula.impl (FamB.isFCB3 (liftTerm 0 (liftTerm 0 p))
              (liftTerm 0 (liftTerm 0 t)))
            (Formula.impl (hasWit (.var 0))
              (TGT (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [substFormula, substF_isFCB3, substF_hasWit, substF_TGT, substTerm,
    Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

/-- Especializacion del SEGUNDO binder (`v`). **Consume `FOL.substTerm_liftLift`.** -/
theorem PHI2_spec2 (t p v : Term) :
    substFormula 0 v (Formula.forall
        (Formula.impl (FamB.isFCB3 (liftTerm 0 (liftTerm 0 p)) (liftTerm 0 (liftTerm 0 t)))
          (Formula.impl (hasWit (.var 0))
            (TGT (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall
          (Formula.impl (FamB.isFCB3 (liftTerm 0 p) (liftTerm 0 t))
            (Formula.impl (hasWit (.var 0))
              (TGT (liftTerm 0 v) (.var 0) (liftTerm 0 t)))) := by
  simp only [substFormula, substF_isFCB3, substF_hasWit, substF_TGT, substTerm,
    Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    FOL.substTerm_liftLift]

/-- Especializacion del TERCER binder (`s`). **Consume `FOL.substTerm_liftTerm`.** -/
theorem PHI2_spec3 (t p v s : Term) :
    substFormula 0 s (Formula.impl (FamB.isFCB3 (liftTerm 0 p) (liftTerm 0 t))
        (Formula.impl (hasWit (.var 0)) (TGT (liftTerm 0 v) (.var 0) (liftTerm 0 t))))
      = Formula.impl (FamB.isFCB3 p t) (Formula.impl (hasWit s) (TGT v s t)) := by
  simp only [substFormula, substF_isFCB3, substF_hasWit, substF_TGT, substTerm,
    FOL.substTerm_liftTerm, if_true]

end Lifts
end S_Lifts

/-! ############################################################################
    # §7 · EL PUENTE DE TESTIGOS y LAS OBLIGACIONES RESIDUALES.
    #
    #  (a) POSITIVO y PROBADO: el testigo del codigo PADRE **es** el testigo de cada
    #      SUBcodigo. El paquete `p` NO decrece: es INVARIANTE en el descenso.
    #  (b) POSITIVO y PROBADO: el DESCENSO bien fundado (`hijo < padre`) sale de la
    #      forma ecuacional con `prf_cantor_mono_*`, sin nada nuevo.
    #  (c) NEGATIVO: el puente A->B (`tripleOk p ⇒ wfAll1 (acT p)`) NO existe.
    #  (d) NEGATIVO: el puente a forma ECUACIONAL existe **en la direccion contraria**.
    ############################################################################ -/

section S_Puente
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open FOL

namespace Puente

/-! ### §7.a · **EL PUENTE DE TESTIGOS — EXISTE, Y ES BARATO.**

    La pregunta del encargo era: «¿del testigo del codigo PADRE sale el testigo de
    cada SUBcodigo?». La respuesta es **SI, y sin trabajo**: el testigo `p` es un
    PAQUETE DE LISTAS, no un arbol; el subcodigo esta en la MISMA lista `acF p`
    (eso es literalmente lo que dice el disyunto del reconocedor). Luego el testigo
    **no decrece y no hay que reconstruirlo**. Lo unico que cambia es el `In`. -/

/-- **PUENTE DE TESTIGOS, caso BINARIO** (tags 5/7/8; y 4 con `acT` en vez de `acF`). -/
theorem puente_testigo_bin (p c : Term) (k : Nat)
    (hrec : Prf (Formula.impl (FamB.isFCB3 p c)
      (land (FamB.shapeBin c k)
        (land (In (nthc c (numeralM 1)) (FamB.acF p))
              (In (nthc c (numeralM 2)) (FamB.acF p)))))) :
    Prf (Formula.impl (FamB.isFCB3 p c)
      (land (FamB.isFCB3 p (nthc c (numeralM 1))) (FamB.isFCB3 p (nthc c (numeralM 2))))) := by
  refine prf_deduction ?_
  have hh : PrfH [FamB.isFCB3 p c] (FamB.isFCB3 p c) := prfH_hyp_self _
  have htr : PrfH [FamB.isFCB3 p c] (FamB.tripleOk p) := PrfH_and_elim_left hh
  have hd := PrfH.mp _ _ _ (prf_to_prfH hrec _) hh
  have hm := PrfH_and_elim_right hd
  exact PrfH_and_intro
    (PrfH_and_intro htr (PrfH_and_elim_left hm))
    (PrfH_and_intro htr (PrfH_and_elim_right hm))

/-- **PUENTE DE TESTIGOS, caso UNARIO** (tags 6/9). -/
theorem puente_testigo_un (p c : Term) (k : Nat)
    (hrec : Prf (Formula.impl (FamB.isFCB3 p c)
      (land (FamB.shapeUn c k) (In (nthc c (numeralM 1)) (FamB.acF p))))) :
    Prf (Formula.impl (FamB.isFCB3 p c) (FamB.isFCB3 p (nthc c (numeralM 1)))) := by
  refine prf_deduction ?_
  have hh : PrfH [FamB.isFCB3 p c] (FamB.isFCB3 p c) := prfH_hyp_self _
  have hd := PrfH.mp _ _ _ (prf_to_prfH hrec _) hh
  exact PrfH_and_intro (PrfH_and_elim_left hh) (PrfH_and_elim_right hd)

/-- **CONTROL — EL TESTIGO ES INVARIANTE**: el paquete del hijo es el MISMO `p`
    que el del padre. (Si hubiera que reconstruirlo, esto no seria `rfl`.) -/
theorem CTRL_testigo_invariante (p c : Term) :
    FamB.isFCB3 p (nthc c (numeralM 1))
      = land (FamB.tripleOk p) (In (nthc c (numeralM 1)) (FamB.acF p)) := rfl

/-! ### §7.b · **EL DESCENSO BIEN FUNDADO — TAMBIEN EXISTE, Y ES BARATO.**
       Reproducido aqui sobre `FamB.shapeUn`/`shapeBin` (identicos por §3 a los
       `FamA.shapeUn`/`shapeBin` de `sondeos/Paso2CasoForall.lean` §7). -/

theorem descenso_un (X : Term) (k : Nat) :
    Prf (Formula.impl (FamB.shapeUn X k) (lt (nthc X (numeralM 1)) X)) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 1)) (cons (nthc X (numeralM 1)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 1)) nil)
      (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (nthc X (numeralM 1))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (FamB.shapeUn X k))) (prf_to_prfH h3 _)

theorem descenso_bin1 (X : Term) (k : Nat) :
    Prf (Formula.impl (FamB.shapeBin X k) (lt (nthc X (numeralM 1)) X)) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 1))
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) := prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_cantor_mono_right _ _
  have h3 : Prf (lt (nthc X (numeralM 1))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (FamB.shapeBin X k))) (prf_to_prfH h3 _)

theorem descenso_bin2 (X : Term) (k : Nat) :
    Prf (Formula.impl (FamB.shapeBin X k) (lt (nthc X (numeralM 2)) X)) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 2)) (cons (nthc X (numeralM 2)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 2)) nil)
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_cantor_mono_right _ _
  have h4 : Prf (lt (nthc X (numeralM 2))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) (prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2)) h3
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (FamB.shapeBin X k))) (prf_to_prfH h4 _)

/-! ### §7.c · **LA OBLIGACION RESIDUAL 1 — EL PUENTE A->B.  *** NO EXISTE. ***

    Esto es el nudo del ensamblaje. Los casos `eqc`(4) y `atomc`(3) consumen
    `pcc_eval_substtc'`, cuya guarda es `FamA.isTC1 w t = wfAll1 w ∧ In t w`.
    El testigo que trae la induccion es `FamB.isFCB3 p f`, que entrega
    `In (nthc f 1̄) (acT p)` — o sea **la mitad `In` sale GRATIS con `w := acT p`**.
    Lo que NO sale es la otra mitad, `FamA.wfAll1 (acT p)`.

    ⚠️ Y no es una diferencia cosmetica: por §3 (NEGATIVO 3/4), `FamA.isTermCodeE1`
    pide `argsIn wT (nthc X 2̄)` (∀ ACOTADO sobre las posiciones de la lista de
    argumentos, contra `wT`) mientras que `FamB.isTermCodeB` pide
    `In (nthc X 2̄) wTs` (pertenencia a la SEGUNDA lista). Pasar de lo segundo a lo
    primero exige recorrer la cadena `carc`/`cdrc` de la lista de argumentos y
    convertirla en un ∀ acotado: **una INDUCCION INTERNA nueva** sobre longitud de
    lista, dentro de `Prov`. -/

/-- **OBLIGACION RESIDUAL 1** (enunciado Lean EXACTO). -/
def PUENTE_AB : Prop :=
  ∀ p : Term, Prf (Formula.impl (FamB.tripleOk p) (FamA.wfAll1 (FamB.acT p)))

/-- Su nucleo PUNTUAL: lo que de verdad falta, quitado el ∀ acotado exterior. -/
def PUENTE_AB_puntual : Prop :=
  ∀ wT wTs X : Term,
    Prf (Formula.impl (land (FamB.isTermCodeB wT wTs X) (FamB.wfAllTsgen FamB.acT FamB.acTs
          (cons wT wTs)))
      (FamA.isTermCodeE1 wT X))

/-- Y su nucleo del nucleo: **de la cadena de pertenencias al ∀ ACOTADO**.
    Esto es una induccion nueva DENTRO de `Prov`; no hay pieza que la cubra. -/
def PUENTE_lista_a_argsIn : Prop :=
  ∀ wT wTs L : Term,
    Prf (Formula.impl (land (In L wTs) (FamB.wfAllTsgen FamB.acT FamB.acTs (cons wT wTs)))
      (FamA.argsIn wT L))

/-! ### §7.d · **LA OBLIGACION RESIDUAL 2 — EL PUENTE A FORMA ECUACIONAL.**
       ⚠️ **La pieza que hay en `sondeos/DiscriminaEcuacional.lean:3461` va en la
       direccion CONTRARIA** a la que el ensamblaje necesita:

         EXISTE  : `prf_isFormCodeE_str : isFormCodeE ⇒ isFormCodeB`   (fortalecimiento)
         HACE FALTA: `isFormCodeB ⇒ isFormCodeE`                       (calculo de la forma)

       La induccion recibe el testigo en forma `isFormCodeB` (es lo que prueba
       `prf_isFCB3_fcodes`) y necesita la ECUACION `X ≐ cons k̄ (cons a (cons b nil))`
       para poder reescribir el codigo y aplicar `paso2_caso_bin`/`_un`. -/

/-- **OBLIGACION RESIDUAL 2** (enunciado Lean EXACTO). -/
def PUENTE_ECU : Prop :=
  ∀ wF wT wTs X : Term,
    Prf (Formula.impl (FamB.isFormCodeB wF wT wTs X) (FamB.isFormCodeE wF wT wTs X))

/-- Su nucleo: de `consOk X ∧ lenc X ≐ 3̄` sale la forma de tres casillas.
    (Con `n = 1` y `n = 2` cubre los otros dos aridades.) -/
def PUENTE_ECU_puntual (n : Nat) : Prop :=
  ∀ X : Term,
    Prf (Formula.impl (land (FamB.consOk X) (Formula.eq (lenc X) (numeralM n)))
      (Formula.eq X (cons (carc X) (cdrc X))))

/-- **ALTERNATIVA MEDIDA a la obligacion 2**: en vez de probar `B ⇒ E`, redefinir el
    testigo DIRECTAMENTE en forma `E`. Es viable porque los ingredientes de no-vacuidad
    ya existen (`prf_shapeNul_real`/`prf_shapeUn_real`/`prf_shapeBin_real`, en
    `sondeos/DiscriminaEcuacional.lean:3400-3413`), y porque la DISCRIMINACION
    sobrevive (`crit_isFormCodeE_rejects`, ibid. :3494). Coste: re-probar
    `okF_fcodes`/`okT_ftcodes`/`okTs_flcodes` de `ParticionTresPredicados` en forma `E`. -/
def ALTERNATIVA_testigo_E : Prop :=
  ∀ φ : Formula, ∃ p : Term,
    Prf (land (land (FamB.wfAllF FamB.acF FamB.acT FamB.acTs p)
                    (land (FamB.wfAllTgen FamB.acT FamB.acTs p)
                          (FamB.wfAllTsgen FamB.acT FamB.acTs p)))
              (In (formCodeM φ) (FamB.acF p)))

end Puente
end S_Puente

/-! ############################################################################
    # §8 · EL ESQUEMA DE INDUCCION REAL — montado, con UN CASO CERRADO DENTRO.
    #
    # No es un boceto: es `prf_strong_induction PHI2 PHI2_lift (...)`, con el
    # analisis de casos de los OCHO constructores hecho por `prf_or_elim_land`
    # sobre `isFormCodeE`, y con la rama `botc` (tag 2) CERRADA de verdad.
    # Las otras siete quedan como hipotesis EXPLICITAS y TIPADAS.
    ############################################################################ -/

section S_Ensamblaje
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.SubstArith ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open FOL FamA Gate Lifts

namespace Ens

/-! ### §8.0 · Utilidades de logica objeto que hacen falta -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

/-- **EL COMBINADOR DEL ANALISIS DE CASOS.** Con el contexto `C` arrastrado en la
    conjuncion, el `or`-elim de los ocho disyuntos son SIETE aplicaciones de ESTE
    lema y nada mas. Es lo que evita manejar contextos `PrfH` crecientes. -/
theorem prf_or_elim_land {C A B D : Formula}
    (ha : Prf (Formula.impl (land C A) D)) (hb : Prf (Formula.impl (land C B) D)) :
    Prf (Formula.impl (land C (lor A B)) D) := by
  refine prf_deduction ?_
  have hh : PrfH [land C (lor A B)] (land C (lor A B)) := prfH_hyp_self _
  have hC : PrfH [land C (lor A B)] C := PrfH_and_elim_left hh
  refine PrfH_or_elim (PrfH_and_elim_right hh) ?_ ?_
  · exact PrfH.mp _ _ _ (prf_to_prfH ha _)
      (PrfH_and_intro (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)) |> PrfH_and_elim_left)
        (PrfH.hyp _ _ (List.Mem.head _)))
  · exact PrfH.mp _ _ _ (prf_to_prfH hb _)
      (PrfH_and_intro (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)) |> PrfH_and_elim_left)
        (PrfH.hyp _ _ (List.Mem.head _)))

/-- Leibniz en el CODIGO del objetivo (3er argumento de `evalSubstfcCode`). -/
theorem PrfH_congr_TGT {Γ : List Formula} {v s X Y : Term}
    (h : PrfH Γ (X =eq Y)) (ht : PrfH Γ (TGT v s X)) : PrfH Γ (TGT v s Y) := by
  have hS : ∀ z : Term, substFormula 0 z (TGT (liftTerm 0 v) (liftTerm 0 s) (.var 0)) = TGT v s z := by
    intro z
    simp only [substF_TGT, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y) ▸ PrfH_leibniz_subst (A := TGT (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
    ((hS X) ▸ ht)

/-- **LA INSTANCIACION COMPLETA DE Φ2** — de la conclusion de `prf_strong_induction`
    a la forma util. Los tres binders se abren con las tres cancelaciones del §6. -/
theorem PHI2_use {Γ : List Formula} (t p v s : Term) (h : PrfH Γ (substFormula 0 t PHI2)) :
    PrfH Γ (Formula.impl (FamB.isFCB3 p t) (Formula.impl (hasWit s) (TGT v s t))) := by
  rw [PHI2_at] at h
  have h1 := PrfH_spec h p
  rw [PHI2_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHI2_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHI2_spec3] at h3

/-! ### §8.1 · LA MAQUINARIA `PSI` (copiada del patron de `sondeos/EvalSubsttc.lean` §11) -/

theorem psi_l1 : liftFormula 0 (PSI PHI2)
    = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHI2) := by
  simp only [PSI, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, PHI2_lift]

theorem psi_l2 : liftFormula 0 (liftFormula 0 (PSI PHI2))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) PHI2) := by
  rw [psi_l1]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, PHI2_lift]

theorem psi_l3 : liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI2)))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) PHI2) := by
  rw [psi_l2]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, PHI2_lift]

def PSI3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI2)))

theorem PSI_inst {Γ : List Formula} (hpsi : PrfH Γ PSI3) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z PHI2)) := by
  unfold PSI3 at hpsi
  rw [psi_l3] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) PHI2)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z PHI2) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-- La HI, ya abierta a `p`, `v`, `s` y con el codigo hijo `z`. -/
theorem IH_at {Γ : List Formula} (hpsi : PrfH Γ PSI3) (z p v s : Term)
    (hlt : PrfH Γ (lt z (.var 3))) :
    PrfH Γ (Formula.impl (FamB.isFCB3 p z) (Formula.impl (hasWit s) (TGT v s z))) :=
  PHI2_use z p v s (PrfH.mp _ _ _ (PSI_inst hpsi z) hlt)

/-! ### §8.2 · EL CONTEXTO EMPAQUETADO y las OCHO RAMAS como hipotesis TIPADAS.

    `CTX` lleva las tres cosas que toda rama puede necesitar: la HI (`PSI3`), el
    testigo del codigo (`isFCB3 #2 #3`) y la guarda del sustituyendo (`hasWit #0`).
    `#3` = codigo, `#2` = testigo, `#1` = v, `#0` = s. -/

def CTX : Formula :=
  land PSI3 (land (FamB.isFCB3 (.var 2) (.var 3)) (hasWit (.var 0)))

/-- El objetivo de toda rama. -/
def GOAL : Formula := TGT (.var 1) (.var 0) (.var 3)

/-- Una RAMA es: «con el contexto y el disyunto `d`, sale el objetivo». -/
def RAMA (d : Formula) : Prop := Prf (Formula.impl (land CTX d) GOAL)

/-- Los ocho disyuntos de `isFormCodeE` sobre `#3`, con el testigo `#2`. -/
def D2 : Formula := FamB.shapeNul (.var 3) 2
def D3 : Formula := land (FamB.shapeBin (.var 3) 3)
  (In (nthc (.var 3) (numeralM 2)) (FamB.acTs (.var 2)))
def D4 : Formula := land (FamB.shapeBin (.var 3) 4)
  (land (In (nthc (.var 3) (numeralM 1)) (FamB.acT (.var 2)))
        (In (nthc (.var 3) (numeralM 2)) (FamB.acT (.var 2))))
def DBIN (k : Nat) : Formula := land (FamB.shapeBin (.var 3) k)
  (land (In (nthc (.var 3) (numeralM 1)) (FamB.acF (.var 2)))
        (In (nthc (.var 3) (numeralM 2)) (FamB.acF (.var 2))))
def DUN (k : Nat) : Formula := land (FamB.shapeUn (.var 3) k)
  (In (nthc (.var 3) (numeralM 1)) (FamB.acF (.var 2)))

/-- ✅ **CONTROL: los ocho disyuntos SON los de `isFormCodeE`** (por `rfl`). -/
theorem CTRL_disyuntos :
    FamB.isFormCodeE (FamB.acF (.var 2)) (FamB.acT (.var 2)) (FamB.acTs (.var 2)) (.var 3)
      = lor D2 (lor D3 (lor D4 (lor (DBIN 5) (lor (DUN 6)
          (lor (DBIN 7) (lor (DBIN 8) (DUN 9))))))) := rfl

/-! ### §8.3 · **LA RAMA `botc` (tag 2), CERRADA DE VERDAD DENTRO DEL ESQUEMA.** -/

/-- `shapeNul X 2` **es** `X ≐ botc`: el disyunto nulario da la ecuacion directamente. -/
theorem shapeNul2_es_botc (X : Term) : FamB.shapeNul X 2 = Formula.eq X botc := rfl

/-- **★ RAMA 2 CERRADA.** Unica hipotesis: `paso2_caso_bottom` de
    `sondeos/SubstfcPlanos.lean` (que es NET-0 y no lleva guarda). -/
theorem rama_D2 (h : Censo.CASO_bottom) : RAMA D2 := by
  refine prf_deduction ?_
  have hh : PrfH [land CTX D2] (land CTX D2) := prfH_hyp_self _
  have hd : PrfH [land CTX D2] (Formula.eq (.var 3) botc) := PrfH_and_elim_right hh
  have hb : PrfH [land CTX D2] (TGT (.var 1) (.var 0) botc) :=
    prf_to_prfH (h (.var 1) (.var 0)) _
  exact PrfH_congr_TGT (PrfH_eq_symm hd) hb

/-! ### §8.4 · **EL PASO INDUCTIVO, MODULO LAS SIETE RAMAS QUE FALTAN.** -/

/-- El puente a forma ecuacional, en la forma exacta que consume el paso. -/
def PUENTE_ECU_step : Prop := ∀ p X : Term,
  Prf (Formula.impl (FamB.isFCB3 p X)
    (FamB.isFormCodeE (FamB.acF p) (FamB.acT p) (FamB.acTs p) X))

/-- **★ EL PASO INDUCTIVO REAL**, con el analisis de los OCHO casos hecho.
    Las siete ramas que no se cierran aqui aparecen como hipotesis EXPLICITAS. -/
theorem PHI2_step (hecu : PUENTE_ECU_step)
    (r2 : RAMA D2) (r3 : RAMA D3) (r4 : RAMA D4)
    (r5 : RAMA (DBIN 5)) (r6 : RAMA (DUN 6)) (r7 : RAMA (DBIN 7))
    (r8 : RAMA (DBIN 8)) (r9 : RAMA (DUN 9)) :
    Prf (Formula.forall (Formula.impl (PSI PHI2) PHI2)) := by
  -- (1) los ocho disyuntos, combinados en UNA implicacion desde `land CTX (isFormCodeE …)`
  have hcases : Prf (Formula.impl (land CTX
      (FamB.isFormCodeE (FamB.acF (.var 2)) (FamB.acT (.var 2)) (FamB.acTs (.var 2)) (.var 3)))
      GOAL) := by
    rw [CTRL_disyuntos]
    exact prf_or_elim_land r2 (prf_or_elim_land r3 (prf_or_elim_land r4
      (prf_or_elim_land r5 (prf_or_elim_land r6
        (prf_or_elim_land r7 (prf_or_elim_land r8 r9))))))
  -- (2) del contexto sale el reconocedor en forma ecuacional
  have hctx : Prf (Formula.impl CTX GOAL) := by
    refine prf_deduction ?_
    have hh : PrfH [CTX] CTX := prfH_hyp_self _
    have hfc : PrfH [CTX] (FamB.isFCB3 (.var 2) (.var 3)) :=
      PrfH_and_elim_left (PrfH_and_elim_right hh)
    have he : PrfH [CTX] (FamB.isFormCodeE (FamB.acF (.var 2)) (FamB.acT (.var 2))
        (FamB.acTs (.var 2)) (.var 3)) :=
      PrfH.mp _ _ _ (prf_to_prfH (hecu (.var 2) (.var 3)) _) hfc
    exact PrfH.mp _ _ _ (prf_to_prfH hcases _) (PrfH_and_intro hh he)
  -- (3) y de ahi, el paso, abriendo los tres binders
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI2] (Formula.forall (Formula.forall PHI2body)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHI2body) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHI2body ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSI3] PHI2body
  refine deduction_aux ?_ (FamB.isFCB3 (.var 2) (.var 3)) [PSI3] rfl
  refine deduction_aux ?_ (hasWit (.var 0)) [FamB.isFCB3 (.var 2) (.var 3), PSI3] rfl
  have hpsi : PrfH [hasWit (.var 0), FamB.isFCB3 (.var 2) (.var 3), PSI3] PSI3 :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hfc : PrfH [hasWit (.var 0), FamB.isFCB3 (.var 2) (.var 3), PSI3]
      (FamB.isFCB3 (.var 2) (.var 3)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hg : PrfH [hasWit (.var 0), FamB.isFCB3 (.var 2) (.var 3), PSI3] (hasWit (.var 0)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  exact PrfH.mp _ _ _ (prf_to_prfH hctx _)
    (PrfH_and_intro hpsi (PrfH_and_intro hfc hg))

/-- **★ EL TEOREMA DIANA, MODULO LAS SIETE RAMAS.** Esta es la forma exacta que
    `pcc_eval_substfc` tendria: `v`, `s`, `f` ABSTRACTOS, guardado por el testigo
    del codigo (`isFCB3 p f`) y por la guarda del sustituyendo (`hasWit s`). -/
theorem pcc_eval_substfc_modulo_7 (hecu : PUENTE_ECU_step)
    (r2 : RAMA D2) (r3 : RAMA D3) (r4 : RAMA D4)
    (r5 : RAMA (DBIN 5)) (r6 : RAMA (DUN 6)) (r7 : RAMA (DBIN 7))
    (r8 : RAMA (DBIN 8)) (r9 : RAMA (DUN 9))
    (p f v s : Term) (hw : Prf (FamB.isFCB3 p f)) (hs : Prf (hasWit s)) :
    Prf (provFromCode (evalSubstfcCode v s f)) := by
  have hall : Prf (substFormula 0 f PHI2) :=
    prf_strong_induction PHI2 PHI2_lift
      (PHI2_step hecu r2 r3 r4 r5 r6 r7 r8 r9) f
  have huse := PHI2_use f p v s (prf_to_prfH hall [])
  have h1 := PrfH.mp _ _ _ huse (prf_to_prfH hw [])
  have h2 := PrfH.mp _ _ _ h1 (prf_to_prfH hs [])
  exact prfH_nil_to_prf h2 rfl

end Ens
end S_Ensamblaje

/-! ############################################################################
    # §9 · CINCO RAMAS MAS, CERRADAS DENTRO DEL ESQUEMA — y el HALLAZGO que sale
    #      de intentarlo: **los ocho casos estan en la forma `Prf → Prf`, y el paso
    #      inductivo los necesita RELATIVIZADOS a un contexto `PrfH Γ`.**
    #
    # Motivo: en el paso, la HI llega DENTRO del contexto (`PrfH Γ (TGT … hijo)`),
    # no como teorema cerrado. `paso2_caso_bottom` sobrevive porque no tiene
    # hipotesis (se sube con `prf_to_prfH`); `paso2_caso_bin` y `paso2_caso_un_guarded`
    # NO, porque sus hipotesis son `Prf`.
    #
    # Es EXACTAMENTE la conversion que `sondeos/Paso2Guardado.lean` §N ya hizo a mano
    # para el caso `∀` («reescrito ENTERO en `PrfH Gamma`»), y para la que produccion
    # ya tiene el combinador clave: `EvalCarcNthcPrf.PrfH_eq_trans_code`.
    ############################################################################ -/

section S_Ramas
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.SubstArith ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open FOL FamA Gate Lifts Ens

namespace Ramas

/-! ### §9.a · LAS FORMAS RELATIVIZADAS (lo que el paso pide de verdad) -/

/-- Caso BINARIO relativizado. Instanciado en `Γ = []` da EXACTAMENTE
    `SubstfcPlanos.paso2_caso_bin` ya especializado (ver `CTRL_bin_es_mas_fuerte`). -/
def CASO_bin_H (k : Nat) : Prop := ∀ (Γ : List Formula) (v s a b : Term),
  PrfH Γ (TGT v s a) → PrfH Γ (TGT v s b) → PrfH Γ (TGT v s (Censo.bnc k a b))

/-- Caso UNARIO relativizado (`∀` tag 6, `∃` tag 9). -/
def CASO_un_H (k : Nat) : Prop := ∀ (Γ : List Formula) (v s f : Term),
  PrfH Γ (hasWit s) →
  PrfH Γ (Formula.impl (hasWit (liftc zero s)) (TGT (succ v) (liftc zero s) f)) →
  PrfH Γ (TGT v s (Censo.unc k f))

/-- ✅ **CONTROL: la forma relativizada es MAS FUERTE.** De `CASO_bin_H k` sale el
    enunciado de los sondeos; el reciproco es lo que hay que trabajar. -/
theorem CTRL_bin_es_mas_fuerte (k : Nat) (h : CASO_bin_H k) : Censo.CASO_bin k :=
  fun v s a b ha hb =>
    prfH_nil_to_prf (h [] v s a b (prf_to_prfH ha _) (prf_to_prfH hb _)) rfl

/-- ✅ Idem para el caso unario, contra `SubstfcEx.paso2_caso_un_guarded`. -/
theorem CTRL_un_es_mas_fuerte (k : Nat) (h : CASO_un_H k) : Censo.CASO_un k :=
  fun v s f hIH =>
    prf_deduction (h [hasWit s] v s f (prfH_hyp_self _) (prf_to_prfH hIH _))

/-! ### §9.b · Extraccion del contexto empaquetado -/

section
variable {d : Formula}

theorem ctx_psi : PrfH [land CTX d] PSI3 :=
  PrfH_and_elim_left (PrfH_and_elim_left (prfH_hyp_self _))
theorem ctx_fc : PrfH [land CTX d] (FamB.isFCB3 (.var 2) (.var 3)) :=
  PrfH_and_elim_left (PrfH_and_elim_right (PrfH_and_elim_left (prfH_hyp_self _)))
theorem ctx_tr : PrfH [land CTX d] (FamB.tripleOk (.var 2)) :=
  PrfH_and_elim_left ctx_fc
theorem ctx_g : PrfH [land CTX d] (hasWit (.var 0)) :=
  PrfH_and_elim_right (PrfH_and_elim_right (PrfH_and_elim_left (prfH_hyp_self _)))
theorem ctx_d : PrfH [land CTX d] d :=
  PrfH_and_elim_right (prfH_hyp_self _)
end

/-! ### §9.c · **LAS TRES RAMAS BINARIAS PLANAS (tags 5, 7, 8), CERRADAS.** -/

theorem rama_DBIN (k : Nat) (hcase : CASO_bin_H k) : RAMA (DBIN k) := by
  refine prf_deduction ?_
  let Γ : List Formula := [land CTX (DBIN k)]
  have hd : PrfH Γ (DBIN k) := ctx_d
  have hshape : PrfH Γ (FamB.shapeBin (.var 3) k) := PrfH_and_elim_left hd
  have hin1 : PrfH Γ (In (nthc (.var 3) (numeralM 1)) (FamB.acF (.var 2))) :=
    PrfH_and_elim_left (PrfH_and_elim_right hd)
  have hin2 : PrfH Γ (In (nthc (.var 3) (numeralM 2)) (FamB.acF (.var 2))) :=
    PrfH_and_elim_right (PrfH_and_elim_right hd)
  -- (1) EL PUENTE DE TESTIGOS: el paquete `#2` sirve tambien para los dos hijos
  have hfc1 : PrfH Γ (FamB.isFCB3 (.var 2) (nthc (.var 3) (numeralM 1))) :=
    PrfH_and_intro ctx_tr hin1
  have hfc2 : PrfH Γ (FamB.isFCB3 (.var 2) (nthc (.var 3) (numeralM 2))) :=
    PrfH_and_intro ctx_tr hin2
  -- (2) EL DESCENSO: cada hijo es menor que el padre
  have hlt1 : PrfH Γ (lt (nthc (.var 3) (numeralM 1)) (.var 3)) :=
    PrfH.mp _ _ _ (prf_to_prfH (Puente.descenso_bin1 (.var 3) k) _) hshape
  have hlt2 : PrfH Γ (lt (nthc (.var 3) (numeralM 2)) (.var 3)) :=
    PrfH.mp _ _ _ (prf_to_prfH (Puente.descenso_bin2 (.var 3) k) _) hshape
  -- (3) LA HI, disparada sobre cada hijo
  have hA : PrfH Γ (TGT (.var 1) (.var 0) (nthc (.var 3) (numeralM 1))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (IH_at ctx_psi (nthc (.var 3) (numeralM 1)) (.var 2) (.var 1) (.var 0) hlt1) hfc1) ctx_g
  have hB : PrfH Γ (TGT (.var 1) (.var 0) (nthc (.var 3) (numeralM 2))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (IH_at ctx_psi (nthc (.var 3) (numeralM 2)) (.var 2) (.var 1) (.var 0) hlt2) hfc2) ctx_g
  -- (4) EL CASO, y vuelta al codigo `#3` por la forma ecuacional
  exact PrfH_congr_TGT (PrfH_eq_symm hshape)
    (hcase Γ (.var 1) (.var 0) _ _ hA hB)

/-! ### §9.d · **LAS DOS RAMAS UNARIAS (tags 6 y 9), CERRADAS.** -/

theorem rama_DUN (k : Nat) (hcase : CASO_un_H k) : RAMA (DUN k) := by
  refine prf_deduction ?_
  let Γ : List Formula := [land CTX (DUN k)]
  have hd : PrfH Γ (DUN k) := ctx_d
  have hshape : PrfH Γ (FamB.shapeUn (.var 3) k) := PrfH_and_elim_left hd
  have hin1 : PrfH Γ (In (nthc (.var 3) (numeralM 1)) (FamB.acF (.var 2))) :=
    PrfH_and_elim_right hd
  have hfc1 : PrfH Γ (FamB.isFCB3 (.var 2) (nthc (.var 3) (numeralM 1))) :=
    PrfH_and_intro ctx_tr hin1
  have hlt1 : PrfH Γ (lt (nthc (.var 3) (numeralM 1)) (.var 3)) :=
    PrfH.mp _ _ _ (prf_to_prfH (Puente.descenso_un (.var 3) k) _) hshape
  -- ⚠️ la HI se instancia con `v := σ v` y `s := liftc 0 s`, que es lo que el
  --    caso `∀`/`∃` consume. El testigo del hijo NO cambia (puente de testigos).
  have hIH : PrfH Γ (Formula.impl (hasWit (liftc zero (.var 0)))
      (TGT (succ (.var 1)) (liftc zero (.var 0)) (nthc (.var 3) (numeralM 1)))) :=
    PrfH.mp _ _ _
      (IH_at ctx_psi (nthc (.var 3) (numeralM 1)) (.var 2) (succ (.var 1))
        (liftc zero (.var 0)) hlt1) hfc1
  exact PrfH_congr_TGT (PrfH_eq_symm hshape)
    (hcase Γ (.var 1) (.var 0) _ ctx_g hIH)

/-! ### §9.e · **EL PASO INDUCTIVO, AHORA MODULO SOLO DOS RAMAS** (`atomc` y `eqc`),
       que son EXACTAMENTE las dos que caen en `substtc`/`substtsc` y por tanto las
       dos que necesitan el puente A->B del §7.c. -/

theorem PHI2_step_modulo_2 (hecu : PUENTE_ECU_step)
    (hbot : Censo.CASO_bottom)
    (hbin : ∀ k : Nat, CASO_bin_H k) (hun : ∀ k : Nat, CASO_un_H k)
    (r3 : RAMA D3) (r4 : RAMA D4) :
    Prf (Formula.forall (Formula.impl (PSI PHI2) PHI2)) :=
  PHI2_step hecu (rama_D2 hbot) r3 r4
    (rama_DBIN 5 (hbin 5)) (rama_DUN 6 (hun 6))
    (rama_DBIN 7 (hbin 7)) (rama_DBIN 8 (hbin 8)) (rama_DUN 9 (hun 9))

/-- **★★ EL TEOREMA DIANA, MODULO DOS RAMAS.**
    `pcc_eval_substfc` con `v`, `s`, `f` ABSTRACTOS queda reducido a:
      (i)   `PUENTE_ECU_step` — el puente a forma ecuacional (§7.d);
      (ii)  las seis ramas planas/unarias, en su forma RELATIVIZADA (§9.a);
      (iii) `RAMA D3` y `RAMA D4` — `atomc` y `eqc`, que requieren el puente A->B (§7.c). -/
theorem pcc_eval_substfc_modulo_2 (hecu : PUENTE_ECU_step)
    (hbot : Censo.CASO_bottom)
    (hbin : ∀ k : Nat, CASO_bin_H k) (hun : ∀ k : Nat, CASO_un_H k)
    (r3 : RAMA D3) (r4 : RAMA D4)
    (p f v s : Term) (hw : Prf (FamB.isFCB3 p f)) (hs : Prf (hasWit s)) :
    Prf (provFromCode (evalSubstfcCode v s f)) :=
  pcc_eval_substfc_modulo_7 hecu (rama_D2 hbot) r3 r4
    (rama_DBIN 5 (hbin 5)) (rama_DUN 6 (hun 6))
    (rama_DBIN 7 (hbin 7)) (rama_DBIN 8 (hbin 8)) (rama_DUN 9 (hun 9))
    p f v s hw hs

/-! ### §9.f · CONTROLES DE NO-VACUIDAD -/

/-- CONTROL NEGATIVO: el objetivo NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- CONTROL: los tags DISCRIMINAN — la parametrizacion no colapsa constructores. -/
theorem CTRL_tags_distintos (a b : Term) : Censo.bnc 5 a b ≠ Censo.bnc 7 a b := by
  intro h
  simp only [Censo.bnc, cons, numeralM, succ, zero, Term.func.injEq, List.cons.injEq,
    and_true, true_and] at h
  exact absurd h.1 (by decide)

/-- CONTROL: `DBIN 4` (el disyunto de `eqc`) NO es `DBIN k` para `k` de formula:
    su carga apunta a `acT` (lista de TERMINOS), no a `acF`. Por eso `rama_DBIN`
    no lo cubre y `RAMA D4` sigue abierta. -/
example : True := by
  fail_if_success
    exact (rfl : D4 = DBIN 4)
  trivial

end Ramas
end S_Ramas

/-! ############################################################################
    # §10 · LAS DOS RAMAS QUE FALTAN (`atomc` tag 3, `eqc` tag 4), y LA REDUCCION
    #       COMPLETA DEL ENSAMBLAJE.
    #
    # Estas dos son las unicas cuyo paso recursivo NO cae en `substfc` sino en
    # `substtc`/`substtsc`. Consumen `pcc_eval_substtc'`/`pcc_eval_substtsc'`
    # (que EXISTEN, net-0) — pero con la guarda de la FAMILIA A, y el testigo que
    # trae la induccion es de la FAMILIA B. Ahi entra, y solo ahi, el puente A->B.
    ############################################################################ -/

section S_Cierre
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.SubstArith ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open FOL FamA Gate Lifts Ens Ramas

namespace Cierre

/-! ### §10.a · Los dos puentes A->B, en la forma EXACTA que consume el paso -/

/-- De «`c` esta en la mitad de TERMINOS del paquete» a la guarda de la familia A. -/
def PUENTE_TC : Prop := ∀ p c : Term,
  Prf (Formula.impl (land (FamB.tripleOk p) (In c (FamB.acT p)))
    (FamA.isTC1 (FamB.acT p) c))

/-- De «`c` esta en la mitad de LISTAS» a la guarda de listas de la familia A. -/
def PUENTE_TSC : Prop := ∀ p c : Term,
  Prf (Formula.impl (land (FamB.tripleOk p) (In c (FamB.acTs p)))
    (land (FamA.wfAll1 (FamB.acT p)) (FamA.argsIn (FamB.acT p) c)))

/-- Lo que le falta a `PUENTE_TSC` por encima de `PUENTE_AB`: convertir la cadena de
    pertenencias `carc`/`cdrc` en el ∀ ACOTADO `argsIn`. **Induccion interna nueva.** -/
def PUENTE_ARGS : Prop := ∀ p c : Term,
  Prf (Formula.impl (land (FamB.tripleOk p) (In c (FamB.acTs p)))
    (FamA.argsIn (FamB.acT p) c))

/-- ✅ **`PUENTE_TC` SE DERIVA DE `PUENTE_AB`** — o sea, lo unico que falta en el
    caso `eqc` es EXACTAMENTE la obligacion residual 1 del §7.c, ni mas ni menos. -/
theorem PUENTE_TC_de_AB (h : Puente.PUENTE_AB) : PUENTE_TC := by
  intro p c
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (FamB.tripleOk p) (In c (FamB.acT p)))
  exact PrfH_and_intro
    (PrfH.mp _ _ _ (prf_to_prfH (h p) _) (PrfH_and_elim_left hh))
    (PrfH_and_elim_right hh)

/-- ✅ **`PUENTE_TSC` SE DERIVA DE `PUENTE_AB` + `PUENTE_ARGS`.** -/
theorem PUENTE_TSC_de (hab : Puente.PUENTE_AB) (hargs : PUENTE_ARGS) : PUENTE_TSC := by
  intro p c
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (FamB.tripleOk p) (In c (FamB.acTs p)))
  exact PrfH_and_intro
    (PrfH.mp _ _ _ (prf_to_prfH (hab p) _) (PrfH_and_elim_left hh))
    (PrfH.mp _ _ _ (prf_to_prfH (hargs p c) _) hh)

/-! ### §10.b · Los dos casos que faltan, en forma RELATIVIZADA -/

/-- tag 4. Consume `SFsubsttc.pcc_eval_substtc'` DOS veces (una por casilla). -/
def CASO_eq_H : Prop := ∀ (Γ : List Formula) (w v s a b : Term),
  PrfH Γ (FamA.isTC1 w a) → PrfH Γ (FamA.isTC1 w b) →
  PrfH Γ (TGT v s (Censo.bnc 4 a b))

/-- tag 3. Consume `SFsubsttc.pcc_eval_substtsc'` (la casilla 1 es OPACA: un `strCode`). -/
def CASO_atom_H : Prop := ∀ (Γ : List Formula) (w v s pc ts : Term),
  PrfH Γ (FamA.wfAll1 w) → PrfH Γ (FamA.argsIn w ts) →
  PrfH Γ (TGT v s (Censo.bnc 3 pc ts))

/-- ✅ CONTROL: `bnc 4` ES `eqc` y `bnc 3` ES `atomc` (por `rfl`). -/
theorem CTRL_bnc4_eqc (a b : Term) : Censo.bnc 4 a b = eqc a b := rfl
theorem CTRL_bnc3_atomc (a b : Term) : Censo.bnc 3 a b = atomc a b := rfl

/-! ### §10.c · **LAS DOS RAMAS, CERRADAS** (modulo los puentes y los dos casos) -/

theorem rama_D4 (hp : PUENTE_TC) (hcase : CASO_eq_H) : RAMA D4 := by
  refine prf_deduction ?_
  have hd : PrfH [land CTX D4] D4 := ctx_d
  have hshape : PrfH [land CTX D4] (FamB.shapeBin (.var 3) 4) := PrfH_and_elim_left hd
  have hin1 : PrfH [land CTX D4] (In (nthc (.var 3) (numeralM 1)) (FamB.acT (.var 2))) :=
    PrfH_and_elim_left (PrfH_and_elim_right hd)
  have hin2 : PrfH [land CTX D4] (In (nthc (.var 3) (numeralM 2)) (FamB.acT (.var 2))) :=
    PrfH_and_elim_right (PrfH_and_elim_right hd)
  have h1 : PrfH [land CTX D4]
      (FamA.isTC1 (FamB.acT (.var 2)) (nthc (.var 3) (numeralM 1))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hp (.var 2) (nthc (.var 3) (numeralM 1))) _)
      (PrfH_and_intro ctx_tr hin1)
  have h2 : PrfH [land CTX D4]
      (FamA.isTC1 (FamB.acT (.var 2)) (nthc (.var 3) (numeralM 2))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hp (.var 2) (nthc (.var 3) (numeralM 2))) _)
      (PrfH_and_intro ctx_tr hin2)
  exact PrfH_congr_TGT (PrfH_eq_symm hshape)
    (hcase _ (FamB.acT (.var 2)) (.var 1) (.var 0) _ _ h1 h2)

theorem rama_D3 (hp : PUENTE_TSC) (hcase : CASO_atom_H) : RAMA D3 := by
  refine prf_deduction ?_
  have hd : PrfH [land CTX D3] D3 := ctx_d
  have hshape : PrfH [land CTX D3] (FamB.shapeBin (.var 3) 3) := PrfH_and_elim_left hd
  have hin2 : PrfH [land CTX D3] (In (nthc (.var 3) (numeralM 2)) (FamB.acTs (.var 2))) :=
    PrfH_and_elim_right hd
  have hb : PrfH [land CTX D3]
      (land (FamA.wfAll1 (FamB.acT (.var 2)))
            (FamA.argsIn (FamB.acT (.var 2)) (nthc (.var 3) (numeralM 2)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hp (.var 2) (nthc (.var 3) (numeralM 2))) _)
      (PrfH_and_intro ctx_tr hin2)
  exact PrfH_congr_TGT (PrfH_eq_symm hshape)
    (hcase _ (FamB.acT (.var 2)) (.var 1) (.var 0) _ _
      (PrfH_and_elim_left hb) (PrfH_and_elim_right hb))

/-! ### §10.d · ★★★ **LA REDUCCION COMPLETA DEL ENSAMBLAJE** ★★★

    Ocho ramas, cero `sorry`, cero axiomas. Todo lo que queda de `pcc_eval_substfc`
    esta en las hipotesis de este teorema, y son EXACTAMENTE:

      A · UN puente de reconocedor      : `hecu`  (§7.d — la direccion CONTRARIA a la
                                          que hay en produccion)
      B · DOS puentes A->B              : `hab` (§7.c) + `hargs` (§10.a)
      C · SEIS casos ya PROBADOS pero en la forma equivocada: hay que RELATIVIZARLOS
          a `PrfH Γ` (`hbot` va tal cual porque no tiene hipotesis)
      D · DOS casos SIN ENSAMBLAR       : `heq`, `hatom` (los ingredientes existen)

    NO queda nada mas: ni gate, ni lifts, ni descenso, ni puente de testigos. -/

theorem pcc_eval_substfc_REDUCIDO
    -- A · el puente a forma ecuacional
    (hecu : PUENTE_ECU_step)
    -- B · los dos puentes familia B -> familia A
    (hab : Puente.PUENTE_AB) (hargs : PUENTE_ARGS)
    -- C · los seis casos ya probados, relativizados
    (hbot : Censo.CASO_bottom)
    (hbin : ∀ k : Nat, CASO_bin_H k) (hun : ∀ k : Nat, CASO_un_H k)
    -- D · los dos casos por ensamblar
    (heq : CASO_eq_H) (hatom : CASO_atom_H)
    -- y el enunciado: `v`, `s`, `f` ABSTRACTOS
    (p f v s : Term) (hw : Prf (FamB.isFCB3 p f)) (hs : Prf (hasWit s)) :
    Prf (provFromCode (evalSubstfcCode v s f)) :=
  pcc_eval_substfc_modulo_2 hecu hbot hbin hun
    (rama_D3 (PUENTE_TSC_de hab hargs) hatom)
    (rama_D4 (PUENTE_TC_de_AB hab) heq)
    p f v s hw hs

/-- **CONTROL DE NO-VACUIDAD DEL ENUNCIADO**: la conclusion es la del encargo,
    literalmente `provFromCode (eqc (substfcT v̇ ṡ ḟ) (substfc v s f)˙)`. -/
theorem CTRL_conclusion (v s f : Term) :
    provFromCode (evalSubstfcCode v s f)
      = provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f))
          (tcFn (substfc v s f))) := rfl

end Cierre
end S_Cierre

/-! ############################################################################
    # FOOTPRINT
    ############################################################################ -/

#print axioms Puentes.br_shapeUn
#print axioms Puentes.br_shapeBin
#print axioms Censo.unif_II_desde_unica
#print axioms Gate.PHI1_lift
#print axioms Gate.PHI2_lift
#print axioms Gate.PHI3_lift
#print axioms Lifts.PHI2_spec1
#print axioms Lifts.PHI2_spec2
#print axioms Lifts.PHI2_spec3
#print axioms Puente.puente_testigo_bin
#print axioms Puente.puente_testigo_un
#print axioms Puente.descenso_un
#print axioms Puente.descenso_bin1
#print axioms Puente.descenso_bin2
#print axioms Ens.prf_or_elim_land
#print axioms Ens.PrfH_congr_TGT
#print axioms Ens.PHI2_use
#print axioms Ens.CTRL_disyuntos
#print axioms Ens.rama_D2
#print axioms Ens.PHI2_step
#print axioms Ens.pcc_eval_substfc_modulo_7
#print axioms Ramas.CTRL_bin_es_mas_fuerte
#print axioms Ramas.CTRL_un_es_mas_fuerte
#print axioms Ramas.rama_DBIN
#print axioms Ramas.rama_DUN
#print axioms Ramas.pcc_eval_substfc_modulo_2
#print axioms Cierre.PUENTE_TC_de_AB
#print axioms Cierre.PUENTE_TSC_de
#print axioms Cierre.rama_D3
#print axioms Cierre.rama_D4
#print axioms Cierre.pcc_eval_substfc_REDUCIDO

/-! ## ENUNCIADOS EXACTOS -/

#check @Ens.pcc_eval_substfc_modulo_7
#check @Ramas.pcc_eval_substfc_modulo_2
#check @Cierre.pcc_eval_substfc_REDUCIDO
#check @Puente.PUENTE_AB
#check @Puente.PUENTE_ECU
#check @Cierre.PUENTE_ARGS
#check @Ramas.CASO_bin_H
#check @Ramas.CASO_un_H
#check @Cierre.CASO_eq_H
#check @Cierre.CASO_atom_H
#check @Ens.PUENTE_ECU_step

/-! ############################################################################
    # §11 · LA MITAD BARATA DEL PUENTE `PUENTE_ECU_step`, **PROBADA AQUI**.
    #
    # `PUENTE_ECU_step` se parte en dos:
    #   (i)  `isFCB3 p c ⇒ isFormCodeB (acF p) (acT p) (acTs p) c`  — de la PERTENENCIA
    #        al RECONOCEDOR. Transposicion exacta de `prf_isTermCodeE1_of_In`
    #        (`sondeos/DescensoLiftc.lean:1183`). **SE PRUEBA AQUI, con `p` y `c`
    #        ABSTRACTOS (ni uno ni otro cerrado).**
    #   (ii) `isFormCodeB ⇒ isFormCodeE` — LA OBLIGACION RESIDUAL 2 (§7.d).
    ############################################################################ -/

section S_Mitad
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.SubstArith ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.BoundedInPrf
open FOL Gate Lifts Ens

namespace Mitad

/-- Leibniz en el codigo (4o argumento) de `isFormCodeB`. -/
theorem PrfH_congr_isFormCodeB {Γ : List Formula} {wF wT wTs X Y : Term}
    (h : PrfH Γ (X =eq Y)) (hi : PrfH Γ (FamB.isFormCodeB wF wT wTs X)) :
    PrfH Γ (FamB.isFormCodeB wF wT wTs Y) := by
  have hS : ∀ z : Term, substFormula 0 z (FamB.isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT)
      (liftTerm 0 wTs) (.var 0)) = FamB.isFormCodeB wF wT wTs z := by
    intro z
    simp only [substF_isFormCodeB, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y) ▸ PrfH_leibniz_subst
    (A := FamB.isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
    h ((hS X) ▸ hi)

/-- Instanciacion del ∀ acotado `wfAllF` en un indice CUALQUIERA (`p` puede ser abierto). -/
theorem PrfH_inst_wfAllF {Γ : List Formula} (p i : Term)
    (h : PrfH Γ (FamB.wfAllF FamB.acF FamB.acT FamB.acTs p)) :
    PrfH Γ (Formula.impl (lt i (lenc (FamB.acF p)))
      (FamB.isFormCodeB (FamB.acF p) (FamB.acT p) (FamB.acTs p) (nthc (FamB.acF p) i))) := by
  have hs := PrfH_spec h i
  simpa only [FamB.wfAllF, FamB.bndFF, substFormula, substF_isFormCodeB, lt, lenc, nthc,
    substTerm, substTerms, FOL.substTerm_liftTerm, if_true, substT_acF, substT_acT,
    substT_acTs] using hs

/-- **★ LA MITAD (i), PROBADA** — con `p` y `c` ABSTRACTOS. -/
theorem prf_isFormCodeB_of_boundedIn (p c : Term) :
    Prf (Formula.impl (boundedIn c (FamB.acF p))
      (Formula.impl (FamB.wfAllF FamB.acF FamB.acT FamB.acTs p)
        (FamB.isFormCodeB (FamB.acF p) (FamB.acT p) (FamB.acTs p) c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAllF, liftF_isFormCodeB, liftT_acF, liftT_acT, liftT_acTs]
  refine deduction_aux ?_ (FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm 0 p)) _ rfl
  have hwf : PrfH [FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (FamB.acF p))))
        (Formula.eq (nthc (liftTerm 0 (FamB.acF p)) (.var 0)) (liftTerm 0 c))]
      (FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm 0 p)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (FamB.acF p))))
        (Formula.eq (nthc (liftTerm 0 (FamB.acF p)) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc (FamB.acF p))))
        (Formula.eq (nthc (liftTerm 0 (FamB.acF p)) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (FamB.acF p))))
        (Formula.eq (nthc (liftTerm 0 (FamB.acF p)) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (FamB.acF (liftTerm 0 p)))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms, liftT_acF] using h
  have heq : PrfH [FamB.wfAllF FamB.acF FamB.acT FamB.acTs (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (FamB.acF p))))
        (Formula.eq (nthc (liftTerm 0 (FamB.acF p)) (.var 0)) (liftTerm 0 c))]
      (Formula.eq (nthc (FamB.acF (liftTerm 0 p)) (.var 0)) (liftTerm 0 c)) := by
    have h := PrfH_and_elim_right hbody
    simpa only [nthc, liftTerm, liftTerms, liftT_acF] using h
  exact PrfH_congr_isFormCodeB heq
    (PrfH.mp _ _ _ (PrfH_inst_wfAllF (liftTerm 0 p) (.var 0) hwf) hlt)

/-- **★ LA MITAD (i), en la forma que consume el paso.** -/
theorem prf_isFormCodeB_of_isFCB3 (p c : Term) :
    Prf (Formula.impl (FamB.isFCB3 p c)
      (FamB.isFormCodeB (FamB.acF p) (FamB.acT p) (FamB.acTs p) c)) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (FamB.isFCB3 p c)
  have hwf : PrfH [FamB.isFCB3 p c] (FamB.wfAllF FamB.acF FamB.acT FamB.acTs p) :=
    PrfH_and_elim_left (PrfH_and_elim_left hh)
  have hin : PrfH [FamB.isFCB3 p c] (In c (FamB.acF p)) := PrfH_and_elim_right hh
  have hbd : PrfH [FamB.isFCB3 p c] (boundedIn c (FamB.acF p)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In c (FamB.acF p)) _) hin
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (prf_isFormCodeB_of_boundedIn p c) _) hbd) hwf

/-- **★★ EL PUENTE DEL PASO SE REDUCE A LA OBLIGACION RESIDUAL 2 Y NADA MAS.** -/
theorem PUENTE_ECU_step_de_PUENTE_ECU (h : Puente.PUENTE_ECU) : PUENTE_ECU_step :=
  fun p X => Ens.impT (prf_isFormCodeB_of_isFCB3 p X)
    (h (FamB.acF p) (FamB.acT p) (FamB.acTs p) X)

/-! ### §11.b · ★★★ **LA REDUCCION FINAL** ★★★ -/

theorem pcc_eval_substfc_FINAL
    -- (1) el UNICO puente de reconocedor que falta: `isFormCodeB ⇒ isFormCodeE`
    (hecu : Puente.PUENTE_ECU)
    -- (2) los DOS puentes familia B -> familia A
    (hab : Puente.PUENTE_AB) (hargs : Cierre.PUENTE_ARGS)
    -- (3) los SEIS casos ya probados (uno tal cual, cinco a relativizar)
    (hbot : Censo.CASO_bottom)
    (hbin : ∀ k : Nat, Ramas.CASO_bin_H k) (hun : ∀ k : Nat, Ramas.CASO_un_H k)
    -- (4) los DOS casos por ensamblar
    (heq : Cierre.CASO_eq_H) (hatom : Cierre.CASO_atom_H)
    (p f v s : Term) (hw : Prf (FamB.isFCB3 p f)) (hs : Prf (FamA.hasWit s)) :
    Prf (provFromCode (FamA.evalSubstfcCode v s f)) :=
  Cierre.pcc_eval_substfc_REDUCIDO (PUENTE_ECU_step_de_PUENTE_ECU hecu)
    hab hargs hbot hbin hun heq hatom p f v s hw hs

end Mitad
end S_Mitad

#print axioms Mitad.prf_isFormCodeB_of_boundedIn
#print axioms Mitad.prf_isFormCodeB_of_isFCB3
#print axioms Mitad.PUENTE_ECU_step_de_PUENTE_ECU
#print axioms Mitad.pcc_eval_substfc_FINAL
#check @Mitad.prf_isFormCodeB_of_isFCB3
#check @Mitad.pcc_eval_substfc_FINAL

/-! ############################################################################
    # §12 · VEREDICTO DE LA MEDICION  (todo lo de arriba COMPILA, net-0)
    #
    # ── LO QUE **NO** ES OBSTACULO (medido, no supuesto) ──────────────────────
    #  · EL GATE.  `liftFormula 1 Φ = Φ` PASA para el predicado que hace falta
    #    (`Gate.PHI2_lift`), con el testigo de FORMULA dentro. Tres binders, los
    #    mismos que `SFsubsttc.PHI`. Tambien pasa la variante existencial (Φ3).
    #  · LOS LIFTS. Con tres binders basta `substTerm_liftLiftLift`, que existe.
    #    El techo de produccion son CUATRO. No hay que escribir nada nuevo.
    #  · EL PUENTE DE TESTIGOS. El paquete `p` es INVARIANTE en el descenso: el
    #    subcodigo esta en la MISMA lista. `Puente.puente_testigo_bin/_un`.
    #  · EL DESCENSO BIEN FUNDADO. `Puente.descenso_un/_bin1/_bin2`, de la forma
    #    ecuacional con `prf_cantor_mono_*`. Nada nuevo.
    #  · LAS GUARDAS SON COMPATIBLES Y SE UNIFICAN. Las tres formas que circulaban
    #    (sin guarda / `hasWit s` / `isTC1 w t`) son la MISMA familia A:
    #    `hasWit c = ∃w. isTC1 w c` y `isTC1 w c = wfAll1 w ∧ In c w` (§4.a, `rfl`).
    #    NO hacen falta dos testigos distintos ni un testigo comun.
    #  · «DE LA PERTENENCIA AL RECONOCEDOR» con `p` y `c` ABIERTOS:
    #    `Mitad.prf_isFormCodeB_of_isFCB3`, probado aqui.
    #
    # ── LO QUE **SI** ES OBSTACULO (cinco piezas, todas con enunciado exacto) ──
    #  1. `Puente.PUENTE_ECU`  : `isFormCodeB ⇒ isFormCodeE`.
    #     ⚠️ En produccion esta LA DIRECCION CONTRARIA (`prf_isFormCodeE_str`,
    #        `sondeos/DiscriminaEcuacional.lean:3461`). La induccion recibe `B` y
    #        necesita `E`. Alternativa medida: redefinir el testigo en forma `E`
    #        (los ingredientes de no-vacuidad y de discriminacion ya existen).
    #  2. `Puente.PUENTE_AB`   : `tripleOk p ⇒ wfAll1 (acT p)`.
    #     LOS DOS RECONOCEDORES ESTAN DESCONECTADOS — probado por `fail_if_success`
    #     en §3 (NEGATIVOS 1-4): `argsIn wT ·` (familia A, posicional) frente a
    #     `In · wTs` (familia B, segunda lista).
    #  3. `Cierre.PUENTE_ARGS` : de la cadena `carc`/`cdrc` al ∀ ACOTADO.
    #     Es una INDUCCION INTERNA nueva dentro de `Prov`. Es la pieza mas cara.
    #  4. `Ramas.CASO_bin_H` / `CASO_un_H` : los casos 5/7/8 y 6/9 EXISTEN, pero en
    #     forma `Prf → Prf`. El paso los necesita RELATIVIZADOS a `PrfH Γ` (la HI
    #     llega DENTRO del contexto). Es mecanico — es la misma conversion que
    #     `sondeos/Paso2Guardado.lean` §N ya hizo a mano para el caso `∀` — pero
    #     hay que hacerla. `botc` se salva porque no tiene hipotesis (`Ens.rama_D2`).
    #  5. `Cierre.CASO_eq_H` / `CASO_atom_H` : los casos `eqc`(4) y `atomc`(3)
    #     **NO EXISTEN ENSAMBLADOS** en ningun sondeo (grep: 0 hits para
    #     `paso2_caso_eq` / `paso2_caso_atom`). Existen sus INGREDIENTES
    #     (`pcc_eval_substtc'` / `pcc_eval_substtsc'`), net-0.
    #
    # ── VEREDICTO ────────────────────────────────────────────────────────────
    #  El ENSAMBLAJE en si (gate, lifts, descenso, testigos, analisis de 8 casos)
    #  **ESTA HECHO Y COMPILA** (`Ens.PHI2_step`, `Cierre.pcc_eval_substfc_REDUCIDO`,
    #  `Mitad.pcc_eval_substfc_FINAL`). NO es ahi donde esta el muro.
    #  El muro es (2)+(3): **los dos reconocedores de codigo de TERMINO no hablan**.
    #  El encargo decia «los ocho casos ya estan cubiertos»: son SEIS, y cinco de
    #  esos seis estan en la forma equivocada.
    ############################################################################ -/

section S_Veredicto
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open FOL

/-- CONTROL FINAL: Φ2 NO es Φ1. Enriquecer el predicado con el testigo del codigo
    **cambia el predicado** (si no, el §8 seria un rodeo). -/
example : True := by
  fail_if_success
    exact (rfl : Gate.PHI2 = Gate.PHI1)
  trivial

/-- CONTROL FINAL: la conclusion del §11 es la del encargo, LITERAL. -/
theorem CTRL_diana (v s f : Term) :
    provFromCode (FamA.evalSubstfcCode v s f)
      = provFromCode (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn
          (FamA.substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))) := rfl

end S_Veredicto

/-! ## LOS CINCO RESIDUOS, IMPRESOS LITERALMENTE -/

#print Puente.PUENTE_ECU
#print Puente.PUENTE_AB
#print Cierre.PUENTE_ARGS
#print Ramas.CASO_bin_H
#print Ramas.CASO_un_H
#print Cierre.CASO_eq_H
#print Cierre.CASO_atom_H
#print Censo.CASO_bottom

#print axioms CTRL_diana

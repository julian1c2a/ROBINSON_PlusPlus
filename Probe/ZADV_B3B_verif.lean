/-
# `Probe/ZADV_B3B_verif.lean` — VERIFICACION ADVERSARIAL del angulo «substtc:riesgos»

Cierra tres huecos que `Probe/B3B_substtc_riesgos.lean` deja abiertos:

* §A — su §3.4 dice «el enunciado del SONDEO, habitado por la constante de PRODUCCION», pero
  como el Probe **no** declara las copias de vocabulario del sondeo (`argsIn`, `isTC1`,
  `consOk`, `varcT`, `predcT`…), esos `example` estan escritos con el vocabulario de
  PRODUCCION: son casi tautologicos. Aqui se declaran las copias LITERALES del sondeo en
  `namespace SS` y se rehace la comprobacion de verdad.
* §B — puentes `rfl` copia-del-sondeo ↔ constante-de-produccion para las 15 definiciones.
* §C — que la colision de los 8 `refl_*` exportados a la RAIZ es AMBIGÜEDAD (error) o
  resolucion silenciosa: se mide.

    lake env lean Probe/ZADV_B3B_verif.lean
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
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ZADVB3B

/-! ## §0 · ARNES -/

example : True := by
  fail_if_success (have : (1 : Nat) = 2 := rfl)
  trivial
example : True := by
  fail_if_success (fail_if_success (have : (1 : Nat) = 1 := rfl))
  trivial

/-! ## §A · LAS COPIAS DE VOCABULARIO DEL SONDEO, LITERALES (`sondeos/EvalSubsttc.lean`) -/

namespace SS

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
def varcT (X : Term) : Term := unT 0 X
def funccT (X Y : Term) : Term := binT 1 X Y
def predcT (x : Term) : Term := funcc (strCode pred_sym) (cons x nil)

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
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))
def AX26_BODY : Formula := pred (succ (.var 0)) =eq (.var 0)

def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))
def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))

end SS

/-! ## §B · PUENTES: la copia del sondeo ES la constante de produccion (`rfl`) -/

open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_shapeUn (X : Term) (k : Nat) : SS.shapeUn X k = shapeUn X k := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_shapeBin (X : Term) (k : Nat) : SS.shapeBin X k = shapeBin X k := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_argsInBody (w Y : Term) : SS.argsInBody w Y = argsInBody w Y := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_argsIn (w Y : Term) : SS.argsIn w Y = argsIn w Y := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_isTermCodeE1 (w X : Term) : SS.isTermCodeE1 w X = isTermCodeE1 w X := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_consOk (X : Term) : SS.consOk X = consOk X := rfl
theorem b_wfAll1Body (w : Term) :
    SS.wfAll1Body w = ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body w := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_wfAll1 (w : Term) : SS.wfAll1 w = wfAll1 w := rfl
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs in
theorem b_isTC1 (w c : Term) : SS.isTC1 w c = isTC1 w c := rfl
theorem b_hasWit (c : Term) :
    SS.hasWit c = ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit c := rfl
theorem b_nilOrCons : SS.nilOrCons = ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons := rfl
theorem b_varcT (X : Term) : SS.varcT X = ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT X := rfl
theorem b_funccT (X Y : Term) :
    SS.funccT X Y = ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT X Y := rfl
theorem b_predcT (x : Term) : SS.predcT x = ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT x := rfl
theorem b_AX26 : SS.AX26_BODY = ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY := rfl

/-! CONTROL NEGATIVO del §B: una copia MAL puesta no cierra por `rfl`. -/
namespace SSMAL
def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 2)) nil))
end SSMAL
example : True := by
  fail_if_success
    (have : ∀ (X : Term) (k : Nat),
      SSMAL.shapeUn X k = ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn X k := fun _ _ => rfl)
  trivial

/-! ## §A' · LO QUE EL §3.4 DEL PROBE AUDITADO **NO** MIDE:
    el enunciado escrito con el vocabulario DEL SONDEO, habitado por produccion. -/

theorem a_argsIn_tail (w hd tl : Term) :
    Prf (Formula.impl (SS.argsIn w (cons hd tl)) (SS.argsIn w tl)) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail w hd tl

theorem a_substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (SS.isTC1 w c) = SS.isTC1 (substTerm v s w) (substTerm v s c) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTC1 v s w c

theorem a_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (SS.consOk Y)) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons Y

theorem a_substtc_predcT (v W x : Term) :
    Prf (substtc v W (SS.predcT x) =eq SS.predcT (substtc v W x)) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_substtc_predcT v W x

theorem a_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (SS.varcT a) =eq SS.varcT (substtc (numeral v) W a)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_varcT_at v W a

theorem a_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (SS.wfAll1 w) (SS.isTermCodeE1 w c))) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In w c

theorem a_shapeUn0 (X : Term) :
    SS.shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeUn0_es_varc X

theorem a_AX26_ok : ax26_pred_succ = Formula.forall SS.AX26_BODY :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY_ok

/-! ## §C · LA COLISION DE LOS 8 `refl_*` EXPORTADOS A LA RAIZ:
    ¿error de ambigüedad, o resolucion silenciosa? Se mide con un homonimo de juguete que
    reproduce la ARIDAD del sondeo (2 explicitos) frente al de produccion (0). -/

/-- FUERA de todo namespace propio: el nombre PELADO resuelve al de PRODUCCION (raiz). -/
theorem c_fuera_resuelve_a_produccion :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) := refl_lista_nil

namespace COL
/-- Homonimo LOCAL con la aridad del sondeo (dos argumentos explicitos). -/
theorem refl_lista_nil (v s : Term) : Prf (v =eq v) := prf_refl v

/-- ⚠️ DENTRO del namespace que lo declara, el LOCAL gana: el de la raiz ya no se alcanza
    por el nombre pelado, ni siquiera cuando es el unico que tipa. **No hay ambigüedad.** -/
example : True := by
  fail_if_success
    (have : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) := refl_lista_nil)
  trivial

theorem c_dentro_resuelve_al_local (v s : Term) : Prf (v =eq v) := refl_lista_nil v s
end COL

/-! ### C.2 · EL CASO QUE DE VERDAD IMPORTA: un CONSUMIDOR aguas abajo que hace `open`
    del modulo promovido, con el `export` de `LiftcCodePrf` tambien visible. Aqui Lean tiene
    DOS candidatos y elige por ELABORACION — silenciosamente, uno u otro segun el tipo. -/

section
open COL
/-- Con `open`, el de la RAIZ sigue alcanzable: gana el que tipa. -/
theorem c_open_gana_produccion :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) := refl_lista_nil
/-- …y con otro tipo gana el del modulo abierto. Mismo texto, DOS constantes. -/
theorem c_open_gana_local (v s : Term) : Prf (v =eq v) := refl_lista_nil v s
end

end ZADVB3B

#print axioms ZADVB3B.b_isTC1
#print axioms ZADVB3B.a_argsIn_tail
#print axioms ZADVB3B.a_substF_isTC1
#print axioms ZADVB3B.a_nil_or_cons
#print axioms ZADVB3B.a_substtc_predcT
#print axioms ZADVB3B.a_substtc_varcT_at
#print axioms ZADVB3B.a_isTermCodeE1_of_In
#print axioms ZADVB3B.a_AX26_ok
#print axioms ZADVB3B.c_fuera_resuelve_a_produccion
#print axioms ZADVB3B.COL.c_dentro_resuelve_al_local
#print axioms ZADVB3B.c_open_gana_produccion
#print axioms ZADVB3B.c_open_gana_local

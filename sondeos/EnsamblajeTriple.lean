/-
# ENSAMBLAJE — la INDUCCION FUERTE con predicado CONJUNTIVO sobre los TRES SORTS

    lake env lean Probe/ENS_triple.lean

Framing (A): un solo `prf_strong_induction` con conclusion CONJUNTIVA de TRES conyuntos
(formula / termino / lista de terminos), sobre el paquete de testigos `p` de
`sondeos/ParticionTresPredicados.lean` (§17-§19).

## RESULTADO (todo net-0: `[propext, Classical.choice, Quot.sound]`, exit 0)

* ✅ **EL GATE PASA**: `hPHI1 : liftFormula 1 PHI = PHI` con el predicado CONJUNTIVO de
  TRES conyuntos **y** la guarda `hasWit s` dentro. Y **sigue habiendo SOLO TRES binders
  exteriores** (`p`, `v`, `s`) — no cuatro ni seis — porque el paquete de testigos ya venia
  EMPAQUETADO en un termino (`ParticionTresPredicados` §1). ⇒ `FOL.substTerm_liftTerm`,
  `FOL.substTerm_liftLift` y `SubstArith.substTerm_liftLiftLift` bastan: **no hace falta
  ninguna version de cuatro o cinco lifts.**
* ✅ **EL ENSAMBLAJE ESTA HECHO**: `PHI_step`, `PHI_all`, los tres `DESCENSO_*` y
  `pcc_eval_substfc`, con `v`, `s`, `f` ABSTRACTOS — **modulo** las diez clausulas de caso
  (`Cases` §8) y su forma minima `CasesCtx` (§12).

## LO QUE FALTA (medido, no estimado)

1. **Γ-parametrizar cinco lemas de caso** (`CasesCtx` §12). Cuatro de los diez ya existen
   TAL CUAL. **`cAtomC` y `cEqC` NO existen** en ningun sondeo: el encargo decia «los ocho
   casos ya estan cubiertos» y de `atomc`(3)/`eqc`(4) solo estan los INGREDIENTES
   (`EvalSubsttc.pcc_eval_substtc'` / `pcc_eval_substtsc'`), no el lema de caso.
2. **Hito (i) en forma ECUACIONAL**: `prf_isFCB3_fcodes` da testigo para la forma
   `carc/lenc` (B), y el fortalecimiento va E ⇒ B, o sea **en la direccion contraria**
   a la que hace falta. Hay que rehacer `ParticionTresPredicados` §19 con `shapeNul/Un/Bin`
   (mas barato: UNA ecuacion por nodo en vez de `carc ≐ k̄ ∧ lenc ≐ n̄`).

Copias LITERALES (cada bloque en su `section`, patron de `sondeos/Paso2Guardado.lean`):
  * `sondeos/GateGuardaEnriquecida.lean` §1-§2: la guarda `hasWit` y su fontaneria.
  * `sondeos/ParticionTresPredicados.lean` §1/§17: `consOk`/`cOk`, `acF`/`acT`/`acTs`.
  * `sondeos/DiscriminaEcuacional.lean` PasoUno §2/§4: las TRES formas ECUACIONALES
    (`shapeNul`/`shapeUn`/`shapeBin`) y los predicados `isTermCodeE`/`isFormCodeE`.
  * `sondeos/EvalSubsttc.lean` §9/§11: `targetSubsttc`/`targetSubsttsc` y el patron
    `PHI_at`/`PHI_spec1-3`/`PHI_use`/`PSI_inst`.
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
open ROBINSON_PlusPlus.Meta.CantorMonoPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ENS3

/-! ############################################################################
    ## §0 · Combinadores logicos (copia literal de `ParticionTresPredicados` §0)
    ############################################################################ -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-! ############################################################################
    ## §1 · CONSTRUCTORES DE CODIGO DOTADOS y los TRES OBJETIVOS
    (definiciones; ninguna ecuacion suya se postula)
    ############################################################################ -/

def substfcT  (v s f  : Term) : Term := funcc (strCode "substfc")  (cons v (cons s (cons f nil)))
def substtcT  (v s t  : Term) : Term := funcc (strCode "substtc")  (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term := funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
def liftcT    (c t : Term)    : Term := funcc (strCode "liftc")    (cons c (cons t nil))

/-- El objetivo de FORMULA, con `v`, `s`, `X` ABSTRACTOS. -/
def targetSubstfc (v s X : Term) : Formula :=
  provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substfc v s X)))
/-- El objetivo de TERMINO (copia literal de `EvalSubsttc.targetSubsttc`). -/
def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))
/-- El objetivo de LISTA (copia literal de `EvalSubsttc.targetSubsttsc`). -/
def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))

/-- CONTROL NEGATIVO: ninguno de los tres es una reflexividad disfrazada. -/
example (v s X : Term) : True := by
  fail_if_success exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn X) = tcFn (substfc v s X))
  fail_if_success exact (rfl : substtcT (tcFn v) (tcFn s) (tcFn X) = tcFn (substtc v s X))
  fail_if_success exact (rfl : substtscT (tcFn v) (tcFn s) (tcFn X) = tcFn (substtsc v s X))
  trivial

theorem liftF_targetSubstfc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubstfc v s X)
      = targetSubstfc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubstfc, liftFormula_provFromCode_open, eqCodeFn, substfcT, funcc, tcFn,
    substfc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

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

theorem substF_targetSubstfc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubstfc v s X)
      = targetSubstfc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubstfc, substFormula_provFromCode_open, eqCodeFn, substfcT, funcc, tcFn,
    substfc, cons, nil, zero, succ, substTerm, substTerms, substTerm_numeral, substTerm_strCode]

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

/-! ### Leibniz sobre el tercer argumento de cada objetivo -/

theorem substF_hole_fc (v s u : Term) :
    substFormula 0 u (targetSubstfc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) = targetSubstfc v s u := by
  rw [substF_targetSubstfc]; simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_tc (v s u : Term) :
    substFormula 0 u (targetSubsttc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) = targetSubsttc v s u := by
  rw [substF_targetSubsttc]; simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_tsc (v s u : Term) :
    substFormula 0 u (targetSubsttsc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttsc v s u := by
  rw [substF_targetSubsttsc]; simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_targetSubstfc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubstfc v s X)) : PrfH Γ (targetSubstfc v s X') :=
  (substF_hole_fc v s X') ▸
    PrfH_leibniz_subst (A := targetSubstfc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_fc v s X) ▸ ha)

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

/-! ############################################################################
    ## §2 · LA GUARDA `hasWit s` sobre el SUSTITUYENDO
    (copia LITERAL de `sondeos/GateGuardaEnriquecida.lean` §1-§2; formato de testigo
    VIEJO — `isTC1`/`wfAll1`/`argsIn` — porque es el que consumen
    `paso2_caso_forall_guarded` / `paso2_caso_ex_guarded`.)
    ############################################################################ -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def shapeUn1 (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin1 (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn1 X 0) (land (shapeBin1 X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

/-- «`c` TIENE testigo» — testigo CUANTIFICADO. -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X) = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn1, shapeBin1, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

theorem liftF_hasWit (k : Nat) (c : Term) :
    liftFormula k (hasWit c) = hasWit (liftTerm k c) := by
  simp only [hasWit, liftFormula, liftF_isTC1, liftTerm, Nat.zero_lt_succ, reduceIte,
    ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X) = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn1, shapeBin1, lor, land, substFormula, substF_argsIn,
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

theorem substF_hasWit (v : Nat) (s c : Term) :
    substFormula v s (hasWit c) = hasWit (substTerm v s c) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [hasWit, substFormula, substF_isTC1, substTerm, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero]

/-! ############################################################################
    ## §3 · EL RECONOCEDOR DE LA TERNA, en FORMA ECUACIONAL
    ############################################################################

    ⚠️ Se usa la forma ECUACIONAL (`X ≐ cons k̄ …`) y no la forma `carc/lenc` de
    `ParticionTresPredicados`: el CONSUMO de la induccion necesita RECONSTRUIR `X` a
    partir del disyunto, y `carc X ≐ k̄ ∧ lenc X ≐ n̄` **no lo reconstruye** (no hay
    axioma de descomposicion de listas) — medido en `sondeos/ClausuraFormaEcuacional.lean`.
    `sondeos/DiscriminaEcuacional.lean` (PasoUno §4-§5) probo que la forma ecuacional
    **FORTALECE** la de `carc/lenc` (`prf_isFormCodeE_str`) y que la DISCRIMINACION
    sobrevive; luego el reflector y el criterio de basura se heredan por composicion. -/

def shapeNul (X : Term) (k : Nat) : Formula := Formula.eq X (cons (numeralM k) nil)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- Copia literal de `DiscriminaEcuacional.PasoUno.isTermCodeE`. -/
def isTermCodeE (wT wTs X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (In (nthc X (numeralM 2)) wTs))

/-- Copia literal de `ParticionTresPredicados.isTermsCodeB` reescrita con `consOk`
    desplegado: **ya estaba en forma ecuacional** (`X ≐ nil` / `X ≐ cons (carc X) (cdrc X)`). -/
def isTermsCodeE (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (land (Formula.eq X (cons (carc X) (cdrc X)))
            (land (In (carc X) wT) (In (cdrc X) wTs)))

/-- Copia literal de `DiscriminaEcuacional.PasoUno.isFormCodeE` — los OCHO disyuntos. -/
def isFormCodeE (wF wT wTs X : Term) : Formula :=
  lorAll (shapeNul X 2)
    [ land (shapeBin X 3) (In (nthc X (numeralM 2)) wTs)
    , land (shapeBin X 4) (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))
    , land (shapeBin X 5) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeUn  X 6) (In (nthc X (numeralM 1)) wF)
    , land (shapeBin X 7) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeBin X 8) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeUn  X 9) (In (nthc X (numeralM 1)) wF) ]

/-! ### Los TRES accesores del paquete (copia literal de `ParticionTresPredicados` §17) -/

def acF  : Term → Term := carc
def acT  : Term → Term := fun p => carc (cdrc p)
def acTs : Term → Term := fun p => cdrc (cdrc p)

def wfAllFE (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc (acF p))))
    (isFormCodeE (liftTerm 0 (acF p)) (liftTerm 0 (acT p)) (liftTerm 0 (acTs p))
      (nthc (liftTerm 0 (acF p)) (.var 0))))

def wfAllTE (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc (acT p))))
    (isTermCodeE (liftTerm 0 (acT p)) (liftTerm 0 (acTs p))
      (nthc (liftTerm 0 (acT p)) (.var 0))))

def wfAllTsE (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc (acTs p))))
    (isTermsCodeE (liftTerm 0 (acT p)) (liftTerm 0 (acTs p))
      (nthc (liftTerm 0 (acTs p)) (.var 0))))

def tripleOkE (p : Term) : Formula :=
  land (wfAllFE p) (land (wfAllTE p) (wfAllTsE p))

/-- `c` es codigo de FORMULA con testigo `p`. -/
def isFCE3  (p c : Term) : Formula := land (tripleOkE p) (In c (acF p))
/-- `c` es codigo de TERMINO con testigo `p`. -/
def isTCE3  (p c : Term) : Formula := land (tripleOkE p) (In c (acT p))
/-- `c` es codigo de LISTA DE TERMINOS con testigo `p`. -/
def isTsCE3 (p c : Term) : Formula := land (tripleOkE p) (In c (acTs p))

/-! ### Fontaneria De Bruijn de los tres reconocedores -/

theorem liftF_shapeNul (k : Nat) (X : Term) (m : Nat) :
    liftFormula k (shapeNul X m) = shapeNul (liftTerm k X) m := by
  simp only [shapeNul, liftFormula, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_shapeUn (k : Nat) (X : Term) (m : Nat) :
    liftFormula k (shapeUn X m) = shapeUn (liftTerm k X) m := by
  simp only [shapeUn, liftFormula, nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_shapeBin (k : Nat) (X : Term) (m : Nat) :
    liftFormula k (shapeBin X m) = shapeBin (liftTerm k X) m := by
  simp only [shapeBin, liftFormula, nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_isTermCodeE (k : Nat) (wT wTs X : Term) :
    liftFormula k (isTermCodeE wT wTs X)
      = isTermCodeE (liftTerm k wT) (liftTerm k wTs) (liftTerm k X) := by
  simp only [isTermCodeE, lor, land, liftFormula, liftF_shapeUn, liftF_shapeBin,
    In, nthc, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_isTermsCodeE (k : Nat) (wT wTs X : Term) :
    liftFormula k (isTermsCodeE wT wTs X)
      = isTermsCodeE (liftTerm k wT) (liftTerm k wTs) (liftTerm k X) := by
  simp only [isTermsCodeE, lor, land, liftFormula, In, carc, cdrc, cons, nil, zero,
    liftTerm, liftTerms]

theorem liftF_isFormCodeE (k : Nat) (wF wT wTs X : Term) :
    liftFormula k (isFormCodeE wF wT wTs X)
      = isFormCodeE (liftTerm k wF) (liftTerm k wT) (liftTerm k wTs) (liftTerm k X) := by
  simp only [isFormCodeE, lorAll, lor, land, liftFormula, liftF_shapeNul, liftF_shapeUn,
    liftF_shapeBin, In, nthc, liftTerm, liftTerms, liftTerm_numeralM]

theorem substF_shapeNul (v : Nat) (u X : Term) (m : Nat) :
    substFormula v u (shapeNul X m) = shapeNul (substTerm v u X) m := by
  simp only [shapeNul, substFormula, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem substF_shapeUn (v : Nat) (u X : Term) (m : Nat) :
    substFormula v u (shapeUn X m) = shapeUn (substTerm v u X) m := by
  simp only [shapeUn, substFormula, nthc, cons, nil, zero, substTerm, substTerms,
    substTerm_numeralM]

theorem substF_shapeBin (v : Nat) (u X : Term) (m : Nat) :
    substFormula v u (shapeBin X m) = shapeBin (substTerm v u X) m := by
  simp only [shapeBin, substFormula, nthc, cons, nil, zero, substTerm, substTerms,
    substTerm_numeralM]

theorem substF_isTermCodeE (v : Nat) (u wT wTs X : Term) :
    substFormula v u (isTermCodeE wT wTs X)
      = isTermCodeE (substTerm v u wT) (substTerm v u wTs) (substTerm v u X) := by
  simp only [isTermCodeE, lor, land, substFormula, substF_shapeUn, substF_shapeBin,
    In, nthc, substTerm, substTerms, substTerm_numeralM]

theorem substF_isTermsCodeE (v : Nat) (u wT wTs X : Term) :
    substFormula v u (isTermsCodeE wT wTs X)
      = isTermsCodeE (substTerm v u wT) (substTerm v u wTs) (substTerm v u X) := by
  simp only [isTermsCodeE, lor, land, substFormula, In, carc, cdrc, cons, nil, zero,
    substTerm, substTerms]

theorem substF_isFormCodeE (v : Nat) (u wF wT wTs X : Term) :
    substFormula v u (isFormCodeE wF wT wTs X)
      = isFormCodeE (substTerm v u wF) (substTerm v u wT) (substTerm v u wTs)
          (substTerm v u X) := by
  simp only [isFormCodeE, lorAll, lor, land, substFormula, substF_shapeNul, substF_shapeUn,
    substF_shapeBin, In, nthc, substTerm, substTerms, substTerm_numeralM]

theorem liftT_acF (k : Nat) (p : Term) : liftTerm k (acF p) = acF (liftTerm k p) := by
  simp only [acF, carc, liftTerm, liftTerms]
theorem liftT_acT (k : Nat) (p : Term) : liftTerm k (acT p) = acT (liftTerm k p) := by
  simp only [acT, carc, cdrc, liftTerm, liftTerms]
theorem liftT_acTs (k : Nat) (p : Term) : liftTerm k (acTs p) = acTs (liftTerm k p) := by
  simp only [acTs, cdrc, liftTerm, liftTerms]
theorem substT_acF (v : Nat) (u p : Term) : substTerm v u (acF p) = acF (substTerm v u p) := by
  simp only [acF, carc, substTerm, substTerms]
theorem substT_acT (v : Nat) (u p : Term) : substTerm v u (acT p) = acT (substTerm v u p) := by
  simp only [acT, carc, cdrc, substTerm, substTerms]
theorem substT_acTs (v : Nat) (u p : Term) : substTerm v u (acTs p) = acTs (substTerm v u p) := by
  simp only [acTs, cdrc, substTerm, substTerms]

theorem liftF_wfAllFE (k : Nat) (p : Term) :
    liftFormula k (wfAllFE p) = wfAllFE (liftTerm k p) := by
  simp only [wfAllFE, liftFormula, liftF_isFormCodeE, lt, lenc, nthc, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero, liftT_acF, liftT_acT,
    liftT_acTs]

theorem liftF_wfAllTE (k : Nat) (p : Term) :
    liftFormula k (wfAllTE p) = wfAllTE (liftTerm k p) := by
  simp only [wfAllTE, liftFormula, liftF_isTermCodeE, lt, lenc, nthc, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero, liftT_acT, liftT_acTs]

theorem liftF_wfAllTsE (k : Nat) (p : Term) :
    liftFormula k (wfAllTsE p) = wfAllTsE (liftTerm k p) := by
  simp only [wfAllTsE, liftFormula, liftF_isTermsCodeE, lt, lenc, nthc, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero, liftT_acT, liftT_acTs]

theorem liftF_tripleOkE (k : Nat) (p : Term) :
    liftFormula k (tripleOkE p) = tripleOkE (liftTerm k p) := by
  simp only [tripleOkE, land, liftFormula, liftF_wfAllFE, liftF_wfAllTE, liftF_wfAllTsE]

theorem liftF_isFCE3 (k : Nat) (p c : Term) :
    liftFormula k (isFCE3 p c) = isFCE3 (liftTerm k p) (liftTerm k c) := by
  simp only [isFCE3, land, liftFormula, liftF_tripleOkE, In, liftTerm, liftTerms, liftT_acF]

theorem liftF_isTCE3 (k : Nat) (p c : Term) :
    liftFormula k (isTCE3 p c) = isTCE3 (liftTerm k p) (liftTerm k c) := by
  simp only [isTCE3, land, liftFormula, liftF_tripleOkE, In, liftTerm, liftTerms, liftT_acT]

theorem liftF_isTsCE3 (k : Nat) (p c : Term) :
    liftFormula k (isTsCE3 p c) = isTsCE3 (liftTerm k p) (liftTerm k c) := by
  simp only [isTsCE3, land, liftFormula, liftF_tripleOkE, In, liftTerm, liftTerms, liftT_acTs]

theorem substF_wfAllFE (v : Nat) (u p : Term) :
    substFormula v u (wfAllFE p) = wfAllFE (substTerm v u p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAllFE, substFormula, substF_isFormCodeE, lt, lenc, nthc, substTerm, substTerms,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero, substT_acF, substT_acT, substT_acTs]

theorem substF_wfAllTE (v : Nat) (u p : Term) :
    substFormula v u (wfAllTE p) = wfAllTE (substTerm v u p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAllTE, substFormula, substF_isTermCodeE, lt, lenc, nthc, substTerm, substTerms,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero, substT_acT, substT_acTs]

theorem substF_wfAllTsE (v : Nat) (u p : Term) :
    substFormula v u (wfAllTsE p) = wfAllTsE (substTerm v u p) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAllTsE, substFormula, substF_isTermsCodeE, lt, lenc, nthc, substTerm, substTerms,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero, substT_acT, substT_acTs]

theorem substF_tripleOkE (v : Nat) (u p : Term) :
    substFormula v u (tripleOkE p) = tripleOkE (substTerm v u p) := by
  simp only [tripleOkE, land, substFormula, substF_wfAllFE, substF_wfAllTE, substF_wfAllTsE]

theorem substF_isFCE3 (v : Nat) (u p c : Term) :
    substFormula v u (isFCE3 p c) = isFCE3 (substTerm v u p) (substTerm v u c) := by
  simp only [isFCE3, land, substFormula, substF_tripleOkE, In, substTerm, substTerms, substT_acF]

theorem substF_isTCE3 (v : Nat) (u p c : Term) :
    substFormula v u (isTCE3 p c) = isTCE3 (substTerm v u p) (substTerm v u c) := by
  simp only [isTCE3, land, substFormula, substF_tripleOkE, In, substTerm, substTerms, substT_acT]

theorem substF_isTsCE3 (v : Nat) (u p c : Term) :
    substFormula v u (isTsCE3 p c) = isTsCE3 (substTerm v u p) (substTerm v u c) := by
  simp only [isTsCE3, land, substFormula, substF_tripleOkE, In, substTerm, substTerms, substT_acTs]

/-! ############################################################################
    ## §4 · EL PREDICADO CONJUNTIVO SOBRE LOS TRES SORTS, y **EL GATE**
    ############################################################################

    `#3` es el CODIGO sobre el que se induce; `#2` el PAQUETE de testigos `p`;
    `#1` = `v`; `#0` = `s`. La guarda `hasWit s` va **DENTRO** del primer conyunto
    (es un `∃` interno: NO anade binder exterior — leccion de
    `sondeos/GateGuardaEnriquecida.lean`), y los tres testigos van EMPAQUETADOS en
    un solo `p` (leccion de `ParticionTresPredicados` §1: la mutualidad obliga a
    empaquetar) ⇒ **siguen siendo TRES binders exteriores**, exactamente los mismos
    que en `sondeos/EvalSubsttc.lean:1537`. -/

def CONJ3 (p v s X : Term) : Formula :=
  land (Formula.impl (land (hasWit s) (isFCE3 p X)) (targetSubstfc v s X))
    (land (Formula.impl (isTCE3  p X) (targetSubsttc  v s X))
          (Formula.impl (isTsCE3 p X) (targetSubsttsc v s X)))

theorem liftF_CONJ3 (k : Nat) (p v s X : Term) :
    liftFormula k (CONJ3 p v s X)
      = CONJ3 (liftTerm k p) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [CONJ3, land, liftFormula, liftF_hasWit, liftF_isFCE3, liftF_isTCE3, liftF_isTsCE3,
    liftF_targetSubstfc, liftF_targetSubsttc, liftF_targetSubsttsc]

theorem substF_CONJ3 (k : Nat) (u p v s X : Term) :
    substFormula k u (CONJ3 p v s X)
      = CONJ3 (substTerm k u p) (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [CONJ3, land, substFormula, substF_hasWit, substF_isFCE3, substF_isTCE3,
    substF_isTsCE3, substF_targetSubstfc, substF_targetSubsttc, substF_targetSubsttsc]

def PHIbody : Formula := CONJ3 (.var 2) (.var 1) (.var 0) (.var 3)
def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

/-- **EL GATE** — `liftFormula 1 Φ = Φ`, que es lo que exige `prf_strong_induction`. -/
theorem hPHI1 : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_CONJ3, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

/-! ############################################################################
    ## §5 · FONTANERIA DE LA INDUCCION FUERTE (patron de `EvalSubsttc` §11)
    ############################################################################ -/

theorem PHI_at (t : Term) :
    substFormula 0 t PHI
      = Formula.forall (Formula.forall (Formula.forall
          (CONJ3 (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI, PHIbody, substFormula, substF_CONJ3, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_spec1 (t p : Term) :
    substFormula 0 p (Formula.forall (Formula.forall
        (CONJ3 (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (CONJ3 (liftTerm 0 (liftTerm 0 p)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_CONJ3, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHI_spec2 (t p v : Term) :
    substFormula 0 v (Formula.forall
        (CONJ3 (liftTerm 0 (liftTerm 0 p)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (CONJ3 (liftTerm 0 p) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_CONJ3, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHI_spec3 (t p v s : Term) :
    substFormula 0 s (CONJ3 (liftTerm 0 p) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = CONJ3 p v s t := by
  simp only [substF_CONJ3, substTerm, FOL.substTerm_liftTerm, if_true]

/-- Instanciacion de las TRES mitades a `p`, `v`, `s` concretos. -/
theorem PHI_use {Γ : List Formula} (t p v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (CONJ3 p v s t) := by
  rw [PHI_at] at h
  have h1 := PrfH_spec h p
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

/-! ############################################################################
    ## §6 · DEL TESTIGO AL NODO — los tres puentes `In c (ac· p) → is·CodeE …`
    ############################################################################ -/

theorem substF_hole_FCE (wF wT wTs u : Term) :
    substFormula 0 u (isFormCodeE (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
      = isFormCodeE wF wT wTs u := by
  rw [substF_isFormCodeE]; simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_TCE (wT wTs u : Term) :
    substFormula 0 u (isTermCodeE (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
      = isTermCodeE wT wTs u := by
  rw [substF_isTermCodeE]; simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_TsCE (wT wTs u : Term) :
    substFormula 0 u (isTermsCodeE (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
      = isTermsCodeE wT wTs u := by
  rw [substF_isTermsCodeE]; simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_isFormCodeE {Γ : List Formula} {wF wT wTs a b : Term} (h : PrfH Γ (a =eq b))
    (ha : PrfH Γ (isFormCodeE wF wT wTs a)) : PrfH Γ (isFormCodeE wF wT wTs b) :=
  (substF_hole_FCE wF wT wTs b) ▸
    PrfH_leibniz_subst
      (A := isFormCodeE (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)) h
      ((substF_hole_FCE wF wT wTs a) ▸ ha)

theorem PrfH_congr_isTermCodeE {Γ : List Formula} {wT wTs a b : Term} (h : PrfH Γ (a =eq b))
    (ha : PrfH Γ (isTermCodeE wT wTs a)) : PrfH Γ (isTermCodeE wT wTs b) :=
  (substF_hole_TCE wT wTs b) ▸
    PrfH_leibniz_subst (A := isTermCodeE (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)) h
      ((substF_hole_TCE wT wTs a) ▸ ha)

theorem PrfH_congr_isTermsCodeE {Γ : List Formula} {wT wTs a b : Term} (h : PrfH Γ (a =eq b))
    (ha : PrfH Γ (isTermsCodeE wT wTs a)) : PrfH Γ (isTermsCodeE wT wTs b) :=
  (substF_hole_TsCE wT wTs b) ▸
    PrfH_leibniz_subst (A := isTermsCodeE (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)) h
      ((substF_hole_TsCE wT wTs a) ▸ ha)

theorem PrfH_inst_wfAllFE {Γ : List Formula} (p i : Term) (h : PrfH Γ (wfAllFE p)) :
    PrfH Γ (Formula.impl (lt i (lenc (acF p)))
      (isFormCodeE (acF p) (acT p) (acTs p) (nthc (acF p) i))) := by
  have hh := PrfH_spec h i
  simpa only [substFormula, lt, substF_isFormCodeE, nthc, lenc, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hh

theorem PrfH_inst_wfAllTE {Γ : List Formula} (p i : Term) (h : PrfH Γ (wfAllTE p)) :
    PrfH Γ (Formula.impl (lt i (lenc (acT p)))
      (isTermCodeE (acT p) (acTs p) (nthc (acT p) i))) := by
  have hh := PrfH_spec h i
  simpa only [substFormula, lt, substF_isTermCodeE, nthc, lenc, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hh

theorem PrfH_inst_wfAllTsE {Γ : List Formula} (p i : Term) (h : PrfH Γ (wfAllTsE p)) :
    PrfH Γ (Formula.impl (lt i (lenc (acTs p)))
      (isTermsCodeE (acT p) (acTs p) (nthc (acTs p) i))) := by
  have hh := PrfH_spec h i
  simpa only [substFormula, lt, substF_isTermsCodeE, nthc, lenc, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hh

theorem prf_isFormCodeE_of_boundedIn (p c : Term) :
    Prf (Formula.impl (boundedIn c (acF p))
      (Formula.impl (wfAllFE p) (isFormCodeE (acF p) (acT p) (acTs p) c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAllFE, liftF_isFormCodeE, liftT_acF, liftT_acT, liftT_acTs]
  refine deduction_aux ?_ (wfAllFE (liftTerm 0 p)) _ rfl
  have hwf : PrfH [wfAllFE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acF p))))
        (Formula.eq (nthc (liftTerm 0 (acF p)) (.var 0)) (liftTerm 0 c))]
      (wfAllFE (liftTerm 0 p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAllFE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acF p))))
        (Formula.eq (nthc (liftTerm 0 (acF p)) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc (acF p))))
        (Formula.eq (nthc (liftTerm 0 (acF p)) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAllFE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acF p))))
        (Formula.eq (nthc (liftTerm 0 (acF p)) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (acF (liftTerm 0 p)))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, acF, carc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAllFE (liftTerm 0 p) (.var 0) hwf) hlt
  refine PrfH_congr_isFormCodeE ?_ hitc
  simpa only [acF, carc, liftTerm, liftTerms] using heq

theorem prf_isTermCodeE_of_boundedIn (p c : Term) :
    Prf (Formula.impl (boundedIn c (acT p))
      (Formula.impl (wfAllTE p) (isTermCodeE (acT p) (acTs p) c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAllTE, liftF_isTermCodeE, liftT_acT, liftT_acTs]
  refine deduction_aux ?_ (wfAllTE (liftTerm 0 p)) _ rfl
  have hwf : PrfH [wfAllTE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acT p))))
        (Formula.eq (nthc (liftTerm 0 (acT p)) (.var 0)) (liftTerm 0 c))]
      (wfAllTE (liftTerm 0 p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAllTE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acT p))))
        (Formula.eq (nthc (liftTerm 0 (acT p)) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc (acT p))))
        (Formula.eq (nthc (liftTerm 0 (acT p)) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAllTE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acT p))))
        (Formula.eq (nthc (liftTerm 0 (acT p)) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (acT (liftTerm 0 p)))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, acT, carc, cdrc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAllTE (liftTerm 0 p) (.var 0) hwf) hlt
  refine PrfH_congr_isTermCodeE ?_ hitc
  simpa only [acT, carc, cdrc, liftTerm, liftTerms] using heq

theorem prf_isTermsCodeE_of_boundedIn (p c : Term) :
    Prf (Formula.impl (boundedIn c (acTs p))
      (Formula.impl (wfAllTsE p) (isTermsCodeE (acT p) (acTs p) c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAllTsE, liftF_isTermsCodeE, liftT_acT, liftT_acTs]
  refine deduction_aux ?_ (wfAllTsE (liftTerm 0 p)) _ rfl
  have hwf : PrfH [wfAllTsE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acTs p))))
        (Formula.eq (nthc (liftTerm 0 (acTs p)) (.var 0)) (liftTerm 0 c))]
      (wfAllTsE (liftTerm 0 p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAllTsE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acTs p))))
        (Formula.eq (nthc (liftTerm 0 (acTs p)) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc (acTs p))))
        (Formula.eq (nthc (liftTerm 0 (acTs p)) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAllTsE (liftTerm 0 p),
      land (lt (.var 0) (liftTerm 0 (lenc (acTs p))))
        (Formula.eq (nthc (liftTerm 0 (acTs p)) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (acTs (liftTerm 0 p)))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, acTs, cdrc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAllTsE (liftTerm 0 p) (.var 0) hwf) hlt
  refine PrfH_congr_isTermsCodeE ?_ hitc
  simpa only [acTs, cdrc, liftTerm, liftTerms] using heq

theorem prf_isFormCodeE_of_In (p c : Term) :
    Prf (Formula.impl (In c (acF p))
      (Formula.impl (wfAllFE p) (isFormCodeE (acF p) (acT p) (acTs p) c))) :=
  impT (prf_boundedIn_of_In c (acF p)) (prf_isFormCodeE_of_boundedIn p c)

theorem prf_isTermCodeE_of_In (p c : Term) :
    Prf (Formula.impl (In c (acT p))
      (Formula.impl (wfAllTE p) (isTermCodeE (acT p) (acTs p) c))) :=
  impT (prf_boundedIn_of_In c (acT p)) (prf_isTermCodeE_of_boundedIn p c)

theorem prf_isTermsCodeE_of_In (p c : Term) :
    Prf (Formula.impl (In c (acTs p))
      (Formula.impl (wfAllTsE p) (isTermsCodeE (acT p) (acTs p) c))) :=
  impT (prf_boundedIn_of_In c (acTs p)) (prf_isTermsCodeE_of_boundedIn p c)

/-! ############################################################################
    ## §7 · EL DESCENSO BIEN FUNDADO — hijo < padre desde la forma ECUACIONAL
    ############################################################################ -/

def unc (m : Nat) (a : Term) : Term := cons (numeralM m) (cons a nil)
def bnc (m : Nat) (a b : Term) : Term := cons (numeralM m) (cons a (cons b nil))

theorem shapeNul_is (X : Term) : shapeNul X 2 = Formula.eq X botc := rfl
theorem shapeUn_is (X : Term) (m : Nat) :
    shapeUn X m = Formula.eq X (unc m (nthc X (numeralM 1))) := rfl
theorem shapeBin_is (X : Term) (m : Nat) :
    shapeBin X m = Formula.eq X (bnc m (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

theorem bnc1_funcc (a b : Term) : bnc 1 a b = funcc a b := rfl
theorem bnc3_atomc (a b : Term) : bnc 3 a b = atomc a b := rfl
theorem bnc4_eqc   (a b : Term) : bnc 4 a b = eqc a b   := rfl
theorem bnc5_implc (a b : Term) : bnc 5 a b = implc a b := rfl
theorem bnc7_andc  (a b : Term) : bnc 7 a b = andc a b  := rfl
theorem bnc8_orc   (a b : Term) : bnc 8 a b = orc a b   := rfl
theorem unc6_forallc (a : Term) : unc 6 a = forallc a := rfl
theorem unc9_exc     (a : Term) : unc 9 a = exc a     := rfl

theorem lt_child_un (m : Nat) (a : Term) : Prf (lt a (unc m a)) :=
  prf_mp (prf_mp (prf_lt_trans _ _ _) (prf_cantor_mono_left a nil))
    (prf_cantor_mono_right (numeralM m) (cons a nil))

theorem lt_child_bin1 (m : Nat) (a b : Term) : Prf (lt a (bnc m a b)) :=
  prf_mp (prf_mp (prf_lt_trans _ _ _) (prf_cantor_mono_left a (cons b nil)))
    (prf_cantor_mono_right (numeralM m) (cons a (cons b nil)))

theorem lt_child_bin2 (m : Nat) (a b : Term) : Prf (lt b (bnc m a b)) :=
  prf_mp (prf_mp (prf_lt_trans _ _ _)
      (prf_mp (prf_mp (prf_lt_trans _ _ _) (prf_cantor_mono_left b nil))
        (prf_cantor_mono_right a (cons b nil))))
    (prf_cantor_mono_right (numeralM m) (cons a (cons b nil)))

/-! ############################################################################
    ## §8 · LAS DOCE CLAUSULAS, en **FORMA IMPLICACION** — la moneda de la
    ##      induccion OBJETO (`sondeos/EvalSubsttc.lean` §10)
    ############################################################################

    ⚠️ **ESTA ES LA OBLIGACION RESIDUAL, y esta MEDIDA.** Las cuatro clausulas de
    TERMINO/LISTA (`cVar`/`cFunc`/`cNil`/`cCons`) existen YA con este enunciado EXACTO en
    `sondeos/EvalSubsttc.lean` (`refl_shapeUn_imp` con `predHyp` descargada,
    `refl_caso_funcc_imp`, `refl_lista_nil`, `refl_lista_cons_imp`). Las de FORMULA
    existen en `sondeos/SubstfcPlanos.lean`, `sondeos/Paso2Guardado.lean` y
    `sondeos/SubstfcEx.lean` **pero con las HI como hipotesis META** (`Prf A → Prf C`),
    no como implicaciones OBJETO (`Prf (A ⇒ C)`), que es lo unico que la induccion
    puede consumir (la HI solo esta disponible DENTRO del contexto `Γ`). -/

structure Cases : Prop where
  /-- `SubstfcPlanos.paso2_caso_bottom` — coincide TAL CUAL (no tiene HI). -/
  cBot  : ∀ v s : Term, Prf (targetSubstfc v s botc)
  /-- de `atomc`: la casilla 2 es LISTA de codigos de termino. -/
  cAtom : ∀ v s a b : Term,
    Prf (Formula.impl (targetSubsttsc v s b) (targetSubstfc v s (atomc a b)))
  /-- de `eqc`: las dos casillas son codigos de TERMINO. -/
  cEq   : ∀ v s a b : Term,
    Prf (Formula.impl (land (targetSubsttc v s a) (targetSubsttc v s b))
      (targetSubstfc v s (eqc a b)))
  /-- `SubstfcPlanos.paso2_caso_bin`, generico en el tag: `implc`(5)/`andc`(7)/`orc`(8). -/
  cBin  : ∀ (k : Nat), (Or (k = 5) (Or (k = 7) (k = 8))) → ∀ v s a b : Term,
    Prf (Formula.impl (land (targetSubstfc v s a) (targetSubstfc v s b))
      (targetSubstfc v s (bnc k a b)))
  /-- `SubstfcEx.paso2_caso_un_guarded`, generico en el tag: `forallc`(6)/`exc`(9). -/
  cUn   : ∀ (m : Nat), (Or (m = 6) (m = 9)) → ∀ v s a : Term,
    Prf (Formula.impl (land (hasWit s) (targetSubstfc (succ v) (liftc zero s) a))
      (targetSubstfc v s (unc m a)))
  /-- `Paso2Guardado.CRIT_hasWit_lift'` — la guarda SUBE al subcodigo. -/
  cLift : ∀ s : Term, Prf (Formula.impl (hasWit s) (hasWit (liftc zero s)))
  /-- `EvalSubsttc.refl_shapeUn_imp predHyp` — coincide TAL CUAL. -/
  cVar  : ∀ v s X : Term, Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X))
  /-- `EvalSubsttc.refl_caso_funcc_imp` — coincide TAL CUAL. -/
  cFunc : ∀ v s a b : Term,
    Prf (Formula.impl (targetSubsttsc v s b) (targetSubsttc v s (funcc a b)))
  /-- `EvalSubsttc.refl_lista_nil` — coincide TAL CUAL. -/
  cNil  : ∀ v s : Term, Prf (targetSubsttsc v s nil)
  /-- `EvalSubsttc.refl_lista_cons_imp` — coincide TAL CUAL. -/
  cCons : ∀ v s h t : Term,
    Prf (Formula.impl (land (targetSubsttc v s h) (targetSubsttsc v s t))
      (targetSubsttsc v s (cons h t)))

/-! ############################################################################
    ## §9 · EL PASO INDUCTIVO — el ENSAMBLAJE
    ############################################################################ -/

/-- `j3` PERMUTADO: permite combinar dos implicaciones **derivadas en `Γ`** sin necesitar
    monotonia de contexto para `PrfH` (que NO existe en el arbol). -/
theorem prf_j3_perm (A B C : Formula) :
    Prf (Formula.impl (Formula.impl A C)
      (Formula.impl (Formula.impl B C) (Formula.impl (lor A B) C))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_ (lor A B)
    [Formula.impl B C, Formula.impl A C] rfl) (Formula.impl B C)
    [Formula.impl A C] rfl)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (PrfH.hyp _ _ (List.Mem.head _)))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

theorem PrfH_or_imp {Γ : List Formula} {A B C : Formula}
    (h1 : PrfH Γ (Formula.impl A C)) (h2 : PrfH Γ (Formula.impl B C)) :
    PrfH Γ (Formula.impl (lor A B) C) :=
  PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_j3_perm A B C) Γ) h1) h2

/-- HI en un hijo de sort FORMULA. -/
theorem ihF_at {Γ : List Formula} (hpsi : PrfH Γ PSI3) (p : Term)
    (htr : PrfH Γ (tripleOkE p)) (y : Term) (hlt : PrfH Γ (lt y (.var 3)))
    (hin : PrfH Γ (In y (acF p))) (v' s' : Term) (hws : PrfH Γ (hasWit s')) :
    PrfH Γ (targetSubstfc v' s' y) :=
  PrfH.mp _ _ _
    (PrfH_and_elim_left (PHI_use y p v' s' (PrfH.mp _ _ _ (PSI_inst hpsi y) hlt)))
    (PrfH_and_intro hws (PrfH_and_intro htr hin))

/-- HI en un hijo de sort TERMINO. -/
theorem ihT_at {Γ : List Formula} (hpsi : PrfH Γ PSI3) (p : Term)
    (htr : PrfH Γ (tripleOkE p)) (y : Term) (hlt : PrfH Γ (lt y (.var 3)))
    (hin : PrfH Γ (In y (acT p))) (v' s' : Term) :
    PrfH Γ (targetSubsttc v' s' y) :=
  PrfH.mp _ _ _
    (PrfH_and_elim_left (PrfH_and_elim_right
      (PHI_use y p v' s' (PrfH.mp _ _ _ (PSI_inst hpsi y) hlt))))
    (PrfH_and_intro htr hin)

/-- HI en un hijo de sort LISTA DE TERMINOS. -/
theorem ihTs_at {Γ : List Formula} (hpsi : PrfH Γ PSI3) (p : Term)
    (htr : PrfH Γ (tripleOkE p)) (y : Term) (hlt : PrfH Γ (lt y (.var 3)))
    (hin : PrfH Γ (In y (acTs p))) (v' s' : Term) :
    PrfH Γ (targetSubsttsc v' s' y) :=
  PrfH.mp _ _ _
    (PrfH_and_elim_right (PrfH_and_elim_right
      (PHI_use y p v' s' (PrfH.mp _ _ _ (PSI_inst hpsi y) hlt))))
    (PrfH_and_intro htr hin)

/-- Transporte del descenso a traves de la ecuacion de forma. -/
theorem lt_of_shape {Γ : List Formula} {X D y : Term} (hsh : PrfH Γ (Formula.eq X D))
    (h : Prf (lt y D)) : PrfH Γ (lt y X) :=
  ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hsh) (prf_to_prfH h _)

/-! ### §9.1 · LA MITAD DE FORMULA — los OCHO disyuntos -/

def AntF : Formula := land (hasWit (.var 0)) (isFCE3 (.var 2) (.var 3))
def GF : List Formula := [AntF, PSI3]
def chA : Term := nthc (.var 3) (numeralM 1)
def chB : Term := nthc (.var 3) (numeralM 2)

theorem hantF : PrfH GF AntF := PrfH.hyp _ _ (List.Mem.head _)

/-- Molde BINARIO con los dos hijos de sort FORMULA (tags 5, 7, 8). -/
theorem mold_bin_F (C : Cases) (k : Nat) (hk : Or (k = 5) (Or (k = 7) (k = 8))) :
    PrfH GF (Formula.impl
      (land (shapeBin (.var 3) k) (land (In chA (acF (.var 2))) (In chB (acF (.var 2)))))
      (targetSubstfc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ _ GF rfl
  have hd : PrfH (land (shapeBin (.var 3) k)
      (land (In chA (acF (.var 2))) (In chB (acF (.var 2)))) :: GF) _ :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hant : PrfH (land (shapeBin (.var 3) k)
      (land (In chA (acF (.var 2))) (In chB (acF (.var 2)))) :: GF) AntF :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (land (shapeBin (.var 3) k)
      (land (In chA (acF (.var 2))) (In chB (acF (.var 2)))) :: GF) PSI3 :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hsh := PrfH_and_elim_left hd
  have hmem := PrfH_and_elim_right hd
  have hw := PrfH_and_elim_left hant
  have htr := PrfH_and_elim_left (PrfH_and_elim_right hant)
  have hA := ihF_at hpsi (.var 2) htr chA (lt_of_shape hsh (lt_child_bin1 k chA chB))
    (PrfH_and_elim_left hmem) (.var 1) (.var 0) hw
  have hB := ihF_at hpsi (.var 2) htr chB (lt_of_shape hsh (lt_child_bin2 k chA chB))
    (PrfH_and_elim_right hmem) (.var 1) (.var 0) hw
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hsh)
    (PrfH.mp _ _ _ (prf_to_prfH (C.cBin k hk (.var 1) (.var 0) chA chB) _)
      (PrfH_and_intro hA hB))

/-- Molde UNARIO con hijo de sort FORMULA (tags 6, 9). -/
theorem mold_un_F (C : Cases) (m : Nat) (hm : Or (m = 6) (m = 9)) :
    PrfH GF (Formula.impl (land (shapeUn (.var 3) m) (In chA (acF (.var 2))))
      (targetSubstfc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ _ GF rfl
  have hd : PrfH (land (shapeUn (.var 3) m) (In chA (acF (.var 2))) :: GF) _ :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hant : PrfH (land (shapeUn (.var 3) m) (In chA (acF (.var 2))) :: GF) AntF :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (land (shapeUn (.var 3) m) (In chA (acF (.var 2))) :: GF) PSI3 :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hsh := PrfH_and_elim_left hd
  have hmem := PrfH_and_elim_right hd
  have hw := PrfH_and_elim_left hant
  have htr := PrfH_and_elim_left (PrfH_and_elim_right hant)
  have hwl := PrfH.mp _ _ _ (prf_to_prfH (C.cLift (.var 0)) _) hw
  have hA := ihF_at hpsi (.var 2) htr chA (lt_of_shape hsh (lt_child_un m chA)) hmem
    (succ (.var 1)) (liftc zero (.var 0)) hwl
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hsh)
    (PrfH.mp _ _ _ (prf_to_prfH (C.cUn m hm (.var 1) (.var 0) chA) _)
      (PrfH_and_intro hw hA))

/-- tag 2 · `botc`. -/
theorem br_nul (C : Cases) :
    PrfH GF (Formula.impl (shapeNul (.var 3) 2)
      (targetSubstfc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ _ GF rfl
  have hd : PrfH (shapeNul (.var 3) 2 :: GF) (shapeNul (.var 3) 2) :=
    PrfH.hyp _ _ (List.Mem.head _)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hd)
    (prf_to_prfH (C.cBot (.var 1) (.var 0)) _)

/-- tag 3 · `atomc`: la casilla 2 es una LISTA de codigos de termino. -/
theorem br_atom (C : Cases) :
    PrfH GF (Formula.impl (land (shapeBin (.var 3) 3) (In chB (acTs (.var 2))))
      (targetSubstfc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ _ GF rfl
  have hd : PrfH (land (shapeBin (.var 3) 3) (In chB (acTs (.var 2))) :: GF) _ :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hant : PrfH (land (shapeBin (.var 3) 3) (In chB (acTs (.var 2))) :: GF) AntF :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (land (shapeBin (.var 3) 3) (In chB (acTs (.var 2))) :: GF) PSI3 :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hsh := PrfH_and_elim_left hd
  have hmem := PrfH_and_elim_right hd
  have htr := PrfH_and_elim_left (PrfH_and_elim_right hant)
  have hB := ihTs_at hpsi (.var 2) htr chB (lt_of_shape hsh (lt_child_bin2 3 chA chB))
    hmem (.var 1) (.var 0)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hsh)
    (PrfH.mp _ _ _ (prf_to_prfH (C.cAtom (.var 1) (.var 0) chA chB) _) hB)

/-- tag 4 · `eqc`: las dos casillas son codigos de TERMINO. -/
theorem br_eq (C : Cases) :
    PrfH GF (Formula.impl
      (land (shapeBin (.var 3) 4) (land (In chA (acT (.var 2))) (In chB (acT (.var 2)))))
      (targetSubstfc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ _ GF rfl
  have hd : PrfH (land (shapeBin (.var 3) 4)
      (land (In chA (acT (.var 2))) (In chB (acT (.var 2)))) :: GF) _ :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hant : PrfH (land (shapeBin (.var 3) 4)
      (land (In chA (acT (.var 2))) (In chB (acT (.var 2)))) :: GF) AntF :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (land (shapeBin (.var 3) 4)
      (land (In chA (acT (.var 2))) (In chB (acT (.var 2)))) :: GF) PSI3 :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hsh := PrfH_and_elim_left hd
  have hmem := PrfH_and_elim_right hd
  have htr := PrfH_and_elim_left (PrfH_and_elim_right hant)
  have hA := ihT_at hpsi (.var 2) htr chA (lt_of_shape hsh (lt_child_bin1 4 chA chB))
    (PrfH_and_elim_left hmem) (.var 1) (.var 0)
  have hB := ihT_at hpsi (.var 2) htr chB (lt_of_shape hsh (lt_child_bin2 4 chA chB))
    (PrfH_and_elim_right hmem) (.var 1) (.var 0)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hsh)
    (PrfH.mp _ _ _ (prf_to_prfH (C.cEq (.var 1) (.var 0) chA chB) _)
      (PrfH_and_intro hA hB))

/-- **LA MITAD DE FORMULA, ENTERA**: los ocho disyuntos ensamblados. -/
theorem half_F (C : Cases) :
    PrfH [PSI3] (Formula.impl AntF (targetSubstfc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ AntF [PSI3] rfl
  have hcode : PrfH GF (isFormCodeE (acF (.var 2)) (acT (.var 2)) (acTs (.var 2)) (.var 3)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isFormCodeE_of_In (.var 2) (.var 3)) _)
      (PrfH_and_elim_right (PrfH_and_elim_right hantF)))
      (PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_right hantF)))
  exact PrfH.mp _ _ _
    (PrfH_or_imp (br_nul C)
      (PrfH_or_imp (br_atom C)
        (PrfH_or_imp (br_eq C)
          (PrfH_or_imp (mold_bin_F C 5 (Or.inl rfl))
            (PrfH_or_imp (mold_un_F C 6 (Or.inl rfl))
              (PrfH_or_imp (mold_bin_F C 7 (Or.inr (Or.inl rfl)))
                (PrfH_or_imp (mold_bin_F C 8 (Or.inr (Or.inr rfl)))
                  (mold_un_F C 9 (Or.inr rfl))))))))) hcode

/-! ### §9.2 · LA MITAD DE TERMINO — los DOS disyuntos -/

def AntT : Formula := isTCE3 (.var 2) (.var 3)
def GT : List Formula := [AntT, PSI3]

theorem half_T (C : Cases) :
    PrfH [PSI3] (Formula.impl AntT (targetSubsttc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ AntT [PSI3] rfl
  have hant : PrfH GT AntT := PrfH.hyp _ _ (List.Mem.head _)
  have hcode : PrfH GT (isTermCodeE (acT (.var 2)) (acTs (.var 2)) (.var 3)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isTermCodeE_of_In (.var 2) (.var 3)) _)
      (PrfH_and_elim_right hant))
      (PrfH_and_elim_left (PrfH_and_elim_right (PrfH_and_elim_left hant)))
  have brVar : PrfH GT (Formula.impl (shapeUn (.var 3) 0)
      (targetSubsttc (.var 1) (.var 0) (.var 3))) :=
    prf_to_prfH (C.cVar (.var 1) (.var 0) (.var 3)) _
  have brFunc : PrfH GT (Formula.impl
      (land (shapeBin (.var 3) 1) (In chB (acTs (.var 2))))
      (targetSubsttc (.var 1) (.var 0) (.var 3))) := by
    refine deduction_aux ?_ _ GT rfl
    have hd : PrfH (land (shapeBin (.var 3) 1) (In chB (acTs (.var 2))) :: GT) _ :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hant2 : PrfH (land (shapeBin (.var 3) 1) (In chB (acTs (.var 2))) :: GT) AntT :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hpsi : PrfH (land (shapeBin (.var 3) 1) (In chB (acTs (.var 2))) :: GT) PSI3 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hsh := PrfH_and_elim_left hd
    have hmem := PrfH_and_elim_right hd
    have htr := PrfH_and_elim_left hant2
    have hB := ihTs_at hpsi (.var 2) htr chB (lt_of_shape hsh (lt_child_bin2 1 chA chB))
      hmem (.var 1) (.var 0)
    exact PrfH_congr_targetSubsttc (PrfH_eq_symm hsh)
      (PrfH.mp _ _ _ (prf_to_prfH (C.cFunc (.var 1) (.var 0) chA chB) _) hB)
  exact PrfH.mp _ _ _ (PrfH_or_imp brVar brFunc) hcode

/-! ### §9.3 · LA MITAD DE LISTA — los DOS disyuntos -/

def AntTs : Formula := isTsCE3 (.var 2) (.var 3)
def GTs : List Formula := [AntTs, PSI3]

theorem half_Ts (C : Cases) :
    PrfH [PSI3] (Formula.impl AntTs (targetSubsttsc (.var 1) (.var 0) (.var 3))) := by
  refine deduction_aux ?_ AntTs [PSI3] rfl
  have hant : PrfH GTs AntTs := PrfH.hyp _ _ (List.Mem.head _)
  have hcode : PrfH GTs (isTermsCodeE (acT (.var 2)) (acTs (.var 2)) (.var 3)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isTermsCodeE_of_In (.var 2) (.var 3)) _)
      (PrfH_and_elim_right hant))
      (PrfH_and_elim_right (PrfH_and_elim_right (PrfH_and_elim_left hant)))
  have brNil : PrfH GTs (Formula.impl (Formula.eq (.var 3) nil)
      (targetSubsttsc (.var 1) (.var 0) (.var 3))) := by
    refine deduction_aux ?_ _ GTs rfl
    have hd : PrfH (Formula.eq (.var 3) nil :: GTs) (Formula.eq (.var 3) nil) :=
      PrfH.hyp _ _ (List.Mem.head _)
    exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hd)
      (prf_to_prfH (C.cNil (.var 1) (.var 0)) _)
  have brCons : PrfH GTs (Formula.impl
      (land (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3))))
        (land (In (carc (.var 3)) (acT (.var 2))) (In (cdrc (.var 3)) (acTs (.var 2)))))
      (targetSubsttsc (.var 1) (.var 0) (.var 3))) := by
    refine deduction_aux ?_ _ GTs rfl
    have hd : PrfH (land (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3))))
        (land (In (carc (.var 3)) (acT (.var 2)))
          (In (cdrc (.var 3)) (acTs (.var 2)))) :: GTs) _ :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hant2 : PrfH (land (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3))))
        (land (In (carc (.var 3)) (acT (.var 2)))
          (In (cdrc (.var 3)) (acTs (.var 2)))) :: GTs) AntTs :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hpsi : PrfH (land (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3))))
        (land (In (carc (.var 3)) (acT (.var 2)))
          (In (cdrc (.var 3)) (acTs (.var 2)))) :: GTs) PSI3 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hsh := PrfH_and_elim_left hd
    have hmem := PrfH_and_elim_right hd
    have htr := PrfH_and_elim_left hant2
    have hH := ihT_at hpsi (.var 2) htr (carc (.var 3))
      (lt_of_shape hsh (prf_cantor_mono_left (carc (.var 3)) (cdrc (.var 3))))
      (PrfH_and_elim_left hmem) (.var 1) (.var 0)
    have hT := ihTs_at hpsi (.var 2) htr (cdrc (.var 3))
      (lt_of_shape hsh (prf_cantor_mono_right (carc (.var 3)) (cdrc (.var 3))))
      (PrfH_and_elim_right hmem) (.var 1) (.var 0)
    exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hsh)
      (PrfH.mp _ _ _ (prf_to_prfH (C.cCons (.var 1) (.var 0)
        (carc (.var 3)) (cdrc (.var 3))) _) (PrfH_and_intro hH hT))
  exact PrfH.mp _ _ _ (PrfH_or_imp brNil brCons) hcode

/-! ### §9.4 · EL PASO, ENSAMBLADO -/

theorem PHI_step (C : Cases) : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] (Formula.forall (Formula.forall PHIbody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIbody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSI3] PHIbody
  exact PrfH_and_intro (half_F C) (PrfH_and_intro (half_T C) (half_Ts C))

/-! ############################################################################
    ## §10 · EL DESCENSO y `pcc_eval_substfc`
    ############################################################################ -/

theorem PHI_all (C : Cases) (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI1 (PHI_step C) t

theorem DESCENSO_fc (C : Cases) (p v s t : Term) :
    Prf (Formula.impl (land (hasWit s) (isFCE3 p t)) (targetSubstfc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PHI_use t p v s (prf_to_prfH (PHI_all C t) []))) rfl

theorem DESCENSO_tc (C : Cases) (p v s t : Term) :
    Prf (Formula.impl (isTCE3 p t) (targetSubsttc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PrfH_and_elim_right
      (PHI_use t p v s (prf_to_prfH (PHI_all C t) [])))) rfl

theorem DESCENSO_tsc (C : Cases) (p v s t : Term) :
    Prf (Formula.impl (isTsCE3 p t) (targetSubsttsc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_right (PrfH_and_elim_right
      (PHI_use t p v s (prf_to_prfH (PHI_all C t) [])))) rfl

/-- **`pcc_eval_substfc`** — el objetivo del encargo, con `v`, `s`, `f` **ABSTRACTOS**,
    el testigo de parseo `p` y la guarda `hasWit s` sobre el sustituyendo. -/
theorem pcc_eval_substfc (C : Cases) (p v s f : Term)
    (hwit : Prf (isFCE3 p f)) (hguard : Prf (hasWit s)) :
    Prf (provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f))
      (tcFn (substfc v s f)))) :=
  prf_mp (DESCENSO_fc C p v s f) (prf_and_intro hguard hwit)

/-! ############################################################################
    ## §11 · CONTROLES DE NO VACUIDAD del reconocedor en forma ECUACIONAL
    ############################################################################

    ⚠️ El control que A3 se salto: un reconocedor puede ser VERDADERO y VACIO.
    Aqui se comprueba que `isFormCodeE` **acepta** un nodo binario REAL (`implc`) y que
    `isTermsCodeE` acepta `nil` — o sea que el antecedente de la induccion tiene testigos. -/

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s; simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) := prf_mp (Prf.incl (Prf₀.j1 A B)) h
theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) := prf_mp (Prf.incl (Prf₀.j2 A B)) h

/-- Un nodo binario REAL satisface su forma ecuacional (copia de
    `DiscriminaEcuacional.PasoUno.prf_shapeBin_real`). -/
theorem prf_shapeBin_real (k : Nat) (a b : Term) : Prf (shapeBin (bnc k a b) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
    (prf_congr_cons_head (prf_nthc_c1 (numeralM k) a (cons b nil)))
    (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c2 (numeralM k) a b nil)))))

/-- **NO VACUIDAD del disyunto `implc`** — `isFormCodeE` acepta un nodo REAL. -/
theorem CTRL_isFormCodeE_implc (wF wT wTs a b : Term)
    (ha : Prf (In a wF)) (hb : Prf (In b wF)) : Prf (isFormCodeE wF wT wTs (implc a b)) := by
  have h1 : Prf (In (nthc (implc a b) (numeralM 1)) wF) :=
    prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM 5) a (cons b nil))) ha
  have h2 : Prf (In (nthc (implc a b) (numeralM 2)) wF) :=
    prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM 5) a b nil)) hb
  exact prf_orR (prf_orR (prf_orR (prf_orL
    (prf_and_intro (prf_shapeBin_real 5 a b) (prf_and_intro h1 h2)))))

/-- **NO VACUIDAD del disyunto DESNUDO** de `isTermsCodeE`. -/
theorem CTRL_isTermsCodeE_nil (wT wTs : Term) : Prf (isTermsCodeE wT wTs nil) :=
  prf_orL (prf_refl nil)

/-- CONTROL: el predicado de la induccion NO colapsa los tres sorts. -/
example (p X : Term) : True := by
  fail_if_success exact (rfl : isFCE3 p X = isTCE3 p X)
  fail_if_success exact (rfl : isTCE3 p X = isTsCE3 p X)
  trivial

/-! ############################################################################
    ## §12 · LA OBLIGACION RESIDUAL, EN SU FORMA MINIMA:
    ##       **Γ-PARAMETRIZAR** los cinco lemas de caso que ya compilan
    ############################################################################

    Los lemas de caso de `substfc` estan escritos con las HI como hipotesis **META**
    (`Prf A → Prf C`), y la induccion solo puede consumir implicaciones **OBJETO**
    (`Prf (A ⇒ C)`), porque la HI unicamente esta disponible DENTRO del contexto `Γ`.

    🔑 **Pero la conversion NO exige rehacer las pruebas: exige Γ-PARAMETRIZARLAS.**
    Los dos puentes de abajo lo demuestran: de la version `∀ Γ, PrfH Γ A → PrfH Γ C`
    sale la forma implicacion **en una linea**. Y la version Γ-parametrica se obtiene
    de la prueba EXISTENTE cambiando `Prf X` por `PrfH Γ X` en hipotesis y conclusion
    (los pasos cerrados ya entran por `prf_to_prfH _ Γ`, que es como estan escritos). -/

theorem imp_of_ctx1 {A C : Formula} (h : ∀ Γ : List Formula, PrfH Γ A → PrfH Γ C) :
    Prf (Formula.impl A C) := prf_deduction (h [A] (prfH_hyp_self A))

theorem imp_of_ctx2 {A B C : Formula}
    (h : ∀ Γ : List Formula, PrfH Γ A → PrfH Γ B → PrfH Γ C) :
    Prf (Formula.impl (land A B) C) :=
  prf_deduction (h [land A B] (PrfH_and_elim_left (prfH_hyp_self _))
    (PrfH_and_elim_right (prfH_hyp_self _)))

/-- **LA OBLIGACION RESIDUAL EXACTA**: los mismos diez lemas, cinco de ellos en version
    Γ-parametrica. Cuatro (`cVarC`/`cNilC`/`cBotC`/`cLiftC`) ya existen TAL CUAL. -/
structure CasesCtx : Prop where
  /-- = `SubstfcPlanos.paso2_caso_bottom` (ya existe, sin cambios). -/
  cBotC  : ∀ v s : Term, Prf (targetSubstfc v s botc)
  /-- NUEVO: no existe lema de caso para `atomc`; existen sus INGREDIENTES
      (`EvalSubsttc.pcc_eval_substtsc'`). -/
  cAtomC : ∀ (Γ : List Formula) (v s a b : Term),
    PrfH Γ (targetSubsttsc v s b) → PrfH Γ (targetSubstfc v s (atomc a b))
  /-- NUEVO: idem para `eqc`; ingredientes en `EvalSubsttc.pcc_eval_substtc'`. -/
  cEqC   : ∀ (Γ : List Formula) (v s a b : Term),
    PrfH Γ (targetSubsttc v s a) → PrfH Γ (targetSubsttc v s b) →
    PrfH Γ (targetSubstfc v s (eqc a b))
  /-- = `SubstfcPlanos.paso2_caso_bin` Γ-PARAMETRIZADO (tags 5/7/8). -/
  cBinC  : ∀ (k : Nat), (Or (k = 5) (Or (k = 7) (k = 8))) →
    ∀ (Γ : List Formula) (v s a b : Term),
    PrfH Γ (targetSubstfc v s a) → PrfH Γ (targetSubstfc v s b) →
    PrfH Γ (targetSubstfc v s (bnc k a b))
  /-- = `SubstfcEx.paso2_caso_un_guarded` Γ-PARAMETRIZADO (tags 6/9). -/
  cUnC   : ∀ (m : Nat), (Or (m = 6) (m = 9)) → ∀ (Γ : List Formula) (v s a : Term),
    PrfH Γ (hasWit s) → PrfH Γ (targetSubstfc (succ v) (liftc zero s) a) →
    PrfH Γ (targetSubstfc v s (unc m a))
  /-- = `Paso2Guardado.CRIT_hasWit_lift'` (ya existe, sin cambios). -/
  cLiftC : ∀ s : Term, Prf (Formula.impl (hasWit s) (hasWit (liftc zero s)))
  /-- = `EvalSubsttc.refl_shapeUn_imp predHyp` (ya existe, sin cambios). -/
  cVarC  : ∀ v s X : Term, Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X))
  /-- = `EvalSubsttc.refl_caso_funcc_imp` (ya existe, sin cambios). -/
  cFuncC : ∀ v s a b : Term,
    Prf (Formula.impl (targetSubsttsc v s b) (targetSubsttc v s (funcc a b)))
  /-- = `EvalSubsttc.refl_lista_nil` (ya existe, sin cambios). -/
  cNilC  : ∀ v s : Term, Prf (targetSubsttsc v s nil)
  /-- = `EvalSubsttc.refl_lista_cons_imp` (ya existe, sin cambios). -/
  cConsC : ∀ v s h t : Term,
    Prf (Formula.impl (land (targetSubsttc v s h) (targetSubsttsc v s t))
      (targetSubsttsc v s (cons h t)))

/-- **EL PUENTE, PROBADO**: la version Γ-parametrica alimenta la induccion. -/
theorem cases_of_ctx (D : CasesCtx) : Cases where
  cBot  := D.cBotC
  cAtom := fun v s a b => imp_of_ctx1 (fun Γ h => D.cAtomC Γ v s a b h)
  cEq   := fun v s a b => imp_of_ctx2 (fun Γ h1 h2 => D.cEqC Γ v s a b h1 h2)
  cBin  := fun k hk v s a b => imp_of_ctx2 (fun Γ h1 h2 => D.cBinC k hk Γ v s a b h1 h2)
  cUn   := fun m hm v s a => imp_of_ctx2 (fun Γ h1 h2 => D.cUnC m hm Γ v s a h1 h2)
  cLift := D.cLiftC
  cVar  := D.cVarC
  cFunc := D.cFuncC
  cNil  := D.cNilC
  cCons := D.cConsC

/-- **`pcc_eval_substfc` MODULO la obligacion residual MINIMA.** -/
theorem pcc_eval_substfc_ctx (D : CasesCtx) (p v s f : Term)
    (hwit : Prf (isFCE3 p f)) (hguard : Prf (hasWit s)) :
    Prf (provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f))
      (tcFn (substfc v s f)))) :=
  pcc_eval_substfc (cases_of_ctx D) p v s f hwit hguard

end ENS3

#print axioms ENS3.hPHI1
#print axioms ENS3.cases_of_ctx
#print axioms ENS3.pcc_eval_substfc_ctx
#print axioms ENS3.CTRL_isFormCodeE_implc
#print axioms ENS3.CTRL_isTermsCodeE_nil
#print axioms ENS3.PHI_use
#print axioms ENS3.PSI_inst
#print axioms ENS3.prf_isFormCodeE_of_In
#print axioms ENS3.half_F
#print axioms ENS3.half_T
#print axioms ENS3.half_Ts
#print axioms ENS3.PHI_step
#print axioms ENS3.PHI_all
#print axioms ENS3.pcc_eval_substfc
#check @ENS3.hPHI1
#check @ENS3.PHI_step
#check @ENS3.pcc_eval_substfc


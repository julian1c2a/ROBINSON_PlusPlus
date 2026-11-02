import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.EvalNthcPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf

/-!
# `Probe/B2_conexion.lean` — ANGULO (C): ¿CONECTA el DESCENSO con PRODUCCION?

⚠️ La lista de `import` de arriba es la CONCRETA (30 modulos de `Meta/`, ninguno es el
barrel): es directamente la que necesita el modulo `Meta/DescensoLiftcPrf.lean` de B2.

Pregunta: `sondeos/DescensoLiftc.lean` (rama B2) redefine `targetLift`, `targetLiftsc`, las
cuatro clausulas del reflector, `isTC1`/`wfAll1`/`argsIn`/`hasWit` y toda la fontaneria.
Produccion ya las tiene (`Meta/LiftcCodePrf.lean`, `Meta/CodeWitnessPrf.lean`).
¿El descenso se reconstruye SOBRE el vocabulario de produccion, o queda enganchado a sus copias?

Este fichero responde COMPILANDO, en dos partes:

* **§0 PUENTES**: copias LITERALES de las definiciones del sondeo, cada una con su `:= rfl`
  contra la de produccion. Si algo no fuese la misma definicion, el `rfl` fallaria.
* **§1–§7 RECONSTRUCCION**: el DESCENSO ENTERO, reconstruido consumiendo SOLO produccion.
  Ni un `targetLift` local, ni un `isTC1` local, ni una clausula de reflector local.
* **§8 CONSUMIDOR**: el `hLift` de `sondeos/Paso2CasoForall.lean:507`, descargado.
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.EvalRunFnPrf

/-! ⚠️ `open` SELECTIVO de `CodeWitnessPrf.SinWTs`: abrirlo entero trae
    `SinWTs.prf_congr_liftc (v : Term) …`, AMBIGUO con `NumCodeClosedPrf.prf_congr_liftc`. -/
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
  (consOk argsIn argsInBody shapeUn shapeBin isTermCodeE1 wfAll1 wfAll1Body isTC1
   prf_cdrc_cons prf_consOk_cons PrfH_congr_lenc PrfH_congr_nthc_lst PrfH_congr_In_left
   liftF_argsIn substF_argsIn liftF_isTermCodeE1 substF_isTermCodeE1 liftF_wfAll1
   PrfH_congr_argsIn PrfH_congr_isTermCodeE1 PrfH_inst_argsIn PrfH_inst_wfAll1
   prf_congr_argsIn prf_congr_In_left prf_orL prf_orR impT)

/-! ⚠️ `substF_wfAll1`, `substF_isTC1`, `liftF_isTC1` y `hasWit` viven en `ENS`, no en
    `SinWTs`. `open` selectivo tambien: `ENS` re-prueba `liftF_argsIn`… (duplicado INTERNO
    de produccion, ver informe) y abrirlo entero seria ambiguo con `SinWTs`. -/
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS
  (hasWit substF_wfAll1 substF_isTC1 liftF_isTC1)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! ############################################################################
    ## §0 · LOS PUENTES — cada definicion del sondeo contra la de PRODUCCION
    ############################################################################ -/

namespace SondeoCopia

/-- `sondeos/DescensoLiftc.lean:56` -/
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
/-- `sondeos/DescensoLiftc.lean:57` -/
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))
/-- `sondeos/DescensoLiftc.lean:61` -/
def varcT (X : Term) : Term := unT 0 X
/-- `sondeos/DescensoLiftc.lean:63` -/
def funccT (X Y : Term) : Term := binT 1 X Y

/-- `sondeos/DescensoLiftc.lean:79` -/
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))
/-- `sondeos/DescensoLiftc.lean:535` -/
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

/-- `sondeos/DescensoLiftc.lean:676` -/
def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
/-- `sondeos/DescensoLiftc.lean:678` -/
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

/-- `sondeos/DescensoLiftc.lean:862` -/
def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
/-- `sondeos/DescensoLiftc.lean:865` -/
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)
/-- `sondeos/DescensoLiftc.lean:867` -/
def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0)
      (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

/-- `sondeos/DescensoLiftc.lean:889` -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
/-- `sondeos/DescensoLiftc.lean:892` -/
def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
/-- `sondeos/DescensoLiftc.lean:897` -/
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)
/-- `sondeos/DescensoLiftc.lean:899` -/
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

/-- `sondeos/DescensoLiftc.lean:1386` -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

end SondeoCopia

/-! ### §0.1 · PUENTE 1 — `targetLift` / `targetLiftsc` (el punto CRITICO del encargo).

    `LiftcCodePrf:225` y `:229`. Si estos `rfl` fallasen, B2 introduciria DOS constantes y el
    descenso no conectaria con nada. NO fallan. -/

theorem BRIDGE_liftcT (c t : Term) :
    SondeoCopia.liftcT c t = ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT c t := rfl
theorem BRIDGE_liftscT (c t : Term) :
    SondeoCopia.liftscT c t = ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT c t := rfl
theorem BRIDGE_varcT (X : Term) :
    SondeoCopia.varcT X = ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT X := rfl
theorem BRIDGE_funccT (X Y : Term) :
    SondeoCopia.funccT X Y = ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT X Y := rfl

theorem BRIDGE_targetLift (s : Term) :
    SondeoCopia.targetLift s = ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s := rfl
theorem BRIDGE_targetLiftsc (b : Term) :
    SondeoCopia.targetLiftsc b = ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc b := rfl

/-! ### §0.2 · PUENTE 2 — el reconocedor: `CodeWitnessPrf.SinWTs` / `ENS`. -/

theorem BRIDGE_shapeUn (X : Term) (k : Nat) :
    SondeoCopia.shapeUn X k = shapeUn X k := rfl
theorem BRIDGE_shapeBin (X : Term) (k : Nat) :
    SondeoCopia.shapeBin X k = shapeBin X k := rfl
theorem BRIDGE_argsInBody (wT Y : Term) :
    SondeoCopia.argsInBody wT Y = argsInBody wT Y := rfl
theorem BRIDGE_argsIn (wT Y : Term) : SondeoCopia.argsIn wT Y = argsIn wT Y := rfl
theorem BRIDGE_isTermCodeE1 (wT X : Term) :
    SondeoCopia.isTermCodeE1 wT X = isTermCodeE1 wT X := rfl
theorem BRIDGE_consOk (X : Term) : SondeoCopia.consOk X = consOk X := rfl
theorem BRIDGE_wfAll1Body (w : Term) : SondeoCopia.wfAll1Body w = wfAll1Body w := rfl
theorem BRIDGE_wfAll1 (w : Term) : SondeoCopia.wfAll1 w = wfAll1 w := rfl
theorem BRIDGE_isTC1 (w c : Term) : SondeoCopia.isTC1 w c = isTC1 w c := rfl
theorem BRIDGE_hasWit (c : Term) : SondeoCopia.hasWit c = hasWit c := rfl

/-! ### §0.3 · PUENTE 3 — los DUPLICADOS que el encargo ya conocia, RE-CONFIRMADOS. -/

/-- `DescensoLiftc.lean:538` (`iz_inv`) **=** `EvalRunFnPrf.prf_substtc_termCode_nil`
    (`nil := zero`, `Minimal/Axioms.lean:126`). NO promover. -/
theorem BRIDGE_iz_inv :
    (fun W => prf_substtc_termCode_nil W)
      = (fun W : Term => ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil W) := rfl

example : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_nil

/-- `DescensoLiftc.lean:74` (`eqc_eq_eqCodeFn`) = `Sigma1AtomPrf.eqCodeFn_eq_eqc` invertido.
    NO promover. -/
theorem BRIDGE_eqc (a b : Term) : eqc a b = eqCodeFn a b :=
  (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc a b).symm

/-! ### §0.4 · PUENTE 4 — DUPLICADOS NUEVOS que este angulo destapa.

    Las §A/§B del sondeo (lineas 56-860) son COPIA de `ReflectorDesdeConsumidor.lean`, que ya
    se promovio ENTERO ayer. Todas estas ya estan en produccion; el sondeo las repite. -/

example (c a b : Term) :
    Prf (provFromCode (eqCodeFn
      (ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT (tcFn c)
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT (tcFn a) (tcFn b)))
      (ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT (tcFn a)
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT (tcFn c) (tcFn b))))) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_func_code c a b

example (s a : Term) (hs : Prf (s =eq varc a)) :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc s a hs

example : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil

example (h t : Term)
    (hh : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift h))
    (ht : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc t)) :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc (cons h t)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons h t hh ht

/-- El sondeo re-prueba `PrfH_eq_trans_code` (`:730`). Ya esta en produccion. -/
example {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z))) :
    PrfH Γ (provFromCode (eqc X Z)) :=
  ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code X Y Z hX h1 h2

/-! ############################################################################
    ## §1 · LA RECONSTRUCCION — a partir de aqui, SOLO vocabulario de PRODUCCION.

    `targetLift`, `targetLiftsc`, `refl_*_imp`, `refl_lista_nil` : `Meta/LiftcCodePrf`.
    `isTC1`, `wfAll1`, `argsIn`, `isTermCodeE1`, `shapeUn/Bin`, `consOk`, `hasWit`:
      `Meta/CodeWitnessPrf` (`SinWTs` / `ENS`).
    Nada de lo que sigue vuelve a definir ninguno de ellos.
    ############################################################################ -/

namespace B2

open ROBINSON_PlusPlus.Meta.LiftcCodePrf
  (targetLift targetLiftsc liftcT liftscT
   refl_shapeUn_imp refl_shapeBin_imp refl_lista_cons_imp refl_lista_nil
   PrfH_congr_targetLift substF_targetLift_hole)

/-! ### §1 · `liftFormula`/`substFormula` atraviesan los DOS objetivos de PRODUCCION.

    Produccion solo tiene `substF_targetLift_hole` (el hueco `#0`). Estas cuatro son NUEVAS:
    van sobre `LiftcCodePrf.targetLift` / `.targetLiftsc`, no sobre copias. -/

theorem liftF_targetLift (k : Nat) (s : Term) :
    liftFormula k (targetLift s) = targetLift (liftTerm k s) := by
  simp only [targetLift, liftFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

theorem liftF_targetLiftsc (k : Nat) (s : Term) :
    liftFormula k (targetLiftsc s) = targetLiftsc (liftTerm k s) := by
  simp only [targetLiftsc, liftFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

theorem substF_targetLift (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

theorem substF_targetLiftsc (v : Nat) (u s : Term) :
    substFormula v u (targetLiftsc s) = targetLiftsc (substTerm v u s) := by
  simp only [targetLiftsc, substFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- Leibniz sobre el argumento de `targetLiftsc`. La companera `PrfH_congr_targetLift` YA
    esta en produccion (`LiftcCodePrf:797`); esta NO. -/
theorem PrfH_congr_targetLiftsc {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLiftsc s)) : PrfH Γ (targetLiftsc s') := by
  have hS : ∀ u : Term, substFormula 0 u (targetLiftsc (.var 0)) = targetLiftsc u := by
    intro u
    rw [substF_targetLiftsc]
    simp only [substTerm, if_true]
  exact (hS s') ▸ PrfH_leibniz_subst (A := targetLiftsc (.var 0)) h ((hS s) ▸ ha)

/-! ### §2 · LA ESTRUCTURA: `⊢ Y ≐ nil ∨ consOk Y` para `Y` ARBITRARIO.
       `consOk` es el de PRODUCCION (`SinWTs:166`). -/

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
    exact prf_mp (Prf.incl (Prfᵢ.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-! ### §3 · `argsIn` se parte en CABEZA y COLA. `argsIn` es el de PRODUCCION. -/

theorem prf_argsIn_head (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (In hd w)) := by
  refine prf_deduction ?_
  have hargs : PrfH [argsIn w (cons hd tl)] (argsIn w (cons hd tl)) := prfH_hyp_self _
  have hlt : PrfH [argsIn w (cons hd tl)] (lt zero (lenc (cons hd tl))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_cons hd tl)) _)
      (prf_to_prfH (prf_zero_lt_succ (lenc tl)) _)
  have hin : PrfH [argsIn w (cons hd tl)] (In (nthc (cons hd tl) zero) w) :=
    PrfH.mp _ _ _ (PrfH_inst_argsIn w (cons hd tl) zero hargs) hlt
  exact PrfH_congr_In_left (prf_to_prfH (prf_nthc_zero hd tl) _) hin

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

/-! ### §4 · Del testigo al NODO. Todo con `wfAll1`/`isTermCodeE1` de PRODUCCION. -/

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

/-! ### §5 · EL PREDICADO DE LA INDUCCION FUERTE, sobre vocabulario de PRODUCCION. -/

def PHIbody : Formula :=
  land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
       (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
         (targetLiftsc (.var 1)))

def PHI : Formula := Formula.forall PHIbody

theorem hPHI : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetLift, liftF_targetLiftsc, liftTerm, Nat.reduceAdd, Nat.reduceLT, reduceIte]

theorem PHI_at (t : Term) :
    substFormula 0 t PHI = Formula.forall (
      land (Formula.impl (isTC1 (.var 0) (liftTerm 0 t)) (targetLift (liftTerm 0 t)))
           (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 t)))
             (targetLiftsc (liftTerm 0 t)))) := by
  simp only [PHI, PHIbody, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetLift, substF_targetLiftsc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_use {Γ : List Formula} (t w : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (land (Formula.impl (isTC1 w t) (targetLift t))
                 (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetLiftsc t))) := by
  rw [PHI_at] at h
  have hs := PrfH_spec h w
  simpa only [land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetLift, substF_targetLiftsc, substTerm, FOL.substTerm_liftTerm, if_true] using hs

theorem psi_lift_form :
    liftFormula 0 (PSI PHI) = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHI) := by
  simp only [PSI, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI]

theorem PSI_inst {Γ : List Formula} (hpsi : PrfH Γ (liftFormula 0 (PSI PHI))) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 1)) (substFormula 0 z PHI)) := by
  rw [psi_lift_form] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 2)) PHI)
      = Formula.impl (lt z (.var 1)) (substFormula 0 z PHI) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-! ### §6 · EL PASO DE LA INDUCCION FUERTE.

    ⚠️ EL PUNTO DEL ENCARGO: `PHI_step` consume las clausulas de PRODUCCION en la moneda
    **OBJETO** (`refl_shapeUn_imp`, `refl_shapeBin_imp`, `refl_lista_cons_imp`), NO las
    meta (`refl_caso_varc`, `refl_caso_funcc`, `refl_lista_cons`). La base `refl_lista_nil`
    es cerrada y sirve en las dos. -/

theorem PHI_step : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (isTC1 (.var 0) (.var 1)) [liftFormula 0 (PSI PHI)] rfl
    have hh : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (isTC1 (.var 0) (.var 1)) := PrfH.hyp _ _ (List.Mem.head _)
    have hpsi : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (liftFormula 0 (PSI PHI)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hwf : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (wfAll1 (.var 0)) := PrfH_and_elim_left hh
    have hin : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (In (.var 1) (.var 0)) := PrfH_and_elim_right hh
    have hitc : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (isTermCodeE1 (.var 0) (.var 1)) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) (.var 1)) _) hin) hwf
    refine PrfH_or_elim hitc ?varc ?func
    case varc =>
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp (.var 1)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    case func =>
      have hb : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
          (land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hwf' : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)] (wfAll1 (.var 0)) :=
        PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      have hpsi' : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)] (liftFormula 0 (PSI PHI)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hshape := PrfH_and_elim_left hb
      have hargs := PrfH_and_elim_right hb
      have h1 : Prf (lt (nthc (.var 1) (numeralM 2)) (cons (nthc (.var 1) (numeralM 2)) nil)) :=
        prf_cantor_mono_left _ _
      have h2 : Prf (lt (cons (nthc (.var 1) (numeralM 2)) nil)
          (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil))) :=
        prf_cantor_mono_right _ _
      have h3 : Prf (lt (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil))
          (cons (numeralM 1)
            (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil)))) :=
        prf_cantor_mono_right _ _
      have h12 : Prf (lt (nthc (.var 1) (numeralM 2))
          (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
      have h123 : Prf (lt (nthc (.var 1) (numeralM 2))
          (cons (numeralM 1)
            (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil)))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
      have hltb := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
      have hphi := PrfH.mp _ _ _ (PSI_inst hpsi' (nthc (.var 1) (numeralM 2))) hltb
      have huse := PHI_use (nthc (.var 1) (numeralM 2)) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp (.var 1)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
      [liftFormula 0 (PSI PHI)] rfl
    have hh : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
        (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) := PrfH.hyp _ _ (List.Mem.head _)
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 1)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 1) nil,
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (Formula.eq (.var 1) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetLiftsc (PrfH_eq_symm heq) (prf_to_prfH refl_lista_nil _)
    case consc =>
      have hcons : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh' : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (liftFormula 0 (PSI PHI)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hwf := PrfH_and_elim_left hh'
      have hargs := PrfH_and_elim_right hh'
      have hlenX := PrfH_eq_trans (PrfH_congr_lenc hcons)
        (prf_to_prfH (prf_lenc_cons (carc (.var 1)) (cdrc (.var 1))) _)
      have hzlt := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hlenX) (prf_to_prfH (prf_zero_lt_succ (lenc (cdrc (.var 1)))) _)
      have hin0 := PrfH.mp _ _ _
        (PrfH_inst_argsIn (.var 0) (.var 1) zero hargs) hzlt
      have hnth0 := PrfH_eq_trans (PrfH_congr_nthc_lst zero hcons)
        (prf_to_prfH (prf_nthc_zero (carc (.var 1)) (cdrc (.var 1))) _)
      have hinhd := PrfH_congr_In_left hnth0 hin0
      have hlthd := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_left (carc (.var 1)) (cdrc (.var 1))) _)
      have huse_hd := PHI_use (carc (.var 1)) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (carc (.var 1))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 0) (carc (.var 1)) (cdrc (.var 1))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 1)) (cdrc (.var 1))) _)
      have huse_tl := PHI_use (cdrc (.var 1)) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (cdrc (.var 1))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp (carc (.var 1)) (cdrc (.var 1))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetLiftsc (PrfH_eq_symm hcons) hres

/-! ### §7 · EL DESCENSO -/

theorem PHI_all (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI PHI_step t

theorem DESCENSO_imp (w s : Term) : Prf (Formula.impl (isTC1 w s) (targetLift s)) :=
  prfH_nil_to_prf (PrfH_and_elim_left (PHI_use s w (prf_to_prfH (PHI_all s) []))) rfl

theorem DESCENSO_lista_imp (w s : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w s)) (targetLiftsc s)) :=
  prfH_nil_to_prf (PrfH_and_elim_right (PHI_use s w (prf_to_prfH (PHI_all s) []))) rfl

theorem DESCENSO (w s : Term) (h : Prf (isTC1 w s)) : Prf (targetLift s) :=
  prf_mp (DESCENSO_imp w s) h

theorem DESCENSO_lista (w s : Term) (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w s)) :
    Prf (targetLiftsc s) :=
  prf_mp (DESCENSO_lista_imp w s) (prf_and_intro hwf hargs)

theorem pcc_eval_liftc (w s : Term) (h : Prf (isTC1 w s)) :
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  DESCENSO w s h

/-- ⚠️ `hasWit` es el de PRODUCCION (`CodeWitnessPrf.ENS:1365`). El sondeo lo redefine
    (`:1386`) — es el 3.er duplicado destapado. -/
theorem DESCENSO_hasWit (s : Term) : Prf (Formula.impl (hasWit s) (targetLift s)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetLift]
  exact PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_imp (.var 0) (liftTerm 0 s)) _) (prfH_hyp_self _)

end B2

/-! ############################################################################
    ## §8 · EL CONSUMIDOR — `sondeos/Paso2CasoForall.lean:507`, LITERAL.

    `paso2_caso_forall` pide
      `hLift : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))`
    con `Paso2.liftcT` (`Paso2CasoForall.lean:90`), que es la MISMA definicion que
    `LiftcCodePrf.liftcT`. Se descarga con el descenso reconstruido.
    ############################################################################ -/

/-- La forma exacta del `hLift`, con `liftcT` de PRODUCCION. -/
theorem CONSUMIDOR_hLift (w s : Term)
    (h : Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 w s)) :
    Prf (provFromCode (eqc
      (ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT (termCode zero) (tcFn s))
      (tcFn (liftc zero s)))) :=
  B2.pcc_eval_liftc w s h

/-- Y por el testigo CUANTIFICADO, que es la forma que de verdad llega rio abajo. -/
theorem CONSUMIDOR_hLift_hasWit (s : Term)
    (h : Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit s)) :
    Prf (provFromCode (eqc
      (ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT (termCode zero) (tcFn s))
      (tcFn (liftc zero s)))) :=
  prf_mp (B2.DESCENSO_hasWit s) h

/-- CONTROL: la no-vacuidad. `CodeWitnessPrf.SinWTs.prf_isTC1_tcodes` (produccion) da el
    antecedente para codigos REALES ⇒ el descenso reconstruido no es vacuo. -/
theorem CONTROL_no_vacuo (t : Term) :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift (termCodeM t)) :=
  B2.DESCENSO _ _ (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTC1_tcodes t)

/-- CONTROL NEGATIVO: el objetivo no es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT (termCode zero) (tcFn s)
      = tcFn (liftc zero s))
  trivial

/-! ## CONTROL DE FOOTPRINT — todo NET-0 sobre la base sancionada. -/

#print axioms B2.PHI_step
#print axioms B2.DESCENSO
#print axioms B2.DESCENSO_hasWit
#print axioms B2.pcc_eval_liftc
#print axioms CONSUMIDOR_hLift
#print axioms CONSUMIDOR_hLift_hasWit
#print axioms CONTROL_no_vacuo
#print axioms BRIDGE_targetLift
#print axioms BRIDGE_targetLiftsc
#print axioms BRIDGE_isTC1
#print axioms BRIDGE_hasWit

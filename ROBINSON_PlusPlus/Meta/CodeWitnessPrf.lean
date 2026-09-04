import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.BdAllIntroPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.D3InDotPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalBoundedPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.EvalNthcPrf
import ROBINSON_PlusPlus.Meta.ForallElimCodePrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NatOrderPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
/-!
# `Meta/CodeWitnessPrf.lean` — TESTIGOS de buena‑formación de códigos, y su NO‑VACUIDAD

El vocabulario del frente `substfc` llega por fin a producción. Hasta ahora **ninguna** de estas
definiciones existía en `Meta/`: vivían sólo en `sondeos/`, redefinidas entre 10 y 13 veces.

Tres bloques, en orden de dependencia:

* **`SinWTs`** — el reconocedor de código de TÉRMINO con **una sola** lista testigo
  (`isTermCodeE1`, `wfAll1`, `isTC1`, `argsIn`), su maquinaria de clausura (`tcodes1`,
  `CodeClosed`, `objList`) y el reconocedor de FÓRMULA posicional (`isFormCodeB2`).
* **`ENS`** — el reconocedor de código de FÓRMULA en forma **ECUACIONAL** con **DOS** listas
  testigo (`isFormCodeE2`, `wfAllF`, `isFC1`, `hasWitF`), más su fontanería De Bruijn.
* **`HW`** — la **NO‑VACUIDAD**: `prf_hasWitF_real (φ) : Prf (ENS.hasWitF (formCodeM φ))`, con
  testigos **explícitos y computables** (`fcodesF`/`tcodesF`). Footprint **net‑0 puro**.

## ⚠️ Deduplicación hecha al promover

`ENS` redefinía **nueve** cosas que `SinWTs` ya tenía, byte a byte, y el fichero de sondeo lo
certificaba con puentes `rfl`. Promoverlas así habría metido en producción **dos constantes para
cada una** — la trampa registrada de «misma definición en dos namespaces». Se resolvió aquí:
`ENS` las toma de `SinWTs` con un `open`, y los puentes desaparecieron por innecesarios.

## Por qué es un módulo pequeño

Su footprint mínimo se **midió ejecutándolo** (`sondeos/HasWitFRealMin.lean`): la no‑vacuidad **no
necesita** el descenso, ni `Paso2`, ni la evaluación de `substtc`, ni el ensamblaje de
`pcc_eval_substfc`. Por eso puede promoverse sola.

⚠️ Los predicados son **DEFINICIONES**: no se postula ninguna ecuación suya como axioma objeto.

Promovido de `sondeos/HasWitFRealMin.lean` (2026‑08‑31). Cero axiomas de Lean, cero `sorry`.
-/

namespace ROBINSON_PlusPlus.Meta.CodeWitnessPrf


set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-! ############################################################################
    COPIA LITERAL de `sondeos/SubstfcEx.lean` lineas 46-4111 (secciones S_Clausura,
    S_Descenso y S_Paso2), que compilan net-0. Aportan `DescMutua.DESCENSO_hasWit`,
    `SinWTs.CRIT_hasWit_lift` y todo el KIT unario `Paso2.*` que necesitan los tags
    6 (`forallc`) y 9 (`exc`).
    ############################################################################ -/
section S_Clausura
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace SinWTs

/-! ## 0 · Combinadores y copias LITERALES del piloto -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prf₀.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prf₀.j2 A B)

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) [])) rfl

theorem prf_congr_liftc {t₁ t₂ : Term} (v : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (liftc v t₁ =eq liftc v t₂) := by
  let f : Formula := Formula.eq (liftc (liftTerm 0 v) (liftTerm 0 t₁))
                                (liftc (liftTerm 0 v) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftc v t₁) (liftc v s) := by
    intro s
    simp only [f, liftc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (liftc v t₁)) [])) rfl

theorem prf_congr_liftsc {t₁ t₂ : Term} (v : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (liftsc v t₁ =eq liftsc v t₂) := by
  let f : Formula := Formula.eq (liftsc (liftTerm 0 v) (liftTerm 0 t₁))
                                (liftsc (liftTerm 0 v) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftsc v t₁) (liftsc v s) := by
    intro s
    simp only [f, liftsc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (liftsc v t₁)) [])) rfl

theorem prf_congr_nthc_lst {w₁ w₂ : Term} (i : Term) (h : Prf (w₁ =eq w₂)) :
    Prf (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) [])) rfl

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

/-! ## 1 · EL PREDICADO SIN `wTs` — via (ii): `∀` ACOTADO sobre las posiciones de la
       lista de argumentos, contra la MISMA lista testigo `wT`.

    Comparese con `CritPiloto.funcOkT`, que pedia `In (nthc X 2̄) wTs` — una segunda lista
    testigo de codigos de LISTA DE TERMINOS. Aqui NO hay segunda lista. -/

/-- Cuerpo del `∀` acotado (el indice es `#0`). -/
def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

/-- «todas las posiciones de `Y` estan en `wT`». `Y` es la lista de argumentos. -/
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

/-- tag 1 (`funcc`), SIN `wTs`. -/
def funcOkT1 (wT X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (argsIn wT (nthc X (numeralM 2)))

/-- `X` es codigo de TERMINO — **un solo testigo**. -/
def isTermCodeB1 (wT X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT1 wT X))

/-! ### Forma ECUACIONAL (la que hace falta para CALCULAR el lift) -/

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

/-- `X` es codigo de TERMINO, forma ECUACIONAL, **un solo testigo**. -/
def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

/-- El testigo es AHORA UNA SOLA LISTA: no hay `p = cons wT wTs`, no hay `carc`/`cdrc`. -/
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

/-! ## 2 · LA DISCRIMINACION SOBREVIVE

    La discriminacion vive ENTERA en la ranura del TAG (`carc X ≐ k̄`), que la
    reformulacion no toca: `funcOkT1` conserva la forma `(tag ∧ len) ∧ CARGA`. -/

theorem crit_num_ne : ∀ (m n : Nat), m ≠ n →
    Prf (Formula.impl (Formula.eq (numeralM m) (numeralM n)) Formula.bottom)
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ =>
      prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (numeralM _)) _)
        (PrfH_eq_symm (prfH_hyp_self _)))
  | m + 1, 0,     _ => prf_succ_ne_zero (numeralM m)
  | m + 1, n + 1, h =>
      impT (prf_succ_inj (numeralM m) (numeralM n)) (crit_num_ne m n (fun e => h (by omega)))

theorem crit_tag_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (Formula.eq (carc X) (numeralM m)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne k m hkm) _)
    (PrfH_eq_trans (prf_to_prfH (prf_eq_symm hX) _) (prfH_hyp_self _)))

theorem crit_cOk2_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) (G : Formula) :
    Prf (Formula.impl (cOk X (land (Formula.eq (carc X) (numeralM m)) G)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_tag_absurd X k m hkm hX) _)
    (PrfH_and_elim_left (PrfH_and_elim_right (prfH_hyp_self _))))

theorem crit_cOk3_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) (G H : Formula) :
    Prf (Formula.impl (cOk X (land (land (Formula.eq (carc X) (numeralM m)) G) H))
      Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_tag_absurd X k m hkm hX) _)
    (PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_right (prfH_hyp_self _)))))

/-- **`isTermCodeB1` RECHAZA todo nodo cuyo tag no sea 0 ni 1** — igual que con `wTs`. -/
theorem crit_isTermCodeB1_rejects (wT X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isTermCodeB1 wT X) Formula.bottom) :=
  prf_or_elim_imp
    (crit_cOk2_absurd X k 0 hk0 hX (Formula.eq (lenc X) (numeralM 2)))
    (crit_cOk3_absurd X k 1 hk1 hX (Formula.eq (lenc X) (numeralM 3))
      (argsIn wT (nthc X (numeralM 2))))

theorem crit_isTermCodeB1_rejects_implc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (implc a b)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (implc a b) 5 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_botc (wT : Term) :
    Prf (Formula.impl (isTermCodeB1 wT botc) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT botc 2 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_atomc (wT p ts : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (atomc p ts)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (atomc p ts) 3 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_eqc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (eqc a b)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (eqc a b) 4 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_forallc (wT a : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (forallc a)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (forallc a) 6 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_andc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (andc a b)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (andc a b) 7 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_orc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (orc a b)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (orc a b) 8 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB1_rejects_exc (wT a : Term) :
    Prf (Formula.impl (isTermCodeB1 wT (exc a)) Formula.bottom) :=
  crit_isTermCodeB1_rejects wT (exc a) 9 (by decide) (by decide) (prf_carc_cons _ _)

/-! ### La forma ECUACIONAL FORTALECE la forma `carc/lenc` (copia del `PasoUno`) -/

theorem prf_shape_strengthens (X C : Term) (k n : Nat)
    (hcarc : Prf (carc C =eq numeralM k))
    (hlenc : Prf (lenc C =eq numeralM n))
    (hcons : Prf (consOk C)) :
    Prf (Formula.impl (Formula.eq X C)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM n))))) := by
  refine prf_deduction ?_
  let f : Formula :=
    land (Formula.eq (.var 0) (cons (carc (.var 0)) (cdrc (.var 0))))
         (land (Formula.eq (carc (.var 0)) (numeralM k))
               (Formula.eq (lenc (.var 0)) (numeralM n)))
  have hS : ∀ s : Term, substFormula 0 s f =
      land (consOk s) (land (Formula.eq (carc s) (numeralM k))
                            (Formula.eq (lenc s) (numeralM n))) := by
    intro s
    simp only [f, consOk, land, carc, cdrc, lenc, cons, substFormula, substTerm, substTerms,
      substTerm_numeralM, if_true]
  have hbase : PrfH [Formula.eq X C] (substFormula 0 C f) := by
    rw [hS]
    exact prf_to_prfH (prf_and_intro hcons (prf_and_intro hcarc hlenc)) _
  have hres : PrfH [Formula.eq X C] (substFormula 0 X f) :=
    PrfH_leibniz_subst (A := f) (PrfH_eq_symm (prfH_hyp_self (Formula.eq X C))) hbase
  rw [hS] at hres
  exact hres

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

theorem prf_lenc_c1 (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc_c2 (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc_c1 b))

theorem prf_lenc_c3 (a b c : Term) :
    Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil))) (prf_eq_congr_succ (prf_lenc_c2 b c))

theorem prf_shapeUn_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeUn X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 2))))) :=
  prf_shape_strengthens X _ k 2 (prf_carc_cons _ _) (prf_lenc_c2 _ _) (prf_consOk_cons _ _)

theorem prf_shapeBin_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeBin X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 3))))) :=
  prf_shape_strengthens X _ k 3 (prf_carc_cons _ _) (prf_lenc_c3 _ _ _) (prf_consOk_cons _ _)

theorem prf_str_and (X : Term) (k n : Nat) (S M : Formula)
    (hstr : Prf (Formula.impl S (land (consOk X)
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)))))) :
    Prf (Formula.impl (land S M)
      (cOk X (land (land (Formula.eq (carc X) (numeralM k))
                         (Formula.eq (lenc X) (numeralM n))) M))) := by
  refine prf_deduction ?_
  let Γ : List Formula := [land S M]
  have hh : PrfH Γ (land S M) := prfH_hyp_self _
  have hs : PrfH Γ (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
      (Formula.eq (lenc X) (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hstr _) (PrfH_and_elim_left hh)
  exact PrfH_and_intro (PrfH_and_elim_left hs)
    (PrfH_and_intro (PrfH_and_elim_right hs) (PrfH_and_elim_right hh))

/-- **La forma ecuacional FORTALECE `isTermCodeB1`** (sin `wTs`). -/
theorem prf_isTermCodeE1_str (wT X : Term) :
    Prf (Formula.impl (isTermCodeE1 wT X) (isTermCodeB1 wT X)) := by
  unfold isTermCodeE1 isTermCodeB1
  refine prf_or_elim_imp (impT (prf_shapeUn_str X 0) (prf_lorL _ _)) ?_
  exact impT (prf_str_and X 1 3 _ _ (prf_shapeBin_str X 1)) (prf_lorR _ _)

/-- **La discriminacion, en la forma ECUACIONAL y SIN `wTs`.** -/
theorem crit_isTermCodeE1_rejects (wT X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isTermCodeE1 wT X) Formula.bottom) :=
  impT (prf_isTermCodeE1_str wT X) (crit_isTermCodeB1_rejects wT X k hk0 hk1 hX)

theorem crit_isTermCodeE1_rejects_implc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeE1 wT (implc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects wT (implc a b) 5 (by decide) (by decide) (prf_carc_cons _ _)

/-! ## 3 · `liftsc zero` ES EL MAP POSICIONAL — por INDUCCION DE LISTAS (`Prf.listInd`)

    🔑 Esto es lo que hace viable la via: `liftsc` esta axiomatizado SOLO en `nil`/`cons`
    (`ax_liftsc_nil` / `ax_liftsc_cons`), y el testigo se lee POSICIONALMENTE (`lenc`/`nthc`).
    El puente entre las dos lecturas es `prf_list_induction`, que es la regla `Prf.listInd`
    del calculo (NO un axioma de Lean, NO un simbolo nuevo). -/

theorem PrfH_congr_succ {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (succ a =eq succ b) := by
  let f : Formula := Formula.eq (succ (liftTerm 0 a)) (succ (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (succ a) (succ s) := by
    intro s
    simp only [f, succ, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (succ a)) Γ)

theorem PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 a)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc a) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (lenc a)) Γ)

theorem PrfH_congr_liftc {Γ : List Formula} {a b : Term} (v : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (liftc v a =eq liftc v b) := by
  let f : Formula := Formula.eq (liftc (liftTerm 0 v) (liftTerm 0 a)) (liftc (liftTerm 0 v) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftc v a) (liftc v s) := by
    intro s
    simp only [f, liftc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (liftc v a)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 a) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc a i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (nthc a i)) Γ)

theorem PrfH_congr_nthc_idx {Γ : List Formula} {i j : Term} (L : Term) (h : PrfH Γ (i =eq j)) :
    PrfH Γ (nthc L i =eq nthc L j) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 L) (liftTerm 0 i)) (nthc (liftTerm 0 L) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc L i) (nthc L s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS j) ▸ PrfH_leibniz_subst (A := f) h ((hS i) ▸ prf_to_prfH (prf_refl (nthc L i)) Γ)

/-! ### G1 · `lenc (liftsc 0 L) ≐ lenc L`, para `L` ARBITRARIO -/

def lencLiftPred : Formula := Formula.eq (lenc (liftsc zero (.var 0))) (lenc (.var 0))

theorem lencLiftPred_at (L : Term) :
    substFormula 0 L lencLiftPred = Formula.eq (lenc (liftsc zero L)) (lenc L) := by
  simp only [lencLiftPred, lenc, liftsc, zero, substFormula, substTerm, substTerms, if_true]

theorem prf_lenc_liftsc_step (h t : Term) :
    Prf (Formula.impl (Formula.eq (lenc (liftsc zero t)) (lenc t))
      (Formula.eq (lenc (liftsc zero (cons h t))) (lenc (cons h t)))) := by
  refine prf_deduction ?_
  have e1 : Prf (lenc (liftsc zero (cons h t)) =eq succ (lenc (liftsc zero t))) :=
    prf_eq_trans (prf_congr_lenc (prf_liftsc_cons zero h t))
      (prf_lenc_cons (liftc zero h) (liftsc zero t))
  have e2 : Prf (succ (lenc t) =eq lenc (cons h t)) := prf_eq_symm (prf_lenc_cons h t)
  exact PrfH_eq_trans (prf_to_prfH e1 _)
    (PrfH_eq_trans (PrfH_congr_succ (prfH_hyp_self _)) (prf_to_prfH e2 _))

theorem prf_lenc_liftsc_all : Prf (Formula.forall lencLiftPred) := by
  refine prf_list_induction lencLiftPred ?base ?step
  · rw [lencLiftPred_at]
    exact prf_congr_lenc (prf_liftsc_nil zero)
  · refine Prf.gen _ (Prf.gen _ ?_)
    have hL : liftFormula 1 lencLiftPred
        = Formula.eq (lenc (liftsc zero (.var 0))) (lenc (.var 0)) := by
      simp only [lencLiftPred, lenc, liftsc, zero, liftFormula, liftTerm, liftTerms,
        Nat.zero_lt_one, reduceIte]
    have hR : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 lencLiftPred))
        = Formula.eq (lenc (liftsc zero (cons (.var 1) (.var 0)))) (lenc (cons (.var 1) (.var 0)))
        := by
      simp only [lencLiftPred, lenc, liftsc, cons, zero, liftFormula, substFormula,
        liftTerm, liftTerms, substTerm, substTerms, Nat.zero_lt_one, Nat.zero_lt_two, reduceIte]
    rw [hR, hL]
    exact prf_lenc_liftsc_step (.var 1) (.var 0)

/-- **G1** — `lenc (liftsc 0 L) ≐ lenc L` para `L` **arbitrario**. -/
theorem prf_lenc_liftsc (L : Term) : Prf (lenc (liftsc zero L) =eq lenc L) := by
  have h := prf_spec prf_lenc_liftsc_all L
  rwa [lencLiftPred_at] at h

/-! ### G2 · `i < lenc L → nthc (liftsc 0 L) i ≐ liftc 0 (nthc L i)` -/

def nthLiftPred : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 1)))
    (Formula.eq (nthc (liftsc zero (.var 1)) (.var 0)) (liftc zero (nthc (.var 1) (.var 0)))))

theorem nthLiftPred_at (L : Term) :
    substFormula 0 L nthLiftPred
      = Formula.forall (Formula.impl (lt (.var 0) (lenc (liftTerm 0 L)))
          (Formula.eq (nthc (liftsc zero (liftTerm 0 L)) (.var 0))
                      (liftc zero (nthc (liftTerm 0 L) (.var 0))))) := by
  simp only [nthLiftPred, lt, lenc, nthc, liftsc, liftc, zero, substFormula, substTerm,
    substTerms, Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceEqDiff,
    reduceIte, if_true]

theorem nthLiftPred_base : Prf (substFormula 0 nil nthLiftPred) := by
  rw [nthLiftPred_at]
  have hnil : liftTerm 0 nil = nil := by simp only [nil, zero, liftTerm, liftTerms]
  rw [hnil]
  refine Prf.gen _ (prf_deduction ?_)
  have hlt : PrfH [lt (.var 0) (lenc nil)] (lt (.var 0) zero) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH prf_lenc_nil _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hlt)

theorem nthLiftPred_step :
    Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 nthLiftPred)
      (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nthLiftPred)))))) := by
  refine Prf.gen _ (Prf.gen _ ?_)
  simp only [nthLiftPred, lt, lenc, nthc, liftsc, liftc, cons, zero, liftFormula, substFormula,
    liftTerm, liftTerms, substTerm, substTerms, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]
  refine prf_mp (Prf.qconf _ _) (Prf.gen _ ?_)
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (lenc (cons (.var 2) (.var 1)))) _ rfl)
  let P0 : Formula := Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 2)))
    (Formula.eq (nthc (liftsc zero (.var 2)) (.var 0)) (liftc zero (nthc (.var 2) (.var 0)))))
  let A0 : Formula := lt (.var 0) (lenc (cons (.var 2) (.var 1)))
  show PrfH [A0, P0] (Formula.eq (nthc (liftsc zero (cons (.var 2) (.var 1))) (.var 0))
    (liftc zero (nthc (cons (.var 2) (.var 1)) (.var 0))))
  -- normalizacion comun: `liftsc 0 (cons h t) ≐ cons (liftc 0 h) (liftsc 0 t)`
  have hcons : ∀ Γ : List Formula, PrfH Γ
      (nthc (liftsc zero (cons (.var 2) (.var 1))) (.var 0)
        =eq nthc (cons (liftc zero (.var 2)) (liftsc zero (.var 1))) (.var 0)) := fun Γ =>
    prf_to_prfH (prf_congr_nthc_lst (.var 0) (prf_liftsc_cons zero (.var 2) (.var 1))) Γ
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?_ ?_
  · -- i = 0
    have hz : PrfH [Formula.eq (.var 0) zero, A0, P0] (Formula.eq (.var 0) zero) :=
      PrfH.hyp _ _ (List.Mem.head _)
    refine PrfH_eq_trans (hcons _) ?_
    refine PrfH_eq_trans (PrfH_congr_nthc_idx _ hz) ?_
    refine PrfH_eq_trans (prf_to_prfH
      (prf_nthc_zero (liftc zero (.var 2)) (liftsc zero (.var 1))) _) ?_
    refine PrfH_congr_liftc _ ?_
    refine PrfH_eq_symm (PrfH_eq_trans (PrfH_congr_nthc_idx _ hz) ?_)
    exact prf_to_prfH (prf_nthc_zero (.var 2) (.var 1)) _
  · -- i = σ (pred i)
    have hs : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0]
        (Formula.eq (.var 0) (succ (pred (.var 0)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hlt : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0] A0 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hP : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0] P0 :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have ihj := PrfH_spec hP (pred (.var 0))
    simp only [P0, lt, lenc, nthc, liftsc, liftc, pred, cons, zero, substFormula, substTerm,
      substTerms, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub,
      reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at ihj
    have hltJ : PrfH [Formula.eq (.var 0) (succ (pred (.var 0))), A0, P0]
        (lt (pred (.var 0)) (lenc (.var 1))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (.var 1))) _)
        (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
          (prf_to_prfH (prf_lenc_cons (.var 2) (.var 1)) _)
          (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst1 hs hlt))
    have ih := PrfH.mp _ _ _ ihj hltJ
    refine PrfH_eq_trans (hcons _) ?_
    refine PrfH_eq_trans (PrfH_congr_nthc_idx _ hs) ?_
    refine PrfH_eq_trans (prf_to_prfH
      (prf_nthc_succ (liftc zero (.var 2)) (liftsc zero (.var 1)) (pred (.var 0))) _) ?_
    refine PrfH_eq_trans ih ?_
    refine PrfH_congr_liftc _ ?_
    refine PrfH_eq_symm (PrfH_eq_trans (PrfH_congr_nthc_idx _ hs) ?_)
    exact prf_to_prfH (prf_nthc_succ (.var 2) (.var 1) (pred (.var 0))) _

/-- **G2** — `i < lenc L ⇒ nthc (liftsc 0 L) i ≐ liftc 0 (nthc L i)`, `L`/`i` **arbitrarios**. -/
theorem prf_nthc_liftsc (L i : Term) :
    Prf (Formula.impl (lt i (lenc L))
      (Formula.eq (nthc (liftsc zero L) i) (liftc zero (nthc L i)))) := by
  have key : Prf (Formula.forall nthLiftPred) :=
    prf_list_induction nthLiftPred nthLiftPred_base nthLiftPred_step
  have hi := prf_spec (prf_spec key L) i
  simpa only [nthLiftPred, lt, lenc, nthc, liftsc, liftc, zero, substFormula, substTerm,
    substTerms, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub,
    reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using hi

/-! ### G3 · `In x w ⇒ In (liftc 0 x) (liftsc 0 w)` -/

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

theorem liftT_liftsc (k : Nat) (t : Term) :
    liftTerm k (liftsc zero t) = liftsc zero (liftTerm k t) := by
  simp only [liftsc, zero, liftTerm, liftTerms]

theorem liftT_liftc (k : Nat) (t : Term) :
    liftTerm k (liftc zero t) = liftc zero (liftTerm k t) := by
  simp only [liftc, zero, liftTerm, liftTerms]

theorem prf_boundedIn_liftsc (x w : Term) :
    Prf (Formula.impl (boundedIn x w) (boundedIn (liftc zero x) (liftsc zero w))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_boundedIn, liftT_liftc, liftT_liftsc]
  let X : Term := liftTerm 0 x
  let W : Term := liftTerm 0 w
  let A : Formula := land (lt (.var 0) (liftTerm 0 (lenc w)))
    (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))
  have hA : A = land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X) := by
    simp only [A, X, W, lenc, nthc, liftTerm, liftTerms]
  show PrfH [A] (boundedIn (liftc zero X) (liftsc zero W))
  rw [hA]
  have hlt : PrfH [land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X)]
      (lt (.var 0) (lenc W)) := PrfH_and_elim_left (prfH_hyp_self _)
  have heq : PrfH [land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X)]
      (Formula.eq (nthc W (.var 0)) X) := PrfH_and_elim_right (prfH_hyp_self _)
  refine PrfH_ex_intro (.var 0) ?_
  simp only [boundedIn, substFormula, substTerm, substTerms, land, lt, nthc, lenc, liftc, liftsc,
    zero, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true, FOL.substTerm_liftTerm]
  refine PrfH_and_intro ?_ ?_
  · exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_liftsc W)) _) hlt
  · refine PrfH_eq_trans (PrfH.mp _ _ _ (prf_to_prfH (prf_nthc_liftsc W (.var 0)) _) hlt) ?_
    exact PrfH_congr_liftc _ heq

/-- **G3** — la IMAGEN del testigo bajo `liftsc 0` contiene la imagen de cada elemento. -/
theorem prf_In_liftsc (x w : Term) :
    Prf (Formula.impl (In x w) (In (liftc zero x) (liftsc zero w))) :=
  impT (prf_boundedIn_of_In x w)
    (impT (prf_boundedIn_liftsc x w) (prf_In_of_boundedIn (liftc zero x) (liftsc zero w)))

/-! ## 4 · CLAUSURA DEL PREDICADO BAJO `liftc zero` — el testigo nuevo es `liftsc zero w` -/

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

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

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

/-- Leibniz en el 2º argumento de `argsIn` (la lista de argumentos). -/
theorem PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)

/-- Leibniz en el 2º argumento de `isTermCodeE1` (el nodo). **Una** Leibniz cubre las
    5 ocurrencias del hueco. -/
theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s
    simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)

/-- Instanciacion de `argsIn` en un indice CUALQUIERA (el testigo puede ser ABIERTO). -/
theorem PrfH_inst_argsIn {Γ : List Formula} (wT Y i : Term) (h : PrfH Γ (argsIn wT Y)) :
    PrfH Γ (Formula.impl (lt i (lenc Y)) (In (nthc Y i) wT)) := by
  have hi := PrfH_spec h i
  simpa only [argsInBody, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hi

theorem PrfH_inst_wfAll1 {Γ : List Formula} (w i : Term) (h : PrfH Γ (wfAll1 w)) :
    PrfH Γ (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i))) := by
  have hi := PrfH_spec h i
  simpa only [wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody, lor, land,
    lt, lenc, nthc, In, cons, nil, zero, substFormula, substTerm, substTerms,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_lift_comm_zero, substTerm_numeralM, if_true] using hi

/-! ### `argsIn` se parte en CABEZA y COLA (posicion 0 / posiciones desplazadas)

    Subidos desde `sondeos/DescensoLiftc.lean` al promover `Meta/EvalLiftcPrf.lean`
    (2026-09-03). Van AQUI, junto a `PrfH_inst_argsIn`, y no en el modulo del descenso:
    son genericos —no mencionan `targetLift`— y estan copiados a mano en SEIS sondeos del
    frente (`DescensoLiftc`, `EvalSubstfcPrf`, `SubstfcEx`, ...). Desde el modulo del
    descenso quedaban invisibles para todos ellos. -/
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

/-! ### Del testigo al NODO: `In c w ⇒ wfAll1 w ⇒ isTermCodeE1 w c`, con `c` y `w`
       **ABSTRACTOS** (ni uno ni otro tienen que ser cerrados).

    Analogo, para el sort TERMINO, de `ENS.prf_isFormCodeE2_of_boundedIn` / `_of_In`:
    esqueleto de prueba identico linea a linea, con `wfAllF`/`isFormCodeE2` cambiados por
    `wfAll1`/`isTermCodeE1`.

    Bajados desde `Meta/EvalLiftcPrf.lean` (2026-09-04) por la misma razon que
    `prf_argsIn_head`/`prf_argsIn_tail` de aqui arriba: son GENERICOS —no mencionan
    `targetLift`— y desde el modulo del DESCENSO quedaban invisibles para los sondeos del
    frente que los tienen copiados a mano. La constante mas tardia que usan es
    `PrfH_inst_wfAll1` (:665), o sea que este es su sitio mas alto posible. -/

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

/-- ⚠️ `impT` SIN cualificar, y aqui es lo CORRECTO: estamos dentro de `namespace SinWTs`,
    asi que resuelve a `SinWTs.impT` y no a la copia `ENS.impT`. Es justamente la
    cualificacion que `Meta/EvalLiftcPrf.lean` tenia que poner a mano —porque aquel modulo
    abre los DOS namespaces— y que al bajar aqui DESAPARECE. -/
theorem prf_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (prf_isTermCodeE1_of_boundedIn w c)


/-- Cuerpo de la clausura de `argsIn`, con el indice `i` LIBRE. -/
theorem prf_argsIn_lift_body (W V i : Term) :
    Prf (Formula.impl (argsIn W V) (Formula.impl (lt i (lenc (liftsc zero V)))
      (In (nthc (liftsc zero V) i) (liftsc zero W)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc (liftsc zero V))) [argsIn W V] rfl)
  let Γ : List Formula := [lt i (lenc (liftsc zero V)), argsIn W V]
  have hlt0 : PrfH Γ (lt i (lenc (liftsc zero V))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH Γ (argsIn W V) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Γ (lt i (lenc V)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_lenc_liftsc V) _) hlt0
  have hin : PrfH Γ (In (nthc V i) W) := PrfH.mp _ _ _ (PrfH_inst_argsIn W V i hargs) hlt
  have hin2 : PrfH Γ (In (liftc zero (nthc V i)) (liftsc zero W)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_In_liftsc (nthc V i) W) _) hin
  have hnth : PrfH Γ (nthc (liftsc zero V) i =eq liftc zero (nthc V i)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_nthc_liftsc V i) _) hlt
  exact PrfH_congr_In_left (PrfH_eq_symm hnth) hin2

/-- **CLAUSURA DE `argsIn`**: la imagen `liftsc 0` de la lista de argumentos sigue teniendo
    todas sus posiciones en la imagen `liftsc 0` del testigo. -/
theorem prf_argsIn_lift (w Y : Term) :
    Prf (Formula.impl (argsIn w Y) (argsIn (liftsc zero w) (liftsc zero Y))) := by
  refine prf_mp (Prf.qconf (argsIn w Y) (argsInBody (liftsc zero w) (liftsc zero Y)))
    (Prf.gen _ ?_)
  rw [liftF_argsIn]
  show Prf (Formula.impl (argsIn (liftTerm 0 w) (liftTerm 0 Y))
    (Formula.impl (lt (.var 0) (liftTerm 0 (lenc (liftsc zero Y))))
      (In (nthc (liftTerm 0 (liftsc zero Y)) (.var 0)) (liftTerm 0 (liftsc zero w)))))
  have h1 : liftTerm 0 (lenc (liftsc zero Y)) = lenc (liftsc zero (liftTerm 0 Y)) := by
    simp only [lenc, liftTerm, liftTerms, liftT_liftsc]
  have h2 : liftTerm 0 (liftsc zero Y) = liftsc zero (liftTerm 0 Y) := liftT_liftsc 0 Y
  have h3 : liftTerm 0 (liftsc zero w) = liftsc zero (liftTerm 0 w) := liftT_liftsc 0 w
  rw [h1, h2, h3]
  exact prf_argsIn_lift_body (liftTerm 0 w) (liftTerm 0 Y) (.var 0)

/-! ### EL LEMA CLAVE — los DOS disyuntos sobreviven al `liftc zero` -/

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

/-- **EL LEMA CLAVE.** `isTermCodeE1 w X ⇒ isTermCodeE1 (liftsc 0 w) (liftc 0 X)`.
    Es la forma ECUACIONAL la que lo hace posible: da la forma `varc a` / `funcc a b`
    EXACTA que piden `ax_liftc_var_ge` / `ax_liftc_func`. -/
theorem prf_isTermCodeE1_lift (w X : Term) :
    Prf (Formula.impl (isTermCodeE1 w X) (isTermCodeE1 (liftsc zero w) (liftc zero X))) := by
  refine prf_or_elim_imp ?varc ?func
  case varc =>
    refine impT ?_ (prf_lorL _ _)
    refine prf_deduction ?_
    let a : Term := nthc X (numeralM 1)
    have h : PrfH [shapeUn X 0] (Formula.eq X (varc a)) := prfH_hyp_self _
    have hL : PrfH [shapeUn X 0] (liftc zero X =eq varc (succ a)) :=
      PrfH_eq_trans (PrfH_congr_liftc zero h)
        (prf_to_prfH (prf_mp (prf_liftc_var_ge zero a) (prf_zero_lt_succ a)) _)
    have hn : PrfH [shapeUn X 0] (nthc (liftc zero X) (numeralM 1) =eq succ a) :=
      PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 1) hL)
        (prf_to_prfH (prf_nthc_c1 zero (succ a) nil) _)
    show PrfH [shapeUn X 0] (Formula.eq (liftc zero X)
      (cons (numeralM 0) (cons (nthc (liftc zero X) (numeralM 1)) nil)))
    exact PrfH_eq_trans hL
      (PrfH_eq_symm (PrfH_congr_cons_tail (PrfH_congr_cons_head hn)))
  case func =>
    refine impT ?_ (prf_lorR _ _)
    refine prf_deduction ?_
    let a : Term := nthc X (numeralM 1)
    let b : Term := nthc X (numeralM 2)
    let H : Formula := land (shapeBin X 1) (argsIn w b)
    have hh : PrfH [H] H := prfH_hyp_self _
    have h : PrfH [H] (Formula.eq X (funcc a b)) := PrfH_and_elim_left hh
    have hargs : PrfH [H] (argsIn w b) := PrfH_and_elim_right hh
    have hL : PrfH [H] (liftc zero X =eq funcc a (liftsc zero b)) :=
      PrfH_eq_trans (PrfH_congr_liftc zero h) (prf_to_prfH (prf_liftc_func zero a b) _)
    have hn1 : PrfH [H] (nthc (liftc zero X) (numeralM 1) =eq a) :=
      PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 1) hL)
        (prf_to_prfH (prf_nthc_c1 (numeralM 1) a (cons (liftsc zero b) nil)) _)
    have hn2 : PrfH [H] (nthc (liftc zero X) (numeralM 2) =eq liftsc zero b) :=
      PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 2) hL)
        (prf_to_prfH (prf_nthc_c2 (numeralM 1) a (liftsc zero b) nil) _)
    refine PrfH_and_intro ?_ ?_
    · show PrfH [H] (Formula.eq (liftc zero X)
        (cons (numeralM 1) (cons (nthc (liftc zero X) (numeralM 1))
          (cons (nthc (liftc zero X) (numeralM 2)) nil))))
      exact PrfH_eq_trans hL (PrfH_eq_symm (PrfH_congr_cons_tail
        (PrfH_eq_trans (PrfH_congr_cons_head hn1)
          (PrfH_congr_cons_tail (PrfH_congr_cons_head hn2)))))
    · refine PrfH_congr_argsIn (PrfH_eq_symm hn2) ?_
      exact PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_lift w b) _) hargs

/-! ### LA CLAUSURA -/

theorem prf_wfAll1_lift_body (W i : Term) :
    Prf (Formula.impl (wfAll1 W) (Formula.impl (lt i (lenc (liftsc zero W)))
      (isTermCodeE1 (liftsc zero W) (nthc (liftsc zero W) i)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc (liftsc zero W))) [wfAll1 W] rfl)
  let Γ : List Formula := [lt i (lenc (liftsc zero W)), wfAll1 W]
  have hlt0 : PrfH Γ (lt i (lenc (liftsc zero W))) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH Γ (wfAll1 W) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Γ (lt i (lenc W)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_lenc_liftsc W) _) hlt0
  have hitc : PrfH Γ (isTermCodeE1 W (nthc W i)) :=
    PrfH.mp _ _ _ (PrfH_inst_wfAll1 W i hwf) hlt
  have hitc2 : PrfH Γ (isTermCodeE1 (liftsc zero W) (liftc zero (nthc W i))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_lift W (nthc W i)) _) hitc
  have hnth : PrfH Γ (nthc (liftsc zero W) i =eq liftc zero (nthc W i)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_nthc_liftsc W i) _) hlt
  exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hnth) hitc2

/-- **LA CLAUSURA DEL TESTIGO BAJO `liftc zero`**, con `w` **ABSTRACTO** (puede ser `#0`):
    si `w` es testigo valido, `liftsc zero w` tambien lo es. -/
theorem prf_wfAll1_lift (w : Term) :
    Prf (Formula.impl (wfAll1 w) (wfAll1 (liftsc zero w))) := by
  refine prf_mp (Prf.qconf (wfAll1 w) (wfAll1Body (liftsc zero w))) (Prf.gen _ ?_)
  rw [liftF_wfAll1]
  show Prf (Formula.impl (wfAll1 (liftTerm 0 w))
    (Formula.impl (lt (.var 0) (liftTerm 0 (lenc (liftsc zero w))))
      (isTermCodeE1 (liftTerm 0 (liftsc zero w))
        (nthc (liftTerm 0 (liftsc zero w)) (.var 0)))))
  have h1 : liftTerm 0 (lenc (liftsc zero w)) = lenc (liftsc zero (liftTerm 0 w)) := by
    simp only [lenc, liftTerm, liftTerms, liftT_liftsc]
  have h2 : liftTerm 0 (liftsc zero w) = liftsc zero (liftTerm 0 w) := liftT_liftsc 0 w
  rw [h1, h2]
  exact prf_wfAll1_lift_body (liftTerm 0 w) (.var 0)

/-- **EL TITULAR**: el reconocedor SIN `wTs` es CERRADO bajo `liftc zero`, con testigo
    ABSTRACTO y testigo nuevo COMPUTABLE (`liftsc zero w`, que ya esta en el vocabulario). -/
theorem prf_isTC1_lift (w c : Term) :
    Prf (Formula.impl (isTC1 w c) (isTC1 (liftsc zero w) (liftc zero c))) := by
  refine prf_deduction ?_
  have hh : PrfH [isTC1 w c] (isTC1 w c) := prfH_hyp_self _
  refine PrfH_and_intro ?_ ?_
  · exact PrfH.mp _ _ _ (prf_to_prfH (prf_wfAll1_lift w) _) (PrfH_and_elim_left hh)
  · exact PrfH.mp _ _ _ (prf_to_prfH (prf_In_liftsc c w) _) (PrfH_and_elim_right hh)

/-! ## 5 · NO VACUIDAD — todo termino REAL tiene testigo, y el testigo es UNA SOLA LISTA

    ⚠️ Sin esto la via no vale nada: el predicado podria ser vacio. Aqui se comprueba que
    `tcodes1 t` (los codigos de TERMINO de los subterminos de `t`, **sin** la lista de
    codigos de LISTA que `sondeos/DiscriminaEcuacional.lean` necesitaba) YA es testigo. -/

theorem prf_congr_argsIn {wT Y₁ Y₂ : Term} (h : Prf (Y₁ =eq Y₂)) (ha : Prf (argsIn wT Y₁)) :
    Prf (argsIn wT Y₂) :=
  prfH_nil_to_prf (PrfH_congr_argsIn (prf_to_prfH h []) (prf_to_prfH ha [])) rfl

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) :=
  prfH_nil_to_prf (PrfH_congr_In_left (prf_to_prfH h []) (prf_to_prfH hin [])) rfl

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j1 A B)) h
theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j2 A B)) h

/-! ### `∀` acotado con cota ABSTRACTA igual a un numeral (copia del piloto §3) -/

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq Φ))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  | n + 1, h => by
      have ih := prf_bdAll_numeral Φ hΦ n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
          = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
        simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
      refine Prf.gen _ (prf_deduction ?_)
      have hsplit : PrfH [lt (.var 0) (numeralM (n + 1))]
          (lor (lt (.var 0) (numeralM n)) (Formula.eq (.var 0) (numeralM n))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (numeralM n)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec ih (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        have hinst : Prf (substFormula 0 (numeralM n) Φ) := h n (Nat.lt_succ_self n)
        have heq : PrfH (Formula.eq (.var 0) (numeralM n) :: [lt (.var 0) (numeralM (n + 1))])
            (Formula.eq (numeralM n) (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have := PrfH_leibniz_subst (A := Φ) heq (prf_to_prfH hinst _)
        rwa [hΦ] at this

theorem prf_bdAll_of_bound (Φ : Formula) (b : Term) (n : Nat)
    (hΦ : substFormula 0 (.var 0) Φ = Φ)
    (hb : Prf (Formula.eq b (numeralM n)))
    (h : ∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) :
    Prf (Formula.forall (Formula.impl (lt (.var 0) b) Φ)) := by
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ)) :=
    prf_bdAll_numeral Φ hΦ n h
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
      = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  refine Prf.gen _ (prf_deduction ?_)
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH hb _) (PrfH.hyp _ _ (List.Mem.head _)))

/-! ### Los dos moldes de nodo, ya en forma ECUACIONAL -/

theorem prf_isTermCodeE1_var (W a : Term) : Prf (isTermCodeE1 W (varc a)) :=
  prf_orL (prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (prf_nthc_c1 (numeralM 0) a nil))))

theorem prf_isTermCodeE1_func (W S C : Term) (h : Prf (argsIn W C)) :
    Prf (isTermCodeE1 W (funcc S C)) :=
  prf_orR (prf_and_intro
    (prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
      (prf_congr_cons_head (prf_nthc_c1 (numeralM 1) S (cons C nil)))
      (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c2 (numeralM 1) S C nil))))))
    (prf_congr_argsIn (prf_eq_symm (prf_nthc_c2 (numeralM 1) S C nil)) h))

/-- Introduccion de `argsIn` para una lista CONCRETA (cota numeral). -/
theorem prf_argsIn_of_closed (W C : Term) (n : Nat)
    (hWl : liftTerm 0 W = W) (hCl : liftTerm 0 C = C)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (hCs : ∀ (v : Nat) (s : Term), substTerm v s C = C)
    (hlen : Prf (lenc C =eq numeralM n))
    (h : ∀ k : Nat, k < n → Prf (In (nthc C (numeralM k)) W)) :
    Prf (argsIn W C) := by
  have hAI : argsIn W C
      = Formula.forall (Formula.impl (lt (.var 0) (lenc C)) (In (nthc C (.var 0)) W)) := by
    simp only [argsIn, argsInBody, lt, lenc, nthc, In, liftTerm, liftTerms, hWl, hCl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc C) n ?_ hlen ?_
  · simp only [In, nthc, substFormula, substTerm, substTerms, hWs, hCs, if_true]
  · intro k hk
    have hk' := h k hk
    simpa only [In, nthc, substFormula, substTerm, substTerms, hWs, hCs,
      substTerm_numeralM, if_true, reduceIte] using hk'

/-! ### `lenc`/`nthc` de `termsCodeM` (la lista de argumentos REAL) -/

theorem prf_lenc_termsCodeM : ∀ ts : List Term,
    Prf (lenc (termsCodeM ts) =eq numeralM ts.length)
  | []      => prf_lenc_nil
  | t :: ts =>
      prf_eq_trans (prf_lenc_cons (termCodeM t) (termsCodeM ts))
        (prf_eq_congr_succ (prf_lenc_termsCodeM ts))

theorem prf_nthc_termsCodeM : ∀ (ts : List Term) (k : Nat) (x : Term), ts[k]? = some x →
    Prf (nthc (termsCodeM ts) (numeralM k) =eq termCodeM x)
  | [],      k,     x, h => by simp at h
  | t :: ts, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero (termCodeM t) (termsCodeM ts)
  | t :: ts, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ (termCodeM t) (termsCodeM ts) (numeralM k))
        (prf_nthc_termsCodeM ts k x h)

theorem mem_of_getElem? : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x → List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? es k x h)

/-! ### EL TESTIGO: **UNA** lista (la de codigos de TERMINO), y nada mas -/

mutual
def tcodes1 : Term → List Term
  | .var n     => [termCodeM (.var n)]
  | .func s ts => termCodeM (.func s ts) :: tcodes1s ts
def tcodes1s : List Term → List Term
  | []      => []
  | t :: ts => tcodes1 t ++ tcodes1s ts
end

theorem mem_self_tcodes1 (t : Term) : List.Mem (termCodeM t) (tcodes1 t) := by
  cases t with
  | var n     => simp only [tcodes1]; exact List.Mem.head _
  | func s ts => simp only [tcodes1]; exact List.Mem.head _

theorem mem_tcodes1s_of_mem : ∀ (ts : List Term) (t : Term), List.Mem t ts →
    List.Mem (termCodeM t) (tcodes1s ts)
  | [],      t, h => by cases h
  | u :: us, t, h => by
      simp only [tcodes1s]
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_append.mpr (Or.inl (mem_self_tcodes1 t))
      · exact List.mem_append.mpr (Or.inr (mem_tcodes1s_of_mem us t h'))

def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

mutual
theorem closed_mem_tcodes1 : ∀ (t x : Term), List.Mem x (tcodes1 t) → CodeClosed x
  | .var n, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.var n)
      · cases h'
  | .func s ts, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.func s ts)
      · exact closed_mem_tcodes1s ts x h'
theorem closed_mem_tcodes1s : ∀ (ts : List Term) (x : Term),
    List.Mem x (tcodes1s ts) → CodeClosed x
  | [], x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodes1 t x hA
      · exact closed_mem_tcodes1s ts x hB
end

theorem liftTerm_objList (c : Nat) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → liftTerm c x = x) → liftTerm c (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, liftTerm, liftTerms, h e (List.Mem.head _),
        liftTerm_objList c es (fun x hx => h x (List.Mem.tail _ hx))]

theorem substTerm_objList (v : Nat) (s : Term) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → substTerm v s x = x) → substTerm v s (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, substTerm, substTerms, h e (List.Mem.head _),
        substTerm_objList v s es (fun x hx => h x (List.Mem.tail _ hx))]

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    Prf (Formula.eq (nthc (objList L) (numeralM k)) x)
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero e (objList es)
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ e (objList es) (numeralM k))
        (prf_nthc_objList es k x h)

theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

/-! ### LA INDUCCION — **UNA sola** familia (con `wTs` habia DOS mutuas) -/

mutual
theorem okE1_T : ∀ (t : Term) (W : Term)
    (_hW : ∀ c : Nat, liftTerm c W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (_ho : ∀ y : Term, List.Mem y (tcodes1 t) → Prf (In y W))
    (x : Term), List.Mem x (tcodes1 t) → Prf (isTermCodeE1 W x)
  | .var n, W, hW, hWs, ho, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (isTermCodeE1 W (termCodeM (.var n)))
        exact prf_isTermCodeE1_var W (numeralM n)
      · cases h'
  | .func s ts, W, hW, hWs, ho, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (isTermCodeE1 W (termCodeM (.func s ts)))
        refine prf_isTermCodeE1_func W (strCodeM s) (termsCodeM ts) ?_
        refine prf_argsIn_of_closed W (termsCodeM ts) ts.length (hW 0)
          (liftTerm_termsCodeM 0 ts) hWs (fun v s' => substTerm_termsCodeM v s' ts)
          (prf_lenc_termsCodeM ts) ?_
        intro k hk
        obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
        refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
        refine ho (termCodeM u) ?_
        simp only [tcodes1]
        exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))
      · exact okE1_Ts ts W hW hWs
          (fun y hy => ho y (by simp only [tcodes1]; exact List.Mem.tail _ hy)) x h'
theorem okE1_Ts : ∀ (ts : List Term) (W : Term)
    (_hW : ∀ c : Nat, liftTerm c W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (_ho : ∀ y : Term, List.Mem y (tcodes1s ts) → Prf (In y W))
    (x : Term), List.Mem x (tcodes1s ts) → Prf (isTermCodeE1 W x)
  | [], W, hW, hWs, ho, x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, W, hW, hWs, ho, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact okE1_T t W hW hWs
          (fun y hy => ho y (by
            simp only [tcodes1s]; exact List.mem_append.mpr (Or.inl hy))) x hA
      · exact okE1_Ts ts W hW hWs
          (fun y hy => ho y (by
            simp only [tcodes1s]; exact List.mem_append.mpr (Or.inr hy))) x hB
end

/-- **HITO (i) PARA LA VIA 2**: todo termino tiene testigo, y el testigo es **UNA SOLA
    LISTA** — `tcodes1 t`. Cero axiomas, cero simbolos nuevos. -/
theorem prf_isTC1_tcodes (t : Term) : Prf (isTC1 (objList (tcodes1 t)) (termCodeM t)) := by
  let L : List Term := tcodes1 t
  let W : Term := objList L
  have hWl : ∀ c : Nat, liftTerm c W = W := fun c =>
    liftTerm_objList c L (fun x hx => (closed_mem_tcodes1 t x hx).1 c)
  have hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W := fun v s =>
    substTerm_objList v s L (fun x hx => (closed_mem_tcodes1 t x hx).2 v s)
  have horacle : ∀ y : Term, List.Mem y L → Prf (In y W) := fun y hy => prf_In_objList L y hy
  refine prf_and_intro ?_ (prf_In_objList L (termCodeM t) (mem_self_tcodes1 t))
  have hAI : wfAll1 W
      = Formula.forall (Formula.impl (lt (.var 0) (lenc W))
          (isTermCodeE1 W (nthc W (.var 0)))) := by
    simp only [wfAll1, wfAll1Body, lt, lenc, nthc, liftF_isTermCodeE1, liftTerm, liftTerms, hWl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc W) L.length ?_ (prf_lenc_objList L) ?_
  · simp only [substF_isTermCodeE1, nthc, substTerm, substTerms, hWs, if_true]
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    have hnode : Prf (isTermCodeE1 W x) :=
      okE1_T t W hWl hWs horacle x (mem_of_getElem? L k x hx)
    have : Prf (isTermCodeE1 W (nthc W (numeralM k))) :=
      prfH_nil_to_prf (PrfH_congr_isTermCodeE1
        (prf_to_prfH (prf_eq_symm (prf_nthc_objList L k x hx)) [])
        (prf_to_prfH hnode [])) rfl
    simpa only [substF_isTermCodeE1, nthc, substTerm, substTerms, hWs,
      substTerm_numeralM, if_true, reduceIte] using this

/-! ## 6 · LA DISCRIMINACION CON TESTIGO **ABIERTO** (sin ninguna hipotesis sobre `w`)

    Es la version fuerte de `sondeos/DiscriminaEcuacional.lean` §CerrarDos, rehecha para el
    testigo de UNA sola lista. `w` puede ser literalmente `#0`. -/

theorem prf_crit_In_rejects_open1 (w c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAll1, liftFormula]
  refine deduction_aux ?_ (wfAll1 (liftTerm 0 w)) _ rfl
  let A : Formula := land (lt (.var 0) (liftTerm 0 (lenc w)))
    (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))
  let Γ' : List Formula := [wfAll1 (liftTerm 0 w), A]
  have hwf : PrfH Γ' (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH Γ' A := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Γ' (lt (.var 0) (lenc (liftTerm 0 w))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [A, lenc, liftTerm, liftTerms] using h
  have heq : PrfH Γ' (Formula.eq (nthc (liftTerm 0 w) (.var 0)) c) := by
    have h := PrfH_and_elim_right hbody
    rwa [hcl 0] at h
  have hitc : PrfH Γ' (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))) :=
    PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) hwf) hlt
  exact PrfH.mp _ _ _
    (prf_to_prfH (crit_isTermCodeE1_rejects (liftTerm 0 w) c k hk0 hk1 hck) _)
    (PrfH_congr_isTermCodeE1 heq hitc)

/-- **`isTC1 w c` con `c` codigo de FORMULA es REFUTABLE — para CUALQUIER testigo `w`.** -/
theorem crit_isTC1_junk_refuted_open (w c : Term)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hck : Prf (carc c =eq numeralM k))
    (hjunk : Prf (isTC1 w c)) : Prf Formula.bottom :=
  prf_mp (prf_mp (impT (prf_boundedIn_of_In c w)
      (prf_crit_In_rejects_open1 w c k hk0 hk1 hcl hck))
    (prf_and_elim_right hjunk)) (prf_and_elim_left hjunk)

theorem crit_closed_implc {a b : Term} (ha : CodeClosed a) (hb : CodeClosed b) :
    CodeClosed (implc a b) := by
  refine ⟨fun n => ?_, fun v s => ?_⟩
  · simp only [implc, cons, nil, zero, succ, liftTerm, liftTerms, ha.1, hb.1]
  · simp only [implc, cons, nil, zero, succ, substTerm, substTerms, ha.2, hb.2]

/-- **EL JUNK EXACTO de `sondeos/SubCodesCritica.lean`** (`implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ`) sigue siendo
    REFUTABLE con el testigo de UNA lista, y con testigo **ARBITRARIO**. -/
theorem crit_junk_SubCodesCritica_open1 (w : Term)
    (hjunk : Prf (isTC1 w (implc (termCodeM (.var 0)) (termCodeM (.var 0))))) :
    Prf Formula.bottom :=
  crit_isTC1_junk_refuted_open w _
    (crit_closed_implc (closed_termCodeM _) (closed_termCodeM _)).1
    5 (by decide) (by decide) (prf_carc_cons _ _) hjunk

/-- Y con el testigo LITERALMENTE `#0`. -/
theorem crit_junk_var0_witness1
    (hjunk : Prf (isTC1 (.var 0) (implc (termCodeM (.var 0)) (termCodeM (.var 0))))) :
    Prf Formula.bottom :=
  crit_junk_SubCodesCritica_open1 (.var 0) hjunk

/-! ## 7 · EXTREMO A EXTREMO: testigo real ⟶ testigo de su lift -/

/-- El testigo de `liftc 0 ⌜t⌝` es `liftsc 0 (objList (tcodes1 t))` — **computable y en el
    vocabulario existente**. (Con `wTs` haria falta un `map` de `liftsc`, que NO existe.) -/
theorem prf_isTC1_tcodes_lifted (t : Term) :
    Prf (isTC1 (liftsc zero (objList (tcodes1 t))) (liftc zero (termCodeM t))) :=
  prf_mp (prf_isTC1_lift (objList (tcodes1 t)) (termCodeM t)) (prf_isTC1_tcodes t)

/-- Iterando: el testigo aguanta CUALQUIER profundidad de binder. -/
theorem prf_isTC1_tcodes_lifted2 (t : Term) :
    Prf (isTC1 (liftsc zero (liftsc zero (objList (tcodes1 t))))
               (liftc zero (liftc zero (termCodeM t)))) :=
  prf_mp (prf_isTC1_lift _ _) (prf_isTC1_tcodes_lifted t)

/-! ## 8 · CONTRACARA HONESTA — lo que la via (ii) DEJA DE EXIGIR

    Con `wTs`, la casilla 2 de un `funcc` pedia `In (nthc X 2̄) wTs`, y **todo** elemento de
    `wTs` cumplia `isTermsCodeB`, o sea: `≐ nil` **o** `consOk` con cabeza en `wT` y cola en
    `wTs` — luego la lista de argumentos era una CADENA `cons` genuina, terminada en `nil`.

    La via (ii) sustituye eso por un `∀` acotado POSICIONAL. Eso NO fuerza la cadena: sólo
    habla de las posiciones `< lenc Y`. Los dos agujeros medidos: -/

/-- (a) **La carga de `varc` sigue sin tipar** — mismo agujero que ya tenia el par con `wTs`
    (`CritPiloto.crit_varOkT_payload_libre`): NO es una regresion de la via 2. -/
theorem crit_isTermCodeE1_payload_libre (W X : Term) : Prf (isTermCodeE1 W (varc X)) :=
  prf_isTermCodeE1_var W X

/-- (b) **AGUJERO NUEVO Y PROPIO DE LA VIA (ii)**: la lista de argumentos ya no tiene que ser
    una cadena `cons` terminada en `nil`; basta con que `lenc` de ella sea `0̄`. Con `wTs`, el
    disyunto `Y ≐ nil` era una ECUACION y no se podia falsear con `lenc`. -/
theorem crit_argsIn_lenc_zero (W Y : Term)
    (hWl : liftTerm 0 W = W) (hYl : liftTerm 0 Y = Y)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (hYs : ∀ (v : Nat) (s : Term), substTerm v s Y = Y)
    (hlen : Prf (lenc Y =eq numeralM 0)) :
    Prf (argsIn W Y) :=
  prf_argsIn_of_closed W Y 0 hWl hYl hWs hYs hlen (fun k hk => absurd hk (by omega))

/-- Y por tanto el nodo `funcc S Y` pasa el reconocedor con ese `Y`. -/
theorem crit_isTermCodeE1_funcc_lenc_zero (W S Y : Term)
    (hWl : liftTerm 0 W = W) (hYl : liftTerm 0 Y = Y)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (hYs : ∀ (v : Nat) (s : Term), substTerm v s Y = Y)
    (hlen : Prf (lenc Y =eq numeralM 0)) :
    Prf (isTermCodeE1 W (funcc S Y)) :=
  prf_isTermCodeE1_func W S Y (crit_argsIn_lenc_zero W Y hWl hYl hWs hYs hlen)

/-! ## 8b · LA CARA DE FORMULA TAMBIEN PIERDE `wTs` — la terna baja a PAR (`wF`, `wT`)

    `strBinOkF wTs X 3` (la lista de argumentos de un `atomc`) era el UNICO sitio donde el
    predicado de FORMULA consultaba `wTs`. Con `argsIn wT` desaparece, y la DISCRIMINACION
    (que vive entera en la ranura del TAG) sobrevive intacta. -/

def nulOkF (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 2)) (Formula.eq (lenc X) (numeralM 1))

def unOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

def binOkF (wA wB X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) wA) (In (nthc X (numeralM 2)) wB))

/-- ⚠️ AQUI el cambio: `In (nthc X 2̄) wTs` ⟶ `argsIn wT (nthc X 2̄)`. -/
def strBinOkF1 (wT X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (argsIn wT (nthc X (numeralM 2)))

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- Predicado de codigo de FORMULA con **DOS** listas testigo (`wF`, `wT`) en vez de tres. -/
def isFormCodeB2 (wF wT X : Term) : Formula :=
  lorAll (cOk X (nulOkF X))
    [ cOk X (strBinOkF1 wT X 3)
    , cOk X (binOkF wT wT X 4)
    , cOk X (binOkF wF wF X 5)
    , cOk X (unOkF  wF X 6)
    , cOk X (binOkF wF wF X 7)
    , cOk X (binOkF wF wF X 8)
    , cOk X (unOkF  wF X 9) ]

/-- **La discriminacion de la cara de FORMULA sobrevive a quitar `wTs`.** -/
theorem crit_isFormCodeB2_rejects (wF wT X : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isFormCodeB2 wF wT X) Formula.bottom) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (crit_cOk2_absurd X k 2 h2 hX _)
   (prf_or_elim_imp (crit_cOk3_absurd X k 3 h3 hX _ _)
    (prf_or_elim_imp (crit_cOk3_absurd X k 4 h4 hX _ _)
     (prf_or_elim_imp (crit_cOk3_absurd X k 5 h5 hX _ _)
      (prf_or_elim_imp (crit_cOk3_absurd X k 6 h6 hX _ _)
       (prf_or_elim_imp (crit_cOk3_absurd X k 7 h7 hX _ _)
        (prf_or_elim_imp (crit_cOk3_absurd X k 8 h8 hX _ _)
                         (crit_cOk3_absurd X k 9 h9 hX _ _)))))))

/-- Un codigo de VARIABLE (tag 0) NO pasa por el predicado de FORMULA — es la mitad de la
    discriminacion que mata `prf_isFC_junk` (`crit_isFC_junk_REFUTED` / `crit_isFCB3_no_termcode`). -/
theorem crit_isFormCodeB2_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (isFormCodeB2 wF wT (varc n)) Formula.bottom) :=
  crit_isFormCodeB2_rejects wF wT (varc n) 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isFormCodeB2_rejects_funcc (wF wT s ts : Term) :
    Prf (Formula.impl (isFormCodeB2 wF wT (funcc s ts)) Formula.bottom) :=
  crit_isFormCodeB2_rejects wF wT (funcc s ts) 1
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _)

/-! ## 9 · CONTROLES NEGATIVOS — los enunciados no son reflexividades disfrazadas -/

example (w : Term) : True := by
  fail_if_success exact (rfl : liftsc zero w = w)
  trivial

example (w : Term) : True := by
  fail_if_success exact (rfl : wfAll1 (liftsc zero w) = wfAll1 w)
  trivial

/-- La clausura vale con el testigo LITERALMENTE `#0` (lo que entrega un `∃`-elim). -/
example : Prf (Formula.impl (isTC1 (.var 0) (.var 1))
    (isTC1 (liftsc zero (.var 0)) (liftc zero (.var 1)))) :=
  prf_isTC1_lift (.var 0) (.var 1)

/-- Y el reconocedor sin `wTs` **no** es el de `wTs` con la lista puesta a `nil`: son
    formulas distintas (la carga de `funcc` cambio de `In` a `∀` acotado). -/
example (W X : Term) : True := by
  fail_if_success exact (rfl : isTermCodeE1 W X = lor (shapeUn X 0)
    (land (shapeBin X 1) (In (nthc X (numeralM 2)) W)))
  trivial

end SinWTs

end S_Clausura

section S_Ens

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.ForallElimCodePrf ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.CheckArith ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf

namespace ENS

/-! ############################################################################
    ## §0 · Combinadores (copias literales de `sondeos/EvalSubsttc.lean` §D)
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
    ## §1 · COPIAS LITERALES del reconocedor de codigo de TERMINO sin `wTs`
       (`sondeos/ClausuraLiftSinWTs.lean:109-145,1389`, identico al de
        `sondeos/EvalSubsttc.lean:1116-1140`, que es lo que consume `pcc_eval_substtc'`).
    ############################################################################ -/

/- ⚠️ **DEDUPLICADO 2026‑08‑31.** Aquí se redefinían **NUEVE** definiciones que `SinWTs` ya
   tenía, byte a byte: `argsInBody`, `argsIn`, `shapeUn`, `shapeBin`, `isTermCodeE1`,
   `wfAll1Body`, `wfAll1`, `isTC1` y `lorAll`. El propio fichero las certificaba idénticas con
   puentes `rfl` (`bridge_argsIn`, `bridge_wfAll1`, …), o sea que la duplicación estaba **vista
   y documentada, pero no resuelta**.

   Promoverlas así a `Meta/` habría metido en producción DOS constantes para cada una — la trampa
   registrada de «misma definición en dos namespaces», que ya ha costado tiempo tres veces en este
   proyecto. Se resuelve **aquí**, que es el momento: se toman de `SinWTs` con un `open`, y los
   puentes dejan de hacer falta.

   Sólo se conservan las DOS que son genuinamente de este bloque. -/
open SinWTs

def shapeNul (X : Term) (k : Nat) : Formula := Formula.eq X (cons (numeralM k) nil)

def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

/-! ### Fontaneria De Bruijn del bloque de TERMINO (copias literales) -/

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X) = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAll1, wfAll1Body, substFormula, substF_isTermCodeE1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

theorem substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) := by
  simp only [isTC1, land, In, substFormula, substF_wfAll1, substTerm, substTerms]


/-! ### Clausura y no‑vacuidad de `hasWit` (promovido de `sondeos/ClausuraLiftSinWTs.lean`, B1)

`CRIT_hasWit_lift` es además **el molde de la obligación A5**
(`hasWitF c ⇒ hasWitF (liftc zero c)`, el análogo del sort FÓRMULA, que no existe): misma
estructura, con **dos** binders en vez de uno. -/

/-- **La clausura en la forma que el descenso necesita.** -/
theorem CRIT_hasWit_lift (c : Term) :
    Prf (Formula.impl (hasWit c) (hasWit (liftc zero c))) := by
  refine prf_ex_elim_imp ?_
  have hgoal : liftFormula 0 (hasWit (liftc zero c))
      = Formula.ex (isTC1 (.var 0) (liftTerm 1 (liftTerm 0 (liftc zero c)))) := by
    simp only [hasWit, liftFormula, liftF_isTC1, liftTerm, Nat.reduceAdd,
      Nat.zero_lt_succ, reduceIte]
  rw [hgoal]
  refine PrfH_ex_intro (liftsc zero (.var 0)) ?_
  have hsub : substFormula 0 (liftsc zero (.var 0))
      (isTC1 (.var 0) (liftTerm 1 (liftTerm 0 (liftc zero c))))
      = isTC1 (liftsc zero (.var 0)) (liftc zero (liftTerm 0 c)) := by
    have hv : substTerm 0 (liftsc zero (Term.var 0)) (Term.var 0) = liftsc zero (.var 0) := by
      simp only [substTerm, if_true]
    rw [← FOL.liftTerm_comm_zero, substF_isTC1, FOL.substTerm_liftTerm, hv, liftT_liftc]
  rw [hsub]
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTC1_lift (.var 0) (liftTerm 0 c)) _)
    (prfH_hyp_self _)

/-- Y **no vacua**: todo término real TIENE testigo en esa forma. -/
theorem CRIT_hasWit_real (t : Term) : Prf (hasWit (termCodeM t)) := by
  refine prf_ex_intro (objList (tcodes1 t)) ?_
  have h : substFormula 0 (objList (tcodes1 t)) (isTC1 (.var 0) (liftTerm 0 (termCodeM t)))
      = isTC1 (objList (tcodes1 t)) (termCodeM t) := by
    simp only [substF_isTC1, substTerm, if_true, FOL.substTerm_liftTerm]
  rw [h]
  exact prf_isTC1_tcodes t

theorem CRIT_hasWit_real_lifted (t : Term) : Prf (hasWit (liftc zero (termCodeM t))) :=
  prf_mp (CRIT_hasWit_lift (termCodeM t)) (CRIT_hasWit_real t)

theorem liftF_hasWit (k : Nat) (c : Term) :
    liftFormula k (hasWit c) = hasWit (liftTerm k c) := by
  simp only [hasWit, liftFormula, liftF_isTC1, liftTerm, Nat.zero_lt_succ, reduceIte,
    ← FOL.liftTerm_comm_zero]

theorem substF_hasWit (v : Nat) (s c : Term) :
    substFormula v s (hasWit c) = hasWit (substTerm v s c) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [hasWit, substFormula, substF_isTC1, substTerm, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero]

/-! ############################################################################
    ## §2 · EL RECONOCEDOR DE CODIGO DE **FORMULA**, forma ECUACIONAL, con
       **DOS** listas testigo (`wF` formulas, `wT` terminos).

    Es la version ECUACIONAL de `SinWTs.isFormCodeB2` (`ClausuraLiftSinWTs.lean:1170`),
    exactamente como `isTermCodeE1` es la version ecuacional de `isTermCodeB1`.
    Ocho disyuntos ↔ ocho ecuaciones de `substfc`. Las casillas de TERMINO apuntan a `wT`
    (`In` para `eqc`, `argsIn` para `atomc`), que es LITERALMENTE lo que pide
    `pcc_eval_substtc'` / `pcc_eval_substtsc'` ⇒ **el puente no hace falta: es la
    definicion.**
    ############################################################################ -/


/-- tag 2 · `botc` -/
def clBot (X : Term) : Formula := shapeNul X 2
/-- tag 3 · `atomc p ts` : casilla 1 OPACA (simbolo), casilla 2 LISTA de terminos. -/
def clAtom (wT X : Term) : Formula :=
  land (shapeBin X 3) (argsIn wT (nthc X (numeralM 2)))
/-- tag 4 · `eqc a b` : las DOS casillas son codigos de TERMINO. -/
def clEq (wT X : Term) : Formula :=
  land (shapeBin X 4)
    (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))
/-- tags 5/7/8 · `implc`/`andc`/`orc` : las DOS casillas son codigos de FORMULA. -/
def clBin (wF X : Term) (k : Nat) : Formula :=
  land (shapeBin X k)
    (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
/-- tags 6/9 · `forallc`/`exc` : UNA casilla de FORMULA. -/
def clUn (wF X : Term) (k : Nat) : Formula :=
  land (shapeUn X k) (In (nthc X (numeralM 1)) wF)

def isFormCodeE2 (wF wT X : Term) : Formula :=
  lorAll (clBot X)
    [ clAtom wT X
    , clEq wT X
    , clBin wF X 5
    , clUn wF X 6
    , clBin wF X 7
    , clBin wF X 8
    , clUn wF X 9 ]

def wfAllFBody (wF wT : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc wF)))
    (isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (nthc (liftTerm 0 wF) (.var 0)))

def wfAllF (wF wT : Term) : Formula := Formula.forall (wfAllFBody wF wT)

/-- **La guarda de FORMULA**: `wT` es un testigo de terminos bien formado, `wF` un testigo
    de formulas bien formado CONTRA `wT`, y `c` esta en `wF`. -/
def isFC1 (wF wT c : Term) : Formula :=
  land (land (wfAll1 wT) (wfAllF wF wT)) (In c wF)

/-! ### Fontaneria De Bruijn del bloque de FORMULA -/

theorem liftF_isFormCodeE2 (k : Nat) (wF wT X : Term) :
    liftFormula k (isFormCodeE2 wF wT X)
      = isFormCodeE2 (liftTerm k wF) (liftTerm k wT) (liftTerm k X) := by
  simp only [isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn, shapeNul, shapeUn,
    shapeBin, lor, land, In, liftFormula, liftF_argsIn, nthc, cons, nil, zero,
    liftTerm, liftTerms, liftTerm_numeralM]

theorem substF_isFormCodeE2 (v : Nat) (s wF wT X : Term) :
    substFormula v s (isFormCodeE2 wF wT X)
      = isFormCodeE2 (substTerm v s wF) (substTerm v s wT) (substTerm v s X) := by
  simp only [isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn, shapeNul, shapeUn,
    shapeBin, lor, land, In, substFormula, substF_argsIn, nthc, cons, nil, zero,
    substTerm, substTerms, substTerm_numeralM]

theorem liftF_wfAllF (k : Nat) (wF wT : Term) :
    liftFormula k (wfAllF wF wT) = wfAllF (liftTerm k wF) (liftTerm k wT) := by
  simp only [wfAllF, wfAllFBody, liftFormula, liftF_isFormCodeE2, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAllF (v : Nat) (s wF wT : Term) :
    substFormula v s (wfAllF wF wT) = wfAllF (substTerm v s wF) (substTerm v s wT) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAllF, wfAllFBody, substFormula, substF_isFormCodeE2, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem liftF_isFC1 (k : Nat) (wF wT c : Term) :
    liftFormula k (isFC1 wF wT c)
      = isFC1 (liftTerm k wF) (liftTerm k wT) (liftTerm k c) := by
  simp only [isFC1, land, In, liftFormula, liftF_wfAll1, liftF_wfAllF, liftTerm, liftTerms]

theorem substF_isFC1 (v : Nat) (s wF wT c : Term) :
    substFormula v s (isFC1 wF wT c)
      = isFC1 (substTerm v s wF) (substTerm v s wT) (substTerm v s c) := by
  simp only [isFC1, land, In, substFormula, substF_wfAll1, substF_wfAllF, substTerm, substTerms]

/-! ### Del testigo al NODO — espejo de `EvalSubsttc.prf_isTermCodeE1_of_In` -/

theorem PrfH_congr_isFormCodeE2 {Γ : List Formula} {wF wT X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (ha : PrfH Γ (isFormCodeE2 wF wT X₁)) :
    PrfH Γ (isFormCodeE2 wF wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (.var 0))
        = isFormCodeE2 wF wT s := by
    intro s
    simp only [substF_isFormCodeE2, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸
    PrfH_leibniz_subst (A := isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (.var 0)) h
      ((hS X₁) ▸ ha)

theorem PrfH_inst_wfAllF {Γ : List Formula} (wF wT i : Term) (h : PrfH Γ (wfAllF wF wT)) :
    PrfH Γ (Formula.impl (lt i (lenc wF)) (isFormCodeE2 wF wT (nthc wF i))) := by
  have hi := PrfH_spec h i
  simpa only [wfAllFBody, isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn,
    shapeNul, shapeUn, shapeBin, argsIn, argsInBody, lor, land, lt, lenc, nthc, In,
    cons, nil, zero, substFormula, substTerm, substTerms,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_lift_comm_zero, substTerm_numeralM, if_true] using hi

theorem prf_isFormCodeE2_of_boundedIn (wF wT c : Term) :
    Prf (Formula.impl (boundedIn c wF)
      (Formula.impl (wfAllF wF wT) (isFormCodeE2 wF wT c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAllF, liftF_isFormCodeE2]
  refine deduction_aux ?_ (wfAllF (liftTerm 0 wF) (liftTerm 0 wT)) _ rfl
  have hwf : PrfH [wfAllF (liftTerm 0 wF) (liftTerm 0 wT),
      land (lt (.var 0) (liftTerm 0 (lenc wF)))
        (Formula.eq (nthc (liftTerm 0 wF) (.var 0)) (liftTerm 0 c))]
      (wfAllF (liftTerm 0 wF) (liftTerm 0 wT)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAllF (liftTerm 0 wF) (liftTerm 0 wT),
      land (lt (.var 0) (liftTerm 0 (lenc wF)))
        (Formula.eq (nthc (liftTerm 0 wF) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc wF)))
        (Formula.eq (nthc (liftTerm 0 wF) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAllF (liftTerm 0 wF) (liftTerm 0 wT),
      land (lt (.var 0) (liftTerm 0 (lenc wF)))
        (Formula.eq (nthc (liftTerm 0 wF) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (liftTerm 0 wF))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAllF (liftTerm 0 wF) (liftTerm 0 wT) (.var 0) hwf) hlt
  exact PrfH_congr_isFormCodeE2 heq hitc

theorem prf_isFormCodeE2_of_In (wF wT c : Term) :
    Prf (Formula.impl (In c wF) (Formula.impl (wfAllF wF wT) (isFormCodeE2 wF wT c))) :=
  impT (prf_boundedIn_of_In c wF) (prf_isFormCodeE2_of_boundedIn wF wT c)


/-! COPIA LITERAL de EvalSubstfcPrf.lean:8243-8244 y 8320-8324 -/

def hasWitF (c : Term) : Formula :=
  Formula.ex (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 c))))

theorem liftF_hasWitF (k : Nat) (c : Term) :
    liftFormula k (hasWitF c) = hasWitF (liftTerm k c) := by
  have h1 : (1 < k + 1 + 1) = True := eq_true (by omega)
  simp only [hasWitF, liftFormula, liftF_isFC1, liftTerm, Nat.reduceAdd, h1, if_true,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]



/-! ### El kit de DISCRIMINACIÓN (promovido de `sondeos/EvalSubstfcPrf.lean`, B8)

Estas piezas se reconstruyeron **a mano** durante las mediciones de la rama C porque no estaban
en producción — señal de que se volverán a necesitar. Son las que prueban que la guarda
**DISCRIMINA** y no es un colador: sin ellas, `pcc_eval_substfc` podría ser vacuo. -/

/-- `shapeUn`/`shapeBin` en la forma con `consOk` (variantes que consume el fortalecimiento). -/
theorem prf_shapeUn_str' (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeUn X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 2))))) :=
  SinWTs.prf_shape_strengthens X _ k 2 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c2 _ _) (SinWTs.prf_consOk_cons _ _)

theorem prf_shapeBin_str' (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeBin X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 3))))) :=
  SinWTs.prf_shape_strengthens X _ k 3 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c3 _ _ _) (SinWTs.prf_consOk_cons _ _)

theorem prf_shapeNul_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeNul X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 1))))) :=
  SinWTs.prf_shape_strengthens X _ k 1 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c1 _) (SinWTs.prf_consOk_cons _ _)

/-- Functorialidad de `lor` en las DOS ramas. -/
theorem lor_map {A A' B B' : Formula} (hA : Prf (A ⇒ A')) (hB : Prf (B ⇒ B')) :
    Prf (lor A B ⇒ lor A' B') :=
  prf_or_elim_imp (impT hA (prf_lorL _ _)) (impT hB (prf_lorR _ _))

/-- **La forma ECUACIONAL fortalece la POSICIONAL** — 8 disyuntos a 8 disyuntos. -/
theorem prf_isFormCodeE2_str (wF wT X : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT X) (SinWTs.isFormCodeB2 wF wT X)) := by
  simp only [isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn,
    SinWTs.isFormCodeB2, SinWTs.lorAll]
  exact lor_map (prf_shapeNul_str X 2)
   (lor_map (SinWTs.prf_str_and X 3 3 _ _ (prf_shapeBin_str' X 3))
    (lor_map (SinWTs.prf_str_and X 4 3 _ _ (prf_shapeBin_str' X 4))
     (lor_map (SinWTs.prf_str_and X 5 3 _ _ (prf_shapeBin_str' X 5))
      (lor_map (SinWTs.prf_str_and X 6 2 _ _ (prf_shapeUn_str' X 6))
       (lor_map (SinWTs.prf_str_and X 7 3 _ _ (prf_shapeBin_str' X 7))
        (lor_map (SinWTs.prf_str_and X 8 3 _ _ (prf_shapeBin_str' X 8))
                 (SinWTs.prf_str_and X 9 2 _ _ (prf_shapeUn_str' X 9))))))))

/-- **CONTROL**: un código de VARIABLE (tag 0) NO pasa por el reconocedor de FÓRMULA. -/
theorem CRIT_E2_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT (varc n)) Formula.bottom) :=
  impT (prf_isFormCodeE2_str wF wT (varc n))
    (SinWTs.crit_isFormCodeB2_rejects_varc wF wT n)

/-- **CONTROL**: un código de FUNCIÓN (tag 1) tampoco. -/
theorem CRIT_E2_rejects_funcc (wF wT p ts : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT (funcc p ts)) Formula.bottom) :=
  impT (prf_isFormCodeE2_str wF wT (funcc p ts))
    (SinWTs.crit_isFormCodeB2_rejects_funcc wF wT p ts)

/-- **CONTROL**: la GUARDA COMPLETA hereda la discriminación. ⚠️ Es la pieza que REFUTÓ la
    tarea A4 del árbol: la guarda sobre argumento ABSTRACTO no es sólo difícil, es FALSA. -/
theorem CRIT_isFC1_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (isFC1 wF wT (varc n)) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isFC1 wF wT (varc n))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (prf_isFormCodeE2_of_In wF wT (varc n)) _) hin) hwF
  exact PrfH.mp _ _ _ (prf_to_prfH (CRIT_E2_rejects_varc wF wT n) _) hcode
end ENS
end S_Ens

/-! ############################################################################
    ## §HW · EL TRANSPORTE: de TRES listas testigo (P1, `prf_isFCB3_of`) a DOS
       (`ENS.isFC1`), en forma ECUACIONAL.

    Objetivo: `prf_isFC1_real` / `prf_hasWitF_real` — la guarda de FORMULA de
    `ENS.pcc_eval_substfc` es SATISFACIBLE por codigos REALES, con testigos
    EXPLICITOS y COMPUTABLES (`fcodesF phi`, `tcodesF phi`).

    La tercera lista de P1 (`flcodes`, codigos de LISTA DE ARGUMENTOS) NO aparece:
    su papel lo juega `SinWTs.argsIn wT` dentro de `ENS.clAtom` — un `∀` acotado sobre
    las posiciones de la lista de argumentos, contra la MISMA `wT`.
    ############################################################################ -/

section S_HW

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace HW

/-! ## §HW.0 · PUENTES `rfl` — `SinWTs.*` y `ENS.*` son la MISMA formula.

    ⚠️ **RETIRADOS 2026‑08‑31 al deduplicar.** Aquí había cinco puentes `rfl`
    (`bridge_argsIn`, `bridge_isTermCodeE1`, `bridge_wfAll1`, `bridge_shapeUn`,
    `bridge_shapeBin`) que certificaban que las copias de `ENS` coincidían con las de `SinWTs`.
    Al eliminar las copias, los puentes se vuelven `X = X`: **la duplicación que certificaban ya
    no existe**, así que sobran. Su trabajo no se pierde — fue lo que permitió deduplicar con
    seguridad. -/

/-! ## §HW.1 · LAS TRES ECUACIONES DE FORMA (`shapeNul`/`shapeUn`/`shapeBin`) SOBRE
       NODOS REALES. Aqui es donde la forma ECUACIONAL sale MAS BARATA que la
       posicional: una sola ecuacion, sin `consOk` ni `carc ≐ k̄` ni `lenc ≐ n̄`. -/

theorem prf_refl' (t : Term) : Prf (t =eq t) := Prf.incl (Prf₀.eqrefl t)

theorem prf_shapeNul_real (k : Nat) : Prf (ENS.shapeNul (cons (numeralM k) nil) k) :=
  prf_refl' _

theorem prf_shapeUn_real (k : Nat) (a : Term) :
    Prf (SinWTs.shapeUn (cons (numeralM k) (cons a nil)) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (SinWTs.prf_nthc_c1 (numeralM k) a nil)))

theorem prf_shapeBin_real (k : Nat) (a b : Term) :
    Prf (SinWTs.shapeBin (cons (numeralM k) (cons a (cons b nil))) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
    (prf_congr_cons_head (SinWTs.prf_nthc_c1 (numeralM k) a (cons b nil)))
    (prf_congr_cons_tail (prf_congr_cons_head
      (SinWTs.prf_nthc_c2 (numeralM k) a b nil)))))

/-! ## §HW.2 · LAS CLAUSULAS, sobre nodos en forma `cons k̄ (...)`.

    🔑 Cada nodo se prueba contra la lista testigo COMPLETA (no hay monotonia
    ni composicion de or-elims). -/

theorem cl_bin_real (WF : Term) (k : Nat) (ca cb : Term)
    (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.clBin WF (cons (numeralM k) (cons ca (cons cb nil))) k) :=
  prf_and_intro (prf_shapeBin_real k ca cb)
    (prf_and_intro
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM k) ca (cons cb nil))) ha)
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM k) ca cb nil)) hb))

theorem cl_un_real (WF : Term) (k : Nat) (ca : Term) (ha : Prf (In ca WF)) :
    Prf (ENS.clUn WF (cons (numeralM k) (cons ca nil)) k) :=
  prf_and_intro (prf_shapeUn_real k ca)
    (SinWTs.prf_congr_In_left
      (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM k) ca nil)) ha)

theorem cl_eq_real (WT ca cb : Term) (ha : Prf (In ca WT)) (hb : Prf (In cb WT)) :
    Prf (ENS.clEq WT (cons (numeralM 4) (cons ca (cons cb nil)))) :=
  prf_and_intro (prf_shapeBin_real 4 ca cb)
    (prf_and_intro
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 4) ca (cons cb nil))) ha)
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 4) ca cb nil)) hb))

theorem cl_atom_real (WT sp cts : Term) (hargs : Prf (SinWTs.argsIn WT cts)) :
    Prf (ENS.clAtom WT (cons (numeralM 3) (cons sp (cons cts nil)))) :=
  prf_and_intro (prf_shapeBin_real 3 sp cts)
    (SinWTs.prf_congr_argsIn
      (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 3) sp cts nil)) hargs)

/-! ## §HW.3 · LOS OCHO NODOS, ya colocados en su disyunto de `isFormCodeE2`. -/

theorem node_bot (WF WT : Term) : Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 2) nil)) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orL (prf_shapeNul_real 2)

theorem node_atom (WF WT sp cts : Term) (hargs : Prf (SinWTs.argsIn WT cts)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 3) (cons sp (cons cts nil)))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orL (cl_atom_real WT sp cts hargs))

theorem node_eq (WF WT ca cb : Term) (ha : Prf (In ca WT)) (hb : Prf (In cb WT)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 4) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orL (cl_eq_real WT ca cb ha hb)))

theorem node_impl (WF WT ca cb : Term) (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 5) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orL (cl_bin_real WF 5 ca cb ha hb))))

theorem node_forall (WF WT ca : Term) (ha : Prf (In ca WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 6) (cons ca nil))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orL (cl_un_real WF 6 ca ha)))))

theorem node_and (WF WT ca cb : Term) (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 7) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orL (cl_bin_real WF 7 ca cb ha hb))))))

theorem node_or (WF WT ca cb : Term) (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 8) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orR (SinWTs.prf_orL (cl_bin_real WF 8 ca cb ha hb)))))))

theorem node_ex (WF WT ca : Term) (ha : Prf (In ca WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 9) (cons ca nil))) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orR (SinWTs.prf_orR (cl_un_real WF 9 ca ha)))))))

/-! ## §HW.4 · LAS **DOS** LISTAS TESTIGO — explicitas y computables.

    `fcodesF phi` : los codigos de FORMULA de todas las subformulas de `phi`.
    `tcodesF phi` : los codigos de TERMINO de todos los SUBTERMINOS de todos los
                    terminos que aparecen en `phi` (cierre por subterminos, que es
                    exactamente lo que `SinWTs.tcodes1`/`tcodes1s` calculan). -/

def fcodesF : Formula → List Term
  | Formula.bottom     => [formCodeM Formula.bottom]
  | Formula.atom p ts  => [formCodeM (Formula.atom p ts)]
  | Formula.eq a b     => [formCodeM (Formula.eq a b)]
  | Formula.impl a b   => formCodeM (Formula.impl a b) :: (fcodesF a ++ fcodesF b)
  | Formula.forall a   => formCodeM (Formula.forall a) :: fcodesF a
  | Formula.and a b    => formCodeM (Formula.and a b) :: (fcodesF a ++ fcodesF b)
  | Formula.or a b     => formCodeM (Formula.or a b) :: (fcodesF a ++ fcodesF b)
  | Formula.ex a       => formCodeM (Formula.ex a) :: fcodesF a

def tcodesF : Formula → List Term
  | Formula.bottom     => []
  | Formula.atom _ ts  => SinWTs.tcodes1s ts
  | Formula.eq a b     => SinWTs.tcodes1 a ++ SinWTs.tcodes1 b
  | Formula.impl a b   => tcodesF a ++ tcodesF b
  | Formula.forall a   => tcodesF a
  | Formula.and a b    => tcodesF a ++ tcodesF b
  | Formula.or a b     => tcodesF a ++ tcodesF b
  | Formula.ex a       => tcodesF a

/-- PERTENENCIA (`mem_self_*` de P1): el propio codigo esta en su lista. -/
theorem mem_self_fcodesF (phi : Formula) : List.Mem (formCodeM phi) (fcodesF phi) := by
  cases phi with
  | bottom    => exact List.Mem.head _
  | atom p ts => exact List.Mem.head _
  | eq a b    => exact List.Mem.head _
  | impl a b  => exact List.Mem.head _
  | «forall» a => exact List.Mem.head _
  | and a b   => exact List.Mem.head _
  | or a b    => exact List.Mem.head _
  | ex a      => exact List.Mem.head _

theorem closed_formCodeM (phi : Formula) : SinWTs.CodeClosed (formCodeM phi) :=
  ⟨fun c => liftTerm_formCodeM c phi, fun v s => substTerm_formCodeM v s phi⟩

/-- CLAUSURA (`closed_mem_*` de P1) para la lista de FORMULA. -/
theorem closed_mem_fcodesF : ∀ (phi : Formula) (x : Term),
    List.Mem x (fcodesF phi) → SinWTs.CodeClosed x
  | Formula.bottom, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | Formula.atom p ts, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | Formula.eq a b, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | Formula.impl a b, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | Formula.forall a, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · exact closed_mem_fcodesF a x h'
  | Formula.and a b, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | Formula.or a b, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | Formula.ex a, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · exact closed_mem_fcodesF a x h'

/-- CLAUSURA para la lista de TERMINO. -/
theorem closed_mem_tcodesF : ∀ (phi : Formula) (x : Term),
    List.Mem x (tcodesF phi) → SinWTs.CodeClosed x
  | Formula.bottom, x, h => by cases h
  | Formula.atom p ts, x, h => SinWTs.closed_mem_tcodes1s ts x h
  | Formula.eq a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact SinWTs.closed_mem_tcodes1 a x hA
      · exact SinWTs.closed_mem_tcodes1 b x hB
  | Formula.impl a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesF a x hA
      · exact closed_mem_tcodesF b x hB
  | Formula.forall a, x, h => closed_mem_tcodesF a x h
  | Formula.and a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesF a x hA
      · exact closed_mem_tcodesF b x hB
  | Formula.or a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesF a x hA
      · exact closed_mem_tcodesF b x hB
  | Formula.ex a, x, h => closed_mem_tcodesF a x h

/-! ## §HW.5 · LOS NODOS DE **TERMINO** de `tcodesF phi`.

    ⚠️ Aqui es donde P2 (`SinWTs.okE1_T`/`okE1_Ts`) se reutiliza ENTERO: `tcodesF`
    esta construido a base de `tcodes1`/`tcodes1s`, que es exactamente el cierre por
    subterminos con el que P2 trabaja. -/

theorem okT_F : ∀ (phi : Formula) (WT : Term)
    (hWl : ∀ c : Nat, liftTerm c WT = WT)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (ho : ∀ y : Term, List.Mem y (tcodesF phi) → Prf (In y WT))
    (x : Term), List.Mem x (tcodesF phi) → Prf (SinWTs.isTermCodeE1 WT x)
  | Formula.bottom, WT, hWl, hWs, ho, x, h => by cases h
  | Formula.atom p ts, WT, hWl, hWs, ho, x, h => SinWTs.okE1_Ts ts WT hWl hWs ho x h
  | Formula.eq a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact SinWTs.okE1_T a WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact SinWTs.okE1_T b WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.impl a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact okT_F a WT hWl hWs (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact okT_F b WT hWl hWs (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.forall a, WT, hWl, hWs, ho, x, h => okT_F a WT hWl hWs ho x h
  | Formula.and a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact okT_F a WT hWl hWs (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact okT_F b WT hWl hWs (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.or a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact okT_F a WT hWl hWs (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact okT_F b WT hWl hWs (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.ex a, WT, hWl, hWs, ho, x, h => okT_F a WT hWl hWs ho x h

/-! ## §HW.6 · LOS NODOS DE **FORMULA** de `fcodesF phi`. -/

theorem okF : ∀ (phi : Formula) (WF WT : Term)
    (hWTl : ∀ c : Nat, liftTerm c WT = WT)
    (hWTs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (hoF : ∀ y : Term, List.Mem y (fcodesF phi) → Prf (In y WF))
    (hoT : ∀ y : Term, List.Mem y (tcodesF phi) → Prf (In y WT))
    (x : Term), List.Mem x (fcodesF phi) → Prf (ENS.isFormCodeE2 WF WT x)
  | Formula.bottom, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact node_bot WF WT
      · cases h'
  | Formula.atom p ts, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT
          (cons (numeralM 3) (cons (strCodeM p) (cons (termsCodeM ts) nil))))
        refine node_atom WF WT (strCodeM p) (termsCodeM ts) ?_
        refine SinWTs.prf_argsIn_of_closed WT (termsCodeM ts) ts.length (hWTl 0)
          (liftTerm_termsCodeM 0 ts) hWTs (fun v s => substTerm_termsCodeM v s ts)
          (SinWTs.prf_lenc_termsCodeM ts) ?_
        intro k hk
        obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
        refine SinWTs.prf_congr_In_left
          (prf_eq_symm (SinWTs.prf_nthc_termsCodeM ts k u hu)) ?_
        exact hoT (termCodeM u)
          (SinWTs.mem_tcodes1s_of_mem ts u (SinWTs.mem_of_getElem? ts k u hu))
      · cases h'
  | Formula.eq a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT
          (cons (numeralM 4) (cons (termCodeM a) (cons (termCodeM b) nil))))
        refine node_eq WF WT (termCodeM a) (termCodeM b) ?_ ?_
        · exact hoT (termCodeM a)
            (List.mem_append.mpr (Or.inl (SinWTs.mem_self_tcodes1 a)))
        · exact hoT (termCodeM b)
            (List.mem_append.mpr (Or.inr (SinWTs.mem_self_tcodes1 b)))
      · cases h'
  | Formula.impl a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT
          (cons (numeralM 5) (cons (formCodeM a) (cons (formCodeM b) nil))))
        refine node_impl WF WT (formCodeM a) (formCodeM b) ?_ ?_
        · exact hoF (formCodeM a) (by
            simp only [fcodesF]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodesF a))))
        · exact hoF (formCodeM b) (by
            simp only [fcodesF]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodesF b))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF a WF WT hWTl hWTs
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))))
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inl hy))) x hA
        · exact okF b WF WT hWTl hWTs
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))))
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.forall a, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 6) (cons (formCodeM a) nil)))
        refine node_forall WF WT (formCodeM a) ?_
        exact hoF (formCodeM a) (by
          simp only [fcodesF]; exact List.Mem.tail _ (mem_self_fcodesF a))
      · exact okF a WF WT hWTl hWTs
          (fun y hy => hoF y (by simp only [fcodesF]; exact List.Mem.tail _ hy))
          (fun y hy => hoT y hy) x h'
  | Formula.and a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT
          (cons (numeralM 7) (cons (formCodeM a) (cons (formCodeM b) nil))))
        refine node_and WF WT (formCodeM a) (formCodeM b) ?_ ?_
        · exact hoF (formCodeM a) (by
            simp only [fcodesF]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodesF a))))
        · exact hoF (formCodeM b) (by
            simp only [fcodesF]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodesF b))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF a WF WT hWTl hWTs
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))))
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inl hy))) x hA
        · exact okF b WF WT hWTl hWTs
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))))
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.or a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT
          (cons (numeralM 8) (cons (formCodeM a) (cons (formCodeM b) nil))))
        refine node_or WF WT (formCodeM a) (formCodeM b) ?_ ?_
        · exact hoF (formCodeM a) (by
            simp only [fcodesF]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodesF a))))
        · exact hoF (formCodeM b) (by
            simp only [fcodesF]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodesF b))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF a WF WT hWTl hWTs
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))))
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inl hy))) x hA
        · exact okF b WF WT hWTl hWTs
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))))
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.ex a, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 9) (cons (formCodeM a) nil)))
        refine node_ex WF WT (formCodeM a) ?_
        exact hoF (formCodeM a) (by
          simp only [fcodesF]; exact List.Mem.tail _ (mem_self_fcodesF a))
      · exact okF a WF WT hWTl hWTs
          (fun y hy => hoF y (by simp only [fcodesF]; exact List.Mem.tail _ hy))
          (fun y hy => hoT y hy) x h'

/-! ## §HW.7 · LOS DOS MOLDES DE `∀` ACOTADO (`wfAll1` y `wfAllF`).

    `prf_wfAllF_of_list` es COPIA LITERAL de `Probe/ADV_novacuo.lean`
    (`PROBE_wfAllF_of_list`); `prf_wfAll1_of_list` es la generalizacion evidente de
    `SinWTs.prf_isTC1_tcodes` a una lista cualquiera. -/

theorem prf_wfAll1_of_list (L : List Term)
    (hcl : ∀ x, List.Mem x L → SinWTs.CodeClosed x)
    (hnode : ∀ x, List.Mem x L → Prf (SinWTs.isTermCodeE1 (objList L) x)) :
    Prf (SinWTs.wfAll1 (objList L)) := by
  have hWl : ∀ c : Nat, liftTerm c (objList L) = objList L := fun c =>
    SinWTs.liftTerm_objList c L (fun x hx => (hcl x hx).1 c)
  have hWs : ∀ (v : Nat) (s : Term), substTerm v s (objList L) = objList L := fun v s =>
    SinWTs.substTerm_objList v s L (fun x hx => (hcl x hx).2 v s)
  have hAI : SinWTs.wfAll1 (objList L)
      = Formula.forall (Formula.impl (lt (.var 0) (lenc (objList L)))
          (SinWTs.isTermCodeE1 (objList L) (nthc (objList L) (.var 0)))) := by
    simp only [SinWTs.wfAll1, SinWTs.wfAll1Body, lt, lenc, nthc, ENS.liftF_isTermCodeE1,
      liftTerm, liftTerms, hWl]
  rw [hAI]
  refine SinWTs.prf_bdAll_of_bound _ (lenc (objList L)) L.length ?_
    (SinWTs.prf_lenc_objList L) ?_
  · simp only [SinWTs.substF_isTermCodeE1, nthc, substTerm, substTerms, hWs, if_true]
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    have hnd : Prf (SinWTs.isTermCodeE1 (objList L) x) :=
      hnode x (SinWTs.mem_of_getElem? L k x hx)
    have h2 : Prf (SinWTs.isTermCodeE1 (objList L) (nthc (objList L) (numeralM k))) :=
      prfH_nil_to_prf (SinWTs.PrfH_congr_isTermCodeE1
        (prf_to_prfH (prf_eq_symm (SinWTs.prf_nthc_objList L k x hx)) [])
        (prf_to_prfH hnd [])) rfl
    simpa only [SinWTs.substF_isTermCodeE1, nthc, substTerm, substTerms, hWs,
      substTerm_numeralM, if_true, reduceIte] using h2

theorem prf_wfAllF_of_list (LF : List Term) (WT : Term)
    (hWTl : ∀ c : Nat, liftTerm c WT = WT)
    (hWTs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (hLl : ∀ x, List.Mem x LF → ∀ c : Nat, liftTerm c x = x)
    (hLs : ∀ x, List.Mem x LF → ∀ (v : Nat) (s : Term), substTerm v s x = x)
    (hnode : ∀ x, List.Mem x LF → Prf (ENS.isFormCodeE2 (objList LF) WT x)) :
    Prf (ENS.wfAllF (objList LF) WT) := by
  have hWl : ∀ c : Nat, liftTerm c (objList LF) = objList LF := fun c =>
    SinWTs.liftTerm_objList c LF (fun x hx => hLl x hx c)
  have hWs : ∀ (v : Nat) (s : Term), substTerm v s (objList LF) = objList LF := fun v s =>
    SinWTs.substTerm_objList v s LF (fun x hx => hLs x hx v s)
  have hAI : ENS.wfAllF (objList LF) WT
      = Formula.forall (Formula.impl (lt (.var 0) (lenc (objList LF)))
          (ENS.isFormCodeE2 (objList LF) WT (nthc (objList LF) (.var 0)))) := by
    simp only [ENS.wfAllF, ENS.wfAllFBody, lt, lenc, nthc, ENS.liftF_isFormCodeE2,
      liftTerm, liftTerms, hWl, hWTl]
  rw [hAI]
  refine SinWTs.prf_bdAll_of_bound _ (lenc (objList LF)) LF.length ?_
    (SinWTs.prf_lenc_objList LF) ?_
  · simp only [ENS.substF_isFormCodeE2, nthc, substTerm, substTerms, hWs, hWTs, if_true]
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LF[k]? = some x := ⟨LF[k], getElem?_pos LF k hk⟩
    have hn : Prf (ENS.isFormCodeE2 (objList LF) WT x) :=
      hnode x (SinWTs.mem_of_getElem? LF k x hx)
    have h2 : Prf (ENS.isFormCodeE2 (objList LF) WT (nthc (objList LF) (numeralM k))) :=
      prfH_nil_to_prf (ENS.PrfH_congr_isFormCodeE2
        (prf_to_prfH (prf_eq_symm (SinWTs.prf_nthc_objList LF k x hx)) [])
        (prf_to_prfH hn [])) rfl
    simpa only [ENS.substF_isFormCodeE2, nthc, substTerm, substTerms, hWs, hWTs,
      substTerm_numeralM, if_true, reduceIte] using h2

/-! ## §HW.8 · EL ENSAMBLAJE. -/

theorem lift_wF (phi : Formula) :
    ∀ c : Nat, liftTerm c (objList (fcodesF phi)) = objList (fcodesF phi) := fun c =>
  SinWTs.liftTerm_objList c _ (fun y hy => (closed_mem_fcodesF phi y hy).1 c)

theorem subst_wF (phi : Formula) : ∀ (v : Nat) (s : Term),
    substTerm v s (objList (fcodesF phi)) = objList (fcodesF phi) := fun v s =>
  SinWTs.substTerm_objList v s _ (fun y hy => (closed_mem_fcodesF phi y hy).2 v s)

theorem lift_wT (phi : Formula) :
    ∀ c : Nat, liftTerm c (objList (tcodesF phi)) = objList (tcodesF phi) := fun c =>
  SinWTs.liftTerm_objList c _ (fun y hy => (closed_mem_tcodesF phi y hy).1 c)

theorem subst_wT (phi : Formula) : ∀ (v : Nat) (s : Term),
    substTerm v s (objList (tcodesF phi)) = objList (tcodesF phi) := fun v s =>
  SinWTs.substTerm_objList v s _ (fun y hy => (closed_mem_tcodesF phi y hy).2 v s)

theorem prf_wfAll1_real (phi : Formula) : Prf (SinWTs.wfAll1 (objList (tcodesF phi))) :=
  prf_wfAll1_of_list (tcodesF phi) (closed_mem_tcodesF phi)
    (fun x hx => okT_F phi (objList (tcodesF phi)) (lift_wT phi) (subst_wT phi)
      (fun y hy => SinWTs.prf_In_objList _ y hy) x hx)

theorem prf_wfAllF_real (phi : Formula) :
    Prf (ENS.wfAllF (objList (fcodesF phi)) (objList (tcodesF phi))) :=
  prf_wfAllF_of_list (fcodesF phi) (objList (tcodesF phi)) (lift_wT phi) (subst_wT phi)
    (fun x hx c => (closed_mem_fcodesF phi x hx).1 c)
    (fun x hx v s => (closed_mem_fcodesF phi x hx).2 v s)
    (fun x hx => okF phi (objList (fcodesF phi)) (objList (tcodesF phi))
      (lift_wT phi) (subst_wT phi)
      (fun y hy => SinWTs.prf_In_objList _ y hy)
      (fun y hy => SinWTs.prf_In_objList _ y hy) x hx)

/-- ★★★ **EL TEOREMA**: la guarda `ENS.isFC1` es SATISFACIBLE por codigos REALES,
    con testigos EXPLICITOS y COMPUTABLES. ★★★ -/
theorem prf_isFC1_real (phi : Formula) :
    Prf (ENS.isFC1 (objList (fcodesF phi)) (objList (tcodesF phi)) (formCodeM phi)) :=
  prf_and_intro (prf_and_intro (prf_wfAll1_real phi) (prf_wfAllF_real phi))
    (SinWTs.prf_In_objList _ (formCodeM phi) (mem_self_fcodesF phi))

/-- ★★★ **LA FORMA SIN TESTIGOS** — la que consume el reflector rio abajo. ★★★ -/
theorem prf_hasWitF_real (phi : Formula) : Prf (ENS.hasWitF (formCodeM phi)) := by
  have hWFl := lift_wF phi
  have hWFs := subst_wF phi
  have key := prf_isFC1_real phi
  have step2 : Prf (substFormula 0 (objList (tcodesF phi))
      (ENS.isFC1 (objList (fcodesF phi)) (.var 0) (formCodeM phi))) := by
    simpa only [ENS.substF_isFC1, substTerm, hWFs, substTerm_formCodeM, if_true,
      reduceIte] using key
  have step1 : Prf (Formula.ex
      (ENS.isFC1 (objList (fcodesF phi)) (.var 0) (formCodeM phi))) :=
    prf_ex_intro _ step2
  have step0 : Prf (substFormula 0 (objList (fcodesF phi))
      (Formula.ex (ENS.isFC1 (.var 1) (.var 0) (formCodeM phi)))) := by
    simpa only [substFormula, ENS.substF_isFC1, substTerm, hWFl, hWFs,
      substTerm_formCodeM, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT,
      Nat.reduceSub, Nat.reduceEqDiff, reduceIte, if_true] using step1
  have hfin : Prf (Formula.ex (Formula.ex
      (ENS.isFC1 (.var 1) (.var 0) (formCodeM phi)))) := prf_ex_intro _ step0
  simpa only [ENS.hasWitF, liftTerm_formCodeM] using hfin

end HW
end S_HW


end ROBINSON_PlusPlus.Meta.CodeWitnessPrf

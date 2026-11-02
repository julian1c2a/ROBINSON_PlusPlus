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
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prfᵢ.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prfᵢ.j2 A B)

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
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
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

end SinWTs
end S_Clausura
end ROBINSON_PlusPlus.Meta.CodeWitnessPrf

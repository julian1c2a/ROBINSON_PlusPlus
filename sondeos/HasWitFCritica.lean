/- # HW_critica — CRITICA COMPILADA del enunciado `prf_hasWitF_real` / `prf_isFC1_real`.

   Ruta (C): no se prueba el teorema; se MIDEN las cuatro preguntas del encargo con Lean.

   ⚠️ CERO `axiom` de Lean, cero `sorry`. Autocontenido (`import ROBINSON_PlusPlus.Meta`).

       lake env lean Probe\HW_critica.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ############################################################################
    BLOQUE A · COPIA LITERAL de `sondeos/EvalSubstfcPrf.lean` lineas 22-1407
    (`section S_Clausura`, namespace `SinWTs`): el reconocedor de TERMINO en forma
    ECUACIONAL, su testigo `prf_isTC1_tcodes` (= P2 del encargo), la discriminacion
    posicional `isFormCodeB2` y el kit `prf_shape_strengthens` / `prf_str_and`.
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


/-! ############################################################################
    VERIFICACION ADVERSARIAL - anexo del auditor. Todo lo de arriba es COPIA
    literal de Probe/Lift_sinwts.lean. Aqui solo se MIDEN las afirmaciones.
    ############################################################################ -/

namespace SinWTs
section CRITICA

/-! ## C1 - DISCRIMINACION ECUACIONAL: los OCHO tags de FORMULA, no solo `implc`.
       (El informe solo compilo `_implc` para la forma ECUACIONAL.) -/

theorem CRIT_E1_botc (w : Term) :
    Prf (Formula.impl (isTermCodeE1 w botc) Formula.bottom) :=
  crit_isTermCodeE1_rejects w botc 2 (by decide) (by decide) (prf_carc_cons _ _)

theorem CRIT_E1_atomc (w p ts : Term) :
    Prf (Formula.impl (isTermCodeE1 w (atomc p ts)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (atomc p ts) 3 (by decide) (by decide) (prf_carc_cons _ _)

theorem CRIT_E1_eqc (w a b : Term) :
    Prf (Formula.impl (isTermCodeE1 w (eqc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (eqc a b) 4 (by decide) (by decide) (prf_carc_cons _ _)

theorem CRIT_E1_forallc (w a : Term) :
    Prf (Formula.impl (isTermCodeE1 w (forallc a)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (forallc a) 6 (by decide) (by decide) (prf_carc_cons _ _)

theorem CRIT_E1_andc (w a b : Term) :
    Prf (Formula.impl (isTermCodeE1 w (andc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (andc a b) 7 (by decide) (by decide) (prf_carc_cons _ _)

theorem CRIT_E1_orc (w a b : Term) :
    Prf (Formula.impl (isTermCodeE1 w (orc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (orc a b) 8 (by decide) (by decide) (prf_carc_cons _ _)

theorem CRIT_E1_exc (w a : Term) :
    Prf (Formula.impl (isTermCodeE1 w (exc a)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (exc a) 9 (by decide) (by decide) (prf_carc_cons _ _)

/-! ## C2 - SATISFACIBILIDAD con codigos REALES CONCRETOS (el encargo lo exige
       explicitamente: `termCodeM (func "f" [var 0])`). -/

def tEjA : Term := Term.func "f" [Term.var 0]
def tEjB : Term := Term.func "f" [Term.func "g" [Term.var 0], Term.var 1]

theorem CRIT_sat_A : Prf (isTC1 (objList (tcodes1 tEjA)) (termCodeM tEjA)) :=
  prf_isTC1_tcodes tEjA

theorem CRIT_sat_B : Prf (isTC1 (objList (tcodes1 tEjB)) (termCodeM tEjB)) :=
  prf_isTC1_tcodes tEjB

theorem CRIT_sat_B_lift :
    Prf (isTC1 (liftsc zero (objList (tcodes1 tEjB))) (liftc zero (termCodeM tEjB))) :=
  prf_isTC1_tcodes_lifted tEjB

theorem CRIT_sat_B_lift2 :
    Prf (isTC1 (liftsc zero (liftsc zero (objList (tcodes1 tEjB))))
               (liftc zero (liftc zero (termCodeM tEjB)))) :=
  prf_isTC1_tcodes_lifted2 tEjB

/-- El testigo NO es la lista vacia ni un truco: un elemento por subtermino. -/
example : (tcodes1 tEjA).length = 2 := by rfl
example : (tcodes1 tEjB).length = 4 := by rfl

/-! ## C3 - EL TEST DECISIVO: `wfAll1` SEPARA. Demostrable para listas REALES
       (C2) y REFUTABLE para una lista testigo que contenga un codigo de FORMULA.
       Sin esto la clausura podria ser vacua (antecedente insatisfacible) o
       trivial (`wfAll1` demostrable para cualquier `w`). -/

def junkC : Term := implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))

theorem CRIT_wfAll1_junk_refutado (h : Prf (wfAll1 (objList [junkC]))) :
    Prf Formula.bottom :=
  crit_junk_SubCodesCritica_open1 (objList [junkC])
    (prf_and_intro h (prf_In_objList [junkC] junkC (List.Mem.head _)))

/-- Y con el junk METIDO EN MEDIO de un testigo por lo demas legitimo. -/
theorem CRIT_wfAll1_junk_contaminado (h : Prf (wfAll1 (objList (tcodes1 tEjB ++ [junkC])))) :
    Prf Formula.bottom :=
  crit_junk_SubCodesCritica_open1 (objList (tcodes1 tEjB ++ [junkC]))
    (prf_and_intro h (prf_In_objList _ junkC (List.mem_append.mpr (Or.inr (List.Mem.head _)))))

/-! ## C4 - EL AGUJERO (b) MEDIDO EN EL PEOR CASO: la ranura del SIMBOLO de
       funcion nunca estuvo tipada (tampoco en el piloto: `CritPiloto.funcOkT`
       solo mira `carc`, `lenc` y `nthc X 2`), y con `lenc Y = 0` la carga de
       argumentos desaparece. Resultado: un "codigo de termino" cuyo simbolo de
       funcion es el CODIGO DE UNA FORMULA pasa el reconocedor, con testigo `nil`. -/

theorem CRIT_hueco_funcc_nil (S : Term) : Prf (isTermCodeE1 nil (funcc S nil)) :=
  crit_isTermCodeE1_funcc_lenc_zero nil S nil
    (by simp only [nil, zero, liftTerm, liftTerms])
    (by simp only [nil, zero, liftTerm, liftTerms])
    (fun v s => by simp only [nil, zero, substTerm, substTerms])
    (fun v s => by simp only [nil, zero, substTerm, substTerms])
    prf_lenc_nil

theorem CRIT_hueco_simbolo_es_formula : Prf (isTermCodeE1 nil (funcc junkC nil)) :=
  CRIT_hueco_funcc_nil junkC

end CRITICA
end SinWTs


/-! ## C5 - LA PRUEBA DE FUEGO: la forma con testigo EXISTENCIAL, que es la que
       de verdad hace falta rio abajo (el testigo llega de un ex-elim, no dado).
       Si "el testigo puede ser #0" significa algo, esto tiene que salir. -/

namespace SinWTs
section CRITICA2

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

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

/-- «`c` TIENE testigo» — el testigo esta CUANTIFICADO, no dado. -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

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

/-- Y no vacua: todo termino real TIENE testigo en esa forma. -/
theorem CRIT_hasWit_real (t : Term) : Prf (hasWit (termCodeM t)) := by
  refine prf_ex_intro (objList (tcodes1 t)) ?_
  have h : substFormula 0 (objList (tcodes1 t)) (isTC1 (.var 0) (liftTerm 0 (termCodeM t)))
      = isTC1 (objList (tcodes1 t)) (termCodeM t) := by
    simp only [substF_isTC1, substTerm, if_true, FOL.substTerm_liftTerm]
  rw [h]
  exact prf_isTC1_tcodes t

theorem CRIT_hasWit_real_lifted (t : Term) : Prf (hasWit (liftc zero (termCodeM t))) :=
  prf_mp (CRIT_hasWit_lift (termCodeM t)) (CRIT_hasWit_real t)

end CRITICA2
end SinWTs
end S_Clausura

/-! ############################################################################
    BLOQUE B · COPIA LITERAL de `sondeos/EvalSubstfcPrf.lean` lineas 5953-6227
    (`section S_Ens`, namespace `ENS`, §0-§2): el reconocedor de FORMULA en forma
    ECUACIONAL con DOS listas (`isFormCodeE2`, `wfAllF`, `isFC1`) y su fontaneria.
    ############################################################################ -/
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

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def shapeNul (X : Term) (k : Nat) : Formula := Formula.eq X (cons (numeralM k) nil)

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

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

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

/-! ############################################################################
    BLOQUE C · COPIA LITERAL de `sondeos/EvalSubstfcPrf.lean` lineas 8242-8324
    (§14 y §15 de `ENS`): `hasWitF`, el fortalecimiento E ==> B y los controles de
    discriminacion ya probados (`CRIT_isFC1_rejects_varc`).
    (`prf_lorL`/`prf_lorR` se copian de `EvalSubstfcPrf.lean:7158-7159`, que viven
     en una seccion intermedia de `ENS` no incluida aqui.)
    ############################################################################ -/

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prf₀.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prf₀.j2 A B)
/-- La misma, con la guarda de formula en forma de `∃` (la que llega rio abajo). -/
def hasWitF (c : Term) : Formula :=
  Formula.ex (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 c))))

/-! ############################################################################
    ## §14 · CONTROLES DE DISCRIMINACION — el reconocedor de FORMULA no acepta
       codigos de TERMINO. La forma ECUACIONAL FORTALECE la posicional
       `SinWTs.isFormCodeB2`, y la discriminacion de aquella se hereda entera.
    ############################################################################ -/

theorem prf_shapeNul_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeNul X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 1))))) :=
  SinWTs.prf_shape_strengthens X _ k 1 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c1 _) (SinWTs.prf_consOk_cons _ _)

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

/-- **CONTROL**: un codigo de VARIABLE (tag 0) NO pasa por el reconocedor de FORMULA. -/
theorem CRIT_E2_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT (varc n)) Formula.bottom) :=
  impT (prf_isFormCodeE2_str wF wT (varc n))
    (SinWTs.crit_isFormCodeB2_rejects_varc wF wT n)

/-- **CONTROL**: un codigo de FUNCION (tag 1) tampoco. -/
theorem CRIT_E2_rejects_funcc (wF wT p ts : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT (funcc p ts)) Formula.bottom) :=
  impT (prf_isFormCodeE2_str wF wT (funcc p ts))
    (SinWTs.crit_isFormCodeB2_rejects_funcc wF wT p ts)

/-- **CONTROL**: la GUARDA COMPLETA hereda la discriminacion — un codigo de termino
    no puede estar en la lista testigo de formulas y ser aceptado. -/
theorem CRIT_isFC1_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (isFC1 wF wT (varc n)) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isFC1 wF wT (varc n))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (prf_isFormCodeE2_of_In wF wT (varc n)) _) hin) hwF
  exact PrfH.mp _ _ _ (prf_to_prfH (CRIT_E2_rejects_varc wF wT n) _) hcode

/-! ############################################################################
    ## §15 · LA FORMA CON LOS TESTIGOS CUANTIFICADOS — la que llega rio abajo.
    ############################################################################ -/

theorem liftF_hasWitF (k : Nat) (c : Term) :
    liftFormula k (hasWitF c) = hasWitF (liftTerm k c) := by
  have h1 : (1 < k + 1 + 1) = True := eq_true (by omega)
  simp only [hasWitF, liftFormula, liftF_isFC1, liftTerm, Nat.reduceAdd, h1, if_true,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

end ENS
end S_Ens

/-! ############################################################################
    ############################################################################
    ##                                                                        ##
    ##   L A   C R I T I C A   —  las cuatro preguntas, respondidas en Lean    ##
    ##                                                                        ##
    ############################################################################
    ############################################################################ -/

section S_Critica
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
open ROBINSON_PlusPlus.Meta.ChainPrf

namespace CRITICA

/-! ############################################################################
    ## P1 · ¿BASTA UNA LISTA?  **NO — y no por dificultad: la guarda con UNA
       sola lista es REFUTABLE para TODO codigo de formula y TODO testigo.**

    El contra-argumento del encargo se confirma y se AFILA: no es que `wfAll1`
    "fallaria"; es que `isFC1 w w (formCodeM φ)` demuestra `⊥` en la teoria objeto.
    ############################################################################ -/

/-- Puente de namespaces: `ENS.wfAll1` y `SinWTs.wfAll1` son la MISMA definicion
    (dos constantes distintas, defeq). Sin este puente los lemas de `SinWTs` no
    se aplican al desmontar `ENS.isFC1`. -/
theorem br_wfAll1 (w : Term) : ENS.wfAll1 w = SinWTs.wfAll1 w := rfl
theorem br_argsIn (w Y : Term) : ENS.argsIn w Y = SinWTs.argsIn w Y := rfl
theorem br_isTermCodeE1 (w X : Term) :
    ENS.isTermCodeE1 w X = SinWTs.isTermCodeE1 w X := rfl

/-- El TAG de un codigo de formula real: siempre en `2..9`, nunca `0` (variable)
    ni `1` (funcion). -/
theorem tag_formCodeM : ∀ φ : Formula,
    ∃ k : Nat, And (k ≠ 0) (And (k ≠ 1) (Prf (carc (formCodeM φ) =eq numeralM k)))
  | .bottom          => ⟨2, by decide, by decide, prf_carc_cons _ _⟩
  | .atom _ _        => ⟨3, by decide, by decide, prf_carc_cons _ _⟩
  | .eq _ _          => ⟨4, by decide, by decide, prf_carc_cons _ _⟩
  | .impl _ _        => ⟨5, by decide, by decide, prf_carc_cons _ _⟩
  | Formula.forall _ => ⟨6, by decide, by decide, prf_carc_cons _ _⟩
  | .and _ _         => ⟨7, by decide, by decide, prf_carc_cons _ _⟩
  | .or _ _          => ⟨8, by decide, by decide, prf_carc_cons _ _⟩
  | .ex _            => ⟨9, by decide, by decide, prf_carc_cons _ _⟩

/-- **RESPUESTA A P1 (generica)**: si el codigo `c` es cerrado y su tag no es de
    TERMINO (`≠0`, `≠1`), la guarda con `wF = wT = w` es REFUTABLE, sea `w` el que sea. -/
theorem CRIT_P1_una_lista_refutada (w c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (ENS.isFC1 w w c) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (ENS.isFC1 w w c)
  have hwf : PrfH [ENS.isFC1 w w c] (SinWTs.wfAll1 w) :=
    PrfH_and_elim_left (PrfH_and_elim_left hh)
  have hin : PrfH [ENS.isFC1 w w c] (In c w) := PrfH_and_elim_right hh
  have hb : PrfH [ENS.isFC1 w w c] (boundedIn c w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In c w) _) hin
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (SinWTs.prf_crit_In_rejects_open1 w c k hk0 hk1 hcl hck) _) hb) hwf

/-- **★ RESPUESTA A P1 ★** — con UNA sola lista, la guarda no es "mas dificil":
    es **IMPOSIBLE**. Para toda formula `φ` y todo testigo `w`,
    `isFC1 w w ⌜φ⌝` demuestra `⊥`. -/
theorem CRIT_P1_una_lista_imposible (w : Term) (φ : Formula) :
    Prf (Formula.impl (ENS.isFC1 w w (formCodeM φ)) Formula.bottom) := by
  obtain ⟨k, h0, h1, hk⟩ := tag_formCodeM φ
  exact CRIT_P1_una_lista_refutada w (formCodeM φ) k h0 h1
    (fun n => liftTerm_formCodeM n φ) hk

/-- Control: la refutacion vale tambien con el testigo LITERALMENTE `#0`
    (el que entrega un `∃`-elim rio abajo). -/
theorem CRIT_P1_var0 (φ : Formula) :
    Prf (Formula.impl (ENS.isFC1 (.var 0) (.var 0) (formCodeM φ)) Formula.bottom) :=
  CRIT_P1_una_lista_imposible (.var 0) φ

/-! ############################################################################
    ## P2 · ¿ATAJO POR EL PREDICADO POSICIONAL (`isFCB3`, que YA tiene testigo)?

    **NO HACE FALTA NINGUN ATAJO.** La direccion que se pedia (B ⇒ E) no se usa:
    para nodos REALES la ecuacion se prueba DIRECTAMENTE, y cuesta 1-3 combinadores.
    Aqui estan los TRES moldes ecuacionales, medidos.
    ############################################################################ -/

/-- Nodo NULO real (`botc`): coste = `prf_refl`. **CERO trabajo.** -/
theorem prf_shapeNul_real (k : Nat) : Prf (ENS.shapeNul (cons (numeralM k) nil) k) :=
  prf_refl _

/-- Nodo UNARIO real (`forallc`, `exc`): **UN** combinador. -/
theorem prf_shapeUn_real (k : Nat) (a : Term) :
    Prf (ENS.shapeUn (cons (numeralM k) (cons a nil)) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (SinWTs.prf_nthc_c1 (numeralM k) a nil)))

/-- Nodo BINARIO real (`atomc`, `eqc`, `implc`, `andc`, `orc`): **TRES** combinadores. -/
theorem prf_shapeBin_real (k : Nat) (a b : Term) :
    Prf (ENS.shapeBin (cons (numeralM k) (cons a (cons b nil))) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
    (prf_congr_cons_head (SinWTs.prf_nthc_c1 (numeralM k) a (cons b nil)))
    (prf_congr_cons_tail (prf_congr_cons_head
      (SinWTs.prf_nthc_c2 (numeralM k) a b nil)))))

/-- Y el molde POSICIONAL correspondiente, para COMPARAR el coste real. -/
theorem prf_binOkF_real (wA wB : Term) (k : Nat) (a b : Term)
    (hA : Prf (In a wA)) (hB : Prf (In b wB)) :
    Prf (SinWTs.binOkF wA wB (cons (numeralM k) (cons a (cons b nil))) k) :=
  prf_and_intro
    (prf_and_intro (prf_carc_cons _ _) (SinWTs.prf_lenc_c3 _ _ _))
    (prf_and_intro
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM k) a (cons b nil))) hA)
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM k) a b nil)) hB))

/-- **MEDIDA**: el nodo ECUACIONAL completo (`clBin`) para un `implc` REAL. -/
theorem prf_clBin_real (wF : Term) (k : Nat) (a b : Term)
    (hA : Prf (In a wF)) (hB : Prf (In b wF)) :
    Prf (ENS.clBin wF (cons (numeralM k) (cons a (cons b nil))) k) :=
  prf_and_intro (prf_shapeBin_real k a b)
    (prf_and_intro
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM k) a (cons b nil))) hA)
      (SinWTs.prf_congr_In_left
        (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM k) a b nil)) hB))

/-- **MEDIDA**: el nodo ECUACIONAL unario (`clUn`) para un `forallc` REAL. -/
theorem prf_clUn_real (wF : Term) (k : Nat) (a : Term) (hA : Prf (In a wF)) :
    Prf (ENS.clUn wF (cons (numeralM k) (cons a nil)) k) :=
  prf_and_intro (prf_shapeUn_real k a)
    (SinWTs.prf_congr_In_left
      (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM k) a nil)) hA)

/-- **CONTROL DE DIRECCION**: el fortalecimiento que EXISTE va E ⇒ B.
    La direccion contraria (B ⇒ E) NO se puede obtener por ascripcion de tipo. -/
example (wF wT X : Term) : True := by
  fail_if_success
    exact (ENS.prf_isFormCodeE2_str wF wT X :
      Prf (Formula.impl (SinWTs.isFormCodeB2 wF wT X) (ENS.isFormCodeE2 wF wT X)))
  trivial

/-- Y los dos predicados NO son la misma formula (el control no es una tautologia). -/
example (wF wT X : Term) : True := by
  fail_if_success exact (rfl : ENS.isFormCodeE2 wF wT X = SinWTs.isFormCodeB2 wF wT X)
  trivial

/-! ############################################################################
    ## P3 · ¿SIRVE `prf_hasWitF_real` RIO ABAJO (los 7 reflectores de `lineWF`)?

    **NO.** Y la medida da algo peor que "no sirve": la version ABSTRACTA de la
    guarda (la tarea A4 del arbol) es **REFUTABLE**, no solo dificil.

    La cadena de evidencia, toda compilada:
    1. `pcc_lineWF_tracked_modulo_7` pide los 7 reflectores con `t : Term` **ABSTRACTO**
       (ver el `#check` al final): no hay ningun `formCodeM φ` en el enunciado.
    2. El esquema `prf_lineWF_q1` es **ESTRUCTURAL**: `lineWF ⟨concl,9̄,A,t⟩ ⇔
       concl ≐ implc (forallc A) (substfc 0 t A)`, con `A` y `t` **ARBITRARIOS**.
       No hay NINGUNA clausula de buena formacion sobre `A`.
    3. Luego hay lineas que `lineWF` ACEPTA cuya casilla de formula `nthc t 2̄` es
       un codigo de VARIABLE — y sobre esa casilla `hasWitF` esta REFUTADA
       (`ENS.CRIT_isFC1_rejects_varc`, ya probado en el frente).
    ############################################################################ -/

/-- La BASURA: el codigo de la variable `x₀`. Tag 0 ⟹ jamas es codigo de formula. -/
def JUNKF : Term := varc zero

theorem closed_JUNKF : ∀ n : Nat, liftTerm n JUNKF = JUNKF := by
  intro n
  simp only [JUNKF, varc, cons, nil, zero, succ, liftTerm, liftTerms]

/-- Una linea Q1 (tag 9) **con basura en la casilla de FORMULA**. -/
def q1junk (w : Term) : Term :=
  cons (implc (forallc JUNKF) (substfc zero w JUNKF))
    (cons (numeralM 9) (cons JUNKF (cons w nil)))

/-- **(a)** `lineWF` ACEPTA la linea basura. Sale del propio esquema Q1, por `refl`. -/
theorem CRIT_P3_lineWF_acepta_junk (w : Term) : Prf (lineWF (q1junk w)) :=
  prf_iff_mpr (prf_lineWF_q1 _ JUNKF w) (prf_refl _)

/-- **(b)** …y su TAG es, en efecto, 9 (es una de las 7 ramas pendientes). -/
theorem CRIT_P3_tag_junk (w : Term) : Prf (lineTag (q1junk w) =eq numeralM 9) :=
  SinWTs.prf_nthc_c1 _ (numeralM 9) (cons JUNKF (cons w nil))

/-- **(c)** …y la casilla de FORMULA de esa linea es exactamente la basura. -/
theorem CRIT_P3_slot_junk (w : Term) :
    Prf (nthc (q1junk w) (numeralM 2) =eq JUNKF) :=
  SinWTs.prf_nthc_c2 _ (numeralM 9) JUNKF (cons w nil)

/-- **(d)** …y sobre la basura la guarda `hasWitF` esta REFUTADA. -/
theorem CRIT_P3_hasWitF_junk_refutada :
    Prf (Formula.impl (ENS.hasWitF JUNKF) Formula.bottom) := by
  have hinner : Prf (Formula.impl
      (Formula.ex (ENS.isFC1 (.var 1) (.var 0) JUNKF)) Formula.bottom) :=
    prf_ex_elim_imp (PrfH.mp _ _ _
      (prf_to_prfH (ENS.CRIT_isFC1_rejects_varc (.var 1) (.var 0) zero) _)
      (prfH_hyp_self _))
  have h : ENS.hasWitF JUNKF
      = Formula.ex (Formula.ex (ENS.isFC1 (.var 1) (.var 0) JUNKF)) := by
    simp only [ENS.hasWitF, closed_JUNKF]
  rw [h]
  exact prf_ex_elim_imp (PrfH.mp _ _ _ (prf_to_prfH hinner _) (prfH_hyp_self _))

/-- Leibniz en el argumento de `hasWitF` (el hueco `#0` bajo los DOS binders). -/
theorem substF_hole_hasWitF (u : Term) :
    substFormula 0 u (ENS.hasWitF (.var 0)) = ENS.hasWitF u := by
  show Formula.ex (Formula.ex (substFormula 2 (liftTerm 0 (liftTerm 0 u))
        (ENS.isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (.var 0))))))
      = Formula.ex (Formula.ex (ENS.isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 u))))
  rw [ENS.substF_isFC1]
  rfl

theorem substF_hole_isFC1 (wF wT u : Term) :
    substFormula 0 u (ENS.isFC1 (liftTerm 0 wF) (liftTerm 0 wT) (.var 0))
      = ENS.isFC1 wF wT u := by
  rw [ENS.substF_isFC1]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_isFC1_arg {Γ : List Formula} {wF wT X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (ha : PrfH Γ (ENS.isFC1 wF wT X₁)) :
    PrfH Γ (ENS.isFC1 wF wT X₂) :=
  (substF_hole_isFC1 wF wT X₂) ▸
    PrfH_leibniz_subst (A := ENS.isFC1 (liftTerm 0 wF) (liftTerm 0 wT) (.var 0)) h
      ((substF_hole_isFC1 wF wT X₁) ▸ ha)

theorem PrfH_congr_hasWitF {Γ : List Formula} {X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (ha : PrfH Γ (ENS.hasWitF X₁)) : PrfH Γ (ENS.hasWitF X₂) :=
  (substF_hole_hasWitF X₂) ▸
    PrfH_leibniz_subst (A := ENS.hasWitF (.var 0)) h ((substF_hole_hasWitF X₁) ▸ ha)

/-- **★ RESPUESTA A P3 ★** — **A4 (la guarda sobre argumento ABSTRACTO) es FALSA.**
    Si de `lineWF t` saliera `hasWitF (nthc t 2̄)`, la teoria objeto seria INCONSISTENTE.
    (Y A4 es exactamente lo que los 7 reflectores necesitan: `pcc_eval_substfc` pide
    `isFC1 wF wT f` con `f = nthc t 2̄` abstracto.) -/
theorem CRIT_P3_A4_da_inconsistencia
    (hA4 : ∀ t : Term, Prf (Formula.impl (lineWF t)
      (ENS.hasWitF (nthc t (numeralM 2))))) :
    Prf Formula.bottom := by
  have h1 : Prf (ENS.hasWitF (nthc (q1junk zero) (numeralM 2))) :=
    prf_mp (hA4 (q1junk zero)) (CRIT_P3_lineWF_acepta_junk zero)
  have h2 : Prf (ENS.hasWitF JUNKF) :=
    prfH_nil_to_prf
      (PrfH_congr_hasWitF (prf_to_prfH (CRIT_P3_slot_junk zero) [])
        (prf_to_prfH h1 [])) rfl
  exact prf_mp CRIT_P3_hasWitF_junk_refutada h2

/-- Variante: tampoco vale con la guarda EXPLICITA (dos listas cuantificadas fuera).
    Ninguna eleccion de `wF`/`wT` salva la linea basura. -/
theorem CRIT_P3_A4_explicita_da_inconsistencia
    (hA4 : ∀ t : Term, ∃ wF wT : Term,
      Prf (Formula.impl (lineWF t) (ENS.isFC1 wF wT (nthc t (numeralM 2))))) :
    Prf Formula.bottom := by
  obtain ⟨wF, wT, h⟩ := hA4 (q1junk zero)
  have h1 : Prf (ENS.isFC1 wF wT (nthc (q1junk zero) (numeralM 2))) :=
    prf_mp h (CRIT_P3_lineWF_acepta_junk zero)
  have h2 : Prf (ENS.isFC1 wF wT JUNKF) :=
    prfH_nil_to_prf
      (PrfH_congr_isFC1_arg (prf_to_prfH (CRIT_P3_slot_junk zero) [])
        (prf_to_prfH h1 [])) rfl
  exact prf_mp (ENS.CRIT_isFC1_rejects_varc wF wT zero) h2

end CRITICA
end S_Critica

/-! ############################################################################
    ## P3-bis · LA VERSION FUERTE: hay lineas que `lineWF` ACEPTA cuya casilla
       de formula esta refutada por **LAS DOS** guardas a la vez (`hasWit` de
       TERMINO y `hasWitF` de FORMULA). Luego tampoco salva el dia una guarda
       DISYUNTIVA "o es codigo de termino o es codigo de formula".
    ############################################################################ -/

section P3bis
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.ChainPrf

namespace CRITICA

/-- `isFC1` es refutable en cuanto el TAG del codigo cae fuera de `2..9`. -/
theorem CRIT_isFC1_rejects_tag (wF wT X : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (ENS.isFC1 wF wT X) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (ENS.isFC1 wF wT X)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT X) _) hin) hwF
  exact PrfH.mp _ _ _ (prf_to_prfH
    (SinWTs.impT (ENS.prf_isFormCodeE2_str wF wT X)
      (SinWTs.crit_isFormCodeB2_rejects wF wT X k h2 h3 h4 h5 h6 h7 h8 h9 hX)) _) hcode

/-- `isTC1` es refutable en cuanto el TAG cae fuera de `{0,1}`. -/
theorem CRIT_isTC1_rejects_tag (w c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (ENS.isTC1 w c) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (ENS.isTC1 w c)
  have hwf : PrfH [ENS.isTC1 w c] (SinWTs.wfAll1 w) := PrfH_and_elim_left hh
  have hin : PrfH [ENS.isTC1 w c] (In c w) := PrfH_and_elim_right hh
  have hb : PrfH [ENS.isTC1 w c] (boundedIn c w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In c w) _) hin
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (SinWTs.prf_crit_In_rejects_open1 w c k hk0 hk1 hcl hck) _) hb) hwf

theorem CRIT_hasWit_rejects_tag (c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (ENS.hasWit c) Formula.bottom) := by
  have h : ENS.hasWit c = Formula.ex (ENS.isTC1 (.var 0) c) := by
    simp only [ENS.hasWit, hcl]
  rw [h]
  exact prf_ex_elim_imp (PrfH.mp _ _ _
    (prf_to_prfH (CRIT_isTC1_rejects_tag (.var 0) c k hk0 hk1 hcl hck) _)
    (prfH_hyp_self _))

theorem CRIT_hasWitF_rejects_tag (c : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (ENS.hasWitF c) Formula.bottom) := by
  have hinner : Prf (Formula.impl
      (Formula.ex (ENS.isFC1 (.var 1) (.var 0) c)) Formula.bottom) :=
    prf_ex_elim_imp (PrfH.mp _ _ _
      (prf_to_prfH (CRIT_isFC1_rejects_tag (.var 1) (.var 0) c k
        h2 h3 h4 h5 h6 h7 h8 h9 hck) _)
      (prfH_hyp_self _))
  have h : ENS.hasWitF c
      = Formula.ex (Formula.ex (ENS.isFC1 (.var 1) (.var 0) c)) := by
    simp only [ENS.hasWitF, hcl]
  rw [h]
  exact prf_ex_elim_imp (PrfH.mp _ _ _ (prf_to_prfH hinner _) (prfH_hyp_self _))

/-- Basura con TAG 30: ni codigo de termino (`≠0,1`) ni codigo de formula (`≠2..9`). -/
def JUNK30 : Term := cons (numeralM 30) nil

theorem closed_JUNK30 : ∀ n : Nat, liftTerm n JUNK30 = JUNK30 := by
  intro n
  simp only [JUNK30, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem carc_JUNK30 : Prf (carc JUNK30 =eq numeralM 30) := prf_carc_cons _ _

/-- Linea Q1 (tag 9) con basura TOTAL en la casilla de formula. -/
def q1junk30 (w : Term) : Term :=
  cons (implc (forallc JUNK30) (substfc zero w JUNK30))
    (cons (numeralM 9) (cons JUNK30 (cons w nil)))

theorem CRIT_P3b_lineWF_acepta (w : Term) : Prf (lineWF (q1junk30 w)) :=
  prf_iff_mpr (prf_lineWF_q1 _ JUNK30 w) (prf_refl _)

theorem CRIT_P3b_tag (w : Term) : Prf (lineTag (q1junk30 w) =eq numeralM 9) :=
  SinWTs.prf_nthc_c1 _ (numeralM 9) (cons JUNK30 (cons w nil))

theorem CRIT_P3b_slot (w : Term) : Prf (nthc (q1junk30 w) (numeralM 2) =eq JUNK30) :=
  SinWTs.prf_nthc_c2 _ (numeralM 9) JUNK30 (cons w nil)

theorem CRIT_P3b_hasWitF_refutada : Prf (Formula.impl (ENS.hasWitF JUNK30) Formula.bottom) :=
  CRIT_hasWitF_rejects_tag JUNK30 30 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) closed_JUNK30 carc_JUNK30

theorem CRIT_P3b_hasWit_refutada : Prf (Formula.impl (ENS.hasWit JUNK30) Formula.bottom) :=
  CRIT_hasWit_rejects_tag JUNK30 30 (by decide) (by decide) closed_JUNK30 carc_JUNK30

/-- Leibniz para `hasWit` (hueco `#0` bajo UN binder). -/
theorem substF_hole_hasWit (u : Term) :
    substFormula 0 u (ENS.hasWit (.var 0)) = ENS.hasWit u := by
  show Formula.ex (substFormula 1 (liftTerm 0 u)
        (ENS.isTC1 (.var 0) (liftTerm 0 (.var 0))))
      = Formula.ex (ENS.isTC1 (.var 0) (liftTerm 0 u))
  rw [ENS.substF_isTC1]
  rfl

theorem PrfH_congr_hasWit {Γ : List Formula} {X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (ha : PrfH Γ (ENS.hasWit X₁)) : PrfH Γ (ENS.hasWit X₂) :=
  (substF_hole_hasWit X₂) ▸
    PrfH_leibniz_subst (A := ENS.hasWit (.var 0)) h ((substF_hole_hasWit X₁) ▸ ha)

/-- **★ RESPUESTA A P3, VERSION FUERTE ★** — ni siquiera la guarda DISYUNTIVA
    (`el slot es codigo de termino O es codigo de formula`) se deja derivar de
    `lineWF`: si se derivara, la teoria objeto seria INCONSISTENTE. -/
theorem CRIT_P3b_guarda_disyuntiva_da_inconsistencia
    (hA4 : ∀ t : Term, Prf (Formula.impl (lineWF t)
      (lor (ENS.hasWit (nthc t (numeralM 2))) (ENS.hasWitF (nthc t (numeralM 2)))))) :
    Prf Formula.bottom := by
  have h1 : Prf (lor (ENS.hasWit (nthc (q1junk30 zero) (numeralM 2)))
      (ENS.hasWitF (nthc (q1junk30 zero) (numeralM 2)))) :=
    prf_mp (hA4 (q1junk30 zero)) (CRIT_P3b_lineWF_acepta zero)
  refine prf_mp (SinWTs.prf_or_elim_imp ?_ ?_) h1
  · refine prf_deduction ?_
    exact PrfH.mp _ _ _ (prf_to_prfH CRIT_P3b_hasWit_refutada _)
      (PrfH_congr_hasWit (prf_to_prfH (CRIT_P3b_slot zero) _) (prfH_hyp_self _))
  · refine prf_deduction ?_
    exact PrfH.mp _ _ _ (prf_to_prfH CRIT_P3b_hasWitF_refutada _)
      (PrfH_congr_hasWitF (prf_to_prfH (CRIT_P3b_slot zero) _) (prfH_hyp_self _))

end CRITICA
end P3bis

/-! ############################################################################
    ## EVIDENCIA RIO ABAJO (los `#check` que sostienen la respuesta a P3)

    * `pcc_lineWF_tracked_modulo_7` pide los 7 reflectores con `t : Term` ABSTRACTO.
    * `prf_lineWF_q1` es un esquema PURAMENTE ESTRUCTURAL: `A` y `t` arbitrarios,
      ninguna clausula de buena formacion.
    * `CTree` (el reificador generico de los RHS de `lineWF`, `Meta/CodeTreeReflect`)
      solo tiene `leaf`/`nul`/`un`/`bin`: **no hay constructor para `substfc`**, que
      es justamente lo que aparece en los RHS de los tags 9, 10 y 13.
    ############################################################################ -/

#check @ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_modulo_7
#check @ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_of_branches
#check @ROBINSON_PlusPlus.Meta.ReprPrf.prf_lineWF_q1
#print ROBINSON_PlusPlus.Meta.CodeTreeReflect.CTree
#check @ROBINSON_PlusPlus.Meta.CodeTreeReflect.pcc_lineWF_tracked_of_tree

/-! ### Los enunciados de la critica -/
#check @CRITICA.CRIT_P1_una_lista_imposible
#check @CRITICA.CRIT_P1_var0
#check @CRITICA.prf_shapeNul_real
#check @CRITICA.prf_shapeUn_real
#check @CRITICA.prf_shapeBin_real
#check @CRITICA.CRIT_P3_lineWF_acepta_junk
#check @CRITICA.CRIT_P3_slot_junk
#check @CRITICA.CRIT_P3_hasWitF_junk_refutada
#check @CRITICA.CRIT_P3_A4_da_inconsistencia
#check @CRITICA.CRIT_P3_A4_explicita_da_inconsistencia
#check @CRITICA.CRIT_P3b_lineWF_acepta
#check @CRITICA.CRIT_P3b_hasWit_refutada
#check @CRITICA.CRIT_P3b_hasWitF_refutada
#check @CRITICA.CRIT_P3b_guarda_disyuntiva_da_inconsistencia

/-! ### AUDITORIA DE FOOTPRINT — todo debe salir sobre la base sancionada -/
#print axioms CRITICA.tag_formCodeM
#print axioms CRITICA.CRIT_P1_una_lista_refutada
#print axioms CRITICA.CRIT_P1_una_lista_imposible
#print axioms CRITICA.CRIT_P1_var0
#print axioms CRITICA.prf_shapeNul_real
#print axioms CRITICA.prf_shapeUn_real
#print axioms CRITICA.prf_shapeBin_real
#print axioms CRITICA.prf_binOkF_real
#print axioms CRITICA.prf_clBin_real
#print axioms CRITICA.prf_clUn_real
#print axioms CRITICA.CRIT_P3_lineWF_acepta_junk
#print axioms CRITICA.CRIT_P3_tag_junk
#print axioms CRITICA.CRIT_P3_slot_junk
#print axioms CRITICA.CRIT_P3_hasWitF_junk_refutada
#print axioms CRITICA.substF_hole_hasWitF
#print axioms CRITICA.PrfH_congr_hasWitF
#print axioms CRITICA.CRIT_P3_A4_da_inconsistencia
#print axioms CRITICA.CRIT_P3_A4_explicita_da_inconsistencia
#print axioms CRITICA.CRIT_isFC1_rejects_tag
#print axioms CRITICA.CRIT_isTC1_rejects_tag
#print axioms CRITICA.CRIT_hasWit_rejects_tag
#print axioms CRITICA.CRIT_hasWitF_rejects_tag
#print axioms CRITICA.CRIT_P3b_lineWF_acepta
#print axioms CRITICA.CRIT_P3b_slot
#print axioms CRITICA.CRIT_P3b_hasWit_refutada
#print axioms CRITICA.CRIT_P3b_hasWitF_refutada
#print axioms CRITICA.CRIT_P3b_guarda_disyuntiva_da_inconsistencia

/-! ############################################################################
    ############################################################################
    ##  P4 / BONUS · EL CIERRE: `prf_isFC1_real` y `prf_hasWitF_real`.
    ##
    ##  El transporte medido en P2 resulta BARATO: con los moldes ECUACIONALES
    ##  (`prf_shapeNul_real` / `prf_shapeUn_real` / `prf_shapeBin_real`) y el kit
    ##  de P2 (`prf_isTC1_tcodes`, `objList`, `prf_bdAll_of_bound`) reutilizado
    ##  TAL CUAL, el testigo de FORMULA sale entero.
    ############################################################################
    ############################################################################ -/

section S_Cierre
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.ChainPrf

namespace CIERRE

open CRITICA (prf_shapeNul_real prf_shapeUn_real prf_shapeBin_real)

/-! ### Los DOS colectores (`tcodesF`, `fcodesF`) — la tercera lista de P1 desaparece -/

/-- Subcodigos de TERMINO de una formula (cierre por subterminos), via `SinWTs.tcodes1`. -/
def tcodesF : Formula → List Term
  | .bottom          => []
  | .atom _ ts       => SinWTs.tcodes1s ts
  | .eq t u          => SinWTs.tcodes1 t ++ SinWTs.tcodes1 u
  | .impl a b        => tcodesF a ++ tcodesF b
  | Formula.forall a => tcodesF a
  | .and a b         => tcodesF a ++ tcodesF b
  | .or a b          => tcodesF a ++ tcodesF b
  | .ex a            => tcodesF a

/-- Subcodigos de FORMULA de una formula. -/
def fcodesF : Formula → List Term
  | .bottom          => [formCodeM .bottom]
  | .atom p ts       => [formCodeM (.atom p ts)]
  | .eq t u          => [formCodeM (.eq t u)]
  | .impl a b        => formCodeM (.impl a b) :: (fcodesF a ++ fcodesF b)
  | Formula.forall a => formCodeM (Formula.forall a) :: fcodesF a
  | .and a b         => formCodeM (.and a b) :: (fcodesF a ++ fcodesF b)
  | .or a b          => formCodeM (.or a b) :: (fcodesF a ++ fcodesF b)
  | .ex a            => formCodeM (.ex a) :: fcodesF a

theorem mem_self_fcodesF (φ : Formula) : List.Mem (formCodeM φ) (fcodesF φ) := by
  cases φ <;> (simp only [fcodesF]; exact List.Mem.head _)

theorem closed_formCodeM (φ : Formula) : SinWTs.CodeClosed (formCodeM φ) :=
  ⟨fun c => liftTerm_formCodeM c φ, fun v s => substTerm_formCodeM v s φ⟩

theorem closed_mem_fcodesF : ∀ (φ : Formula) (x : Term),
    List.Mem x (fcodesF φ) → SinWTs.CodeClosed x
  | .bottom, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | .atom p ts, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | .eq t u, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | .impl a b, x, h => by
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
  | .and a b, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | .or a b, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | .ex a, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · exact closed_mem_fcodesF a x h'

theorem closed_mem_tcodesF : ∀ (φ : Formula) (x : Term),
    List.Mem x (tcodesF φ) → SinWTs.CodeClosed x
  | .bottom, x, h => by simp only [tcodesF] at h; cases h
  | .atom p ts, x, h => by
      simp only [tcodesF] at h
      exact SinWTs.closed_mem_tcodes1s ts x h
  | .eq t u, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact SinWTs.closed_mem_tcodes1 t x hA
      · exact SinWTs.closed_mem_tcodes1 u x hB
  | .impl a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesF a x hA
      · exact closed_mem_tcodesF b x hB
  | Formula.forall a, x, h => by
      simp only [tcodesF] at h; exact closed_mem_tcodesF a x h
  | .and a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesF a x hA
      · exact closed_mem_tcodesF b x hB
  | .or a b, x, h => by
      simp only [tcodesF] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesF a x hA
      · exact closed_mem_tcodesF b x hB
  | .ex a, x, h => by
      simp only [tcodesF] at h; exact closed_mem_tcodesF a x h

/-! ### La cara de TERMINO: se DELEGA entera en `SinWTs.okE1_T` / `okE1_Ts` (P2, sin tocar) -/

theorem okT_tcodesF : ∀ (φ : Formula) (WT : Term)
    (hWl : ∀ c : Nat, liftTerm c WT = WT)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (ho : ∀ y : Term, List.Mem y (tcodesF φ) → Prf (In y WT))
    (x : Term), List.Mem x (tcodesF φ) → Prf (ENS.isTermCodeE1 WT x)
  | .bottom, WT, hWl, hWs, ho, x, h => by simp only [tcodesF] at h; cases h
  | .atom p ts, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      exact SinWTs.okE1_Ts ts WT hWl hWs ho x h
  | .eq t u, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      rcases List.mem_append.mp h with hA | hB
      · exact SinWTs.okE1_T t WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact SinWTs.okE1_T u WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | .impl a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      rcases List.mem_append.mp h with hA | hB
      · exact okT_tcodesF a WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact okT_tcodesF b WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | Formula.forall a, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      exact okT_tcodesF a WT hWl hWs ho x h
  | .and a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      rcases List.mem_append.mp h with hA | hB
      · exact okT_tcodesF a WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact okT_tcodesF b WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | .or a b, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      rcases List.mem_append.mp h with hA | hB
      · exact okT_tcodesF a WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inl hy))) x hA
      · exact okT_tcodesF b WT hWl hWs
          (fun y hy => ho y (List.mem_append.mpr (Or.inr hy))) x hB
  | .ex a, WT, hWl, hWs, ho, x, h => by
      simp only [tcodesF] at h ho
      exact okT_tcodesF a WT hWl hWs ho x h

/-! ### Los OCHO nodos ECUACIONALES de FORMULA, para codigos REALES -/

/-- `argsIn WT (termsCodeM ts)` para una lista de terminos REAL. Copia del molde de
    `SinWTs.okE1_T`, caso `.func`. -/
theorem prf_argsIn_termsCodeM (WT : Term) (ts : List Term)
    (hWl : ∀ c : Nat, liftTerm c WT = WT)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (ho : ∀ u : Term, List.Mem u ts → Prf (In (termCodeM u) WT)) :
    Prf (ENS.argsIn WT (termsCodeM ts)) := by
  refine SinWTs.prf_argsIn_of_closed WT (termsCodeM ts) ts.length (hWl 0)
    (liftTerm_termsCodeM 0 ts) hWs (fun v s => substTerm_termsCodeM v s ts)
    (SinWTs.prf_lenc_termsCodeM ts) ?_
  intro k hk
  obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
  exact SinWTs.prf_congr_In_left (prf_eq_symm (SinWTs.prf_nthc_termsCodeM ts k u hu))
    (ho u (SinWTs.mem_of_getElem? ts k u hu))

/-! ### LA INDUCCION SOBRE `Formula` — los ocho disyuntos -/

theorem okF_fcodesF : ∀ (φ : Formula) (WF WT : Term)
    (hWl : ∀ c : Nat, liftTerm c WT = WT)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (hoT : ∀ y : Term, List.Mem y (tcodesF φ) → Prf (In y WT))
    (hoF : ∀ y : Term, List.Mem y (fcodesF φ) → Prf (In y WF))
    (x : Term), List.Mem x (fcodesF φ) → Prf (ENS.isFormCodeE2 WF WT x)
  | .bottom, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        exact SinWTs.prf_orL (prf_shapeNul_real 2)
      · cases h'
  | .atom p ts, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orL ?_)
        refine prf_and_intro (prf_shapeBin_real 3 (strCodeM p) (termsCodeM ts)) ?_
        refine SinWTs.prf_congr_argsIn
          (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 3) (strCodeM p) (termsCodeM ts) nil)) ?_
        refine prf_argsIn_termsCodeM WT ts hWl hWs (fun u hu => ?_)
        exact hoT (termCodeM u) (by
          simp only [tcodesF]; exact SinWTs.mem_tcodes1s_of_mem ts u hu)
      · cases h'
  | .eq t u, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orL ?_))
        refine prf_and_intro (prf_shapeBin_real 4 (termCodeM t) (termCodeM u)) ?_
        refine prf_and_intro ?_ ?_
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 4) (termCodeM t)
              (cons (termCodeM u) nil)))
            (hoT (termCodeM t) (by
              simp only [tcodesF]
              exact List.mem_append.mpr (Or.inl (SinWTs.mem_self_tcodes1 t))))
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 4) (termCodeM t) (termCodeM u) nil))
            (hoT (termCodeM u) (by
              simp only [tcodesF]
              exact List.mem_append.mpr (Or.inr (SinWTs.mem_self_tcodes1 u))))
      · cases h'
  | .impl a b, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orL ?_)))
        refine prf_and_intro (prf_shapeBin_real 5 (formCodeM a) (formCodeM b)) ?_
        refine prf_and_intro ?_ ?_
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 5) (formCodeM a)
              (cons (formCodeM b) nil)))
            (hoF (formCodeM a) (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodesF a)))))
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 5) (formCodeM a) (formCodeM b) nil))
            (hoF (formCodeM b) (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodesF b)))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF_fcodesF a WF WT hWl hWs
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact okF_fcodesF b WF WT hWl hWs
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | Formula.forall a, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
          (SinWTs.prf_orL ?_))))
        refine prf_and_intro (prf_shapeUn_real 6 (formCodeM a)) ?_
        exact SinWTs.prf_congr_In_left
          (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 6) (formCodeM a) nil))
          (hoF (formCodeM a) (by
            simp only [fcodesF]; exact List.Mem.tail _ (mem_self_fcodesF a)))
      · exact okF_fcodesF a WF WT hWl hWs
          (fun y hy => hoT y (by simp only [tcodesF]; exact hy))
          (fun y hy => hoF y (by simp only [fcodesF]; exact List.Mem.tail _ hy)) x h'
  | .and a b, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
          (SinWTs.prf_orR (SinWTs.prf_orL ?_)))))
        refine prf_and_intro (prf_shapeBin_real 7 (formCodeM a) (formCodeM b)) ?_
        refine prf_and_intro ?_ ?_
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 7) (formCodeM a)
              (cons (formCodeM b) nil)))
            (hoF (formCodeM a) (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodesF a)))))
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 7) (formCodeM a) (formCodeM b) nil))
            (hoF (formCodeM b) (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodesF b)))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF_fcodesF a WF WT hWl hWs
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact okF_fcodesF b WF WT hWl hWs
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .or a b, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
          (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orL ?_))))))
        refine prf_and_intro (prf_shapeBin_real 8 (formCodeM a) (formCodeM b)) ?_
        refine prf_and_intro ?_ ?_
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 8) (formCodeM a)
              (cons (formCodeM b) nil)))
            (hoF (formCodeM a) (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodesF a)))))
        · exact SinWTs.prf_congr_In_left
            (prf_eq_symm (SinWTs.prf_nthc_c2 (numeralM 8) (formCodeM a) (formCodeM b) nil))
            (hoF (formCodeM b) (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodesF b)))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF_fcodesF a WF WT hWl hWs
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact okF_fcodesF b WF WT hWl hWs
            (fun y hy => hoT y (by
              simp only [tcodesF]; exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hoF y (by
              simp only [fcodesF]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .ex a, WF, WT, hWl, hWs, hoT, hoF, x, h => by
      simp only [fcodesF] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [ENS.isFormCodeE2, ENS.lorAll]
        refine SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
          (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR ?_))))))
        refine prf_and_intro (prf_shapeUn_real 9 (formCodeM a)) ?_
        exact SinWTs.prf_congr_In_left
          (prf_eq_symm (SinWTs.prf_nthc_c1 (numeralM 9) (formCodeM a) nil))
          (hoF (formCodeM a) (by
            simp only [fcodesF]; exact List.Mem.tail _ (mem_self_fcodesF a)))
      · exact okF_fcodesF a WF WT hWl hWs
          (fun y hy => hoT y (by simp only [tcodesF]; exact hy))
          (fun y hy => hoF y (by simp only [fcodesF]; exact List.Mem.tail _ hy)) x h'

/-! ### EL ENSAMBLAJE — espejo EXACTO de `SinWTs.prf_isTC1_tcodes` -/

/-- **★ `prf_isFC1_real` ★** — la guarda de FORMULA con testigos EXPLICITOS y
    computables, descargada para TODO codigo de formula REAL. Cero axiomas. -/
theorem prf_isFC1_real (φ : Formula) :
    Prf (ENS.isFC1 (objList (fcodesF φ)) (objList (tcodesF φ)) (formCodeM φ)) := by
  let LF : List Term := fcodesF φ
  let LT : List Term := tcodesF φ
  let WF : Term := objList LF
  let WT : Term := objList LT
  have hWFl : ∀ c : Nat, liftTerm c WF = WF := fun c =>
    SinWTs.liftTerm_objList c LF (fun x hx => (closed_mem_fcodesF φ x hx).1 c)
  have hWFs : ∀ (v : Nat) (s : Term), substTerm v s WF = WF := fun v s =>
    SinWTs.substTerm_objList v s LF (fun x hx => (closed_mem_fcodesF φ x hx).2 v s)
  have hWTl : ∀ c : Nat, liftTerm c WT = WT := fun c =>
    SinWTs.liftTerm_objList c LT (fun x hx => (closed_mem_tcodesF φ x hx).1 c)
  have hWTs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT := fun v s =>
    SinWTs.substTerm_objList v s LT (fun x hx => (closed_mem_tcodesF φ x hx).2 v s)
  have horT : ∀ y : Term, List.Mem y LT → Prf (In y WT) := fun y hy =>
    SinWTs.prf_In_objList LT y hy
  have horF : ∀ y : Term, List.Mem y LF → Prf (In y WF) := fun y hy =>
    SinWTs.prf_In_objList LF y hy
  refine prf_and_intro (prf_and_intro ?_ ?_)
    (SinWTs.prf_In_objList LF (formCodeM φ) (mem_self_fcodesF φ))
  · -- `wfAll1 WT`
    have hAI : ENS.wfAll1 WT
        = Formula.forall (Formula.impl (lt (.var 0) (lenc WT))
            (ENS.isTermCodeE1 WT (nthc WT (.var 0)))) := by
      simp only [ENS.wfAll1, ENS.wfAll1Body, lt, lenc, nthc, ENS.liftF_isTermCodeE1,
        liftTerm, liftTerms, hWTl]
    rw [hAI]
    refine SinWTs.prf_bdAll_of_bound _ (lenc WT) LT.length ?_
      (SinWTs.prf_lenc_objList LT) ?_
    · simp only [ENS.substF_isTermCodeE1, nthc, substTerm, substTerms, hWTs, if_true]
    · intro k hk
      obtain ⟨x, hx⟩ : ∃ x, LT[k]? = some x := ⟨LT[k], getElem?_pos LT k hk⟩
      have hnode : Prf (ENS.isTermCodeE1 WT x) :=
        okT_tcodesF φ WT hWTl hWTs horT x (SinWTs.mem_of_getElem? LT k x hx)
      have hz : Prf (ENS.isTermCodeE1 WT (nthc WT (numeralM k))) :=
        prfH_nil_to_prf (SinWTs.PrfH_congr_isTermCodeE1
          (prf_to_prfH (prf_eq_symm (SinWTs.prf_nthc_objList LT k x hx)) [])
          (prf_to_prfH hnode [])) rfl
      simpa only [ENS.substF_isTermCodeE1, nthc, substTerm, substTerms, hWTs,
        substTerm_numeralM, if_true, reduceIte] using hz
  · -- `wfAllF WF WT`
    have hAI : ENS.wfAllF WF WT
        = Formula.forall (Formula.impl (lt (.var 0) (lenc WF))
            (ENS.isFormCodeE2 WF WT (nthc WF (.var 0)))) := by
      simp only [ENS.wfAllF, ENS.wfAllFBody, lt, lenc, nthc, ENS.liftF_isFormCodeE2,
        liftTerm, liftTerms, hWFl, hWTl]
    rw [hAI]
    refine SinWTs.prf_bdAll_of_bound _ (lenc WF) LF.length ?_
      (SinWTs.prf_lenc_objList LF) ?_
    · simp only [ENS.substF_isFormCodeE2, nthc, substTerm, substTerms, hWFs, hWTs, if_true]
    · intro k hk
      obtain ⟨x, hx⟩ : ∃ x, LF[k]? = some x := ⟨LF[k], getElem?_pos LF k hk⟩
      have hnode : Prf (ENS.isFormCodeE2 WF WT x) :=
        okF_fcodesF φ WF WT hWTl hWTs horT horF x (SinWTs.mem_of_getElem? LF k x hx)
      have hz : Prf (ENS.isFormCodeE2 WF WT (nthc WF (numeralM k))) :=
        prfH_nil_to_prf (ENS.PrfH_congr_isFormCodeE2
          (prf_to_prfH (prf_eq_symm (SinWTs.prf_nthc_objList LF k x hx)) [])
          (prf_to_prfH hnode [])) rfl
      simpa only [ENS.substF_isFormCodeE2, nthc, substTerm, substTerms, hWFs, hWTs,
        substTerm_numeralM, if_true, reduceIte] using hz

/-! ### De los testigos EXPLICITOS al `∃∃` — `prf_hasWitF_real` -/

theorem closed_objList_fcodesF (φ : Formula) (c : Nat) :
    liftTerm c (objList (fcodesF φ)) = objList (fcodesF φ) :=
  SinWTs.liftTerm_objList c (fcodesF φ) (fun x hx => (closed_mem_fcodesF φ x hx).1 c)

theorem closed_objList_tcodesF (φ : Formula) (c : Nat) :
    liftTerm c (objList (tcodesF φ)) = objList (tcodesF φ) :=
  SinWTs.liftTerm_objList c (tcodesF φ) (fun x hx => (closed_mem_tcodesF φ x hx).1 c)

/-- **★ `prf_hasWitF_real` ★** — EL CONTROL DE NO VACUIDAD de `pcc_eval_substfc`:
    todo codigo de formula REAL satisface la guarda `hasWitF`. Cero axiomas. -/
theorem prf_hasWitF_real (φ : Formula) : Prf (ENS.hasWitF (formCodeM φ)) := by
  have hcl : ∀ n : Nat, liftTerm n (formCodeM φ) = formCodeM φ :=
    fun n => liftTerm_formCodeM n φ
  have hgoal : ENS.hasWitF (formCodeM φ)
      = Formula.ex (Formula.ex (ENS.isFC1 (.var 1) (.var 0) (formCodeM φ))) := by
    simp only [ENS.hasWitF, hcl]
  rw [hgoal]
  refine prfH_nil_to_prf (PrfH_ex_intro (objList (fcodesF φ)) ?_) rfl
  have hstep : substFormula 0 (objList (fcodesF φ))
      (Formula.ex (ENS.isFC1 (.var 1) (.var 0) (formCodeM φ)))
      = Formula.ex (ENS.isFC1 (objList (fcodesF φ)) (.var 0) (formCodeM φ)) := by
    simp only [substFormula, ENS.substF_isFC1, substTerm, formCodeM,
      substTerm_formCodeM, closed_objList_fcodesF]
    rfl
  rw [hstep]
  refine PrfH_ex_intro (objList (tcodesF φ)) ?_
  have hWFs : ∀ (v : Nat) (s : Term),
      substTerm v s (objList (fcodesF φ)) = objList (fcodesF φ) := fun v s =>
    SinWTs.substTerm_objList v s (fcodesF φ)
      (fun x hx => (closed_mem_fcodesF φ x hx).2 v s)
  have hstep2 : substFormula 0 (objList (tcodesF φ))
      (ENS.isFC1 (objList (fcodesF φ)) (.var 0) (formCodeM φ))
      = ENS.isFC1 (objList (fcodesF φ)) (objList (tcodesF φ)) (formCodeM φ) := by
    simp only [ENS.substF_isFC1, substTerm, hWFs, substTerm_formCodeM, if_true]
  rw [hstep2]
  exact prf_to_prfH (prf_isFC1_real φ) []

end CIERRE
end S_Cierre

#check @CIERRE.fcodesF
#check @CIERRE.tcodesF
#check @CIERRE.prf_isFC1_real
#check @CIERRE.prf_hasWitF_real
#print axioms CIERRE.okT_tcodesF
#print axioms CIERRE.okF_fcodesF
#print axioms CIERRE.prf_isFC1_real
#print axioms CIERRE.prf_hasWitF_real

/-! ############################################################################
    ## CONTROLES FINALES · la guarda NO es vacua Y NO es un colador
    ############################################################################ -/

section S_Controles
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.Provability

/-- Los testigos son listas CONCRETAS y computables (control de no degeneracion). -/
example : (CIERRE.fcodesF (Formula.impl Formula.bottom Formula.bottom)).length = 3 := rfl
example : (CIERRE.tcodesF (Formula.impl Formula.bottom Formula.bottom)).length = 0 := rfl
example : (CIERRE.fcodesF Formula.bottom).length = 1 := rfl

/-- **LA GUARDA DISCRIMINA**: se SATISFACE en los codigos reales y se REFUTA en la
    basura. Las dos mitades a la vez, sobre el mismo predicado `ENS.isFC1`. -/
theorem CONTROL_guarda_discrimina (φ : Formula) :
    And (Prf (ENS.isFC1 (objList (CIERRE.fcodesF φ)) (objList (CIERRE.tcodesF φ))
              (formCodeM φ)))
        (∀ wF wT : Term, Prf (Formula.impl (ENS.isFC1 wF wT CRITICA.JUNK30) Formula.bottom)) :=
  ⟨CIERRE.prf_isFC1_real φ,
   fun wF wT => CRITICA.CRIT_isFC1_rejects_tag wF wT CRITICA.JUNK30 30
     (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) CRITICA.carc_JUNK30⟩

/-- El objetivo NO es una reflexividad disfrazada: `isFC1` no es `True` disfrazado. -/
example (wF wT c : Term) : True := by
  fail_if_success exact (rfl : ENS.isFC1 wF wT c = ROBINSON_PlusPlus.Minimal.Axioms.top)
  trivial

end S_Controles

#check @CONTROL_guarda_discrimina
#print axioms CONTROL_guarda_discrimina

/-! ############################################################################
    ## P4 · EL COSTE MEDIDO (recuento real, no estimacion)

    §19 de `sondeos/ParticionTresPredicados.lean` = lineas 1880-2530 = **651 lineas**
      · moldes de nodo POSICIONALES (1888-1957)        70 l.
      · TRES colectores + clausura (1958-2095)        138 l.
      · TRES inducciones mutuas (2096-2337)           242 l.
      · ensamblaje de la TERNA `tripleF` (2338-2530)  193 l.

    Transporte real a DOS listas + forma ECUACIONAL (seccion `CIERRE` de este fichero):
      · moldes de nodo ECUACIONALES (en `CRITICA`)      15 l.   ⟵ 70 l. ⇒ 15 l.
      · DOS colectores + clausura                      109 l.   ⟵ 138 l. ⇒ 109 l.
      · UNA induccion de FORMULA (`okF_fcodesF`)       171 l.
        + delegacion de la cara TERMINO (`okT_tcodesF`) 48 l.   ⟵ 242 l. ⇒ 219 l.
      · ensamblaje (`prf_isFC1_real` + `prf_hasWitF_real`) 98 l. ⟵ 193 l. ⇒ 98 l.
      TOTAL NUEVO ≈ **441 lineas**

    REUTILIZADO **TAL CUAL**, sin tocar una linea, del precedente P2
    (`SinWTs`, ~200 l.): `tcodes1`/`tcodes1s`, `mem_self_tcodes1`,
    `mem_tcodes1s_of_mem`, `closed_mem_tcodes1(s)`, `CodeClosed`, `mem_of_getElem?`,
    `liftTerm_objList`, `substTerm_objList`, `prf_lenc_objList`, `prf_nthc_objList`,
    `prf_In_objList`, `prf_bdAll_of_bound`, `prf_argsIn_of_closed`,
    `prf_lenc_termsCodeM`, `prf_nthc_termsCodeM`, **`okE1_T` / `okE1_Ts` enteras**,
    `prf_congr_In_left`, `prf_congr_argsIn`, `prf_nthc_c1`/`c2`, `prf_orL`/`prf_orR`,
    `PrfH_congr_isTermCodeE1`.

    ⇒ **651 l. de §19  ⟶  441 l. nuevas (−32%)**. El ahorro NO viene de la forma
    ecuacional (que ahorra 55 l. en los moldes y poco mas): viene de (a) que la
    TERCERA lista y el empaquetado `tripleF` DESAPARECEN, y (b) de que la cara de
    TERMINO se delega ENTERA en `okE1_T`/`okE1_Ts` de P2.
    ############################################################################ -/

/- # HW_transporte — LA NO-VACUIDAD DE LA GUARDA DE FORMULA de `pcc_eval_substfc`.

   §HW (al final del fichero) es lo NUEVO. Todo lo anterior es COPIA LITERAL de
   `sondeos/EvalSubstfcPrf.lean` lineas 11-8374 (autocontencion: no se puede importar
   `sondeos/`), de modo que los enunciados de §HW hablan de las constantes REALES
   `ENS.isFC1`, `ENS.hasWitF`, `ENS.pcc_eval_substfc` — no de copias homonimas.

   RESULTADO:
     HW.prf_isFC1_real          — testigos EXPLICITOS y COMPUTABLES (`fcodesF`,`tcodesF`)
     HW.prf_hasWitF_real        — la forma SIN testigos, la que consume el reflector
     HW.pcc_eval_substfc_REAL   — `pcc_eval_substfc` YA SIN GUARDA sobre codigos reales
     HW.pcc_eval_substfc_wit_REAL

   ⚠️ CERO `axiom` de Lean, cero `sorry`.

       lake env lean Probe/HW_transporte.lean
-/
import ROBINSON_PlusPlus.Meta

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

section S_Descenso
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
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace DescMutua

/-! ## §A · COPIA LITERAL de sondeos/ReflectorDesdeConsumidor.lean §1-§7 -/

/-! ## §1 · Los constructores de codigo (DEFINICIONES; ninguna ecuacion suya se postula) -/

def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

/-- `varc x = cons 0 (cons x nil)` ⇒ su imagen punteada es el `unT 0` del KIT. CERO simbolos
    nuevos. -/
def varcT (X : Term) : Term := unT 0 X
/-- `funcc a b = cons 1 (cons a (cons b nil))` ⇒ su imagen punteada es el `binT 1` del KIT. -/
def funccT (X Y : Term) : Term := binT 1 X Y

theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftscT_termCode (c t : Term) :
    liftscT (termCode c) (termCode t) = termCode (liftsc c t) := rfl
theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl

/-- `eqc` y `eqCodeFn` son EL MISMO constructor. -/
theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-! ## §2 · EL OBJETIVO EXACTO — copiado del enunciado de `paso2_caso_forall` -/

/-- La hipotesis sin descargar de `sondeos/Paso2CasoForall.lean:507`, literal. -/
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))

/-- CONTROL NEGATIVO: no es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

/-! ## §3 · Fontaneria: congruencias e invariancias de los constructores nuevos -/

theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy

theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y
theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))
theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados (copia de Paso2 §2) -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) := by
  unfold binT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a)) :=
  prf_substtc_unT_at 0 v W a
theorem prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binT_at 1 v W a b

/-! ## §4 · LAS ECUACIONES DE `liftc`/`liftsc`, DOTADAS

    Las cinco ecuaciones recursivas de `liftc`/`liftsc` (`ax_liftc_var_lt`, `ax_liftc_var_ge`,
    `ax_liftc_func`, `ax_liftsc_nil`, `ax_liftsc_cons`) son `forall_2`/`forall_3`/`forall_`.
    Su imagen DOTADA sale por `pcc_axiom_inst*` + computo del `substfc` sobre el codigo
    explicito (patron `pcc_nthc_zero_code`, `pcc_substfc_forall_dot`).

    ⚠️ MEDIDA CENTRAL DE ESTE FICHERO: **todas son LIBRES DE CUANTIFICADOR**. Ni un solo
    `bdAllCode` aparece aqui. -/

def LIFTC_FUNC_BODY : Formula :=
  liftc (.var 2) (funcc (.var 1) (.var 0)) =eq funcc (.var 1) (liftsc (.var 2) (.var 0))

theorem LIFTC_FUNC_BODY_ok : ax_liftc_func = forall_3 LIFTC_FUNC_BODY := rfl

/-- **`ax_liftc_func` DOTADA**: `⊢ Prov(⌜ liftc(ċ, funcc(ȧ,ḃ)) = funcc(ȧ, liftsc(ċ,ḃ)) ⌝)`,
    con `c`, `a`, `b` **ABSTRACTOS**. -/
theorem pcc_liftc_func_code (c a b : Term) :
    Prf (provFromCode (eqCodeFn
      (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
      (funccT (tcFn a) (liftscT (tcFn c) (tcFn b))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTC_FUNC_BODY)
      =eq eqCodeFn (liftcT W2 (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTC_FUNC_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftcT W2 (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftcT hA2 (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn a)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftcT (tcFn c) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (varc (numeral 0))))
                   (funccT (tcFn a) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) ?_
      refine prf_congr_liftcT hc1 ?_
      exact prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) (prf_congr_funccT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) ?_
      refine prf_congr_funccT hv1 ?_
      exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftcT (tcFn c) (funccT (tcFn a) (varc (numeral 0))))
        (funccT (tcFn a) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
                   (funccT (tcFn a) (liftscT (tcFn c) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
      refine prf_congr_liftcT (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _)
        (prf_congr_funccT (prf_substtc_tcFn W0 a) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _) ?_
      refine prf_congr_funccT (prf_substtc_tcFn W0 a) ?_
      exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _)
        (prf_congr_liftscT (prf_substtc_tcFn W0 c) (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode LIFTC_FUNC_BODY)))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
                   (funccT (tcFn a) (liftscT (tcFn c) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTC_FUNC_BODY (show ax_liftc_func ∈ axioms by simp [axioms])
      (tcFn c) (tcFn a) (tcFn b))

/-- `substfc` atraviesa un atomo binario de codigo. -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

def LIFTC_VARGE_BODY : Formula :=
  Formula.impl (lt (.var 1) (succ (.var 0)))
    (liftc (.var 1) (varc (.var 0)) =eq varc (succ (.var 0)))

theorem LIFTC_VARGE_BODY_ok : ax_liftc_var_ge = forall_2 LIFTC_VARGE_BODY := rfl

/-- **`ax_liftc_var_ge` DOTADA** (con la guarda interna `ċ < σṅ` SIN descargar). -/
theorem pcc_liftc_var_ge_code (c n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
      (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n)))))) := by
  let W1 : Term := liftc zero (tcFn c)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ zero) W1 (formCode LIFTC_VARGE_BODY)
      =eq implc (ltCodeFn W1 (succcT (varc (numeral 0))))
            (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
              (varcT (succcT (varc (numeral 0)))))) :=
    prf_substfc_arith_open 1 W1 LIFTC_VARGE_BODY
  have hA1 : Prf (W1 =eq tcFn c) := prf_liftc_tcFn c
  have hnorm : Prf (implc (ltCodeFn W1 (succcT (varc (numeral 0))))
        (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
          (varcT (succcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn c) (succcT (varc (numeral 0))))
            (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
              (varcT (succcT (varc (numeral 0)))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn hA1 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_liftcT hA1 (prf_refl _)) (prf_refl _))
  have hout : Prf (substfc zero W0 (implc (ltCodeFn (tcFn c) (succcT (varc (numeral 0))))
        (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
          (varcT (succcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n))))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · refine prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _) ?_
      refine prf_congr_atom2CodeFn (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_funcc1 zero W0 _ _)
        (prf_congr_succcT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
        exact prf_congr_liftcT (prf_substtc_tcFn W0 c)
          (prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0)))
      · refine prf_eq_trans (prf_substtc_varcT_at 0 W0 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_funcc1 zero W0 _ _)
          (prf_congr_succcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode LIFTC_VARGE_BODY))
      =eq implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n))))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 LIFTC_VARGE_BODY (show ax_liftc_var_ge ∈ axioms by simp [axioms])
      (tcFn c) (tcFn n))

def LIFTSC_NIL_BODY : Formula := liftsc (.var 0) nil =eq nil

theorem LIFTSC_NIL_BODY_ok : ax_liftsc_nil = Formula.forall LIFTSC_NIL_BODY := rfl

/-- **`ax_liftsc_nil` DOTADA**. -/
theorem pcc_liftsc_nil_code (c : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (tcFn c) (termCode nil)) (termCode nil))) := by
  have hin : Prf (substfc zero (tcFn c) (formCode LIFTSC_NIL_BODY)
      =eq eqCodeFn (liftscT (tcFn c) (termCode nil)) (termCode nil)) :=
    prf_substfc_arith_open 0 (tcFn c) LIFTSC_NIL_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst LIFTSC_NIL_BODY (show ax_liftsc_nil ∈ axioms by simp [axioms]) (tcFn c))

def LIFTSC_CONS_BODY : Formula :=
  liftsc (.var 2) (cons (.var 1) (.var 0))
    =eq cons (liftc (.var 2) (.var 1)) (liftsc (.var 2) (.var 0))

theorem LIFTSC_CONS_BODY_ok : ax_liftsc_cons = forall_3 LIFTSC_CONS_BODY := rfl

/-- **`ax_liftsc_cons` DOTADA**, con `c`, `h`, `t` **ABSTRACTOS**. -/
theorem pcc_liftsc_cons_code (c h t : Term) :
    Prf (provFromCode (eqCodeFn
      (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn h)
  let W0 : Term := tcFn t
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTSC_CONS_BODY)
      =eq eqCodeFn (liftscT W2 (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT W2 (varc (numeral 1))) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTSC_CONS_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftscT W2 (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT W2 (varc (numeral 1))) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT (tcFn c) (varc (numeral 1)))
              (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftscT hA2 (prf_refl _))
      (prf_congr_consT (prf_congr_liftcT hA2 (prf_refl _))
        (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn h) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn h)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftscT (tcFn c) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (liftcT (tcFn c) (varc (numeral 1))) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (varc (numeral 0))))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) ?_
      refine prf_congr_liftscT hc1 ?_
      exact prf_eq_trans (prf_substtc_consT (succ zero) W1 _ _) (prf_congr_consT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_consT (succ zero) W1 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) (prf_congr_liftcT hc1 hv1)
      · exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftscT (tcFn c) (consT (tcFn h) (varc (numeral 0))))
        (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftscT zero W0 _ _) ?_
      refine prf_congr_liftscT (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_consT zero W0 _ _)
        (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_consT zero W0 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_tcFn W0 c) (prf_substtc_tcFn W0 h))
      · exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _)
          (prf_congr_liftscT (prf_substtc_tcFn W0 c) (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode LIFTSC_CONS_BODY)))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTSC_CONS_BODY (show ax_liftsc_cons ∈ axioms by simp [axioms])
      (tcFn c) (tcFn h) (tcFn t))

/-! ## §5 · LA GUARDA INTERNA SE DESCARGA — y las cuatro ecuaciones quedan a NIVEL `zero`

    `pcc_lt_tracked` (`Meta/Delta0ReflectPrf.lean:233`, completitud‑Δ₀ provable del atomo `<`,
    con argumentos **ABIERTOS**) refleja `0 < σn` sin pedir clausura. La guarda de
    `ax_liftc_var_ge` **no es un obstaculo**. -/

theorem pcc_zero_lt_succ_code (n : Term) :
    Prf (provFromCode (ltCodeFn (tcFn zero) (succcT (tcFn n)))) := by
  have h : Prf (provFromCode (ltCodeFn (tcFn zero) (tcFn (succ n)))) :=
    prf_mp (pcc_lt_tracked zero (succ n)) (prf_zero_lt_succ n)
  exact prf_mp (prf_provCode_congr (prf_congr_atom2CodeFn (prf_refl _) (prf_tc_succ' n))) h

theorem pcc_liftc0_var_code (n : Term) :
    Prf (provFromCode (eqCodeFn (liftcT (termCode zero) (varcT (tcFn n)))
      (varcT (succcT (tcFn n))))) := by
  have h := pcc_mp_code_apply (pcc_liftc_var_ge_code zero n) (pcc_zero_lt_succ_code n)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT prf_tc_zero (prf_refl _)) (prf_refl _))) h

theorem pcc_liftc0_func_code (a b : Term) :
    Prf (provFromCode (eqCodeFn (liftcT (termCode zero) (funccT (tcFn a) (tcFn b)))
      (funccT (tcFn a) (liftscT (termCode zero) (tcFn b))))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftcT prf_tc_zero (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_liftscT prf_tc_zero (prf_refl _)))))
    (pcc_liftc_func_code zero a b)

theorem pcc_liftsc0_nil_code :
    Prf (provFromCode (eqCodeFn (liftscT (termCode zero) (tcFn nil)) (tcFn nil))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT prf_tc_zero (prf_eq_symm prf_tc_zero)) (prf_eq_symm prf_tc_zero)))
    (pcc_liftsc_nil_code zero)

theorem pcc_liftsc0_cons_code (h t : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT prf_tc_zero (prf_refl _))
      (prf_congr_consT (prf_congr_liftcT prf_tc_zero (prf_refl _))
        (prf_congr_liftscT prf_tc_zero (prf_refl _)))))
    (pcc_liftsc_cons_code zero h t)

/-! ## §6 · Congruencias INTERNAS (dentro de `Prov`) para los constructores nuevos.
     Patron `pcc_congr_binT_2_code` (`Meta/CodeCtorKit.lean:248`). -/

theorem pcc_congr_liftcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftcT A X) (liftcT A Y))) := by
  let Ac : Term := eqc (liftcT A X) (liftcT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftcT A X) (liftcT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftcT A X) (liftcT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftcT zero w A X) (prf_congr_liftcT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftcT zero w A (varc (numeral 0)))
        (prf_congr_liftcT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftcT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_liftscT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftscT A X) (liftscT A Y))) := by
  let Ac : Term := eqc (liftscT A X) (liftscT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftscT A X) (liftscT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftscT A X) (liftscT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftscT zero w A X) (prf_congr_liftscT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftscT zero w A (varc (numeral 0)))
        (prf_congr_liftscT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftscT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la COLA de `consT` (para el paso `cons` de la lista). -/
theorem pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) := by
  let Ac : Term := eqc (consT A X) (consT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT A X) (consT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT A X) (consT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w A X) (prf_congr_consT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
        (prf_congr_consT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la CABEZA de `consT`. -/
theorem pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) := by
  let Ac : Term := eqc (consT X B) (consT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT X B) (consT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT X B) (consT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w X B) (prf_congr_consT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
        (prf_congr_consT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ## §7 · LAS CUATRO CLAUSULAS DE LA RECURSION — el esqueleto entero de `hLift`

    `targetLift s` es LITERALMENTE la hipotesis sin descargar de `paso2_caso_forall`.
    `targetLiftsc b` es su companera sobre listas de argumentos.

    ⚠️ Observese el ENUNCIADO de las cuatro: la guarda entra **SOLO como una ecuacion PLANA**
    (`s ≐ varc a`, `s ≐ funcc p b`). Ni `wfAll1`, ni `argsIn`, ni `In`, ni ningun `bdAllCode`
    aparecen en ninguna de ellas. -/

def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

theorem iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  fun W => prf_substtc_termCode_zero 0 W

/-- **(1) BASE `varc` — CERRADA, sin hipotesis mas alla de la forma ecuacional.** -/
theorem refl_caso_varc (s a : Term) (hs : Prf (s =eq varc a)) : Prf (targetLift s) := by
  unfold targetLift
  have hplain : Prf (liftc zero s =eq varc (succ a)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_mp (prf_liftc_var_ge zero a) (prf_zero_lt_succ a))
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (varc a)))
      =eq liftcT (termCode zero) (tcFn (varc a))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_tcFn (varc a))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (varcT (tcFn a)))
      =eq liftcT (termCode zero) (varcT (tcFn a))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_unT (substtc_inv_tcFn a))
  have s1 : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (varc a)))
      (liftcT (termCode zero) (varcT (tcFn a))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (varc a)) (varcT (tcFn a))
      iz_inv (substtc_inv_tcFn (varc a))) (pcc_dot_un_symm 0 a)
  have s2 : Prf (provFromCode (eqc (liftcT (termCode zero) (varcT (tcFn a)))
      (varcT (succcT (tcFn a))))) := pcc_liftc0_var_code a
  have s3 : Prf (provFromCode (eqc (varcT (succcT (tcFn a))) (tcFn (varc (succ a))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_varcT (prf_tc_succ' a)) (prf_refl _)))
      (pcc_dot_un 0 (succ a))
  have hchain : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (varc a)))
      (tcFn (varc (succ a))))) :=
    pcc_eq_trans_code _ _ _ hX s1 (pcc_eq_trans_code _ _ _ hY s2 s3)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(2) PASO `funcc`** — el unico salto: pide la companera sobre la LISTA de argumentos. -/
theorem refl_caso_funcc (s p b : Term) (hs : Prf (s =eq funcc p b))
    (hb : Prf (targetLiftsc b)) : Prf (targetLift s) := by
  unfold targetLift
  unfold targetLiftsc at hb
  have hplain : Prf (liftc zero s =eq funcc p (liftsc zero b)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_liftc_func zero p b)
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (funcc p b)))
      =eq liftcT (termCode zero) (tcFn (funcc p b))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (termCode zero) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT iz_inv
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (termCode zero) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p)
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))
  have s1 : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (funcc p b)))
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) iz_inv (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b))))) := pcc_liftc0_func_code p b
  have s3 : Prf (provFromCode (eqc (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc zero b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (liftscT (termCode zero) (tcFn b))
      (tcFn (liftsc zero b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (liftsc zero b)))
      (tcFn (funcc p (liftsc zero b))))) := pcc_dot_bin 1 p (liftsc zero b)
  have hchain : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (funcc p b)))
      (tcFn (funcc p (liftsc zero b))))) :=
    pcc_eq_trans_code _ _ _ hX s1
      (pcc_eq_trans_code _ _ _ hY s2 (pcc_eq_trans_code _ _ _ hZ s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil : Prf (targetLiftsc nil) := by
  unfold targetLiftsc
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_nil zero))))) pcc_liftsc0_nil_code

/-- **(4) PASO de la LISTA (`cons`)** — pide la companera sobre la cabeza y sobre la cola. -/
theorem refl_lista_cons (h t : Term) (hh : Prf (targetLift h)) (ht : Prf (targetLiftsc t)) :
    Prf (targetLiftsc (cons h t)) := by
  unfold targetLift at hh
  unfold targetLiftsc at ht ⊢
  have hplain : Prf (liftsc zero (cons h t) =eq cons (liftc zero h) (liftsc zero t)) :=
    prf_liftsc_cons zero h t
  have hX : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (tcFn (cons h t)))
      =eq liftscT (termCode zero) (tcFn (cons h t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      =eq liftscT (termCode zero) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have s1 : Prf (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (liftscT (termCode zero) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_liftscT_arg2_code (termCode zero) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) iz_inv (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
    pcc_liftsc0_cons_code h t
  have s3 : Prf (provFromCode (eqc
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (liftscT (termCode zero) (tcFn t))
      (liftcT (termCode zero) (tcFn h)) (tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
      (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (liftc zero h))
      (liftscT (termCode zero) (tcFn t)) (tcFn (liftsc zero t))
      (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    pcc_dot_cons (liftc zero h) (liftsc zero t)
  have hchain : Prf (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    pcc_eq_trans_code _ _ _ hX s1
      (pcc_eq_trans_code _ _ _ hY s2
        (pcc_eq_trans_code _ _ _ hZ s3
          (pcc_eq_trans_code _ _ _ hU s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-! ## §B · COPIA LITERAL de sondeos/ReflectorDesdeConsumidor.lean §9-§10 -/

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

theorem shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

/-! ### La guarda llega como HIPOTESIS OBJETO, no como `Prf`: el transporte de Leibniz -/

mutual
theorem substTerm_termCode (v : Nat) (u : Term) :
    ∀ t : Term, substTerm v u (termCode t) = termCode t
  | .var _ => by simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
  | .func s ts => by
      simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_strCode, substTerm_termsCode v u ts]
theorem substTerm_termsCode (v : Nat) (u : Term) :
    ∀ ts : List Term, substTerm v u (termsCode ts) = termsCode ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCode, cons, substTerm, substTerms, substTerm_termCode v u t,
        substTerm_termsCode v u ts]
end

theorem substF_targetLift_hole (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode, if_true]

theorem PrfH_congr_targetLift {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLift s)) : PrfH Γ (targetLift s') :=
  (substF_targetLift_hole s') ▸
    PrfH_leibniz_subst
      (A := provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0))))) h ((substF_targetLift_hole s) ▸ ha)

/-- **EL DISYUNTO `varc`, EN LA MONEDA QUE PIDE LA INDUCCION OBJETO** (implicacion interna,
    guarda como HIPOTESIS): `⊢ shapeUn X 0 ⇒ targetLift X`. CERRADO, sin hipotesis. -/
theorem refl_shapeUn_imp (X : Term) : Prf (Formula.impl (shapeUn X 0) (targetLift X)) := by
  refine prf_deduction ?_
  let a : Term := nthc X (numeralM 1)
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc a)) := prfH_hyp_self _
  exact PrfH_congr_targetLift (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc (varc a) a (prf_refl _)) _)

/-! ### El disyunto `funcc`: la HI llega tambien como hipotesis OBJETO -/

/-- Transitividad interna de `=` **en contexto `PrfH`** (para mezclar hechos libres con la HI). -/
theorem PrfH_eq_trans_code {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z))) :
    PrfH Γ (provFromCode (eqc X Z)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hY : PrfH Γ (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp Y))) _) h1
  have hZ : PrfH Γ (provFromCode (substfc zero Z Ac)) := PrfH_leibniz_apply Ac Y Z h2 hY
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Z)) _) hZ

/-- **(2') PASO `funcc`, en forma IMPLICACION**: la companera de la lista entra como
    hipotesis OBJETO. Es la moneda que consume una induccion objeto. -/
theorem refl_caso_funcc_imp (p b : Term) :
    Prf (Formula.impl (targetLiftsc b) (targetLift (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetLiftsc b] (targetLiftsc b) := prfH_hyp_self _
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (funcc p b)))
      =eq liftcT (termCode zero) (tcFn (funcc p b))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (termCode zero) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (termCode zero) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))
  have s1 : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (tcFn (funcc p b)))
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) iz_inv (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b))))) :=
    prf_to_prfH (pcc_liftc0_func_code p b) _
  have s3 : PrfH [targetLiftsc b] (provFromCode (eqc
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc zero b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))) _) hb
  have s4 : PrfH [targetLiftsc b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (liftsc zero b))) (tcFn (funcc p (liftsc zero b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (liftsc zero b)) _
  have hchain : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (tcFn (funcc p b))) (tcFn (funcc p (liftsc zero b))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2 (PrfH_eq_trans_code _ _ _ hZ s3 s4))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftc_func zero p b))))) _) hchain

/-- **EL DISYUNTO `funcc`, EN LA MONEDA DE LA INDUCCION OBJETO**:
    `⊢ (shapeBin X 1 ∧ targetLiftsc (nthc X 2̄)) ⇒ targetLift X`. -/
theorem refl_shapeBin_imp (X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetLiftsc (nthc X (numeralM 2))))
      (targetLift X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetLiftsc b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hb : PrfH [H] (targetLiftsc b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetLift (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp p b) _) hb
  exact PrfH_congr_targetLift (PrfH_eq_symm hs) hfb

/-- **(4') PASO de la LISTA, en forma IMPLICACION.** -/
theorem refl_lista_cons_imp (h t : Term) :
    Prf (Formula.impl (land (targetLift h) (targetLiftsc t)) (targetLiftsc (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetLift h) (targetLiftsc t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetLift h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetLiftsc t) := PrfH_and_elim_right hh0
  have hX : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (tcFn (cons h t)))
      =eq liftscT (termCode zero) (tcFn (cons h t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      =eq liftscT (termCode zero) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have s1 : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (liftscT (termCode zero) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftscT_arg2_code (termCode zero) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) iz_inv (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
    prf_to_prfH (pcc_liftsc0_cons_code h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code (liftscT (termCode zero) (tcFn t))
      (liftcT (termCode zero) (tcFn h)) (tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
      (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (liftc zero h))
      (liftscT (termCode zero) (tcFn t)) (tcFn (liftsc zero t))
      (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    prf_to_prfH (pcc_dot_cons (liftc zero h) (liftsc zero t)) _
  have hchain : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 (PrfH_eq_trans_code _ _ _ hU s4 s5)))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_cons zero h t))))) _) hchain

/-! ## §10 · EL PREDICADO SIN‑`wTs` ENTERO, CONTRA EL OBJETIVO — la MEDIDA

    Copia LITERAL de `Probe/CritLift_sinwts.lean:109‑135` del predicado de un nodo. -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-! ## §C · COPIA de sondeos/ClausuraLiftSinWTs.lean — el predicado `isTC1` y su fontaneria -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

/-- El testigo es AHORA UNA SOLA LISTA: no hay `p = cons wT wTs`, no hay `carc`/`cdrc`. -/
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

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

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

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

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

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

/-! ############################################################################
    ## §D · LO NUEVO: EL DESCENSO
    ############################################################################ -/

/-! ### D.0 · `liftFormula`/`substFormula` atraviesan los dos objetivos y caen sobre el
       argumento. (El cuerpo Σ₁ de `provFromCode` es cerrado; el unico hueco es el codigo.) -/

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

/-- Leibniz sobre el argumento de `targetLiftsc` (la que falta en el reflector). -/
theorem PrfH_congr_targetLiftsc {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLiftsc s)) : PrfH Γ (targetLiftsc s') := by
  have hS : ∀ u : Term, substFormula 0 u (targetLiftsc (.var 0)) = targetLiftsc u := by
    intro u
    rw [substF_targetLiftsc]
    simp only [substTerm, if_true]
  exact (hS s') ▸ PrfH_leibniz_subst (A := targetLiftsc (.var 0)) h ((hS s) ▸ ha)

/-! ### D.1 · LA ESTRUCTURA: `⊢ Y ≐ nil ∨ Y ≐ cons (carc Y) (cdrc Y)` para `Y` ARBITRARIO.

    Es lo que `argsIn` (POSICIONAL) no da, y lo unico que la induccion fuerte no puede
    fabricar (ordena valores, no descompone). Sale de `Prf.listInd` con un paso que **no usa
    la hipotesis de induccion**: `prf_consOk_cons` a secas. -/

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
    exact prf_mp (Prf.incl (Prf₀.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

/-- **`⊢ Y ≐ nil ∨ consOk Y`** con `Y` **abstracto** (puede ser `#0`). -/
theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-! ### D.2 · `argsIn` se parte en CABEZA y COLA (posicion 0 / posiciones desplazadas) -/

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

/-! ### D.3 · Del testigo al NODO: `In c w ⇒ wfAll1 w ⇒ isTermCodeE1 w c`, con `c` y `w`
       **ABSTRACTOS** (ni uno ni otro tienen que ser cerrados). -/

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

/-! ### D.4 · EL PREDICADO DE LA INDUCCION FUERTE — las DOS mitades a la vez.

    `w` va **cuantificado dentro** (lo exige `hΦ : liftFormula 1 Φ = Φ`: con `w` libre haria
    falta `liftTerm 1 w = w`, que no se descarga). `#1` es el codigo sobre el que se induce. -/

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

/-- Instanciacion de las dos mitades a un testigo `w` concreto. -/
theorem PHI_use {Γ : List Formula} (t w : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (land (Formula.impl (isTC1 w t) (targetLift t))
                 (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetLiftsc t))) := by
  rw [PHI_at] at h
  have hs := PrfH_spec h w
  simpa only [land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetLift, substF_targetLiftsc, substTerm, FOL.substTerm_liftTerm, if_true] using hs

/-- La forma de la HI de curso de valores dentro del paso, tras el `gen` de `w`. -/
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

/-! ### D.5 · EL PASO DE LA INDUCCION FUERTE -/

theorem PHI_step : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    -- `X = #1`, `w = #0`; hipotesis: `isTC1 w X`
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
      -- `b < X`: `b < cons b nil < cons p (cons b nil) < cons 1̄ (…) = X` (Cantor)
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
      -- (a) la CABEZA esta en el testigo y es MENOR ⟹ `targetLift (carc X)` por la HI
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
      -- (b) la COLA hereda `argsIn` y es MENOR ⟹ `targetLiftsc (cdrc X)` por la HI
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 0) (carc (.var 1)) (cdrc (.var 1))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 1)) (cdrc (.var 1))) _)
      have huse_tl := PHI_use (cdrc (.var 1)) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (cdrc (.var 1))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp (carc (.var 1)) (cdrc (.var 1))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetLiftsc (PrfH_eq_symm hcons) hres

/-! ### D.6 · EL DESCENSO -/

theorem PHI_all (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI PHI_step t

/-- **EL DESCENSO, en forma de IMPLICACION OBJETO**, con `w` y `s` **ABSTRACTOS**. -/
theorem DESCENSO_imp (w s : Term) : Prf (Formula.impl (isTC1 w s) (targetLift s)) :=
  prfH_nil_to_prf (PrfH_and_elim_left (PHI_use s w (prf_to_prfH (PHI_all s) []))) rfl

/-- Su gemela sobre LISTAS de argumentos. -/
theorem DESCENSO_lista_imp (w s : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w s)) (targetLiftsc s)) :=
  prfH_nil_to_prf (PrfH_and_elim_right (PHI_use s w (prf_to_prfH (PHI_all s) []))) rfl

/-- **DESCENSO** (la forma pedida). -/
theorem DESCENSO (w s : Term) (h : Prf (isTC1 w s)) : Prf (targetLift s) :=
  prf_mp (DESCENSO_imp w s) h

theorem DESCENSO_lista (w s : Term) (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w s)) :
    Prf (targetLiftsc s) :=
  prf_mp (DESCENSO_lista_imp w s) (prf_and_intro hwf hargs)

/-- **`pcc_eval_liftc`** — el `hLift` de `sondeos/Paso2CasoForall.lean:505`, LITERAL. -/
theorem pcc_eval_liftc (w s : Term) (h : Prf (isTC1 w s)) :
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  DESCENSO w s h

/-! ### D.7 · La forma que de verdad llega rio abajo: el testigo viene de un `∃`.
       (Copia de `SinWTs.hasWit`: «`c` TIENE testigo», con el testigo CUANTIFICADO.) -/

def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

theorem DESCENSO_hasWit (s : Term) : Prf (Formula.impl (hasWit s) (targetLift s)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetLift]
  exact PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_imp (.var 0) (liftTerm 0 s)) _) (prfH_hyp_self _)

/-! ############################################################################
    ## §E · CONTROLES ADVERSARIALES (copias LITERALES de sondeos/ClausuraLiftSinWTs.lean)

    E.1 la DISCRIMINACION del antecedente (no vale cualquier codigo)
    E.2 la SATISFACIBILIDAD del antecedente por codigos REALES (no es vacuo)
    E.3 el JUNK, refutado con testigo ARBITRARIO
    ############################################################################ -/

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prf₀.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prf₀.j2 A B)

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

/-- tag 1 (`funcc`), SIN `wTs`. -/
def funcOkT1 (wT X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (argsIn wT (nthc X (numeralM 2)))

/-- `X` es codigo de TERMINO — **un solo testigo**. -/
def isTermCodeB1 (wT X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT1 wT X))


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

/-! ### §F · LO QUE MIDEN LOS CONTROLES, APLICADO AL **DESCENSO** -/

/-- **NO ES VACUO (1)**: para **todo** termino REAL `t` — abierto incluido — el antecedente
    `isTC1 W ⌜t⌝` es DEMOSTRABLE con testigo explicito y computable, luego el DESCENSO
    **dispara** y entrega el `hLift` de `paso2_caso_forall`. -/
theorem CRIT_targetLift_real (t : Term) : Prf (targetLift (termCodeM t)) :=
  DESCENSO (objList (tcodes1 t)) (termCodeM t) (prf_isTC1_tcodes t)

-- ⚠️ Los dos ejemplos usan SOLO simbolos de `Minimal/Axioms.lean` (`σ`, `+`): CERO simbolos
--    de funcion objeto nuevos. Ambos son terminos ABIERTOS (`#0`, `#1`).
def tEjA : Term := succ (Term.var 0)
def tEjB : Term := add (succ (Term.var 0)) (Term.var 1)

theorem CRIT_real_A : Prf (targetLift (termCodeM tEjA)) := CRIT_targetLift_real tEjA
theorem CRIT_real_B : Prf (targetLift (termCodeM tEjB)) := CRIT_targetLift_real tEjB

/-- Y la mitad de LISTAS tambien dispara: sobre la lista de argumentos REAL de un `funcc`
    (el testigo es el mismo del termino entero, `tcodes1`). -/
theorem CRIT_targetLiftsc_real (f : String) (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) := by
  have h := prf_isTC1_tcodes (Term.func f ts)
  refine DESCENSO_lista (objList (tcodes1 (Term.func f ts))) _ (prf_and_elim_left h) ?_
  refine prf_argsIn_of_closed _ (termsCodeM ts) ts.length
    (liftTerm_objList 0 _ (fun x hx => (closed_mem_tcodes1 _ x hx).1 0))
    (liftTerm_termsCodeM 0 ts)
    (fun v s => substTerm_objList v s _ (fun x hx => (closed_mem_tcodes1 _ x hx).2 v s))
    (fun v s => substTerm_termsCodeM v s ts)
    (prf_lenc_termsCodeM ts) ?_
  intro k hk
  obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
  refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
  refine prf_In_objList _ (termCodeM u) ?_
  simp only [tcodes1]
  exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))

theorem CRIT_real_lista :
    Prf (targetLiftsc (termsCodeM [succ (Term.var 0), Term.var 1])) :=
  CRIT_targetLiftsc_real add_sym _

/-- **NO ES VACUO (2), lado contrario**: el antecedente **NO** lo cumple cualquier codigo.
    Con el codigo de una FORMULA (`implc …`) y testigo **ARBITRARIO** (`#0` incluido),
    `isTC1` es REFUTABLE ⟹ el DESCENSO no es un `⊥ ⇒ …` disfrazado por el otro lado. -/
theorem CRIT_antecedente_discrimina
    (hjunk : Prf (isTC1 (.var 0) (implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))))) :
    Prf Formula.bottom :=
  crit_junk_var0_witness1 hjunk

/-! ### CONTROLES NEGATIVOS: los enunciados no son reflexividades disfrazadas -/

example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftscT (termCode zero) (tcFn s) = tcFn (liftsc zero s))
  trivial

/-- El predicado de la induccion NO es trivial: `PHI` no es `⊤` ni se reduce a la conclusion. -/
example : True := by
  fail_if_success exact (rfl : PHIbody = targetLift (.var 1))
  trivial

/-- La forma con testigo EXISTENCIAL tampoco es vacua: todo termino real tiene testigo. -/
theorem CRIT_hasWit_real (t : Term) : Prf (hasWit (termCodeM t)) := by
  refine prf_ex_intro (objList (tcodes1 t)) ?_
  have h : substFormula 0 (objList (tcodes1 t)) (isTC1 (.var 0) (liftTerm 0 (termCodeM t)))
      = isTC1 (objList (tcodes1 t)) (termCodeM t) := by
    simp only [substF_isTC1, substTerm, if_true, FOL.substTerm_liftTerm]
  rw [h]
  exact prf_isTC1_tcodes t

theorem CRIT_hasWit_descenso (t : Term) : Prf (targetLift (termCodeM t)) :=
  prf_mp (DESCENSO_hasWit (termCodeM t)) (CRIT_hasWit_real t)

end DescMutua
end S_Descenso

section S_Paso2
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
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace Paso2

/-! ## §0 · Piezas GENÉRICAS que faltaban en producción -/

/-- `substtc` sobre un `funcc` de **tres** argumentos (hueco de `prf_substtc_funcc1/2`). -/
theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_liftc_funcc2 (c sc x y : Term) :
    Prf (liftc c (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) nil))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y nil)
            (prf_congr_cons_tail (prf_liftsc_nil c))))))

theorem prf_liftc_funcc3 (c sc x y z : Term) :
    Prf (liftc c (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) (cons (liftc c z) nil)))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_liftsc_cons c z nil)
                (prf_congr_cons_tail (prf_liftsc_nil c))))))))

/-- INJERTO de `Ctor_directo.lean:94` — deduplica las tres congruencias ternarias. -/
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-! ## §1 · Los SEIS constructores de código (DEFINICIONES, sin ecuaciones postuladas) -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))
def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

/-! ### Puentes `_termCode`, por `rfl` -/

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl
theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s ts : Term) :
    substtscT (termCode v) (termCode s) (termCode ts) = termCode (substtsc v s ts) := rfl
theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl
theorem liftscT_termCode (c ts : Term) :
    liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) := rfl

/-! ### Congruencias META (vía el injerto `prf_congr_funcc3`) -/

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf
theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))
theorem prf_congr_liftfcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftfcT c t =eq liftfcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))
theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

/-! ### `substtc` / `liftc` atraviesan (nivel ARBITRARIO) -/

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z
theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z
theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z
theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y
theorem prf_substtc_liftfcT (v W x y : Term) :
    Prf (substtc v W (liftfcT x y) =eq liftfcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftfc") x y
theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

theorem prf_liftc_substfcT (c x y z : Term) :
    Prf (liftc c (substfcT x y z) =eq substfcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substfc") x y z
theorem prf_liftc_substtcT (c x y z : Term) :
    Prf (liftc c (substtcT x y z) =eq substtcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtc") x y z
theorem prf_liftc_substtscT (c x y z : Term) :
    Prf (liftc c (substtscT x y z) =eq substtscT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtsc") x y z
theorem prf_liftc_liftcT (c x y : Term) :
    Prf (liftc c (liftcT x y) =eq liftcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftc") x y
theorem prf_liftc_liftfcT (c x y : Term) :
    Prf (liftc c (liftfcT x y) =eq liftfcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftfc") x y
theorem prf_liftc_liftscT (c x y : Term) :
    Prf (liftc c (liftscT x y) =eq liftscT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftsc") x y

/-! ### Invariancias `substtc` a nivel `zero` (la forma que consumen los Leibniz internos) -/

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z) (prf_congr_substtcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z) (prf_congr_substtscT (hX W) (hY W) (hZ W))
theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))
theorem substtc_inv_liftfcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftfcT X Y) =eq liftfcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftfcT zero W X Y) (prf_congr_liftfcT (hX W) (hY W))
theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ### Conmutación META con `liftTerm`/`substTerm` — LOS SEIS (desdec sólo tenía 2) -/

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_substtcT (k : Nat) (v s f : Term) :
    liftTerm k (substtcT v s f) = substtcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substtcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substtcT (k : Nat) (u v s f : Term) :
    substTerm k u (substtcT v s f)
      = substtcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substtcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_substtscT (k : Nat) (v s f : Term) :
    liftTerm k (substtscT v s f) = substtscT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substtscT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substtscT (k : Nat) (u v s f : Term) :
    substTerm k u (substtscT v s f)
      = substtscT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substtscT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftcT (k : Nat) (c t : Term) :
    liftTerm k (liftcT c t) = liftcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftcT (k : Nat) (u c t : Term) :
    substTerm k u (liftcT c t) = liftcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftfcT (k : Nat) (c t : Term) :
    liftTerm k (liftfcT c t) = liftfcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftfcT (k : Nat) (u c t : Term) :
    substTerm k u (liftfcT c t) = liftfcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftscT (k : Nat) (c t : Term) :
    liftTerm k (liftscT c t) = liftscT (liftTerm k c) (liftTerm k t) := by
  simp only [liftscT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftscT (k : Nat) (u c t : Term) :
    substTerm k u (liftscT c t) = liftscT (substTerm k u c) (substTerm k u t) := by
  simp only [liftscT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-! ## §2 · Utilidades de NIVEL (`substtc` a nivel `numeral v` arbitrario) -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

/-! ## §3 · PRUEBA DE FUEGO (c): la instancia INTERNA de `ax_substfc_forall` -/

def AXF_BODY : Formula :=
  substfc (.var 2) (.var 1) (forallc (.var 0))
    =eq forallc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))

theorem AXF_BODY_ok : ax_substfc_forall = forall_3 AXF_BODY := rfl

theorem pcc_substfc_forall_dot (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
      (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn a))
  let W1 : Term := liftc zero (tcFn b)
  let W0 : Term := tcFn f
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode AXF_BODY)
      =eq eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 AXF_BODY
  have hA2 : Prf (W2 =eq tcFn a) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a)) (prf_liftc_tcFn a)
  have hnorm : Prf (eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hA2 (prf_refl _) (prf_refl _))
      (prf_congr_unT (prf_congr_substfcT (prf_congr_succcT hA2) (prf_refl _) (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn b) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn b)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have ha1 : Prf (substtc (succ zero) W1 (tcFn a) =eq tcFn a) := prf_substtc_tcFn_at 1 W1 a
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ha1 hv1 ?_
      exact prf_eq_trans (prf_substtc_unT_at 6 1 W1 (varc (numeral 0))) (prf_congr_unT hv0)
    · refine prf_eq_trans (prf_substtc_unT_at 6 1 W1 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ hv0
      · exact prf_eq_trans (prf_substtc_succcT (succ zero) W1 (tcFn a)) (prf_congr_succcT ha1)
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 1 W1) hv1)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT (prf_substtc_tcFn W0 a) (prf_substtc_tcFn W0 b) ?_
      exact prf_eq_trans (prf_substtc_unT_at 6 0 W0 (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_unT_at 6 0 W0 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ (prf_substtc_varc0 W0)
      · exact prf_eq_trans (prf_substtc_succcT zero W0 (tcFn a))
          (prf_congr_succcT (prf_substtc_tcFn W0 a))
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 0 W0) (prf_substtc_tcFn W0 b))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode AXF_BODY)))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 AXF_BODY (show ax_substfc_forall ∈ axioms by simp [axioms])
      (tcFn a) (tcFn b) (tcFn f))

/-! ## §4 · LA PIEZA QUE FALTABA EN LOS TRES: congruencias INTERNAS (dentro de `Prov`)

Patrón `pcc_congr_binT_1_code` / `pcc_congr_unT_code` (`Meta/CodeCtorKit.lean:267,286`).
Sin ellas no hay forma de reescribir un subtérmino de `substfcT`/`liftcT` DENTRO de `Prov`,
que es exactamente lo que pide el paso inductivo del PASO 2. -/

theorem pcc_congr_substfcT_arg1_code (B C X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hC : ∀ W, Prf (substtc zero W C =eq C))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT X B C) (substfcT Y B C))) := by
  let Ac : Term := eqc (substfcT X B C) (substfcT (varc (numeral 0)) B C)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT X B C) (substfcT w B C)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT X B C)
      (substfcT (varc (numeral 0)) B C)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w X B C)
        (prf_congr_substfcT (hX w) (hB w) (hC w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w (varc (numeral 0)) B C)
        (prf_congr_substfcT (prf_substtc_varc0 w) (hB w) (hC w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT X B C))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substfcT_arg2_code (A C X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hC : ∀ W, Prf (substtc zero W C =eq C))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A X C) (substfcT A Y C))) := by
  let Ac : Term := eqc (substfcT A X C) (substfcT A (varc (numeral 0)) C)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A X C) (substfcT A w C)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A X C)
      (substfcT A (varc (numeral 0)) C)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A X C)
        (prf_congr_substfcT (hA w) (hX w) (hC w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A (varc (numeral 0)) C)
        (prf_congr_substfcT (hA w) (prf_substtc_varc0 w) (hC w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A X C))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substfcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) := by
  let Ac : Term := eqc (substfcT A B X) (substfcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A B X) (substfcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A B X)
      (substfcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B X)
        (prf_congr_substfcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
        (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_liftcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftcT A X) (liftcT A Y))) := by
  let Ac : Term := eqc (liftcT A X) (liftcT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftcT A X) (liftcT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftcT A X) (liftcT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftcT zero w A X) (prf_congr_liftcT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftcT zero w A (varc (numeral 0)))
        (prf_congr_liftcT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftcT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ## §5 · FUEGO (a)+(b): (c) compuesta con el KIT — la forma DOTADA del paso inductivo -/

/-- (a) `pcc_eq_trans_code` + (b) el KIT (`pcc_dot_un_symm`) + §4. -/
theorem fuego_ab (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  have hdot : Prf (provFromCode (eqc (tcFn (forallc f)) (unT 6 (tcFn f)))) :=
    pcc_dot_un_symm 6 f
  have hcongr : Prf (provFromCode (eqc
      (substfcT (tcFn a) (tcFn b) (tcFn (forallc f)))
      (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f))))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn a) (tcFn b) (tcFn (forallc f)) (unT 6 (tcFn f))
      (substtc_inv_tcFn a) (substtc_inv_tcFn b) (substtc_inv_tcFn (forallc f))) hdot
  exact pcc_eq_trans_code _ _ _
    (substtc_inv_substfcT (substtc_inv_tcFn a) (substtc_inv_tcFn b)
      (substtc_inv_tcFn (forallc f)))
    hcongr (pcc_substfc_forall_dot a b f)


/-! ## §6 · SONDAS DEL PASO 2 — especificacion de `pcc_eval_substfc` -/

/-- El codigo de la ecuacion interna (patron `evalNthcCode`, `Meta/EvalNthcPrf.lean:191`). -/
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

/-- CONTROL NEGATIVO: el enunciado NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- **EL PASO INDUCTIVO `∀` DE `pcc_eval_substfc`, CERRADO MODULO UNA SOLA PIEZA.**

    `hIH`   = hipotesis de induccion sobre el subcodigo `f`, con `v`/`s` cuantificados dentro.
    `hLift` = **`pcc_dot_liftc`**. **NO EXISTE** en produccion (grep: 0 ocurrencias de
              `pcc_dot_liftc` / `pcc_eval_liftc`).

    Todo lo demas sale de produccion + §1-§5. Es la MEDIDA exacta del hueco: el caso `∀`
    (y su gemelo `∃`) se reduce a `pcc_dot_liftc` y a nada mas. -/
theorem paso2_caso_forall (v s f : Term)
    (hIH : Prf (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))
    (hLift : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))) :
    Prf (provFromCode (evalSubstfcCode v s (forallc f))) := by
  unfold evalSubstfcCode at hIH ⊢
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn s))
      =eq liftcT (termCode zero) (tcFn s)) := substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (forallc f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (forallc f))
  -- (1) fuego (a)+(b): la instancia interna del axioma, ya dotada
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab v s f
  -- (2) `succcT v̇ ↦ (σv)˙` : ecuacion de CODIGO, GRATIS (`prf_tc_succ'`)
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1
  -- (3) `liftcT ⌜0⌝ ṡ ↦ (liftc 0 s)˙` : INTERNO — aqui entra `hLift`
  have h3 : Prf (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    prf_mp (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f)))
      (prf_mp (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) hLift)
  -- (4) la HI, bajo el `unT 6`
  have h4 : Prf (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (unT 6 (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    prf_mp (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) hIH
  -- (5) el KIT pliega el `unT 6` en el punto de `forallc`
  have h5 : Prf (provFromCode (eqc (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (forallc (substfc (succ v) (liftc zero s) f))))) :=
    pcc_dot_un 6 (substfc (succ v) (liftc zero s) f)
  -- (6) la ecuacion OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h6 : Prf (provFromCode (eqc (tcFn (forallc (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (forallc f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_forall v s f)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn (forallc (substfc (succ v) (liftc zero s) f))))
  -- (7) cadena
  exact pcc_eq_trans_code _ _ _ iA h2
    (pcc_eq_trans_code _ _ _
      (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL
        (substtc_inv_tcFn f)))
      h3
      (pcc_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v))
          (substtc_inv_tcFn (liftc zero s)) (substtc_inv_tcFn f)))
        h4
        (pcc_eq_trans_code _ _ _
          (substtc_inv_unT (substtc_inv_tcFn (substfc (succ v) (liftc zero s) f)))
          h5 h6)))

/-! ############################################################################
    ## §GEN · LA FACTORIZACION POR EL **TAG**.
    ##
    ## `ax_substfc_forall` (tag 6) y `ax_substfc_ex` (tag 9) son el MISMO enunciado
    ## modulo el tag: `unc6`/`unc9` y `AXBODY6`/`AXBODY9` lo certifican **por `rfl`**.
    ## Todo el KIT unario de produccion (`unT`, `pcc_dot_un`, `pcc_congr_unT_code`,
    ## `substtc_inv_unT`, `prf_substtc_unT_at`) YA es generico en el tag, asi que la
    ## unica pieza que hubo que anadir para abstraer el tag es `substCodeT_unc`
    ## (`substCodeT` sobre `numeralM m` con `m` ABSTRACTO no reduce por `rfl`).
    ############################################################################ -/

/-- Constructor UNARIO de codigo de FORMULA, parametrizado por el tag. -/
def unc (m : Nat) (a : Term) : Term := cons (numeralM m) (cons a nil)

/-- **Los dos constructores son el MISMO, con distinto tag** (`rfl`). -/
theorem unc6 (a : Term) : unc 6 a = forallc a := rfl
theorem unc9 (a : Term) : unc 9 a = exc a := rfl

/-- El cuerpo comun de `ax_substfc_forall` / `ax_substfc_ex`. -/
def AXBODY (m : Nat) : Formula :=
  substfc (.var 2) (.var 1) (unc m (.var 0))
    =eq unc m (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))

/-- **ESPEJO PERFECTO, certificado por el kernel**: los dos axiomas de produccion son
    la MISMA formula parametrizada, y la identificacion es `rfl` (ni `simp` hizo falta). -/
theorem AXBODY6 : ax_substfc_forall = forall_3 (AXBODY 6) := rfl
theorem AXBODY9 : ax_substfc_ex = forall_3 (AXBODY 9) := rfl

/-- LA UNICA pieza nueva de la abstraccion: con `m` abstracto, `substCodeT v w (numeralM m)`
    ya no reduce por `rfl` (con `m` literal si). Se cierra con `substCodeT_closed`. -/
theorem substCodeT_unc (v : Nat) (w : Term) (m : Nat) (a : Term) :
    substCodeT v w (unc m a) = unT m (substCodeT v w a) := by
  show consT (substCodeT v w (numeralM m)) (consT (substCodeT v w a) (termCode nil))
      = unT m (substCodeT v w a)
  rw [substCodeT_closed v w (numeralM m) (fun c => liftTerm_numeralM c m)]
  rfl

theorem substCodeF_AXBODY (m : Nat) (W : Term) :
    substCodeF 2 W (AXBODY m)
      = eqCodeFn
        (substfcT W (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT W) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))) := by
  show eqCodeFn (substCodeT 2 W (substfc (.var 2) (.var 1) (unc m (.var 0))))
      (substCodeT 2 W (unc m (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))) = _
  rw [substCodeT_unc 2 W m (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))]
  show eqCodeFn (substfcT (substCodeT 2 W (.var 2)) (substCodeT 2 W (.var 1))
        (substCodeT 2 W (unc m (.var 0))))
      (unT m (substCodeT 2 W (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))) = _
  rw [substCodeT_unc 2 W m (.var 0)]
  rfl

/-- **§3-GEN** — `pcc_substfc_forall_dot` con el tag ABSTRACTO. Copia estructural
    literal del caso `forall`: cambia `6` por `m` y `hin` pasa por `substCodeF_AXBODY`. -/
theorem pcc_substfc_un_dot (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms) (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (unT m (tcFn f)))
      (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn a))
  let W1 : Term := liftc zero (tcFn b)
  let W0 : Term := tcFn f
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode (AXBODY m))
      =eq eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) := by
    have h := prf_substfc_arith_open 2 W2 (AXBODY m)
    rwa [substCodeF_AXBODY m W2] at h
  have hA2 : Prf (W2 =eq tcFn a) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a)) (prf_liftc_tcFn a)
  have hnorm : Prf (eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hA2 (prf_refl _) (prf_refl _))
      (prf_congr_unT (prf_congr_substfcT (prf_congr_succcT hA2) (prf_refl _) (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn b) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn b)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have ha1 : Prf (substtc (succ zero) W1 (tcFn a) =eq tcFn a) := prf_substtc_tcFn_at 1 W1 a
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ha1 hv1 ?_
      exact prf_eq_trans (prf_substtc_unT_at m 1 W1 (varc (numeral 0))) (prf_congr_unT hv0)
    · refine prf_eq_trans (prf_substtc_unT_at m 1 W1 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ hv0
      · exact prf_eq_trans (prf_substtc_succcT (succ zero) W1 (tcFn a)) (prf_congr_succcT ha1)
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 1 W1) hv1)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (tcFn f)))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT (prf_substtc_tcFn W0 a) (prf_substtc_tcFn W0 b) ?_
      exact prf_eq_trans (prf_substtc_unT_at m 0 W0 (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_unT_at m 0 W0 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ (prf_substtc_varc0 W0)
      · exact prf_eq_trans (prf_substtc_succcT zero W0 (tcFn a))
          (prf_congr_succcT (prf_substtc_tcFn W0 a))
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 0 W0) (prf_substtc_tcFn W0 b))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode (AXBODY m))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (tcFn f)))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 (AXBODY m) hmem (tcFn a) (tcFn b) (tcFn f))

/-- **§5-GEN** — `fuego_ab` con el tag ABSTRACTO. -/
theorem fuego_ab_un (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms) (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (tcFn (unc m f)))
      (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  have hdot : Prf (provFromCode (eqc (tcFn (unc m f)) (unT m (tcFn f)))) :=
    pcc_dot_un_symm m f
  have hcongr : Prf (provFromCode (eqc
      (substfcT (tcFn a) (tcFn b) (tcFn (unc m f)))
      (substfcT (tcFn a) (tcFn b) (unT m (tcFn f))))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn a) (tcFn b) (tcFn (unc m f)) (unT m (tcFn f))
      (substtc_inv_tcFn a) (substtc_inv_tcFn b) (substtc_inv_tcFn (unc m f))) hdot
  exact pcc_eq_trans_code _ _ _
    (substtc_inv_substfcT (substtc_inv_tcFn a) (substtc_inv_tcFn b)
      (substtc_inv_tcFn (unc m f)))
    hcongr (pcc_substfc_un_dot m hmem a b f)

/-- Las dos pertenencias, discriminadas por `simp [axioms]`. -/
theorem mem6 : forall_3 (AXBODY 6) ∈ axioms := show ax_substfc_forall ∈ axioms by simp [axioms]
theorem mem9 : forall_3 (AXBODY 9) ∈ axioms := show ax_substfc_ex ∈ axioms by simp [axioms]

/-- **CONTROL A**: la generica en tag 6 typechequea contra el enunciado LITERAL de
    `fuego_ab` (el original del sondeo `forall`). -/
theorem fuego_ab_es_generico (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) :=
  fuego_ab_un 6 mem6 a b f

/-- **CONTROL A'**: y en tag 9 da el enunciado espejo con `exc`. -/
theorem fuego_ab_ex (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (tcFn (exc f)))
      (unT 9 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) :=
  fuego_ab_un 9 mem9 a b f

end Paso2
end S_Paso2

section S_Substtc
/-! ############################################################################
    COPIA LITERAL de `sondeos/EvalSubsttc.lean` (lineas 13-1868), que compila net-0.
    Aporta `DESCENSO_imp` y `DESCENSO_lista_imp` en forma IMPLICACION -- que es la
    unica forma utilizable dentro del paso inductivo (la guarda llega como HIPOTESIS).
    ############################################################################ -/
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
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.PropCodePrf
open ROBINSON_PlusPlus.Meta.NatMulPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace SFsubsttc

/-! ############################################################################
    ## §1 · CONSTRUCTORES DE CODIGO (DEFINICIONES; ninguna ecuacion suya se postula)
    ############################################################################ -/

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
/-- `varc x = cons 0 (cons x nil)` ⇒ su imagen punteada es el `unT 0` del KIT. -/
def varcT (X : Term) : Term := unT 0 X
/-- `funcc a b = cons 1 (cons a (cons b nil))` ⇒ su imagen punteada es `binT 1`. -/
def funccT (X Y : Term) : Term := binT 1 X Y
/-- Imagen punteada de `pred` (identica en forma a `succcT`). -/
def predcT (x : Term) : Term := funcc (strCode pred_sym) (cons x nil)

theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s t : Term) :
    substtscT (termCode v) (termCode s) (termCode t) = termCode (substtsc v s t) := rfl
theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl
theorem predcT_termCode (x : Term) : predcT (termCode x) = termCode (pred x) := rfl

theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-! ## §2 · Fontaneria basica: congruencias e invariancias -/

/-- Congruencia ternaria sobre `funcc` (injerto de `sondeos/Paso2CasoForall.lean:74`). -/
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-- `substtc` sobre un `funcc` de **tres** argumentos. -/
theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy
theorem prf_congr_predcT {x y : Term} (h : Prf (x =eq y)) : Prf (predcT x =eq predcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z
theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z
theorem prf_substtc_predcT (v W x : Term) :
    Prf (substtc v W (predcT x) =eq predcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode pred_sym) x

theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z) (prf_congr_substtcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z) (prf_congr_substtscT (hX W) (hY W) (hZ W))
theorem substtc_inv_predcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (predcT X) =eq predcT X) := fun W =>
  prf_eq_trans (prf_substtc_predcT zero W X) (prf_congr_predcT (hX W))

/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados (copia de Paso2 §2) -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) := by
  unfold binT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a)) :=
  prf_substtc_unT_at 0 v W a
theorem prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binT_at 1 v W a b

/-! ## §3 · `pcc_axiom_inst4` — la pieza que faltaba (los dos axiomas clave son `forall_4`) -/

theorem pcc_thm_inst4 (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
          (formCode φ)))))) := by
  have h3 : Prf (provFromCode (substfc zero w₃ (substfc (succ zero) (liftc zero w₂)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₁))
        (formCode (Formula.forall φ)))))) :=
    pcc_thm_inst3 (Formula.forall φ) h w₁ w₂ w₃
  -- empuja los tres `substfc` bajo el binder, uno a uno
  have e2 : Prf (substfc (succ (succ zero)) (liftc zero (liftc zero w₁))
        (forallc (formCode φ))
      =eq forallc (substfc (succ (succ (succ zero)))
        (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))) :=
    prf_substfc_forall (succ (succ zero)) (liftc zero (liftc zero w₁)) (formCode φ)
  have h3' := prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
    (prf_congr_substfc_arg3 e2))) h3
  have e1 : Prf (substfc (succ zero) (liftc zero w₂)
        (forallc (substfc (succ (succ (succ zero)))
          (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))
      =eq forallc (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero)))
          (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))) :=
    prf_substfc_forall (succ zero) (liftc zero w₂) _
  have h3'' := prf_mp (prf_provCode_congr (prf_congr_substfc_arg3 e1)) h3'
  have e0 : Prf (substfc zero w₃
        (forallc (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
          (substfc (succ (succ (succ zero)))
            (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))
      =eq forallc (substfc (succ zero) (liftc zero w₃)
        (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
          (substfc (succ (succ (succ zero)))
            (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) :=
    prf_substfc_forall zero w₃ _
  have h3''' := prf_mp (prf_provCode_congr e0) h3''
  exact prf_mp (pcc_forallElim_code_open _ w₄) h3'''

theorem pcc_axiom_inst4 (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
          (formCode φ)))))) :=
  pcc_thm_inst4 φ (prf_ax hmem) w₁ w₂ w₃ w₄

/-! ############################################################################
    ## §4 · LAS SEIS ECUACIONES DE `substtc`/`substtsc`, DOTADAS
    ############################################################################ -/

/-! ### (a) `ax_substtsc_nil` (`forall_2`) -/

def SUBSTTSC_NIL_BODY : Formula := substtsc (.var 1) (.var 0) nil =eq nil

theorem SUBSTTSC_NIL_BODY_ok : ax_substtsc_nil = forall_2 SUBSTTSC_NIL_BODY := rfl

theorem pcc_substtsc_nil_code (v s : Term) :
    Prf (provFromCode (eqCodeFn
      (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (succ zero) W1 (formCode SUBSTTSC_NIL_BODY)
      =eq eqCodeFn (substtscT W1 (varc (numeral 0)) (termCode nil)) (termCode nil)) :=
    prf_substfc_arith_open 1 W1 SUBSTTSC_NIL_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substtscT W1 (varc (numeral 0)) (termCode nil)) (termCode nil)
      =eq eqCodeFn (substtscT (tcFn v) (varc (numeral 0)) (termCode nil)) (termCode nil)) :=
    prf_congr_eqCodeFn (prf_congr_substtscT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0
        (eqCodeFn (substtscT (tcFn v) (varc (numeral 0)) (termCode nil)) (termCode nil))
      =eq eqCodeFn (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_termCode_zero 0 W0)
    exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
      (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
        (prf_substtc_termCode_zero 0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode SUBSTTSC_NIL_BODY))
      =eq eqCodeFn (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 SUBSTTSC_NIL_BODY (show ax_substtsc_nil ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s))

/-! ### (b) `ax_substtc_func` (`forall_4`) -/

def SUBSTTC_FUNC_BODY : Formula :=
  substtc (.var 3) (.var 2) (funcc (.var 1) (.var 0))
    =eq funcc (.var 1) (substtsc (.var 3) (.var 2) (.var 0))

theorem SUBSTTC_FUNC_BODY_ok : ax_substtc_func = forall_4 SUBSTTC_FUNC_BODY := rfl

theorem pcc_substtc_func_code (v s p b : Term) :
    Prf (provFromCode (eqCodeFn
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn p)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTC_FUNC_BODY)
      =eq eqCodeFn
        (substtcT W3 (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 SUBSTTC_FUNC_BODY
  have hA3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn v)))
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v))
  have hnorm : Prf (eqCodeFn
        (substtcT W3 (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substtcT (tcFn v) (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_substtcT hA3 (prf_refl _) (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _)))
  -- nivel 2 : `varc 2̄ ↦ ṡ`
  have hA2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have g2v2 : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hA2
  have g2v1 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1)) (prf_gnum_lt (by omega))
  have g2v0 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0)) (prf_gnum_lt (by omega))
  have g2tv : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have hL2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substtcT (tcFn v) (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substtcT g2tv g2v2 ?_
      exact prf_eq_trans (prf_substtc_funccT_at 2 W2 _ _) (prf_congr_funccT g2v1 g2v0)
    · refine prf_eq_trans (prf_substtc_funccT_at 2 W2 _ _) ?_
      refine prf_congr_funccT g2v1 ?_
      exact prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _)
        (prf_congr_substtscT g2tv g2v2 g2v0)
  -- nivel 1 : `varc 1̄ ↦ ṗ`
  have hA1 : Prf (W1 =eq tcFn p) := prf_liftc_tcFn p
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn p) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have g1ts : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have hL1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (varc (numeral 0))))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtcT g1tv g1ts ?_
      exact prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) (prf_congr_funccT g1v1 g1v0)
    · refine prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) ?_
      refine prf_congr_funccT g1v1 ?_
      exact prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _)
        (prf_congr_substtscT g1tv g1ts g1v0)
  -- nivel 0 : `varc 0̄ ↦ ḃ`
  have hL0 : Prf (substfc zero W0 (eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (varc (numeral 0))))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
      refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _)
        (prf_congr_funccT (prf_substtc_tcFn W0 p) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _) ?_
      refine prf_congr_funccT (prf_substtc_tcFn W0 p) ?_
      exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
        (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
          (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2
          (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTC_FUNC_BODY))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm))))
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 hL2))
        (prf_eq_trans (prf_congr_substfc_arg3 hL1) hL0))
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 SUBSTTC_FUNC_BODY (show ax_substtc_func ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn p) (tcFn b))

/-! ### (c) `ax_substtsc_cons` (`forall_4`) -/

def SUBSTTSC_CONS_BODY : Formula :=
  substtsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
    =eq cons (substtc (.var 3) (.var 2) (.var 1)) (substtsc (.var 3) (.var 2) (.var 0))

theorem SUBSTTSC_CONS_BODY_ok : ax_substtsc_cons = forall_4 SUBSTTSC_CONS_BODY := rfl

theorem pcc_substtsc_cons_code (v s h t : Term) :
    Prf (provFromCode (eqCodeFn
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn h)
  let W0 : Term := tcFn t
  have hin : Prf (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTSC_CONS_BODY)
      =eq eqCodeFn
        (substtscT W3 (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 SUBSTTSC_CONS_BODY
  have hA3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn v)))
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v))
  have hnorm : Prf (eqCodeFn
        (substtscT W3 (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substtscT (tcFn v) (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _))
      (prf_congr_consT (prf_congr_substtcT hA3 (prf_refl _) (prf_refl _))
        (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _)))
  have hA2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have g2v2 : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hA2
  have g2v1 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1)) (prf_gnum_lt (by omega))
  have g2v0 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0)) (prf_gnum_lt (by omega))
  have g2tv : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have hL2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substtscT (tcFn v) (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substtscT g2tv g2v2 ?_
      exact prf_eq_trans (prf_substtc_consT (numeral 2) W2 _ _) (prf_congr_consT g2v1 g2v0)
    · refine prf_eq_trans (prf_substtc_consT (numeral 2) W2 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT (numeral 2) W2 _ _ _)
          (prf_congr_substtcT g2tv g2v2 g2v1)
      · exact prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _)
          (prf_congr_substtscT g2tv g2v2 g2v0)
  have hA1 : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn h) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have g1ts : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have hL1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtscT g1tv g1ts ?_
      exact prf_eq_trans (prf_substtc_consT (numeral 1) W1 _ _) (prf_congr_consT g1v1 g1v0)
    · refine prf_eq_trans (prf_substtc_consT (numeral 1) W1 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _)
          (prf_congr_substtcT g1tv g1ts g1v1)
      · exact prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _)
          (prf_congr_substtscT g1tv g1ts g1v0)
  have hL0 : Prf (substfc zero W0 (eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (tcFn t)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _) ?_
      refine prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_consT zero W0 _ _)
        (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_consT zero W0 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _)
          (prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
            (prf_substtc_tcFn W0 h))
      · exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
          (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
            (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2
          (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTSC_CONS_BODY))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (tcFn t)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm))))
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 hL2))
        (prf_eq_trans (prf_congr_substfc_arg3 hL1) hL0))
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 SUBSTTSC_CONS_BODY (show ax_substtsc_cons ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn h) (tcFn t))

/-! ### (d) las TRES clausulas guardadas de `varc` (`forall_3`) -/

/-- `substfc` atraviesa un atomo binario de codigo (copia de `DescensoLiftc:251`). -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

def SUBSTTC_VAR_EQ_BODY : Formula :=
  Formula.impl ((.var 2) =eq (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq (.var 1))
def SUBSTTC_VAR_GT_BODY : Formula :=
  Formula.impl (lt (.var 2) (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (pred (.var 0)))
def SUBSTTC_VAR_LT_BODY : Formula :=
  Formula.impl (lt (.var 0) (.var 2))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (.var 0))

theorem SUBSTTC_VAR_EQ_BODY_ok : ax_substtc_var_eq = forall_3 SUBSTTC_VAR_EQ_BODY := rfl
theorem SUBSTTC_VAR_GT_BODY_ok : ax_substtc_var_gt = forall_3 SUBSTTC_VAR_GT_BODY := rfl
theorem SUBSTTC_VAR_LT_BODY_ok : ax_substtc_var_lt = forall_3 SUBSTTC_VAR_LT_BODY := rfl

theorem pcc_substtc_var_eq_code (v s n : Term) :
    Prf (provFromCode (implc (eqCodeFn (tcFn v) (tcFn n))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s)))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_EQ_BODY)
      =eq implc (eqCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_EQ_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (eqCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))
      =eq implc (eqCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))) :=
    prf_congr_implc (prf_congr_eqCodeFn hA2 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (eqCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varc (numeral 1))))
      =eq implc (eqCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0)))) (tcFn s))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _)
        (prf_congr_eqCodeFn g1tv g1v0)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ g1v1
      refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtcT g1tv g1v1 ?_
      exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (eqCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0)))) (tcFn s)))
      =eq implc (eqCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_eq zero W0 _ _)
        (prf_congr_eqCodeFn (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn W0 s)
      refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
      refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_EQ_BODY)))
      =eq implc (eqCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_EQ_BODY (show ax_substtc_var_eq ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

theorem pcc_substtc_var_gt_code (v s n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn v) (tcFn n))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (varcT (predcT (tcFn n)))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_GT_BODY)
      =eq implc (ltCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_GT_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (ltCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn hA2 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (ltCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varcT (predcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' (numeral 1) W1 _ _)
        (prf_congr_atom2CodeFn g1tv g1v0)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
        refine prf_congr_substtcT g1tv g1v1 ?_
        exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
      · refine prf_eq_trans (prf_substtc_varcT_at 1 W1 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_predcT (numeral 1) W1 _) (prf_congr_predcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (ltCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
            (varcT (predcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
              (varcT (predcT (tcFn n))))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _)
        (prf_congr_atom2CodeFn (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
        refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
        exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
      · refine prf_eq_trans (prf_substtc_varcT_at 0 W0 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_predcT zero W0 _)
          (prf_congr_predcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_GT_BODY)))
      =eq implc (ltCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
              (varcT (predcT (tcFn n))))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_GT_BODY (show ax_substtc_var_gt ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

theorem pcc_substtc_var_lt_code (v s n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn n) (tcFn v))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_LT_BODY)
      =eq implc (ltCodeFn (varc (numeral 0)) W2)
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_LT_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (ltCodeFn (varc (numeral 0)) W2)
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn (prf_refl _) hA2)
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (ltCodeFn (varc (numeral 0)) (tcFn v))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' (numeral 1) W1 _ _)
        (prf_congr_atom2CodeFn g1v0 g1tv)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
        refine prf_congr_substtcT g1tv g1v1 ?_
        exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
      · exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (ltCodeFn (varc (numeral 0)) (tcFn v))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
            (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn n) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _)
        (prf_congr_atom2CodeFn (prf_substtc_varc0 W0) (prf_substtc_tcFn W0 v))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
        refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
        exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
      · exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _)
          (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_LT_BODY)))
      =eq implc (ltCodeFn (tcFn n) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_LT_BODY (show ax_substtc_var_lt ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

/-! ############################################################################
    ## §5 · EL OBJETIVO y las CONGRUENCIAS INTERNAS
    ############################################################################ -/

/-- El objetivo, con `v`, `s`, `X` **ABSTRACTOS**. -/
def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))
/-- Su companera sobre LISTAS de codigos de termino. -/
def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))

/-- CONTROL NEGATIVO: no es una reflexividad disfrazada. -/
example (v s X : Term) : True := by
  fail_if_success
    exact (rfl : substtcT (tcFn v) (tcFn s) (tcFn X) = tcFn (substtc v s X))
  trivial

theorem pcc_congr_substtcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtcT A B X) (substtcT A B Y))) := by
  let Ac : Term := eqc (substtcT A B X) (substtcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substtcT A B X) (substtcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substtcT A B X)
      (substtcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substtcT zero w A B X)
        (prf_congr_substtcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substtcT zero w A B (varc (numeral 0)))
        (prf_congr_substtcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substtcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substtscT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtscT A B X) (substtscT A B Y))) := by
  let Ac : Term := eqc (substtscT A B X) (substtscT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term,
      Prf (substfc zero w Ac =eq eqc (substtscT A B X) (substtscT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substtscT A B X)
      (substtscT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substtscT zero w A B X)
        (prf_congr_substtscT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substtscT zero w A B (varc (numeral 0)))
        (prf_congr_substtscT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substtscT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la CABEZA de `consT` (copia de `DescensoLiftc:508`). -/
theorem pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) := by
  let Ac : Term := eqc (consT X B) (consT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT X B) (consT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT X B) (consT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w X B) (prf_congr_consT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
        (prf_congr_consT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la COLA de `consT`. -/
theorem pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) := by
  let Ac : Term := eqc (consT A X) (consT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT A X) (consT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT A X) (consT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w A X) (prf_congr_consT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
        (prf_congr_consT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ############################################################################
    ## §6 · LAS CLAUSULAS ESTRUCTURALES (`funcc`, `nil`, `cons`) — CERRADAS
    ############################################################################ -/

theorem invA (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (tcFn X))
      =eq substtcT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)
theorem invAs (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (tcFn X))
      =eq substtscT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)

/-- **(2) PASO `funcc`** — el unico salto: pide la companera sobre la LISTA de argumentos. -/
theorem refl_caso_funcc (v s X p b : Term) (hX : Prf (X =eq funcc p b))
    (hb : Prf (targetSubsttsc v s b)) : Prf (targetSubsttc v s X) := by
  unfold targetSubsttc
  unfold targetSubsttsc at hb
  have hplain : Prf (substtc v s X =eq funcc p (substtsc v s b)) :=
    prf_eq_trans (prf_congr_substtc3 hX) (prf_substtc_func v s p b)
  have hY : ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      =eq substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (invAs v s b)
  have s1 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (funcc p b))) (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) :=
    pcc_substtc_func_code v s p b
  have s3 : Prf (provFromCode (eqc
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      (funccT (tcFn p) (tcFn (substtsc v s b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))
      (tcFn (substtsc v s b)) (substtc_inv_tcFn p) (invAs v s b)) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (substtsc v s b)))
      (tcFn (funcc p (substtsc v s b))))) := pcc_dot_bin 1 p (substtsc v s b)
  have hchain : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (tcFn (funcc p (substtsc v s b))))) :=
    pcc_eq_trans_code _ _ _ (invA v s (funcc p b)) s1
      (pcc_eq_trans_code _ _ _ hY s2 (pcc_eq_trans_code _ _ _ hZ s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_substtcT (prf_refl _) (prf_refl _) (prf_congr_tcFn (prf_eq_symm hX)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil (v s : Term) : Prf (targetSubsttsc v s nil) := by
  unfold targetSubsttsc
  refine prf_mp (prf_provCode_congr (prf_congr_eqCodeFn ?_ ?_)) (pcc_substtsc_nil_code v s)
  · exact prf_congr_substtscT (prf_refl _) (prf_refl _) (prf_eq_symm prf_tc_zero)
  · exact prf_eq_trans (prf_eq_symm prf_tc_zero)
      (prf_congr_tcFn (prf_eq_symm (prf_substtsc_nil v s)))

/-- **(4) PASO de la LISTA (`cons`)** — pide la companera sobre la cabeza y sobre la cola. -/
theorem refl_lista_cons (v s h t : Term) (hh : Prf (targetSubsttc v s h))
    (ht : Prf (targetSubsttsc v s t)) : Prf (targetSubsttsc v s (cons h t)) := by
  unfold targetSubsttc at hh
  unfold targetSubsttsc at ht ⊢
  have hplain : Prf (substtsc v s (cons h t)
      =eq cons (substtc v s h) (substtsc v s t)) := prf_substtsc_cons v s h t
  have hY : ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      =eq substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (invA v s h) (invAs v s t)
  have hU : ∀ W, Prf (substtc zero W (consT (tcFn (substtc v s h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (substtc v s h)) (invAs v s t)
  have s1 : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_substtscT_arg3_code (tcFn v) (tcFn s) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons h t))) (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) := pcc_substtsc_cons_code v s h t
  have s3 : Prf (provFromCode (eqc
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (substtscT (tcFn v) (tcFn s) (tcFn t))
      (substtcT (tcFn v) (tcFn s) (tcFn h)) (tcFn (substtc v s h))
      (invAs v s t) (invA v s h)) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (substtc v s h))
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))
      (substtc_inv_tcFn (substtc v s h)) (invAs v s t)) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    pcc_dot_cons (substtc v s h) (substtsc v s t)
  have hchain : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    pcc_eq_trans_code _ _ _ (invAs v s (cons h t)) s1
      (pcc_eq_trans_code _ _ _ hY s2
        (pcc_eq_trans_code _ _ _ hZ s3 (pcc_eq_trans_code _ _ _ hU s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-! ############################################################################
    ## §7 · LA CLAUSULA `varc`: LA TRICOTOMIA, REFLEJADA DENTRO DE `Prov`
    ############################################################################

    Las tres clausulas de `substtc _ _ (varc n)` estan guardadas por `v ≐ n` / `v < n` / `n < v`
    con `v` **ABSTRACTO**. La tricotomia se elimina a nivel **OBJETO** (`prf_lt_trichotomy` +
    `Prf₀.j3`), y cada guarda se **refleja** dentro de `Prov`:
    * `<` por `pcc_lt_tracked` (produccion, argumentos ABIERTOS);
    * `=` por reflexividad codificada + Leibniz (`pcc_eq_tracked`, aqui abajo).

    ⚠️ ***NO hace falta un or-elim INTERNO*** (`pcc_or_elim_code`): la disyuncion se elimina
    FUERA de `Prov`, porque la conclusion `targetSubsttc` es la MISMA en las tres ramas. -/

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-- **REFLECTOR DEL ATOMO `=`** (el gemelo de `pcc_lt_tracked`, que no estaba):
    `⊢ (a ≐ b) ⇒ Prov(⌜ ȧ = ḃ ⌝)`, con `a`, `b` **ABSTRACTOS**. Sale de la reflexividad
    codificada (`prf_provFromCode_eqCodeFn_refl`) mas Leibniz OBJETO. -/
theorem pcc_eq_tracked (a b : Term) :
    Prf ((a =eq b) ⇒ provFromCode (eqCodeFn (tcFn a) (tcFn b))) := by
  refine prf_deduction ?_
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl (tcFn a)) _)
      (PrfH_congr_tcFn (prfH_hyp_self _)))
    (prf_to_prfH (prf_provFromCode_eqCodeFn_refl (tcFn a)) _)

/-- Rama `v < n` (clausula `ax_substtc_var_gt`). **La UNICA que necesita `pred` dotado.** -/
theorem br_lt (v s n : Term)
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (Formula.impl (lt v n)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [lt v n] (lt v n) := prfH_hyp_self _
  have hdotg : PrfH [lt v n] (provFromCode (ltCodeFn (tcFn v) (tcFn n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked v n) _) hg
  have e1 : PrfH [lt v n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (predcT (tcFn n))))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_gt_code v s n) _) hdotg
  have hpd : PrfH [lt v n] (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hPred _) hg
  have e2 : PrfH [lt v n] (provFromCode (eqc
      (varcT (predcT (tcFn n))) (varcT (tcFn (pred n))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code 0 (predcT (tcFn n)) (tcFn (pred n))
      (substtc_inv_predcT (substtc_inv_tcFn n))) _) hpd
  have e3 : PrfH [lt v n] (provFromCode (eqc (varcT (tcFn (pred n))) (tcFn (varc (pred n))))) :=
    prf_to_prfH (pcc_dot_un 0 (pred n)) _
  have hchain : PrfH [lt v n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn (varc (pred n))))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
        (substtc_inv_unT (substtc_inv_tcFn n))) e1
      (PrfH_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_predcT (substtc_inv_tcFn n))) e2 e3)
  have hobj : PrfH [lt v n] (substtc v s (varc n) =eq varc (pred n)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_gt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- Rama `v ≐ n` (clausula `ax_substtc_var_eq`). CERRADA, sin hipotesis. -/
theorem br_eq (v s n : Term) :
    Prf (Formula.impl (v =eq n)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [v =eq n] (v =eq n) := prfH_hyp_self _
  have hdotg : PrfH [v =eq n] (provFromCode (eqCodeFn (tcFn v) (tcFn n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked v n) _) hg
  have e1 : PrfH [v =eq n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_eq_code v s n) _) hdotg
  have hobj : PrfH [v =eq n] (substtc v s (varc n) =eq s) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_eq v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    e1

/-- Rama `n < v` (clausula `ax_substtc_var_lt`). CERRADA, sin hipotesis. -/
theorem br_gt (v s n : Term) :
    Prf (Formula.impl (lt n v)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [lt n v] (lt n v) := prfH_hyp_self _
  have hdotg : PrfH [lt n v] (provFromCode (ltCodeFn (tcFn n) (tcFn v))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked n v) _) hg
  have e1 : PrfH [lt n v] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_lt_code v s n) _) hdotg
  have e2 : PrfH [lt n v] (provFromCode (eqc (varcT (tcFn n)) (tcFn (varc n)))) :=
    prf_to_prfH (pcc_dot_un 0 n) _
  have hchain : PrfH [lt n v] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn (varc n)))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
        (substtc_inv_unT (substtc_inv_tcFn n))) e1 e2
  have hobj : PrfH [lt n v] (substtc v s (varc n) =eq varc n) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_lt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- **(1) BASE `varc`, con la TRICOTOMIA ya eliminada.** Unica hipotesis: `pred` dotado. -/
theorem refl_caso_varc_at (v s n : Term)
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (targetSubsttc v s (varc n)) := by
  unfold targetSubsttc
  have s0 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (varc n)))
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))))) :=
    prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (varc n)) (varcT (tcFn n))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (varc n)))
      (pcc_dot_un_symm 0 n)
  have hmain : Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
      (tcFn (substtc v s (varc n))))) :=
    prf_or_elim (prf_lt_trichotomy v n) (br_lt v s n hPred)
      (prf_or_elim_imp (br_eq v s n) (br_gt v s n))
  exact pcc_eq_trans_code _ _ _ (invA v s (varc n)) s0 hmain

/-- La forma que consume la induccion: la guarda llega como ecuacion PLANA `X ≐ varc n`. -/
theorem refl_caso_varc (v s X n : Term) (hX : Prf (X =eq varc n))
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (targetSubsttc v s X) := by
  unfold targetSubsttc
  have h := refl_caso_varc_at v s n hPred
  unfold targetSubsttc at h
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_substtcT (prf_refl _) (prf_refl _) (prf_congr_tcFn (prf_eq_symm hX)))
    (prf_congr_tcFn (prf_eq_symm (prf_congr_substtc3 hX))))) h

/-! ############################################################################
    ## §8 · EL TESTIGO Y SU FONTANERIA — copia LITERAL de `sondeos/DescensoLiftc.lean`
       §B/§C/§D.1-§D.3 (es INDEPENDIENTE del objetivo: habla solo de codigos de TERMINO)
    ############################################################################ -/

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

theorem shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

theorem PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 a)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc a) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (lenc a)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 a) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc a i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (nthc a i)) Γ)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

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

theorem PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)

theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s
    simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)

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

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j1 A B)) h
theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j2 A B)) h

/-! ### D.1 · `⊢ Y ≐ nil ∨ consOk Y` para `Y` ARBITRARIO -/

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
    exact prf_mp (Prf.incl (Prf₀.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-! ### D.2 · `argsIn` se hereda a la COLA -/

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

/-! ### D.3 · Del testigo al NODO -/

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

/-! ############################################################################
    ## §9 · `liftFormula`/`substFormula` atraviesan los dos objetivos
    ############################################################################ -/

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

theorem substF_hole_tc (v s u : Term) :
    substFormula 0 u (targetSubsttc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttc v s u := by
  rw [substF_targetSubsttc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_tsc (v s u : Term) :
    substFormula 0 u (targetSubsttsc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttsc v s u := by
  rw [substF_targetSubsttsc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

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

/-! ## §10 · Las clausulas en forma IMPLICACION (la moneda de la induccion OBJETO) -/

/-- La UNICA hipotesis externa del frente: la evaluacion DOTADA de `pred`, en su forma
    GUARDADA (la mas debil que sirve). Otro agente la esta construyendo. -/
def PredHyp : Prop := ∀ v n : Term,
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))

theorem refl_shapeUn_imp (hP : PredHyp) (v s X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc (nthc X (numeralM 1)))) := prfH_hyp_self _
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc_at v s (nthc X (numeralM 1)) (hP v (nthc X (numeralM 1)))) _)

theorem refl_caso_funcc_imp (v s p b : Term) :
    Prf (Formula.impl (targetSubsttsc v s b) (targetSubsttc v s (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetSubsttsc v s b] (targetSubsttsc v s b) := prfH_hyp_self _
  have hY : ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      =eq substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (invAs v s b)
  have s1 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (funcc p b))) (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) :=
    prf_to_prfH (pcc_substtc_func_code v s p b) _
  have s3 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      (funccT (tcFn p) (tcFn (substtsc v s b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (substtscT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtsc v s b))
      (substtc_inv_tcFn p) (invAs v s b)) _) hb
  have s4 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (substtsc v s b))) (tcFn (funcc p (substtsc v s b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (substtsc v s b)) _
  have hchain : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (tcFn (funcc p (substtsc v s b))))) :=
    PrfH_eq_trans_code _ _ _ (invA v s (funcc p b)) s1
      (PrfH_eq_trans_code _ _ _ hY s2 (PrfH_eq_trans_code _ _ _ hZ s3 s4))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtc_func v s p b))))) _) hchain

theorem refl_shapeBin_imp (v s X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetSubsttsc v s (nthc X (numeralM 2))))
      (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetSubsttsc v s b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hbb : PrfH [H] (targetSubsttsc v s b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetSubsttc v s (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp v s p b) _) hbb
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hs) hfb

theorem refl_lista_cons_imp (v s h t : Term) :
    Prf (Formula.impl (land (targetSubsttc v s h) (targetSubsttsc v s t))
      (targetSubsttsc v s (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetSubsttc v s h) (targetSubsttsc v s t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetSubsttc v s h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetSubsttsc v s t) := PrfH_and_elim_right hh0
  have hY : ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      =eq substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (invA v s h) (invAs v s t)
  have hU : ∀ W, Prf (substtc zero W (consT (tcFn (substtc v s h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (substtc v s h)) (invAs v s t)
  have s1 : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substtscT_arg3_code (tcFn v) (tcFn s) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons h t))) (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    prf_to_prfH (pcc_substtsc_cons_code v s h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (substtcT (tcFn v) (tcFn s) (tcFn h))
      (tcFn (substtc v s h)) (invAs v s t) (invA v s h)) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (substtc v s h))
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))
      (substtc_inv_tcFn (substtc v s h)) (invAs v s t)) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    prf_to_prfH (pcc_dot_cons (substtc v s h) (substtsc v s t)) _
  have hchain : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    PrfH_eq_trans_code _ _ _ (invAs v s (cons h t)) s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 (PrfH_eq_trans_code _ _ _ hU s4 s5)))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtsc_cons v s h t))))) _) hchain

/-! ############################################################################
    ## §11 · EL PREDICADO DE LA INDUCCION FUERTE — las DOS mitades y los DOS
       parametros `v`/`s`, todos CUANTIFICADOS DENTRO (lo exige `liftFormula 1 Φ = Φ`)
    ############################################################################ -/

def CONJ (w v s X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (targetSubsttc v s X))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (targetSubsttsc v s X))

theorem liftF_CONJ (k : Nat) (w v s X : Term) :
    liftFormula k (CONJ w v s X)
      = CONJ (liftTerm k w) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [CONJ, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetSubsttc, liftF_targetSubsttsc]

theorem substF_CONJ (k : Nat) (u w v s X : Term) :
    substFormula k u (CONJ w v s X)
      = CONJ (substTerm k u w) (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [CONJ, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetSubsttc, substF_targetSubsttsc]

/-- `#3` es el CODIGO sobre el que se induce; `#2` el testigo, `#1` = `v`, `#0` = `s`. -/
def PHIbody : Formula := CONJ (.var 2) (.var 1) (.var 0) (.var 3)
def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

theorem hPHI1 : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_CONJ, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHI_at (t : Term) :
    substFormula 0 t PHI
      = Formula.forall (Formula.forall (Formula.forall
          (CONJ (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI, PHIbody, substFormula, substF_CONJ, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
        (CONJ (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHI_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
        (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHI_spec3 (t w v s : Term) :
    substFormula 0 s (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = CONJ w v s t := by
  simp only [substF_CONJ, substTerm, FOL.substTerm_liftTerm, if_true]

/-- Instanciacion de las DOS mitades a `w`, `v`, `s` concretos. -/
theorem PHI_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (CONJ w v s t) := by
  rw [PHI_at] at h
  have h1 := PrfH_spec h w
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

/-! ### El PASO de la induccion fuerte -/

theorem PHI_step (hP : PredHyp) : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] (Formula.forall (Formula.forall PHIbody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIbody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSI3] PHIbody
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (isTC1 (.var 2) (.var 3)) [PSI3] rfl
    have hh : PrfH [isTC1 (.var 2) (.var 3), PSI3] (isTC1 (.var 2) (.var 3)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwf : PrfH [isTC1 (.var 2) (.var 3), PSI3] (wfAll1 (.var 2)) :=
      PrfH_and_elim_left hh
    have hin : PrfH [isTC1 (.var 2) (.var 3), PSI3] (In (.var 3) (.var 2)) :=
      PrfH_and_elim_right hh
    have hitc : PrfH [isTC1 (.var 2) (.var 3), PSI3]
        (isTermCodeE1 (.var 2) (.var 3)) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH (prf_isTermCodeE1_of_In (.var 2) (.var 3)) _) hin) hwf
    refine PrfH_or_elim hitc ?varc ?func
    case varc =>
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp hP (.var 1) (.var 0) (.var 3)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    case func =>
      have hb : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3]
          (land (shapeBin (.var 3) 1) (argsIn (.var 2) (nthc (.var 3) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hwf' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3] (wfAll1 (.var 2)) :=
        PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      have hpsi' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3] PSI3 :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hshape := PrfH_and_elim_left hb
      have hargs := PrfH_and_elim_right hb
      have h1 : Prf (lt (nthc (.var 3) (numeralM 2)) (cons (nthc (.var 3) (numeralM 2)) nil)) :=
        prf_cantor_mono_left _ _
      have h2 : Prf (lt (cons (nthc (.var 3) (numeralM 2)) nil)
          (cons (nthc (.var 3) (numeralM 1)) (cons (nthc (.var 3) (numeralM 2)) nil))) :=
        prf_cantor_mono_right _ _
      have h3 : Prf (lt (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil))
          (cons (numeralM 1) (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil)))) :=
        prf_cantor_mono_right _ _
      have h12 : Prf (lt (nthc (.var 3) (numeralM 2))
          (cons (nthc (.var 3) (numeralM 1)) (cons (nthc (.var 3) (numeralM 2)) nil))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
      have h123 : Prf (lt (nthc (.var 3) (numeralM 2))
          (cons (numeralM 1) (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil)))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
      have hltb := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
      have hphi := PrfH.mp _ _ _ (PSI_inst hpsi' (nthc (.var 3) (numeralM 2))) hltb
      have huse := PHI_use (nthc (.var 3) (numeralM 2)) (.var 2) (.var 1) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp (.var 1) (.var 0) (.var 3)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) [PSI3] rfl
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 3) nil,
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (Formula.eq (.var 3) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm heq)
        (prf_to_prfH (refl_lista_nil (.var 1) (.var 0)) _)
    case consc =>
      have hcons : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh' : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3] PSI3 :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hwf := PrfH_and_elim_left hh'
      have hargs := PrfH_and_elim_right hh'
      -- (a) la CABEZA esta en el testigo y es MENOR
      have hlenX := PrfH_eq_trans (PrfH_congr_lenc hcons)
        (prf_to_prfH (prf_lenc_cons (carc (.var 3)) (cdrc (.var 3))) _)
      have hzlt := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hlenX) (prf_to_prfH (prf_zero_lt_succ (lenc (cdrc (.var 3)))) _)
      have hin0 := PrfH.mp _ _ _ (PrfH_inst_argsIn (.var 2) (.var 3) zero hargs) hzlt
      have hnth0 := PrfH_eq_trans (PrfH_congr_nthc_lst zero hcons)
        (prf_to_prfH (prf_nthc_zero (carc (.var 3)) (cdrc (.var 3))) _)
      have hinhd := PrfH_congr_In_left hnth0 hin0
      have hlthd := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_left (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_hd := PHI_use (carc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (carc (.var 3))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      -- (b) la COLA hereda `argsIn` y es MENOR
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 2) (carc (.var 3)) (cdrc (.var 3))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_tl := PHI_use (cdrc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (cdrc (.var 3))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp (.var 1) (.var 0)
          (carc (.var 3)) (cdrc (.var 3))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hcons) hres

/-! ### §12 · EL DESCENSO y `pcc_eval_substtc` -/

theorem PHI_all (hP : PredHyp) (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI1 (PHI_step hP) t

theorem DESCENSO_imp (hP : PredHyp) (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PHI_use t w v s (prf_to_prfH (PHI_all hP t) []))) rfl

theorem DESCENSO_lista_imp (hP : PredHyp) (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_right (PHI_use t w v s (prf_to_prfH (PHI_all hP t) []))) rfl

/-- **`pcc_eval_substtc`** — el objetivo del encargo, con `v`, `s`, `t` **ABSTRACTOS**
    y el testigo `w` como GUARDA (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc (hP : PredHyp) (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  prf_mp (DESCENSO_imp hP w v s t) h

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem pcc_eval_substtsc (hP : PredHyp) (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  prf_mp (DESCENSO_lista_imp hP w v s t) (prf_and_intro hwf hargs)

/-- La forma que de verdad llega rio abajo: el testigo viene de un `∃`. -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

theorem pcc_eval_substtc_hasWit (hP : PredHyp) (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetSubsttc]
  exact PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_imp hP (.var 0) (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t)) _)
    (prfH_hyp_self _)

/-! ############################################################################
    ## §13 · LA HIPOTESIS `PredHyp` SE DESCARGA — `pred` DOTADO bajo la guarda `v < n`.

    `v < n` da (por `ax13`) un testigo `k` con `v + σk = n`, o sea **`n` es un SUCESOR**
    (`prf_add_succ_t`). Y para un sucesor, `pred` dotado sale de **`ax26_pred_succ`
    instanciado DENTRO de `Prov`** (`pcc_axiom_inst`), sin induccion ninguna.
    ############################################################################ -/

def AX26_BODY : Formula := pred (succ (.var 0)) =eq (.var 0)

theorem AX26_BODY_ok : ax26_pred_succ = Formula.forall AX26_BODY := rfl

/-- **`ax26_pred_succ` DOTADA**: `⊢ Prov(⌜ pred(σ(ṁ)) = ṁ ⌝)`, con `m` **ABSTRACTO**. -/
theorem pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) := by
  have hin : Prf (substfc zero (tcFn m) (formCode AX26_BODY)
      =eq eqCodeFn (predcT (succcT (tcFn m))) (tcFn m)) :=
    prf_substfc_arith_open 0 (tcFn m) AX26_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst AX26_BODY (show ax26_pred_succ ∈ axioms by simp [axioms]) (tcFn m))

theorem PrfH_congr_pred {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (pred a =eq pred b) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 a)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred a) (pred s) := by
    intro s
    simp only [f, pred, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (pred a)) Γ)

theorem PrfH_congr_predcT {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (predcT a =eq predcT b) := by
  let f : Formula := Formula.eq (predcT (liftTerm 0 a)) (predcT (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (predcT a) (predcT s) := by
    intro s
    simp only [f, predcT, funcc, cons, nil, zero, succ, substFormula, substTerm, substTerms,
      substTerm_strCode, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (predcT a)) Γ)

theorem PrfH_pred_dot_of_succ {Γ : List Formula} (n m : Term) (h : PrfH Γ (n =eq succ m)) :
    PrfH Γ (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := by
  have e1 : PrfH Γ (predcT (tcFn n) =eq predcT (succcT (tcFn m))) :=
    PrfH_congr_predcT (PrfH_eq_trans (PrfH_congr_tcFn h) (prf_to_prfH (prf_tc_succ' m) _))
  have hpn : PrfH Γ (pred n =eq m) :=
    PrfH_eq_trans (PrfH_congr_pred h) (prf_to_prfH (prf_pred_succ m) _)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_eq_symm e1) (PrfH_congr_tcFn (PrfH_eq_symm hpn)))
    (prf_to_prfH (pcc_pred_succ_code m) _)

theorem liftT_predcode (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) := by
  simp only [eqc, predcT, funcc, tcFn, pred, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode]

/-- **`PredHyp` DESCARGADA.** -/
theorem predHyp : PredHyp := by
  intro v n
  refine prf_deduction ?_
  have hiff : PrfH [lt v n]
      (Formula.ex (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_lt_iff v n)) _) (prfH_hyp_self _)
  refine PrfH_ex_elim hiff ?_
  rw [liftFormula_provFromCode_open, liftT_predcode]
  have hh : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsucc : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (liftTerm 0 n =eq succ (add (liftTerm 0 v) (.var 0))) :=
    PrfH_eq_trans (PrfH_eq_symm hh)
      (prf_to_prfH (prf_add_succ_t (liftTerm 0 v) (.var 0)) _)
  exact PrfH_pred_dot_of_succ (liftTerm 0 n) (add (liftTerm 0 v) (.var 0)) hsucc

/-! ### §14 · EL TEOREMA, YA SIN NINGUNA HIPOTESIS EXTERNA -/

/-- **`pcc_eval_substtc`** — SIN hipotesis: la evaluacion PROVABLE de `substtc` con
    `v`, `s`, `t` **ABSTRACTOS**, guardada por el testigo `w` (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc' (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  pcc_eval_substtc predHyp w v s t h

/-- Su gemela sobre LISTAS de codigos de termino, SIN hipotesis. -/
theorem pcc_eval_substtsc' (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  pcc_eval_substtsc predHyp w v s t hwf hargs

/-- La forma con el testigo CUANTIFICADO (la que llega rio abajo), SIN hipotesis. -/
theorem pcc_eval_substtc_hasWit' (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) :=
  pcc_eval_substtc_hasWit predHyp v s t

end SFsubsttc
end S_Substtc

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
    ## §3 · EL OBJETIVO (copia literal de `sondeos/Paso2CasoForall.lean` §6)
    ############################################################################ -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

def targetSubstfc (v s X : Term) : Formula := provFromCode (evalSubstfcCode v s X)

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

theorem liftF_targetSubstfc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubstfc v s X)
      = targetSubstfc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubstfc, liftFormula_provFromCode_open, liftTerm_evalSubstfcCode]

theorem substF_targetSubstfc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubstfc v s X)
      = targetSubstfc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubstfc, substFormula_provFromCode_open, substTerm_evalSubstfcCode]

theorem substF_hole_fc (v s u : Term) :
    substFormula 0 u (targetSubstfc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubstfc v s u := by
  rw [substF_targetSubstfc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_targetSubstfc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubstfc v s X)) : PrfH Γ (targetSubstfc v s X') :=
  (substF_hole_fc v s X') ▸
    PrfH_leibniz_subst (A := targetSubstfc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_fc v s X) ▸ ha)

/-! ############################################################################
    ## §4 · EL PREDICADO DE LA INDUCCION FUERTE.

    CUATRO binders INTERNOS (`wF`, `wT`, `v`, `s`) y la guarda DENTRO (es un `∃`
    interno via `hasWit`, luego NO anade binder exterior — leccion de
    `sondeos/GateGuardaEnriquecida.lean`). El codigo sobre el que se induce es `#4`.
    ############################################################################ -/

/-- La guarda completa: el sustituyendo tiene testigo de TERMINO y el codigo tiene
    testigo de FORMULA (que a su vez lleva su testigo de TERMINO). -/
def GUARD (wF wT s X : Term) : Formula := land (hasWit s) (isFC1 wF wT X)

def BODY (wF wT v s X : Term) : Formula :=
  Formula.impl (GUARD wF wT s X) (targetSubstfc v s X)

theorem liftF_BODY (k : Nat) (wF wT v s X : Term) :
    liftFormula k (BODY wF wT v s X)
      = BODY (liftTerm k wF) (liftTerm k wT) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [BODY, GUARD, land, liftFormula, liftF_hasWit, liftF_isFC1, liftF_targetSubstfc]

theorem substF_BODY (k : Nat) (u wF wT v s X : Term) :
    substFormula k u (BODY wF wT v s X)
      = BODY (substTerm k u wF) (substTerm k u wT) (substTerm k u v) (substTerm k u s)
          (substTerm k u X) := by
  simp only [BODY, GUARD, land, substFormula, substF_hasWit, substF_isFC1, substF_targetSubstfc]

/-- `#4` es el CODIGO; `#3` = `wF`, `#2` = `wT`, `#1` = `v`, `#0` = `s`. -/
def PHIbody : Formula := BODY (.var 3) (.var 2) (.var 1) (.var 0) (.var 4)

def PHI : Formula :=
  Formula.forall (Formula.forall (Formula.forall (Formula.forall PHIbody)))

/-- **EL GATE de `prf_strong_induction`.** -/
theorem hPHI : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_BODY, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

/-! ### Instanciacion de los cuatro binders -/

theorem PHI_at (t : Term) :
    substFormula 0 t PHI
      = Formula.forall (Formula.forall (Formula.forall (Formula.forall
          (BODY (.var 3) (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))))) := by
  simp only [PHI, PHIbody, substFormula, substF_BODY, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_spec1 (t wF : Term) :
    substFormula 0 wF (Formula.forall (Formula.forall (Formula.forall
        (BODY (.var 3) (.var 2) (.var 1) (.var 0)
          (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))))
      = Formula.forall (Formula.forall (Formula.forall
          (BODY (liftTerm 0 (liftTerm 0 (liftTerm 0 wF))) (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, substTerm_liftLiftLiftLift]

theorem PHI_spec2 (t wF wT : Term) :
    substFormula 0 wT (Formula.forall (Formula.forall
        (BODY (liftTerm 0 (liftTerm 0 (liftTerm 0 wF))) (.var 2) (.var 1) (.var 0)
          (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODY (liftTerm 0 (liftTerm 0 wF)) (liftTerm 0 (liftTerm 0 wT)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, substTerm_liftLiftLift]

theorem PHI_spec3 (t wF wT v : Term) :
    substFormula 0 v (Formula.forall
        (BODY (liftTerm 0 (liftTerm 0 wF)) (liftTerm 0 (liftTerm 0 wT)) (.var 1) (.var 0)
          (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall
          (BODY (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHI_spec4 (t wF wT v s : Term) :
    substFormula 0 s
        (BODY (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = BODY wF wT v s t := by
  simp only [substF_BODY, substTerm, FOL.substTerm_liftTerm, if_true]

theorem PHI_use {Γ : List Formula} (t wF wT v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (BODY wF wT v s t) := by
  rw [PHI_at] at h
  have h1 := PrfH_spec h wF
  rw [PHI_spec1] at h1
  have h2 := PrfH_spec h1 wT
  rw [PHI_spec2] at h2
  have h3 := PrfH_spec h2 v
  rw [PHI_spec3] at h3
  have h4 := PrfH_spec h3 s
  rwa [PHI_spec4] at h4

/-! ### El `PSI` de la induccion fuerte, en la forma que se usa DENTRO del paso -/

def PSIat (X : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 X)) PHI)

theorem PSIat_eq (X : Term) : substFormula 0 X (PSI PHI) = PSIat X := psi_at PHI X

theorem PSIat_inst {Γ : List Formula} {X : Term} (h : PrfH Γ (PSIat X)) (z : Term) :
    PrfH Γ (Formula.impl (lt z X) (substFormula 0 z PHI)) := by
  have hi := PrfH_spec h z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (liftTerm 0 X)) PHI)
      = Formula.impl (lt z X) (substFormula 0 z PHI) := by
    simp only [substFormula, lt, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  rwa [e] at hi

/-- **La HIPOTESIS DE INDUCCION, ya instanciada**: si `z < X`, `z` tiene testigo de formula
    y `s'` testigo de termino, entonces vale el objetivo en `z` con `v'`/`s'` LIBRES. -/
theorem IH_at {Γ : List Formula} {X : Term} (hpsi : PrfH Γ (PSIat X)) (z : Term)
    (hlt : PrfH Γ (lt z X)) (wF wT v' s' : Term)
    (hguard : PrfH Γ (GUARD wF wT s' z)) : PrfH Γ (targetSubstfc v' s' z) :=
  PrfH.mp _ _ _ (PHI_use z wF wT v' s' (PrfH.mp _ _ _ (PSIat_inst hpsi z) hlt)) hguard

/-! ############################################################################
    ## §5 · EL DESCENSO — copia literal de `sondeos/Paso2CasoForall.lean` §7
    ############################################################################ -/

theorem descenso_un (X : Term) (k : Nat) : Prf (shapeUn X k ⇒ lt (nthc X (numeralM 1)) X) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 1)) (cons (nthc X (numeralM 1)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 1)) nil)
      (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (nthc X (numeralM 1)) (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeUn X k))) (prf_to_prfH h3 _)

theorem descenso_bin1 (X : Term) (k : Nat) : Prf (shapeBin X k ⇒ lt (nthc X (numeralM 1)) X) := by
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
    (PrfH_eq_symm (prfH_hyp_self (shapeBin X k))) (prf_to_prfH h3 _)

theorem descenso_bin2 (X : Term) (k : Nat) : Prf (shapeBin X k ⇒ lt (nthc X (numeralM 2)) X) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 2)) (cons (nthc X (numeralM 2)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 2)) nil)
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_cantor_mono_right _ _
  have h4 : Prf (lt (nthc X (numeralM 2))
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  have h5 : Prf (lt (nthc X (numeralM 2))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h4) h3
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeBin X k))) (prf_to_prfH h5 _)

/-! ############################################################################
    ## §6 · LOS OCHO CASOS, como HIPOTESIS con enunciado EXACTO.

    Cada uno es exactamente la forma en que el paso inductivo los consume.
    ############################################################################ -/

/-- tag 2 · `botc`. Cubierto por `sondeos/SubstfcPlanos.paso2_caso_bottom`. -/
def CasoBot : Prop := ∀ v s X : Term,
  Prf (Formula.impl (shapeNul X 2) (targetSubstfc v s X))

/-- tag 3 · `atomc`. Consume `pcc_eval_substtsc'` (lista de terminos). -/
def CasoAtom : Prop := ∀ wT v s X : Term,
  Prf (Formula.impl
    (land (wfAll1 wT) (land (shapeBin X 3) (argsIn wT (nthc X (numeralM 2)))))
    (targetSubstfc v s X))

/-- tag 4 · `eqc`. Consume `pcc_eval_substtc'` DOS veces. -/
def CasoEq : Prop := ∀ wT v s X : Term,
  Prf (Formula.impl
    (land (wfAll1 wT) (land (shapeBin X 4)
      (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))))
    (targetSubstfc v s X))

/-- tags 5/7/8 · `implc`/`andc`/`orc`. Cubierto por `SubstfcPlanos.paso2_caso_bin`. -/
def CasoBin (k : Nat) : Prop := ∀ v s X : Term,
  Prf (Formula.impl
    (land (shapeBin X k)
      (land (targetSubstfc v s (nthc X (numeralM 1)))
            (targetSubstfc v s (nthc X (numeralM 2)))))
    (targetSubstfc v s X))

/-- tags 6/9 · `forallc`/`exc`. Cubierto por `Paso2Guardado.paso2_caso_forall_guarded`
    y `SubstfcEx.paso2_caso_ex_guarded`, **modulo reformular la HI de `Prf` a conjunto**. -/
def CasoUn (k : Nat) : Prop := ∀ v s X : Term,
  Prf (Formula.impl
    (land (hasWit s) (land (shapeUn X k)
      (targetSubstfc (succ v) (liftc zero s) (nthc X (numeralM 1)))))
    (targetSubstfc v s X))

/-- La clausura de la guarda bajo `liftc zero` — `SinWTs.CRIT_hasWit_lift`. -/
def HasWitLift : Prop := ∀ s : Term, Prf (Formula.impl (hasWit s) (hasWit (liftc zero s)))

/-! ############################################################################
    ## §7 · EL PASO INDUCTIVO — las OCHO ramas, cada una con contexto de DOS
       hipotesis (nunca cadenas de `List.Mem.tail`), y el or-elim al nivel `Prf`.
    ############################################################################ -/

/-- Todo lo que la rama necesita del contexto, empaquetado en UNA formula. -/
def CTXF (wF wT s X : Term) : Formula :=
  land (land (PSIat X) (wfAll1 wT)) (land (hasWit s) (wfAllF wF wT))

section Ramas
variable (wF wT v s X : Term)

theorem rama_bot (hbot : CasoBot) :
    Prf (Formula.impl (clBot X) (Formula.impl (CTXF wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXF wF wT s X) [clBot X] rfl)
  exact PrfH.mp _ _ _ (prf_to_prfH (hbot v s X) _)
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

theorem rama_atom (hatom : CasoAtom) :
    Prf (Formula.impl (clAtom wT X) (Formula.impl (CTXF wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXF wF wT s X) [clAtom wT X] rfl)
  have hcl : PrfH [CTXF wF wT s X, clAtom wT X] (clAtom wT X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXF wF wT s X, clAtom wT X] (CTXF wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwT : PrfH [CTXF wF wT s X, clAtom wT X] (wfAll1 wT) :=
    PrfH_and_elim_right (PrfH_and_elim_left hctx)
  exact PrfH.mp _ _ _ (prf_to_prfH (hatom wT v s X) _) (PrfH_and_intro hwT hcl)

theorem rama_eq (heq : CasoEq) :
    Prf (Formula.impl (clEq wT X) (Formula.impl (CTXF wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXF wF wT s X) [clEq wT X] rfl)
  have hcl : PrfH [CTXF wF wT s X, clEq wT X] (clEq wT X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXF wF wT s X, clEq wT X] (CTXF wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwT : PrfH [CTXF wF wT s X, clEq wT X] (wfAll1 wT) :=
    PrfH_and_elim_right (PrfH_and_elim_left hctx)
  exact PrfH.mp _ _ _ (prf_to_prfH (heq wT v s X) _) (PrfH_and_intro hwT hcl)

theorem rama_bin (k : Nat) (hbin : CasoBin k) :
    Prf (Formula.impl (clBin wF X k)
      (Formula.impl (CTXF wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXF wF wT s X) [clBin wF X k] rfl)
  have hcl : PrfH [CTXF wF wT s X, clBin wF X k] (clBin wF X k) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXF wF wT s X, clBin wF X k] (CTXF wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi := PrfH_and_elim_left (PrfH_and_elim_left hctx)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  have hws := PrfH_and_elim_left (PrfH_and_elim_right hctx)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_right hctx)
  have hshape := PrfH_and_elim_left hcl
  have hin1 := PrfH_and_elim_left (PrfH_and_elim_right hcl)
  have hin2 := PrfH_and_elim_right (PrfH_and_elim_right hcl)
  have hlt1 : PrfH [CTXF wF wT s X, clBin wF X k] (lt (nthc X (numeralM 1)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH (descenso_bin1 X k) _) hshape
  have hlt2 : PrfH [CTXF wF wT s X, clBin wF X k] (lt (nthc X (numeralM 2)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH (descenso_bin2 X k) _) hshape
  have hIH1 : PrfH [CTXF wF wT s X, clBin wF X k]
      (targetSubstfc v s (nthc X (numeralM 1))) :=
    IH_at hpsi _ hlt1 wF wT v s
      (PrfH_and_intro hws (PrfH_and_intro (PrfH_and_intro hwT hwF) hin1))
  have hIH2 : PrfH [CTXF wF wT s X, clBin wF X k]
      (targetSubstfc v s (nthc X (numeralM 2))) :=
    IH_at hpsi _ hlt2 wF wT v s
      (PrfH_and_intro hws (PrfH_and_intro (PrfH_and_intro hwT hwF) hin2))
  exact PrfH.mp _ _ _ (prf_to_prfH (hbin v s X) _)
    (PrfH_and_intro hshape (PrfH_and_intro hIH1 hIH2))

theorem rama_un (k : Nat) (hun : CasoUn k) (hwl : HasWitLift) :
    Prf (Formula.impl (clUn wF X k)
      (Formula.impl (CTXF wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXF wF wT s X) [clUn wF X k] rfl)
  have hcl : PrfH [CTXF wF wT s X, clUn wF X k] (clUn wF X k) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXF wF wT s X, clUn wF X k] (CTXF wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi := PrfH_and_elim_left (PrfH_and_elim_left hctx)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  have hws := PrfH_and_elim_left (PrfH_and_elim_right hctx)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_right hctx)
  have hshape := PrfH_and_elim_left hcl
  have hin1 := PrfH_and_elim_right hcl
  have hlt1 : PrfH [CTXF wF wT s X, clUn wF X k] (lt (nthc X (numeralM 1)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH (descenso_un X k) _) hshape
  -- el sustituyendo LEVANTADO conserva testigo
  have hwsl : PrfH [CTXF wF wT s X, clUn wF X k] (hasWit (liftc zero s)) :=
    PrfH.mp _ _ _ (prf_to_prfH (hwl s) _) hws
  -- la HI se instancia con `v ↦ σv`, `s ↦ liftc 0 s` (van CUANTIFICADOS dentro de Φ)
  have hIH1 : PrfH [CTXF wF wT s X, clUn wF X k]
      (targetSubstfc (succ v) (liftc zero s) (nthc X (numeralM 1))) :=
    IH_at hpsi _ hlt1 wF wT (succ v) (liftc zero s)
      (PrfH_and_intro hwsl (PrfH_and_intro (PrfH_and_intro hwT hwF) hin1))
  exact PrfH.mp _ _ _ (prf_to_prfH (hun v s X) _)
    (PrfH_and_intro hws (PrfH_and_intro hshape hIH1))

end Ramas

/-- **LAS OCHO RAMAS, ENSAMBLADAS** por or-elim al nivel `Prf` (sin cadenas de contexto). -/
theorem clauses_imp (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) (wF wT v s X : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT X)
      (Formula.impl (CTXF wF wT s X) (targetSubstfc v s X))) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_or_elim_imp (rama_bot wF wT v s X hbot)
   (prf_or_elim_imp (rama_atom wF wT v s X hatom)
    (prf_or_elim_imp (rama_eq wF wT v s X heq)
     (prf_or_elim_imp (rama_bin wF wT v s X 5 h5)
      (prf_or_elim_imp (rama_un wF wT v s X 6 h6 hwl)
       (prf_or_elim_imp (rama_bin wF wT v s X 7 h7)
        (prf_or_elim_imp (rama_bin wF wT v s X 8 h8)
                         (rama_un wF wT v s X 9 h9 hwl)))))))

/-! ### El `PSI` levantado CUATRO veces (uno por binder interno) -/

theorem psi_l1 : liftFormula 0 (PSI PHI)
    = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHI) := by
  simp only [PSI, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI]

theorem psi_l2 : liftFormula 0 (liftFormula 0 (PSI PHI))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) PHI) := by
  rw [psi_l1]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hPHI]

theorem psi_l3 : liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) PHI) := by
  rw [psi_l2]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hPHI]

theorem psi_l4 : liftFormula 0 (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI))))
    = PSIat (.var 4) := by
  rw [psi_l3]
  simp only [PSIat, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI]

/-- **EL PASO DE LA INDUCCION FUERTE.** -/
theorem PHI_step (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) :
    Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] (Formula.forall (Formula.forall (Formula.forall PHIbody))) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall (Formula.forall PHIbody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIbody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIbody ?_
  simp only [List.map_cons, List.map_nil, psi_l4]
  show PrfH [PSIat (.var 4)] PHIbody
  refine deduction_aux ?_ (GUARD (.var 3) (.var 2) (.var 0) (.var 4)) [PSIat (.var 4)] rfl
  have hg : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (GUARD (.var 3) (.var 2) (.var 0) (.var 4)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (PSIat (.var 4)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hws := PrfH_and_elim_left hg
  have hfc := PrfH_and_elim_right hg
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hfc)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hfc)
  have hin := PrfH_and_elim_right hfc
  have hcode : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (isFormCodeE2 (.var 3) (.var 2) (.var 4)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isFormCodeE2_of_In (.var 3) (.var 2) (.var 4)) _) hin) hwF
  have hctx : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (CTXF (.var 3) (.var 2) (.var 0) (.var 4)) :=
    PrfH_and_intro (PrfH_and_intro hpsi hwT) (PrfH_and_intro hws hwF)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (clauses_imp hbot hatom heq h5 h7 h8 h6 h9 hwl
      (.var 3) (.var 2) (.var 1) (.var 0) (.var 4)) _) hcode) hctx

/-! ############################################################################
    ## §8 · EL TEOREMA — `pcc_eval_substfc` GUARDADO, argumentos ABSTRACTOS
    ############################################################################ -/

theorem PHI_all (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) (t : Term) :
    Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI (PHI_step hbot hatom heq h5 h7 h8 h6 h9 hwl) t

theorem DESCENSO_imp (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) (wF wT v s t : Term) :
    Prf (Formula.impl (GUARD wF wT s t) (targetSubstfc v s t)) :=
  prfH_nil_to_prf
    (PHI_use t wF wT v s
      (prf_to_prfH (PHI_all hbot hatom heq h5 h7 h8 h6 h9 hwl t) [])) rfl

/-- **`pcc_eval_substfc`** — la evaluacion provable de `substfc` con `v`, `s`, `f`
    ABSTRACTOS, guardada por los DOS testigos (formula y termino), MODULO los 8 casos. -/
theorem pcc_eval_substfc_modulo_8
    (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  prf_mp (DESCENSO_imp hbot hatom heq h5 h7 h8 h6 h9 hwl wF wT v s f)
    (prf_and_intro hws hfc)

/-! ############################################################################
    ## §9 · DESCARGA de `CasoBot` y de `CasoBin 5/7/8`.

    Copia LITERAL de `sondeos/SubstfcPlanos.lean` §0-§6 (que compila net-0), mas UNA
    pieza nueva: `paso2_caso_bin_imp`, que es `paso2_caso_bin` reescrito en `PrfH Γ`
    — hace falta porque la HI de la induccion llega como HIPOTESIS del contexto, no
    como teorema `Prf` cerrado.
    ############################################################################ -/

theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero n W)))

theorem pcc_thm_inst4 (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) := by
  have h0 : Prf (provFromCode (formCode (forall_4 φ))) := repr_pos'_prf h
  have h1 : Prf (provFromCode (substfc zero w₁ (formCode (forall_3 φ)))) :=
    prf_mp (pcc_forallElim_code_open (formCode (forall_3 φ)) w₁) h0
  have h2 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₁)
      (formCode (forall_2 φ))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₁ (formCode (forall_2 φ)))) h1
  have h3 : Prf (provFromCode (substfc zero w₂ (substfc (numeral 1) (liftc zero w₁)
      (formCode (forall_2 φ))))) :=
    prf_mp (pcc_forallElim_code_open _ w₂) h2
  have h4 : Prf (provFromCode (substfc zero w₂ (forallc (substfc (numeral 2)
      (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 1) (liftc zero w₁) (forallc (formCode φ))))) h3
  have h5 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₂)
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₂
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ))))) h4
  have h6 : Prf (provFromCode (substfc zero w₃ (substfc (numeral 1) (liftc zero w₂)
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (pcc_forallElim_code_open _ w₃) h5
  have h7 : Prf (provFromCode (substfc zero w₃ (substfc (numeral 1) (liftc zero w₂)
      (forallc (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁)))
        (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 2) (liftc zero (liftc zero w₁)) (formCode φ))))) h6
  have h8 : Prf (provFromCode (substfc zero w₃ (forallc (substfc (numeral 2)
      (liftc zero (liftc zero w₂))
      (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 1) (liftc zero w₂)
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) h7
  have h9 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₃
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) h8
  exact prf_mp (pcc_forallElim_code_open _ w₄) h9

theorem pcc_axiom_inst4 (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_thm_inst4 φ (prf_ax hmem) w₁ w₂ w₃ w₄

theorem pcc_congr_substfcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) := by
  let Ac : Term := eqc (substfcT A B X) (substfcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A B X) (substfcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A B X)
      (substfcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B X)
        (prf_congr_substfcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
        (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ### §9.1 · CASO `bottom` -/

def AXBOT_BODY : Formula := substfc (.var 1) (.var 0) botc =eq botc

theorem AXBOT_BODY_ok : ax_substfc_bottom = forall_2 AXBOT_BODY := rfl

theorem pcc_substfc_bottom_dot (v s : Term) :
    Prf (provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (numeral 1) W1 (formCode AXBOT_BODY)
      =eq eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_substfc_arith_open 1 W1 AXBOT_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)
      =eq eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_congr_eqCodeFn (prf_congr_substfcT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0 (eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2))
        (nulT 2))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_nulT 2 W0)
    refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
    exact prf_congr_substfcT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
      (prf_substtc_nulT 2 W0)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (formCode AXBOT_BODY))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 AXBOT_BODY (show ax_substfc_bottom ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s))

theorem paso2_caso_bottom (v s : Term) :
    Prf (provFromCode (evalSubstfcCode v s botc)) := by
  unfold evalSubstfcCode
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn botc))
      =eq substfcT (tcFn v) (tcFn s) (tcFn botc)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)
  have iB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (nulT 2))
      =eq substfcT (tcFn v) (tcFn s) (nulT 2)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_nulT 2)
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn botc))
      (substfcT (tcFn v) (tcFn s) (nulT 2)))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn botc) (nulT 2)
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)) (pcc_dot_nul_symm 2)
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) :=
    pcc_substfc_bottom_dot v s
  have h3 : Prf (provFromCode (eqc (nulT 2) (tcFn botc))) := pcc_dot_nul 2
  have h4 : Prf (provFromCode (eqc (tcFn botc) (tcFn (substfc v s botc)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_bottom v s)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn botc))
  exact pcc_eq_trans_code _ _ _ iA h1
    (pcc_eq_trans_code _ _ _ iB h2
      (pcc_eq_trans_code _ _ _ (substtc_inv_nulT 2) h3 h4))

/-- **`CasoBot` DESCARGADO** (Leibniz desde la forma ecuacional). -/
theorem casoBot : CasoBot := by
  intro v s X
  refine prf_deduction ?_
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm (prfH_hyp_self (shapeNul X 2)))
    (prf_to_prfH (paso2_caso_bottom v s) _)

/-! ### §9.2 · CASO BINARIO (`implc`/`andc`/`orc`) -/

def binct (T a b : Term) : Term := cons T (cons a (cons b nil))

def AXBIN_BODY (T : Term) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

theorem AXBIN_impl : ax_substfc_impl = forall_4 (AXBIN_BODY (numeralM 5)) := rfl
theorem AXBIN_and : ax_substfc_and = forall_4 (AXBIN_BODY (numeralM 7)) := rfl
theorem AXBIN_or : ax_substfc_or = forall_4 (AXBIN_BODY (numeralM 8)) := rfl

theorem pcc_substfc_bin_dot (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (hmem : forall_4 (AXBIN_BODY T) ∈ axioms) (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
      (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXBIN_BODY T))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 (AXBIN_BODY T)
  rw [hkc] at hin0
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
        (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _)))
  have k2v : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have k2s : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hs2
  have k21 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1))
      (prf_gnum_lt (show (1 : Nat) < 2 by omega))
  have k20 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 2 by omega))
  have hmid2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k20)
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k10)
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXBIN_BODY T)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 (AXBIN_BODY T) hmem (tcFn v) (tcFn s) (tcFn a) (tcFn b))

/-- **PIEZA NUEVA**: `SubstfcPlanos.paso2_caso_bin` reescrito en forma IMPLICACION
    (`PrfH Γ`), porque en la induccion la HI llega como HIPOTESIS, no como `Prf` cerrada. -/
theorem paso2_caso_bin_imp (k : Nat) (v s a b : Term)
    (hax : Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : Prf (substfc v s (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))) :
    Prf (Formula.impl (land (targetSubstfc v s a) (targetSubstfc v s b))
      (targetSubstfc v s (cons (numeralM k) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (targetSubstfc v s a) (targetSubstfc v s b))
  have hA : PrfH [land (targetSubstfc v s a) (targetSubstfc v s b)]
      (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)))) :=
    PrfH_and_elim_left hh
  have hB : PrfH [land (targetSubstfc v s a) (targetSubstfc v s b)]
      (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b)))) :=
    PrfH_and_elim_right hh
  have iSA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn a))
      =eq substfcT (tcFn v) (tcFn s) (tcFn a)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn a)
  have iSB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn b))
      =eq substfcT (tcFn v) (tcFn s) (tcFn b)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn b)
  have iX0 : ∀ W, Prf (substtc zero W
        (substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM k) (cons a (cons b nil)))))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM k) (cons a (cons b nil))))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM k) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT iSA iSB
  have iX3 : ∀ W, Prf (substtc zero W (binT k (tcFn (substfc v s a))
        (substfcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substfc v s a)) iSB
  have iX4 : ∀ W, Prf (substtc zero W (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b)))
      =eq binT k (tcFn (substfc v s a)) (tcFn (substfc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substfc v s a)) (substtc_inv_tcFn (substfc v s b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s)
      (tcFn (cons (numeralM k) (cons a (cons b nil)))) (binT k (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM k) (cons a (cons b nil)))))
    (pcc_dot_bin_symm k a b)) [land (targetSubstfc v s a) (targetSubstfc v s b)]
  have h2 := prf_to_prfH hax [land (targetSubstfc v s a) (targetSubstfc v s b)]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code k
      (substfcT (tcFn v) (tcFn s) (tcFn b))
      (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)) iSB iSA) _) hA
  have h4 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code k (tcFn (substfc v s a))
      (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b))
      (substtc_inv_tcFn (substfc v s a)) iSB) _) hB
  have h5 := prf_to_prfH (pcc_dot_bin k (substfc v s a) (substfc v s b))
    [land (targetSubstfc v s a) (targetSubstfc v s b)]
  have h6 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))))
    [land (targetSubstfc v s a) (targetSubstfc v s b)]
  exact PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6))))

/-- **`CasoBin k` DESCARGADO**, generico en el tag. -/
theorem casoBin_gen (k : Nat)
    (hax : ∀ v s a b : Term, Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : ∀ v s a b : Term, Prf (substfc v s (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))) :
    CasoBin k := by
  intro v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (shapeBin X k)
    (land (targetSubstfc v s (nthc X (numeralM 1))) (targetSubstfc v s (nthc X (numeralM 2)))))
  have hshape := PrfH_and_elim_left hh
  have hab := PrfH_and_elim_right hh
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (paso2_caso_bin_imp k v s (nthc X (numeralM 1)) (nthc X (numeralM 2))
      (hax v s (nthc X (numeralM 1)) (nthc X (numeralM 2)))
      (hobj v s (nthc X (numeralM 1)) (nthc X (numeralM 2)))) _) hab
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

theorem casoBin5 : CasoBin 5 :=
  casoBin_gen 5
    (fun v s a b => pcc_substfc_bin_dot (numeralM 5) (fun c => liftTerm_numeralM c 5)
      (show ax_substfc_impl ∈ axioms by simp [axioms]) v s a b)
    (fun v s a b => prf_substfc_impl v s a b)

theorem casoBin7 : CasoBin 7 :=
  casoBin_gen 7
    (fun v s a b => pcc_substfc_bin_dot (numeralM 7) (fun c => liftTerm_numeralM c 7)
      (show ax_substfc_and ∈ axioms by simp [axioms]) v s a b)
    (fun v s a b => prf_substfc_and v s a b)

theorem casoBin8 : CasoBin 8 :=
  casoBin_gen 8
    (fun v s a b => pcc_substfc_bin_dot (numeralM 8) (fun c => liftTerm_numeralM c 8)
      (show ax_substfc_or ∈ axioms by simp [axioms]) v s a b)
    (fun v s a b => prf_substfc_or v s a b)

/-- **EL TEOREMA CON CUATRO HIPOTESIS MENOS**: quedan `CasoAtom`, `CasoEq`,
    `CasoUn 6`, `CasoUn 9` y `HasWitLift`. -/
theorem pcc_eval_substfc_modulo_5
    (hatom : CasoAtom) (heq : CasoEq) (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  pcc_eval_substfc_modulo_8 casoBot hatom heq casoBin5 casoBin7 casoBin8 h6 h9 hwl
    wF wT v s f hws hfc

/-! ############################################################################
    ## §10 · DESCARGA de `HasWitLift` — copia LITERAL de
       `sondeos/ClausuraLiftSinWTs.lean` §3-§4 (`prf_lenc_liftsc`, `prf_nthc_liftsc`,
       `prf_In_liftsc`, `prf_argsIn_lift`, `prf_isTermCodeE1_lift`, `prf_wfAll1_lift`,
       `prf_isTC1_lift`) mas `CRIT_hasWit_lift`.
    ############################################################################ -/

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prf₀.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prf₀.j2 A B)

theorem prf_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) [])) rfl

theorem prf_congr_nthc_lst {w₁ w₂ : Term} (i : Term) (h : Prf (w₁ =eq w₂)) :
    Prf (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) [])) rfl

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


/-- **`HasWitLift` DESCARGADO** (`SinWTs.CRIT_hasWit_lift`). -/
theorem casoHasWitLift : HasWitLift := by
  intro c
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

/-- **EL TEOREMA CON CINCO HIPOTESIS MENOS**: quedan SOLO `CasoAtom`, `CasoEq`,
    `CasoUn 6` y `CasoUn 9` — los CUATRO constructores de `substfc` que no estaban
    disponibles en la forma IMPLICACION que la induccion consume. -/
theorem pcc_eval_substfc_modulo_4
    (hatom : CasoAtom) (heq : CasoEq) (h6 : CasoUn 6) (h9 : CasoUn 9)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  pcc_eval_substfc_modulo_8 casoBot hatom heq casoBin5 casoBin7 casoBin8 h6 h9
    casoHasWitLift wF wT v s f hws hfc

/-! ############################################################################
    ## §11 · DESCARGA de `CasoEq` y `CasoAtom` — LO QUE **NO** EXISTIA.

    Ni `pcc_substfc_eq_dot` ni `pcc_substfc_atom_dot` estaban en `sondeos/` ni en
    produccion (grep sobre el arbol entero: cero apariciones). Lo que si existia es la
    parte de TERMINO (`SFsubsttc.DESCENSO_imp` / `DESCENSO_lista_imp`, copiadas arriba).

    EL PUENTE «del testigo de FORMULA sale el testigo de TERMINO para sus subcodigos»
    NO HACE FALTA: se DISUELVE por construccion. La guarda `isFC1 wF wT c` lleva DENTRO
    `wfAll1 wT`, y las clausulas `clEq`/`clAtom` piden `In (nthc X i) wT` / `argsIn wT ...`
    — que es LITERALMENTE `SFsubsttc.isTC1 wT (nthc X i)` y la premisa de
    `DESCENSO_lista_imp`. Los puentes `:= rfl` de abajo lo certifican.
    ############################################################################ -/

theorem bridge_wfAll1 (w : Term) : SFsubsttc.wfAll1 w = wfAll1 w := rfl
theorem bridge_isTC1 (w c : Term) : SFsubsttc.isTC1 w c = isTC1 w c := rfl
theorem bridge_argsIn (w Y : Term) : SFsubsttc.argsIn w Y = argsIn w Y := rfl
theorem bridge_hasWit (c : Term) : SFsubsttc.hasWit c = hasWit c := rfl
theorem bridge_isTermCodeE1 (w X : Term) :
    SFsubsttc.isTermCodeE1 w X = isTermCodeE1 w X := rfl

/-- La evaluacion provable de `substtc`, en forma IMPLICACION y SIN hipotesis. -/
theorem eval_substtc_imp (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (SFsubsttc.targetSubsttc v s t)) :=
  SFsubsttc.DESCENSO_imp SFsubsttc.predHyp w v s t

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem eval_substtsc_imp (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (SFsubsttc.targetSubsttsc v s t)) :=
  SFsubsttc.DESCENSO_lista_imp SFsubsttc.predHyp w v s t

/-! ### §11.1 · La funcion ternaria GENERICA (para escribir UN solo lema `dot`) -/

def gO (nm : String) (v s f : Term) : Term := Term.func nm [v, s, f]
def gT (nm : String) (v s f : Term) : Term :=
  funcc (strCode nm) (cons v (cons s (cons f nil)))

theorem gO_substfc (v s f : Term) : gO "substfc" v s f = substfc v s f := rfl
theorem gO_substtc (v s f : Term) : gO "substtc" v s f = substtc v s f := rfl
theorem gO_substtsc (v s f : Term) : gO "substtsc" v s f = substtsc v s f := rfl
theorem gT_substfcT (v s f : Term) : gT "substfc" v s f = substfcT v s f := rfl
theorem gT_substtcT (v s f : Term) : gT "substtc" v s f = SFsubsttc.substtcT v s f := rfl
theorem gT_substtscT (v s f : Term) : gT "substtsc" v s f = SFsubsttc.substtscT v s f := rfl

theorem prf_congr_gT (nm : String) {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (gT nm v s f =eq gT nm v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_gT (nm : String) (v W x y z : Term) :
    Prf (substtc v W (gT nm x y z)
      =eq gT nm (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode nm) x y z

theorem substtc_inv_gT (nm : String) {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (gT nm X Y Z) =eq gT nm X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_gT nm zero W X Y Z) (prf_congr_gT nm (hX W) (hY W) (hZ W))

/-! ### §11.2 · `pcc_substfc_ter_dot` — la instancia INTERNA de un axioma
    `substfc v s (⟨T⟩ a b) ≐ ⟨T⟩ (F v s a) (F v s b)` con `F` GENERICA.
    Con `F = substfc` reproduce `pcc_substfc_bin_dot`; con `F = substtc` da `eqc`. -/

def AXTER_BODY (T : Term) (nm : String) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (gO nm (.var 3) (.var 2) (.var 1)) (gO nm (.var 3) (.var 2) (.var 0))

theorem AXTER_eq : ax_substfc_eq = forall_4 (AXTER_BODY (numeralM 4) "substtc") := rfl
theorem AXTER_impl : ax_substfc_impl = forall_4 (AXTER_BODY (numeralM 5) "substfc") := rfl

theorem pcc_substfc_ter_dot (T : Term) (nm : String) (hT : ∀ c : Nat, liftTerm c T = T)
    (hmem : forall_4 (AXTER_BODY T nm) ∈ axioms) (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
      (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
        (gT nm (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXTER_BODY T nm))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (gT nm W3 (varc (numeral 2)) (varc (numeral 1)))
          (gT nm W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 (AXTER_BODY T nm)
  rw [hkc] at hin0
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm W3 (varc (numeral 2)) (varc (numeral 1)))
          (gT nm W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_congr_gT nm hv3 (prf_refl _) (prf_refl _))
        (prf_congr_gT nm hv3 (prf_refl _) (prf_refl _)))
  have k2v : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have k2s : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hs2
  have k21 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1))
      (prf_gnum_lt (show (1 : Nat) < 2 by omega))
  have k20 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 2 by omega))
  have hmid2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (varc (numeral 1)))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 2) W2 _ _ _)
          (prf_congr_gT nm k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 2) W2 _ _ _)
          (prf_congr_gT nm k2v k2s k20)
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (varc (numeral 1)))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 1) W1 _ _ _)
          (prf_congr_gT nm k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 1) W1 _ _ _)
          (prf_congr_gT nm k1v k1s k10)
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_gT nm zero W0 _ _ _)
          (prf_congr_gT nm k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_gT nm zero W0 _ _ _)
          (prf_congr_gT nm k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXTER_BODY T nm)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 (AXTER_BODY T nm) hmem (tcFn v) (tcFn s) (tcFn a) (tcFn b))

/-! ### §11.3 · `pcc_substfc_atom_dot` — el axioma `atomc`, cuya PRIMERA casilla
    (el simbolo de predicado) es OPACA y no se toca. -/

def AXATOM_BODY : Formula :=
  substfc (.var 3) (.var 2) (binct (numeralM 3) (.var 1) (.var 0))
    =eq binct (numeralM 3) (.var 1) (gO "substtsc" (.var 3) (.var 2) (.var 0))

theorem AXATOM_ok : ax_substfc_atom = forall_4 AXATOM_BODY := rfl

theorem pcc_substfc_atom_dot (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT 3 (tcFn a) (tcFn b)))
      (binT 3 (tcFn a) (SFsubsttc.substtscT (tcFn v) (tcFn s) (tcFn b))))) := by
  let T : Term := numeralM 3
  have hT : ∀ c : Nat, liftTerm c T = T := fun c => liftTerm_numeralM c 3
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode AXATOM_BODY)
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (varc (numeral 1))
          (gT "substtsc" W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 AXATOM_BODY
  rw [hkc] at hin0
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_refl _) (prf_congr_gT _ hv3 (prf_refl _) (prf_refl _)))
  have k2v : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have k2s : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hs2
  have k21 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1))
      (prf_gnum_lt (show (1 : Nat) < 2 by omega))
  have k20 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 2 by omega))
  have hmid2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK k21 ?_
      exact prf_eq_trans (prf_substtc_gT _ (numeral 2) W2 _ _ _)
        (prf_congr_gT _ k2v k2s k20)
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (tcFn a)
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK k1a ?_
      exact prf_eq_trans (prf_substtc_gT _ (numeral 1) W1 _ _ _)
        (prf_congr_gT _ k1v k1s k10)
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (tcFn a)
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (tcFn a) (gT "substtsc" (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK k0a ?_
      exact prf_eq_trans (prf_substtc_gT _ zero W0 _ _ _) (prf_congr_gT _ k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode AXATOM_BODY))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (tcFn a) (gT "substtsc" (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 AXATOM_BODY (show ax_substfc_atom ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn a) (tcFn b))

/-! ### §11.4 · Los DOS ensamblajes, en forma IMPLICACION -/

theorem caso_eq_core (v s a b : Term) :
    Prf (Formula.impl
      (land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b))
      (targetSubstfc v s (cons (numeralM 4) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self
    (land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b))
  have hA : PrfH [land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b)]
      (provFromCode (eqc (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn a))
        (tcFn (substtc v s a)))) := PrfH_and_elim_left hh
  have hB : PrfH [land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b)]
      (provFromCode (eqc (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b))
        (tcFn (substtc v s b)))) := PrfH_and_elim_right hh
  have iX0 : ∀ W, Prf (substtc zero W
        (substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 4) (cons a (cons b nil)))))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 4) (cons a (cons b nil))))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 4) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT 4 (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT 4 (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W (binT 4 (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn a))
        (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT 4 (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn a))
        (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (SFsubsttc.invA v s a) (SFsubsttc.invA v s b)
  have iX3 : ∀ W, Prf (substtc zero W (binT 4 (tcFn (substtc v s a))
        (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT 4 (tcFn (substtc v s a)) (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substtc v s a)) (SFsubsttc.invA v s b)
  have iX4 : ∀ W, Prf (substtc zero W (binT 4 (tcFn (substtc v s a)) (tcFn (substtc v s b)))
      =eq binT 4 (tcFn (substtc v s a)) (tcFn (substtc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substtc v s a)) (substtc_inv_tcFn (substtc v s b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s)
      (tcFn (cons (numeralM 4) (cons a (cons b nil)))) (binT 4 (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 4) (cons a (cons b nil)))))
    (pcc_dot_bin_symm 4 a b))
    [land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b)]
  have h2 := prf_to_prfH (pcc_substfc_ter_dot (numeralM 4) "substtc"
      (fun c => liftTerm_numeralM c 4)
      (show ax_substfc_eq ∈ axioms by simp [axioms]) v s a b)
    [land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b)]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code 4
      (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b))
      (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substtc v s a))
      (SFsubsttc.invA v s b) (SFsubsttc.invA v s a)) _) hA
  have h4 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 4 (tcFn (substtc v s a))
      (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtc v s b))
      (substtc_inv_tcFn (substtc v s a)) (SFsubsttc.invA v s b)) _) hB
  have h5 := prf_to_prfH (pcc_dot_bin 4 (substtc v s a) (substtc v s b))
    [land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b)]
  have h6 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_eq v s a b)))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM 4) (cons (substtc v s a) (cons (substtc v s b) nil))))))
    [land (SFsubsttc.targetSubsttc v s a) (SFsubsttc.targetSubsttc v s b)]
  exact PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6))))

theorem caso_atom_core (v s a b : Term) :
    Prf (Formula.impl (SFsubsttc.targetSubsttsc v s b)
      (targetSubstfc v s (cons (numeralM 3) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hB : PrfH [SFsubsttc.targetSubsttsc v s b]
      (provFromCode (eqc (SFsubsttc.substtscT (tcFn v) (tcFn s) (tcFn b))
        (tcFn (substtsc v s b)))) := prfH_hyp_self _
  have iX0 : ∀ W, Prf (substtc zero W
        (substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 3) (cons a (cons b nil)))))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 3) (cons a (cons b nil))))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 3) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT 3 (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT 3 (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W
        (binT 3 (tcFn a) (SFsubsttc.substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT 3 (tcFn a) (SFsubsttc.substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn a) (SFsubsttc.invAs v s b)
  have iX3 : ∀ W, Prf (substtc zero W (binT 3 (tcFn a) (tcFn (substtsc v s b)))
      =eq binT 3 (tcFn a) (tcFn (substtsc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn (substtsc v s b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s)
      (tcFn (cons (numeralM 3) (cons a (cons b nil)))) (binT 3 (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 3) (cons a (cons b nil)))))
    (pcc_dot_bin_symm 3 a b)) [SFsubsttc.targetSubsttsc v s b]
  have h2 := prf_to_prfH (pcc_substfc_atom_dot v s a b) [SFsubsttc.targetSubsttsc v s b]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 3 (tcFn a)
      (SFsubsttc.substtscT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtsc v s b))
      (substtc_inv_tcFn a) (SFsubsttc.invAs v s b)) _) hB
  have h4 := prf_to_prfH (pcc_dot_bin 3 a (substtsc v s b)) [SFsubsttc.targetSubsttsc v s b]
  have h5 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_atom v s a b)))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM 3) (cons a (cons (substtsc v s b) nil))))))
    [SFsubsttc.targetSubsttsc v s b]
  exact PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4 h5)))

/-! ### §11.5 · `CasoEq` y `CasoAtom`, DESCARGADOS -/

theorem casoEq : CasoEq := by
  intro wT v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (wfAll1 wT) (land (shapeBin X 4)
    (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))))
  have hwT := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hin1 := PrfH_and_elim_left (PrfH_and_elim_right hR)
  have hin2 := PrfH_and_elim_right (PrfH_and_elim_right hR)
  -- la evaluacion de TERMINO entra como LEMA EXTERNO sobre los DOS subcodigos
  have hTA := PrfH.mp _ _ _
    (prf_to_prfH (eval_substtc_imp wT v s (nthc X (numeralM 1))) _)
    (PrfH_and_intro hwT hin1)
  have hTB := PrfH.mp _ _ _
    (prf_to_prfH (eval_substtc_imp wT v s (nthc X (numeralM 2))) _)
    (PrfH_and_intro hwT hin2)
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (caso_eq_core v s (nthc X (numeralM 1)) (nthc X (numeralM 2))) _)
    (PrfH_and_intro hTA hTB)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

theorem casoAtom : CasoAtom := by
  intro wT v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (wfAll1 wT) (land (shapeBin X 3)
    (argsIn wT (nthc X (numeralM 2)))))
  have hwT := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hargs := PrfH_and_elim_right hR
  have hTB := PrfH.mp _ _ _
    (prf_to_prfH (eval_substtsc_imp wT v s (nthc X (numeralM 2))) _)
    (PrfH_and_intro hwT hargs)
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (caso_atom_core v s (nthc X (numeralM 1)) (nthc X (numeralM 2))) _) hTB
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

/-- **EL TEOREMA CON SIETE HIPOTESIS MENOS**: quedan SOLO `CasoUn 6` y `CasoUn 9`
    (`forallc` y `exc`), los DOS unicos constructores con `liftc` en el sustituyendo. -/
theorem pcc_eval_substfc_modulo_2 (h6 : CasoUn 6) (h9 : CasoUn 9)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  pcc_eval_substfc_modulo_8 casoBot casoAtom casoEq casoBin5 casoBin7 casoBin8 h6 h9
    casoHasWitLift wF wT v s f hws hfc

/-! ############################################################################
    ## §12 · DESCARGA de `CasoUn 6` (`forallc`) y `CasoUn 9` (`exc`).

    `Paso2.paso2_caso_un_guarded` existe (`sondeos/SubstfcEx.lean:4307`) pero pide la HI
    como `Prf` CERRADA (`hIH : Prf (hasWit (liftc 0 s) ⇒ ...)`), y dentro del paso
    inductivo la HI llega como HIPOTESIS del contexto. Aqui va la MISMA prueba con la HI
    ya aplicada, como CONJUNTO de la premisa: `paso2_caso_un_conj`.
    ############################################################################ -/

theorem bridge_substfcT_Paso2 (v s f : Term) : Paso2.substfcT v s f = substfcT v s f := rfl
theorem bridge_evalSubstfcCode_Paso2 (v s f : Term) :
    Paso2.evalSubstfcCode v s f = evalSubstfcCode v s f := rfl
theorem bridge_hasWit_SinWTs (c : Term) : SinWTs.hasWit c = hasWit c := rfl
theorem bridge_hasWit_DescMutua (c : Term) : DescMutua.hasWit c = hasWit c := rfl
theorem bridge_isTC1_SinWTs (w c : Term) : SinWTs.isTC1 w c = isTC1 w c := rfl

/-- El DESCENSO de `liftc` (`DescMutua.DESCENSO_hasWit`), en los simbolos de este fichero. -/
theorem DESCENSO_hasWit_local (s : Term) :
    Prf (Formula.impl (hasWit s)
      (provFromCode (eqc (Paso2.liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))) :=
  DescMutua.DESCENSO_hasWit s

/-- **`paso2_caso_un_guarded` con la HI como CONJUNTO** (no como `Prf` cerrada).
    Prueba identica a `sondeos/SubstfcEx.lean:4307`, salvo que `hIHg` se lee del contexto
    en vez de obtenerse por MP con `CRIT_hasWit_lift`. -/
theorem paso2_caso_un_conj (m : Nat) (hmem : forall_3 (Paso2.AXBODY m) ∈ axioms)
    (hobj : ∀ v s a : Term,
      Prf (substfc v s (Paso2.unc m a) =eq Paso2.unc m (substfc (succ v) (liftc zero s) a)))
    (v s f : Term) :
    Prf (Formula.impl (land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f))
      (targetSubstfc v s (Paso2.unc m f))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f))
  have hg : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)] (hasWit s) :=
    PrfH_and_elim_left hh
  have hIHg : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))
        (tcFn (substfc (succ v) (liftc zero s) f)))) := PrfH_and_elim_right hh
  have hLift : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc (Paso2.liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_hasWit_local s) _) hg
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (Paso2.liftcT (termCode zero) (tcFn s))
      =eq Paso2.liftcT (termCode zero) (tcFn s)) :=
    Paso2.substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (Paso2.unc m f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (Paso2.unc m f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (Paso2.unc m f))
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (Paso2.unc m f)))
      (unT m (substfcT (succcT (tcFn v)) (Paso2.liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    Paso2.fuego_ab_un m hmem v s f
  have h2 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (substfcT (tcFn v) (tcFn s) (tcFn (Paso2.unc m f)))
        (unT m (substfcT (tcFn (succ v)) (Paso2.liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1) _
  have h3 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (unT m (substfcT (tcFn (succ v)) (Paso2.liftcT (termCode zero) (tcFn s)) (tcFn f)))
        (unT m (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code m _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (Paso2.pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (Paso2.liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) _) hLift)
  have h4 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (unT m (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
        (unT m (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code m _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) _) hIHg
  have h5 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (unT m (tcFn (substfc (succ v) (liftc zero s) f)))
        (tcFn (Paso2.unc m (substfc (succ v) (liftc zero s) f))))) :=
    prf_to_prfH (pcc_dot_un m (substfc (succ v) (liftc zero s) f)) _
  have h6 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (tcFn (Paso2.unc m (substfc (succ v) (liftc zero s) f)))
        (tcFn (substfc v s (Paso2.unc m f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (hobj v s f)))))
      (prf_provFromCode_eqCodeFn_refl
        (tcFn (Paso2.unc m (substfc (succ v) (liftc zero s) f))))) _
  exact PrfH_eq_trans_code _ _ _ iA h2
    (PrfH_eq_trans_code _ _ _
      (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL
        (substtc_inv_tcFn f)))
      h3
      (PrfH_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v))
          (substtc_inv_tcFn (liftc zero s)) (substtc_inv_tcFn f)))
        h4
        (PrfH_eq_trans_code _ _ _
          (substtc_inv_unT (substtc_inv_tcFn (substfc (succ v) (liftc zero s) f)))
          h5 h6)))

/-- **`CasoUn m` DESCARGADO**, generico en el tag. -/
theorem casoUn_gen (m : Nat) (hmem : forall_3 (Paso2.AXBODY m) ∈ axioms)
    (hobj : ∀ v s a : Term,
      Prf (substfc v s (Paso2.unc m a) =eq Paso2.unc m (substfc (succ v) (liftc zero s) a))) :
    CasoUn m := by
  intro v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (hasWit s) (land (shapeUn X m)
    (targetSubstfc (succ v) (liftc zero s) (nthc X (numeralM 1)))))
  have hws := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hIH := PrfH_and_elim_right hR
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (paso2_caso_un_conj m hmem hobj v s (nthc X (numeralM 1))) _)
    (PrfH_and_intro hws hIH)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

theorem casoUn6 : CasoUn 6 := casoUn_gen 6 Paso2.mem6 prf_substfc_forall
theorem casoUn9 : CasoUn 9 := casoUn_gen 9 Paso2.mem9 prf_substfc_ex

/-! ############################################################################
    ## §13 · **`pcc_eval_substfc` — SIN NINGUNA HIPOTESIS**
    ############################################################################ -/

/-- **EL DESCENSO COMPLETO**, sin hipotesis colgando. -/
theorem DESCENSO_substfc (wF wT v s t : Term) :
    Prf (Formula.impl (GUARD wF wT s t) (targetSubstfc v s t)) :=
  DESCENSO_imp casoBot casoAtom casoEq casoBin5 casoBin7 casoBin8 casoUn6 casoUn9
    casoHasWitLift wF wT v s t

/-- **★ `pcc_eval_substfc` ★** — la evaluacion PROVABLE de `substfc` con `v`, `s`, `f`
    **ABSTRACTOS**, guardada por los DOS testigos (formula `wF` y termino `wT`).
    CERO axiomas de Lean, cero `sorry`, cero hipotesis. -/
theorem pcc_eval_substfc (wF wT v s f : Term)
    (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  prf_mp (DESCENSO_substfc wF wT v s f) (prf_and_intro hws hfc)

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

/-- **`pcc_eval_substfc` con los DOS testigos CUANTIFICADOS** (la forma que consume
    el reflector rio abajo: ninguna lista testigo aparece en el enunciado). -/
theorem pcc_eval_substfc_wit (v s f : Term) :
    Prf (Formula.impl (land (hasWit s) (hasWitF f)) (targetSubstfc v s f)) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (hasWit s) (hasWitF f))
  have hwf : PrfH [land (hasWit s) (hasWitF f)]
      (Formula.ex (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 f))))) :=
    PrfH_and_elim_right hh
  refine PrfH_ex_elim hwf ?_
  rw [liftF_targetSubstfc]
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  rw [liftF_targetSubstfc]
  refine PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_substfc (.var 1) (.var 0)
      (liftTerm 0 (liftTerm 0 v)) (liftTerm 0 (liftTerm 0 s))
      (liftTerm 0 (liftTerm 0 f))) _)
    (PrfH_and_intro ?_ ?_)
  · rw [← liftF_hasWit, ← liftF_hasWit]
    exact PrfH_and_elim_left
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · exact PrfH.hyp _ _ (List.Mem.head _)

/-! ### CONTROLES NEGATIVOS -/

set_option linter.unusedVariables false in
/-- El objetivo NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- El predicado de FORMULA NO es el de TERMINO con las listas fusionadas. -/
example (wF wT X : Term) : True := by
  fail_if_success exact (rfl : isFormCodeE2 wF wT X = isTermCodeE1 wT X)
  trivial

/-- La guarda de FORMULA lleva DENTRO la guarda de TERMINO que pide `pcc_eval_substtc'`
    — la mitad `wfAll1 wT` es LITERALMENTE la de `sondeos/EvalSubsttc.lean`. -/
example (wF wT c : Term) :
    isFC1 wF wT c = land (land (wfAll1 wT) (wfAllF wF wT)) (In c wF) := rfl

/-- Y de la guarda de FORMULA sale, por `rfl`, el `isTC1` que consume `pcc_eval_substtc'`
    en cuanto se tiene la pertenencia del SUBcodigo a `wT`. -/
example (wT z : Term) : isTC1 wT z = land (wfAll1 wT) (In z wT) := rfl

end ENS

end S_Ens

/-! ############################################################################
    ## §HW · EL TRANSPORTE: de TRES listas testigo (P1, `prf_isFCB3_of`) a DOS
       (`ENS.isFC1`), en forma ECUACIONAL.

    Objetivo: `prf_isFC1_real` / `prf_hasWitF_real` — la guarda de FORMULA de
    `ENS.pcc_eval_substfc` es SATISFACIBLE por codigos REALES, con testigos
    EXPLICITOS y COMPUTABLES (`fcodesF phi`, `tcodesF phi`).

    La tercera lista de P1 (`flcodes`, codigos de LISTA DE ARGUMENTOS) NO aparece:
    su papel lo juega `ENS.argsIn wT` dentro de `ENS.clAtom` — un `∀` acotado sobre
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

    (Regla del proyecto: misma definicion en dos namespaces son DOS constantes.
     Estos puentes certifican que aqui coinciden, y salen net-0.) -/

theorem bridge_argsIn (w Y : Term) : SinWTs.argsIn w Y = ENS.argsIn w Y := rfl
theorem bridge_isTermCodeE1 (w X : Term) :
    SinWTs.isTermCodeE1 w X = ENS.isTermCodeE1 w X := rfl
theorem bridge_wfAll1 (w : Term) : SinWTs.wfAll1 w = ENS.wfAll1 w := rfl
theorem bridge_shapeUn (X : Term) (k : Nat) : SinWTs.shapeUn X k = ENS.shapeUn X k := rfl
theorem bridge_shapeBin (X : Term) (k : Nat) : SinWTs.shapeBin X k = ENS.shapeBin X k := rfl

/-! ## §HW.1 · LAS TRES ECUACIONES DE FORMA (`shapeNul`/`shapeUn`/`shapeBin`) SOBRE
       NODOS REALES. Aqui es donde la forma ECUACIONAL sale MAS BARATA que la
       posicional: una sola ecuacion, sin `consOk` ni `carc ≐ k̄` ni `lenc ≐ n̄`. -/

theorem prf_refl' (t : Term) : Prf (t =eq t) := Prf.incl (Prf₀.eqrefl t)

theorem prf_shapeNul_real (k : Nat) : Prf (ENS.shapeNul (cons (numeralM k) nil) k) :=
  prf_refl' _

theorem prf_shapeUn_real (k : Nat) (a : Term) :
    Prf (ENS.shapeUn (cons (numeralM k) (cons a nil)) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (SinWTs.prf_nthc_c1 (numeralM k) a nil)))

theorem prf_shapeBin_real (k : Nat) (a b : Term) :
    Prf (ENS.shapeBin (cons (numeralM k) (cons a (cons b nil))) k) :=
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
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orL (prf_shapeNul_real 2)

theorem node_atom (WF WT sp cts : Term) (hargs : Prf (SinWTs.argsIn WT cts)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 3) (cons sp (cons cts nil)))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orL (cl_atom_real WT sp cts hargs))

theorem node_eq (WF WT ca cb : Term) (ha : Prf (In ca WT)) (hb : Prf (In cb WT)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 4) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orL (cl_eq_real WT ca cb ha hb)))

theorem node_impl (WF WT ca cb : Term) (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 5) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orL (cl_bin_real WF 5 ca cb ha hb))))

theorem node_forall (WF WT ca : Term) (ha : Prf (In ca WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 6) (cons ca nil))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orL (cl_un_real WF 6 ca ha)))))

theorem node_and (WF WT ca cb : Term) (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 7) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orL (cl_bin_real WF 7 ca cb ha hb))))))

theorem node_or (WF WT ca cb : Term) (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 8) (cons ca (cons cb nil)))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
  exact SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR (SinWTs.prf_orR
    (SinWTs.prf_orR (SinWTs.prf_orL (cl_bin_real WF 8 ca cb ha hb)))))))

theorem node_ex (WF WT ca : Term) (ha : Prf (In ca WF)) :
    Prf (ENS.isFormCodeE2 WF WT (cons (numeralM 9) (cons ca nil))) := by
  simp only [ENS.isFormCodeE2, ENS.lorAll]
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
    Prf (ENS.wfAll1 (objList L)) := by
  have hWl : ∀ c : Nat, liftTerm c (objList L) = objList L := fun c =>
    SinWTs.liftTerm_objList c L (fun x hx => (hcl x hx).1 c)
  have hWs : ∀ (v : Nat) (s : Term), substTerm v s (objList L) = objList L := fun v s =>
    SinWTs.substTerm_objList v s L (fun x hx => (hcl x hx).2 v s)
  have hAI : ENS.wfAll1 (objList L)
      = Formula.forall (Formula.impl (lt (.var 0) (lenc (objList L)))
          (SinWTs.isTermCodeE1 (objList L) (nthc (objList L) (.var 0)))) := by
    simp only [ENS.wfAll1, ENS.wfAll1Body, lt, lenc, nthc, ENS.liftF_isTermCodeE1,
      liftTerm, liftTerms, hWl, bridge_isTermCodeE1]
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

theorem prf_wfAll1_real (phi : Formula) : Prf (ENS.wfAll1 (objList (tcodesF phi))) :=
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


/-! ## §HW.9 · EL PAGO RIO ABAJO: `pcc_eval_substfc` **SIN GUARDA** sobre codigos REALES.

    Aqui se ve que el teorema del muro NO era vacio: sobre `⌈φ⌉` (cualquier `φ`) y
    `⌈t⌉` (cualquier `t`) la guarda entera se descarga, y queda la evaluacion pelada. -/

theorem pcc_eval_substfc_REAL (v : Term) (t : Term) (phi : Formula) :
    Prf (provFromCode (eqc
      (ENS.substfcT (tcFn v) (tcFn (termCodeM t)) (tcFn (formCodeM phi)))
      (tcFn (substfc v (termCodeM t) (formCodeM phi))))) :=
  ENS.pcc_eval_substfc (objList (fcodesF phi)) (objList (tcodesF phi)) v
    (termCodeM t) (formCodeM phi) (SinWTs.CRIT_hasWit_real t) (prf_isFC1_real phi)

/-- La misma, pasando por la forma con los DOS testigos CUANTIFICADOS
    (`ENS.pcc_eval_substfc_wit`) — o sea, por `hasWitF`, no por `isFC1`. -/
theorem pcc_eval_substfc_wit_REAL (v : Term) (t : Term) (phi : Formula) :
    Prf (ENS.targetSubstfc v (termCodeM t) (formCodeM phi)) :=
  prf_mp (ENS.pcc_eval_substfc_wit v (termCodeM t) (formCodeM phi))
    (prf_and_intro (SinWTs.CRIT_hasWit_real t) (prf_hasWitF_real phi))

/-! ### CONTROLES NEGATIVOS — los enunciados no son reflexividades disfrazadas. -/

example : True := by
  fail_if_success exact (rfl : fcodesF Formula.bottom = [])
  trivial

example : True := by
  fail_if_success exact (rfl : tcodesF (Formula.eq (.var 0) (.var 1)) = [])
  trivial

/-- La guarda SIGUE discriminando: `isFC1` con un codigo de VARIABLE es REFUTABLE
    (`ENS.CRIT_isFC1_rejects_varc`), asi que `prf_isFC1_real` no la ha trivializado. -/
example (n : Term) : Prf (Formula.impl (ENS.isFC1 (objList (fcodesF Formula.bottom))
    (objList (tcodesF Formula.bottom)) (varc n)) Formula.bottom) :=
  ENS.CRIT_isFC1_rejects_varc _ _ n

/-! ### INSTANCIA NO TRIVIAL — ejercita a la vez `clUn 6`, `clBin 5`, `clAtom`
    (con `argsIn` sobre un termino COMPUESTO) y `clEq`. -/

def PHI_demo : Formula :=
  Formula.forall (Formula.impl
    (Formula.atom "P" [Term.func "f" [Term.var 0, Term.var 1]])
    (Formula.eq (Term.var 0) (Term.func "g" [Term.var 1])))

example : Prf (ENS.isFC1 (objList (fcodesF PHI_demo)) (objList (tcodesF PHI_demo))
    (formCodeM PHI_demo)) := prf_isFC1_real PHI_demo

example : Prf (ENS.hasWitF (formCodeM PHI_demo)) := prf_hasWitF_real PHI_demo

example (v t : Term) : Prf (ENS.targetSubstfc v (termCodeM t) (formCodeM PHI_demo)) :=
  pcc_eval_substfc_wit_REAL v t PHI_demo

end HW
end S_HW

#print axioms HW.prf_isFC1_real
#print axioms HW.prf_hasWitF_real
#print axioms HW.pcc_eval_substfc_REAL
#print axioms HW.pcc_eval_substfc_wit_REAL
#print axioms HW.bridge_isTermCodeE1
#print axioms HW.bridge_wfAll1
#print axioms HW.okF
#print axioms HW.okT_F
#check @HW.prf_isFC1_real
#check @HW.prf_hasWitF_real
#check @HW.pcc_eval_substfc_wit_REAL
#check @HW.fcodesF
#check @HW.tcodesF

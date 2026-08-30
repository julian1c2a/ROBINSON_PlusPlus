/-
# SF_ex — EL CASO `∃` DE `pcc_eval_substfc`, CON GUARDA — **Y FACTORIZADO CON EL `∀`**.
#
# ## RESULTADO PRINCIPAL
# `forall` y `ex` NO son dos pruebas: son UNA, parametrizada por el TAG.
#
#   Paso2.unc     m a  = cons (numeralM m) (cons a nil)        -- el ctor unario, generico
#   Paso2.AXBODY  m         -- el cuerpo comun de ax_substfc_forall / ax_substfc_ex
#   Paso2.unc6 / unc9       : unc 6 a = forallc a  /  unc 9 a = exc a          -- rfl
#   Paso2.AXBODY6 / AXBODY9 : ax_substfc_forall = forall_3 (AXBODY 6)
#                             ax_substfc_ex     = forall_3 (AXBODY 9)          -- rfl
#
#   P2G.paso2_caso_un_guarded (m) (hmem) (hobj) : el paso inductivo unario CON GUARDA
#   P2G.paso2_caso_forall_guarded_gen = paso2_caso_un_guarded 6 mem6 prf_substfc_forall
#   P2G.paso2_caso_ex_guarded         = paso2_caso_un_guarded 9 mem9 prf_substfc_ex   ★
#
# `CTRL_forall_reemplazable` certifica que la instancia en tag 6 tiene EXACTAMENTE el tipo
# del `paso2_caso_forall_guarded` original; `CTRL_tag_discrimina` y el CONTROL F
# (dos `fail_if_success`) certifican que la parametrizacion NO es cosmetica.
#
# ## HALLAZGO
# El espejo es PERFECTO (misma aridad `forall_3`, mismo orden de argumentos, misma forma
# en `prf_substfc_ex`). Todo el KIT unario de produccion (`unT`, `pcc_dot_un(_symm)`,
# `pcc_congr_unT_code`, `substtc_inv_unT`, `prf_substtc_unT_at`) YA era generico en el tag,
# y el DESCENSO (`DESCENSO_hasWit`) y `CRIT_hasWit_lift` son tag-INDEPENDIENTES (hablan del
# SUSTITUYENDO, no del constructor). La UNICA pieza nueva que exigio abstraer el tag es
# `Paso2.substCodeT_unc`: con `m` abstracto `substCodeT v w (numeralM m)` deja de reducir
# por `rfl` (con `m` literal si reduce). Es un artefacto de reduccion de Lean, no una
# asimetria matematica; se cierra con `substCodeT_closed` + `liftTerm_numeralM`.
#
# Fichero AUTOCONTENIDO. Copias LITERALES (sin editar una linea de sus pruebas) de:
#   * sondeos/ClausuraLiftSinWTs.lean  (namespace SinWTs)    -> hasWit, CRIT_hasWit_lift
#   * sondeos/DescensoLiftc.lean       (namespace DescMutua) -> targetLift, DESCENSO_hasWit
#   * sondeos/Paso2CasoForall.lean     (namespace Paso2)     -> el kit del PASO 2
#   * sondeos/Paso2Guardado.lean       (namespace P2G)       -> el caso `forall` con guarda
# Cada copia va en su propia `section` para que sus `open` no se contaminen entre si.
# Lo NUEVO de esta pasada: `Paso2` §GEN (al final de S_Paso2) y `P2G` §N.1-GEN / §N.4.
#
# CERO axiomas de Lean nuevos, cero `sorry`. Ninguna ecuacion de recursion de
# `substfcT`/`liftcT` se postula: son DEFINICIONES y nada mas.
#
#   lake env lean Probe/SF_ex.lean
-/
import ROBINSON_PlusPlus.Meta

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


/-! ############################################################################
    ## §NEW · EL PASO INDUCTIVO `∀` DE `pcc_eval_substfc`, **CON GUARDA**, TODO
    ##         EN `PrfH Γ` CON `Γ = [hasWit s]`.
    ##
    ## Las dos hipotesis que colgaban en `Paso2.paso2_caso_forall` (`hLift` y la
    ## guarda de la HI) se DESCARGAN de la guarda:
    ##   * `hLift`  ← `DescMutua.DESCENSO_hasWit s : Prf (hasWit s ⇒ targetLift s)`
    ##   * la guarda de la HI ← `SinWTs.CRIT_hasWit_lift s : Prf (hasWit s ⇒ hasWit (liftc 0 s))`
    ##
    ## El unico obstaculo real era que `pcc_eq_trans_code` toma sus eslabones como
    ## `Prf`. NO hizo falta helper nuevo: **`PrfH_eq_trans_code` YA ESTA EN PRODUCCION**
    ## (`Meta/EvalCarcNthcPrf.lean:66`, exportado a la raiz).
    ############################################################################ -/

section S_Nuevo

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

namespace P2G

open Paso2

/-! ### §N.0 · Los dos puentes por `rfl` entre los sondeos -/

/-- `hasWit` es LA MISMA formula en los dos sondeos (definiciones identicas). -/
theorem hasWit_bridge (c : Term) : SinWTs.hasWit c = DescMutua.hasWit c := rfl

/-- La guarda, con el nombre del enunciado diana. -/
abbrev hasWit (c : Term) : Formula := SinWTs.hasWit c

/-- `targetLift` de `DescMutua` es LITERALMENTE el `hLift` de `Paso2.paso2_caso_forall`
    (mismo `liftcT`, por `rfl`). -/
theorem targetLift_bridge (s : Term) :
    DescMutua.targetLift s
      = provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))) := rfl

/-- **DESCENSO_hasWit**, reexpresado en los simbolos que consume el PASO 2. -/
theorem DESCENSO_hasWit' (s : Term) :
    Prf (Formula.impl (hasWit s)
      (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))) :=
  DescMutua.DESCENSO_hasWit s

/-- **CRIT_hasWit_lift**, con el nombre local. -/
theorem CRIT_hasWit_lift' (s : Term) :
    Prf (Formula.impl (hasWit s) (hasWit (liftc zero s))) :=
  SinWTs.CRIT_hasWit_lift s

/-! ### §N.1 · EL TEOREMA -/

/-- **EL PASO INDUCTIVO `∀` CON GUARDA — CERRADO.**

    Reescritura de `Paso2.paso2_caso_forall` en forma `PrfH Γ` con `Γ = [hasWit s]`.
    Las DOS hipotesis que colgaban se descargan solas: `hLift` por `DESCENSO_hasWit`
    y la guarda de la HI por `CRIT_hasWit_lift`. Queda UNA sola hipotesis: la HI,
    ya en su forma guardada (la que produce `prf_strong_induction` sobre `PHI_guarded`). -/
theorem paso2_caso_forall_guarded (v s f : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero s))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))) :
    Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (forallc f)))) := by
  unfold evalSubstfcCode at hIH ⊢
  refine prf_deduction ?_
  -- la GUARDA, disponible en el contexto
  have hg : PrfH [hasWit s] (hasWit s) := prfH_hyp_self _
  -- (I) `hLift` DESCARGADA por el DESCENSO
  have hLift : PrfH [hasWit s] (provFromCode (eqc (liftcT (termCode zero) (tcFn s))
      (tcFn (liftc zero s)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_hasWit' s) _) hg
  -- (II) la guarda SUBE al subcodigo, y con ella se dispara la HI
  have hgl : PrfH [hasWit s] (hasWit (liftc zero s)) :=
    PrfH.mp _ _ _ (prf_to_prfH (CRIT_hasWit_lift' s) _) hg
  have hIHg : PrfH [hasWit s] (provFromCode (eqc
      (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))
      (tcFn (substfc (succ v) (liftc zero s) f)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hIH _) hgl
  -- ### invariancias `substtc` (identicas a las de `paso2_caso_forall`)
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn s))
      =eq liftcT (termCode zero) (tcFn s)) := substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (forallc f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (forallc f))
  -- (1) fuego (a)+(b): la instancia interna del axioma, ya dotada  [LIBRE]
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab v s f
  -- (2) `succcT v̇ ↦ (σv)˙`  [LIBRE, sube a Γ por `prf_to_prfH`]
  have h2 : PrfH [hasWit s] (provFromCode (eqc
      (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1) _
  -- (3) `liftcT ⌜0⌝ ṡ ↦ (liftc 0 s)˙` — aqui entra `hLift`, que VIVE EN Γ
  have h3 : PrfH [hasWit s] (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) _) hLift)
  -- (4) la HI bajo el `unT 6` — VIVE EN Γ
  have h4 : PrfH [hasWit s] (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (unT 6 (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) _) hIHg
  -- (5) el KIT pliega el `unT 6` en el punto de `forallc`  [LIBRE]
  have h5 : PrfH [hasWit s] (provFromCode (eqc
      (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (forallc (substfc (succ v) (liftc zero s) f))))) :=
    prf_to_prfH (pcc_dot_un 6 (substfc (succ v) (liftc zero s) f)) _
  -- (6) la ecuacion OBJETO del axioma, dotada GRATIS  [LIBRE]
  have h6 : PrfH [hasWit s] (provFromCode (eqc
      (tcFn (forallc (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (forallc f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_forall v s f)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn (forallc (substfc (succ v) (liftc zero s) f))))) _
  -- (7) LA CADENA, ahora entera en `PrfH Γ` via `PrfH_eq_trans_code`
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

/-! ### §N.2 · EL GATE: el `Φ` CON GUARDA sigue siendo admisible por `prf_strong_induction`
       (o sea: la forma guardada del paso inductivo es la que la induccion produce y consume). -/

theorem liftF_hasWit (k : Nat) (c : Term) :
    liftFormula k (hasWit c) = hasWit (liftTerm k c) := by
  simp only [hasWit, SinWTs.hasWit, liftFormula, SinWTs.liftF_isTC1, liftTerm,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

theorem substF_hasWit (v : Nat) (s c : Term) :
    substFormula v s (hasWit c) = hasWit (substTerm v s c) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [hasWit, SinWTs.hasWit, substFormula, SinWTs.substF_isTC1, substTerm, hz, hz2,
    if_false, FOL.substTerm_lift_comm_zero]

/-- El predicado de `pcc_eval_substfc` ENRIQUECIDO con la guarda sobre `s` (`#0`). -/
def PHI_guarded : Formula :=
  Formula.forall (Formula.forall (Formula.impl (hasWit (.var 0))
    (provFromCode (evalSubstfcCode (.var 1) (.var 0) (.var 2)))))

/-- **EL GATE, SUPERADO**: `liftFormula 1 Φ = Φ`, que es lo que exige `prf_strong_induction`. -/
theorem PHI_guarded_lift : liftFormula 1 PHI_guarded = PHI_guarded := by
  simp only [PHI_guarded, liftFormula, liftF_hasWit, liftFormula_provFromCode_open,
    liftTerm_evalSubstfcCode, liftTerm, Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

/-- La instancia de `Φ` en un codigo `t`: es EXACTAMENTE la forma guardada. -/
theorem PHI_guarded_at (t : Term) :
    substFormula 0 t PHI_guarded
      = Formula.forall (Formula.forall (Formula.impl (hasWit (.var 0))
          (provFromCode (evalSubstfcCode (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI_guarded, substFormula, substFormula_provFromCode_open, substF_hasWit,
    substTerm_evalSubstfcCode, substTerm, substTerms, liftTerm, liftTerms,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceGT, reduceIte,
    if_true]

/-! ############################################################################
    ## §N.1-GEN · **EL PASO INDUCTIVO UNARIO CON GUARDA, PARAMETRIZADO POR EL TAG**.
    ##
    ## Un solo lema cubre `forall` (tag 6) y `ex` (tag 9). Las dos hipotesis que
    ## instancia el llamador son AMBAS gratis en produccion:
    ##   `hmem` = `ax_substfc_{forall,ex} ∈ axioms`      (`simp [axioms]`)
    ##   `hobj` = `prf_substfc_{forall,ex}`              (teorema de `Meta/ArithPrf.lean`)
    ############################################################################ -/

theorem paso2_caso_un_guarded (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms)
    (hobj : ∀ v s a : Term,
      Prf (substfc v s (unc m a) =eq unc m (substfc (succ v) (liftc zero s) a)))
    (v s f : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero s))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))) :
    Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (unc m f)))) := by
  unfold evalSubstfcCode at hIH ⊢
  refine prf_deduction ?_
  have hg : PrfH [hasWit s] (hasWit s) := prfH_hyp_self _
  have hLift : PrfH [hasWit s] (provFromCode (eqc (liftcT (termCode zero) (tcFn s))
      (tcFn (liftc zero s)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_hasWit' s) _) hg
  have hgl : PrfH [hasWit s] (hasWit (liftc zero s)) :=
    PrfH.mp _ _ _ (prf_to_prfH (CRIT_hasWit_lift' s) _) hg
  have hIHg : PrfH [hasWit s] (provFromCode (eqc
      (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))
      (tcFn (substfc (succ v) (liftc zero s) f)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hIH _) hgl
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn s))
      =eq liftcT (termCode zero) (tcFn s)) := substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (unc m f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (unc m f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (unc m f))
  -- (1) fuego (a)+(b) GENERICO
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (unc m f)))
      (unT m (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab_un m hmem v s f
  -- (2) `succcT v̇ ↦ (σv)˙`
  have h2 : PrfH [hasWit s] (provFromCode (eqc
      (substfcT (tcFn v) (tcFn s) (tcFn (unc m f)))
      (unT m (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1) _
  -- (3) `liftcT ⌜0⌝ ṡ ↦ (liftc 0 s)˙` — el DESCENSO, que vive en Γ
  have h3 : PrfH [hasWit s] (provFromCode (eqc
      (unT m (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (unT m (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code m _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) _) hLift)
  -- (4) la HI bajo el `unT m`
  have h4 : PrfH [hasWit s] (provFromCode (eqc
      (unT m (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (unT m (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code m _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) _) hIHg
  -- (5) el KIT pliega el `unT m` en el punto del constructor
  have h5 : PrfH [hasWit s] (provFromCode (eqc
      (unT m (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (unc m (substfc (succ v) (liftc zero s) f))))) :=
    prf_to_prfH (pcc_dot_un m (substfc (succ v) (liftc zero s) f)) _
  -- (6) la ecuacion OBJETO del axioma, dotada GRATIS — aqui entra `hobj`
  have h6 : PrfH [hasWit s] (provFromCode (eqc
      (tcFn (unc m (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (unc m f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (hobj v s f)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn (unc m (substfc (succ v) (liftc zero s) f))))) _
  -- (7) LA CADENA
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

/-! ### §N.1-a · LAS DOS INSTANCIAS. Nada nuevo: `mem6/mem9` + `prf_substfc_forall/_ex`. -/

/-- **EL CASO `∀`, DERIVADO DEL LEMA GENERICO** — enunciado IDENTICO al
    `paso2_caso_forall_guarded` original (typechequea contra el). -/
theorem paso2_caso_forall_guarded_gen (v s f : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero s))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))) :
    Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (forallc f)))) :=
  paso2_caso_un_guarded 6 mem6 prf_substfc_forall v s f hIH

/-- **★ EL CASO `∃`, CON GUARDA — CERRADO.** Espejo exacto del `∀`: mismo lema,
    tag 9 en vez de 6, `ax_substfc_ex` en vez de `ax_substfc_forall`. -/
theorem paso2_caso_ex_guarded (v s f : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero s))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))) :
    Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (exc f)))) :=
  paso2_caso_un_guarded 9 mem9 prf_substfc_ex v s f hIH

/-! ### §N.3 · CONTROLES -/

/-- CONTROL NEGATIVO: el enunciado NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- CONTROL: la guarda NO es vacua — todo codigo REAL la satisface. -/
theorem CRIT_guarda_no_vacua (t : Term) : Prf (hasWit (termCodeM t)) :=
  SinWTs.CRIT_hasWit_real t

/-- CONTROL: sobre un codigo REAL la guarda se descarga y queda la ecuacion PELADA. -/
theorem paso2_caso_forall_guarded_real (v f : Term) (t : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero (termCodeM t)))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero (termCodeM t)) f)))) :
    Prf (provFromCode (evalSubstfcCode v (termCodeM t) (forallc f))) :=
  prf_mp (paso2_caso_forall_guarded v (termCodeM t) f hIH) (SinWTs.CRIT_hasWit_real t)

/-! ### §N.4 · CONTROLES DE LA FACTORIZACION Y DEL CASO `∃` -/

/-- **CONTROL B — LA FACTORIZACION ES EXACTA.** Para que esta igualdad TYPECHEQUEE,
    el enunciado de la version generica-en-tag-6 y el del `paso2_caso_forall_guarded`
    original (escrito a mano en el sondeo) han de ser el MISMO tipo. Lo son. -/
theorem CTRL_forall_reemplazable :
    @paso2_caso_forall_guarded = @paso2_caso_forall_guarded_gen := rfl

/-- **CONTROL C — EL TAG DISCRIMINA DE VERDAD**: la parametrizacion NO colapsa los dos
    constructores. Si `unc` fuese indiferente al tag, esto seria irrefutable. -/
theorem CTRL_tag_discrimina (a : Term) : unc 6 a ≠ unc 9 a := by
  intro h
  simp only [unc, cons, numeralM, succ, zero, Term.func.injEq, List.cons.injEq,
    and_true, true_and] at h
  exact absurd h.1 (by decide)

/-- CONTROL D: sobre un codigo REAL la guarda del caso `∃` se descarga tambien. -/
theorem paso2_caso_ex_guarded_real (v f : Term) (t : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero (termCodeM t)))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero (termCodeM t)) f)))) :
    Prf (provFromCode (evalSubstfcCode v (termCodeM t) (exc f))) :=
  prf_mp (paso2_caso_ex_guarded v (termCodeM t) f hIH) (SinWTs.CRIT_hasWit_real t)

/-- CONTROL E: el `Φ` con guarda del §N.2 sigue valiendo tal cual — el gate de
    `prf_strong_induction` NO depende del constructor, luego la misma induccion
    fuerte alimenta los DOS casos. -/
theorem CTRL_gate_intacto : liftFormula 1 PHI_guarded = PHI_guarded := PHI_guarded_lift

/-- **CONTROL F — LA PARAMETRIZACION NO ES COSMETICA.** El lema generico en tag 9 NO
    entrega la conclusion del caso `∀`, ni el de tag 6 la del caso `∃`. Si `unc` fuese
    indiferente al tag estos dos `fail_if_success` fallarian. -/
example : True := by
  fail_if_success
    have : ∀ (v s f : Term),
        Prf (Formula.impl (hasWit (liftc zero s))
          (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f))) →
        Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (forallc f)))) :=
      paso2_caso_un_guarded 9 mem9 prf_substfc_ex
    exact trivial
  fail_if_success
    have : ∀ (v s f : Term),
        Prf (Formula.impl (hasWit (liftc zero s))
          (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f))) →
        Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (exc f)))) :=
      paso2_caso_un_guarded 6 mem6 prf_substfc_forall
    exact trivial
  trivial

/-- CONTROL G: `mem9` NO es `mem6` disfrazado — es la pertenencia de `ax_substfc_ex`. -/
theorem CTRL_mem9_es_ax_ex : forall_3 (AXBODY 9) = ax_substfc_ex := rfl

end P2G

end S_Nuevo

/-! ## FOOTPRINT -/

#print axioms P2G.hasWit_bridge
#print axioms P2G.targetLift_bridge
#print axioms P2G.DESCENSO_hasWit'
#print axioms P2G.CRIT_hasWit_lift'
#print axioms P2G.paso2_caso_forall_guarded
#print axioms P2G.PHI_guarded_lift
#print axioms P2G.PHI_guarded_at
#print axioms P2G.CRIT_guarda_no_vacua
#print axioms P2G.paso2_caso_forall_guarded_real

-- CONTROL A: el footprint es EL MISMO que el del teorema que se reescribe y el de sus dos piezas.
#print axioms Paso2.paso2_caso_forall
#print axioms DescMutua.DESCENSO_hasWit
#print axioms SinWTs.CRIT_hasWit_lift

-- CONTROL B: la base sancionada es EXACTAMENTE la que ya carga produccion.
#print axioms ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.prf_strong_induction
#print axioms ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons

/-! ## FOOTPRINT DE LO NUEVO (§GEN + §N.1-GEN + caso `∃`) -/

#print axioms Paso2.unc6
#print axioms Paso2.unc9
#print axioms Paso2.AXBODY6
#print axioms Paso2.AXBODY9
#print axioms Paso2.substCodeT_unc
#print axioms Paso2.substCodeF_AXBODY
#print axioms Paso2.mem6
#print axioms Paso2.mem9
#print axioms Paso2.pcc_substfc_un_dot
#print axioms Paso2.fuego_ab_un
#print axioms Paso2.fuego_ab_es_generico
#print axioms Paso2.fuego_ab_ex
#print axioms P2G.paso2_caso_un_guarded
#print axioms P2G.paso2_caso_forall_guarded_gen
#print axioms P2G.paso2_caso_ex_guarded
#print axioms P2G.paso2_caso_ex_guarded_real
#print axioms P2G.CTRL_forall_reemplazable
#print axioms P2G.CTRL_tag_discrimina
#print axioms P2G.CTRL_gate_intacto
#print axioms P2G.CTRL_mem9_es_ax_ex

/-! ############################################################################
    ## §MED · MEDIDA (no es una prueba, es una MEDICION): la misma factorizacion
    ##        por tag cubre TRES de los siete constructores que faltan.
    ##
    ## `ax_substfc_impl` (5), `_and` (7), `_or` (8) son el MISMO `forall_4` modulo
    ## el tag — y **sin `liftc`**, luego NO necesitan guarda `hasWit`: un
    ## `paso2_caso_bin_guardless (m) (hmem) (hobj)` los cerraria de una vez,
    ## con `binT`/`pcc_dot_bin`/`pcc_congr_binT_*_code`, ya genericos en produccion.
    ##
    ## `eqc` (4) y `atomc` (3) NO entran en esta familia: su paso recursivo cae en
    ## `substtc`/`substtsc`, no en `substfc` (el teorema es MUTUO, no una recursion
    ## sobre codigos de formula). `botc` (2) es nulario.
    ############################################################################ -/

section S_Medida
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert

namespace MedBin

/-- Constructor BINARIO de codigo de formula, parametrizado por el tag. -/
def bnc (m : Nat) (a b : Term) : Term := cons (numeralM m) (cons a (cons b nil))

theorem bnc5 (a b : Term) : bnc 5 a b = implc a b := rfl
theorem bnc7 (a b : Term) : bnc 7 a b = andc a b := rfl
theorem bnc8 (a b : Term) : bnc 8 a b = orc a b := rfl

/-- El cuerpo comun de `ax_substfc_impl` / `_and` / `_or`. **Sin `liftc`, sin `succ`.** -/
def AXBODY2 (m : Nat) : Formula :=
  substfc (.var 3) (.var 2) (bnc m (.var 1) (.var 0))
    =eq bnc m (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

theorem AXBODY2_impl : ax_substfc_impl = forall_4 (AXBODY2 5) := rfl
theorem AXBODY2_and : ax_substfc_and = forall_4 (AXBODY2 7) := rfl
theorem AXBODY2_or : ax_substfc_or = forall_4 (AXBODY2 8) := rfl

/-- CONTROL: `eqc` (tag 4) NO cae en la familia — su axioma NO es `forall_4 (AXBODY2 4)`
    porque el paso recursivo usa `substtc` (codigos de TERMINO), no `substfc`. -/
example : True := by
  fail_if_success
    have : ax_substfc_eq = forall_4 (AXBODY2 4) := rfl
    exact trivial
  trivial

end MedBin
end S_Medida

#print axioms MedBin.bnc5
#print axioms MedBin.bnc7
#print axioms MedBin.bnc8
#print axioms MedBin.AXBODY2_impl
#print axioms MedBin.AXBODY2_and
#print axioms MedBin.AXBODY2_or

/-! ## ENUNCIADOS LITERALES -/

#check @P2G.paso2_caso_forall_guarded
#check @P2G.DESCENSO_hasWit'
#check @P2G.CRIT_hasWit_lift'
#check @P2G.paso2_caso_forall_guarded_real
#check @Paso2.unc
#check @Paso2.AXBODY
#check @Paso2.pcc_substfc_un_dot
#check @Paso2.fuego_ab_un
#check @P2G.paso2_caso_un_guarded
#check @P2G.paso2_caso_forall_guarded_gen
#check @P2G.paso2_caso_ex_guarded
#check @P2G.paso2_caso_ex_guarded_real

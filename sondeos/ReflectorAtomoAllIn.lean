/-
# VÍA 1 — EL ÁTOMO `allIn`: ¿se disuelve el `∀` ANIDADO dotándolo COMO ÁTOMO?

Molde: `sondeos/A3IsFCBTracked.lean` (idea #2 del proyecto: `inFormCodeFn`).

    lake env lean Probe/Refl_atomo.lean

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más).
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
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf ROBINSON_PlusPlus.Meta.NumListPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ReflAtomo

/-! ## 0 · Combinadores (copia literal de `sondeos/A3IsFCBTracked.lean` §0) -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_orL_imp (Ac Bc : Term) : Prf (provFromCode Ac ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Ac (orc Ac Bc)) (pcc_j1_code Ac Bc)

theorem prf_orR_imp (Ac Bc : Term) : Prf (provFromCode Bc ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Bc (orc Ac Bc)) (pcc_j2_code Ac Bc)

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-! ### Congruencias OBJETO de `carc` / `cdrc` / `lenc` (no estaban en producción) -/

theorem PrfH_congr_carc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (carc t₁ =eq carc t₂) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 t₁)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc t₁) (carc s) := by
    intro s
    simp only [f, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (carc t₁)) Γ)

theorem PrfH_congr_cdrc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (cdrc t₁ =eq cdrc t₂) := by
  let f : Formula := Formula.eq (cdrc (liftTerm 0 t₁)) (cdrc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cdrc t₁) (cdrc s) := by
    intro s
    simp only [f, cdrc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (cdrc t₁)) Γ)

theorem PrfH_congr_lenc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) Γ)

/-! ## 1 · EL OBJETO — el predicado sin `wTs`, con **`allIn`** en vez de `argsIn`

    (`sondeos/ClausuraLiftSinWTs.lean` §1, con `argsIn wT Y ↦ allIn wT Y`; son
    PROVABLEMENTE equivalentes: `argsIn = boundedAllIn` por `rfl` y
    `prf_allIn_iff_boundedAllIn` está en producción.) -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

/-- `X` es código de TÉRMINO, forma ECUACIONAL, UN solo testigo, y la carga es el **ÁTOMO**
    `allIn` (no el `∀` acotado desplegado). -/
def isTermCodeE1' (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (allIn wT (nthc X (numeralM 2))))

def wfAll1'Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1' (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAll1' (w : Term) : Formula := Formula.forall (wfAll1'Body w)

def isTC1' (w c : Term) : Formula := land (wfAll1' w) (In c w)

/-! ## 2 · LA IMAGEN PUNTEADA — `allIn` va como ÁTOMO (`allInFn`).
    ⇒ el cuerpo del `∀` acotado EXTERNO **no tiene ningún binder**. -/

/-- Constructor object del código del átomo `allIn` — instancia de `atom2CodeFn`, que ya
    existía en producción justamente para `chainOk`/`In`/**`allIn`**. NO es un símbolo nuevo. -/
noncomputable def allInFn (Wc Lc : Term) : Term := atom2CodeFn "allIn" Wc Lc

theorem allInFn_termCode (c L : Term) :
    allInFn (termCode c) (termCode L) = formCode (allIn c L) := rfl

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

/-- Imagen punteada del disyunto: la forma ecuacional se refleja sobre la forma
    `carc/lenc` (que es la que tiene puentes: `pcc_eval_carc`, `pcc_eval_lenc`). -/
noncomputable def isTCE1Dot (W X : Term) : Term :=
  orc (shapeDot X 0 2)
      (andc (shapeDot X 1 3) (allInFn W (nthcT X (tcFn (numeralM 2)))))

/-- **`PsiF`**: el cuerpo dotado del `∀` acotado externo, con el hueco `⌜v₀⌝` en el ÍNDICE.
    ⚠️ SIN BINDER: el `allIn` es un átomo. -/
noncomputable def PsiF (w : Term) : Term :=
  isTCE1Dot (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

noncomputable def wfAll1Dot (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiF w)

noncomputable def isTC1Dot (w c : Term) : Term :=
  andc (wfAll1Dot w) (inFormCodeFn (tcFn c) (tcFn w))

/-! ## 3 · EL DESCENSO de `substfc zero s` por los 2 disyuntos — TODO NIVEL 0 -/

theorem prf_substfc_shapeDot (s X X' : Term) (k n : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (shapeDot X k n) =eq shapeDot X' k n) := by
  unfold shapeDot
  refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_eq zero s _ _) (prf_congr_eqCodeFn ?_ ?_)
    · exact prf_eq_trans (prf_substtc_carcT zero s X) (prf_congr_carcT hX)
    · exact substtc_inv_tcFn (numeralM k) s
  · refine prf_eq_trans (prf_substfc_eq zero s _ _) (prf_congr_eqCodeFn ?_ ?_)
    · exact prf_eq_trans (prf_substtc_lencT zero s X) (prf_congr_lencT hX)
    · exact substtc_inv_tcFn (numeralM n) s

theorem prf_substtc_child (s X X' : Term) (k : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substtc zero s (nthcT X (tcFn (numeralM k))) =eq nthcT X' (tcFn (numeralM k))) :=
  prf_eq_trans (prf_substtc_nthcT zero s X (tcFn (numeralM k)))
    (prf_congr_nthcT hX (substtc_inv_tcFn (numeralM k) s))

/-- `substfc 0 s` sobre el código del átomo `allIn`, con el hueco en el **2º** argumento
    (gemelo de `prf_substfc_inDot` de A3, que lo tenía en el 1º). -/
theorem prf_substfc_allInDot (s W A A' : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hA : Prf (substtc zero s A =eq A')) :
    Prf (substfc zero s (allInFn W A) =eq allInFn W A') := by
  show Prf (substfc zero s (atomc (strCode "allIn") (cons W (cons A nil)))
    =eq atomc (strCode "allIn") (cons W (cons A' nil)))
  refine prf_eq_trans (prf_substfc_atom zero s (strCode "allIn") (cons W (cons A nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero s W (cons A nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head (hW s)) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons zero s A nil)
    (prf_eq_trans (prf_congr_cons_head hA) (prf_congr_cons_tail (prf_substtsc_nil zero s)))

/-- **EL DESCENSO**: `substfc zero s` atraviesa los 2 disyuntos y sólo toca el hueco de `X`. -/
theorem prf_substfc_isTCE1Dot_gen (s W X X' : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (isTCE1Dot W X) =eq isTCE1Dot W X') := by
  unfold isTCE1Dot
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 0 2 hX) ?_)
  refine prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' 1 3 hX) ?_)
  exact prf_substfc_allInDot s W _ _ hW (prf_substtc_child s X X' 2 hX)

theorem prf_substfc_PsiF (w s : Term) :
    Prf (substfc zero s (PsiF w) =eq isTCE1Dot (tcFn w) (nthcT (tcFn w) s)) :=
  prf_substfc_isTCE1Dot_gen s (tcFn w) _ _ (substtc_inv_tcFn w)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s)))

/-! ## 4 · Las 8 obligaciones de `pcc_bdAll_intro` (las 6 sintácticas + `hPsiId`) -/

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hPl_ok : ∀ (k : Nat) (q : Term), liftTerm k (PsiF q) = PsiF (liftTerm k q) := by
  intro k q
  simp only [PsiF, isTCE1Dot, shapeDot, allInFn, atom2CodeFn, inFormCodeFn, eqCodeFn, andc, orc,
    carcT, lencT, nthcT, funcc, varc, tcFn, cons, nil, zero, succ, numeralM, liftTerm, liftTerms,
    liftTerm_numeral, liftTerm_strCode]

theorem hPs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (PsiF q) = PsiF (substTerm v t q) := by
  intro v t q
  simp only [PsiF, isTCE1Dot, shapeDot, allInFn, atom2CodeFn, inFormCodeFn, eqCodeFn, andc, orc,
    carcT, lencT, nthcT, funcc, varc, tcFn, cons, nil, zero, succ, numeralM, substTerm, substTerms,
    substTerm_numeral, substTerm_strCode]

theorem hCl_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAll1' q) = wfAll1' (liftTerm k q) := by
  intro k q
  simp only [wfAll1', wfAll1'Body, isTermCodeE1', shapeUn, shapeBin, lor, land, lt, lenc, nthc,
    allIn, cons, nil, zero, liftFormula, liftTerm, liftTerms, liftTerm_numeralM,
    if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCs_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAll1' q) = wfAll1' (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAll1', wfAll1'Body, isTermCodeE1', shapeUn, shapeBin, lor, land, lt, lenc, nthc,
    allIn, cons, nil, zero, substFormula, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

/-- **`hPsiId`**: sale por instanciación PURA del descenso (el RHS es `PsiF q` por `rfl`). -/
theorem hPsiId_ok : ∀ q : Term,
    Prf (substfc zero (varc (numeral 0)) (PsiF q) =eq PsiF q) :=
  fun q => prf_substfc_PsiF q (varc (numeral 0))

/-! ## 5 · La forma ECUACIONAL IMPLICA la forma `carc`/`lenc` **y** `consOk`

    Así se conserva LITERALMENTE el predicado objeto de `sondeos/ClausuraLiftSinWTs.lean`
    (el que tiene la clausura bajo `liftc`) y se reutiliza el puente barato de A3. -/

theorem prf_shapeUn_carc (X : Term) (k : Nat) :
    Prf (shapeUn X k ⇒ Formula.eq (carc X) (numeralM k)) := by
  refine prf_deduction ?_
  exact PrfH_eq_trans (PrfH_congr_carc (prfH_hyp_self (shapeUn X k)))
    (prf_to_prfH (prf_carc_cons _ _) _)

theorem prf_shapeUn_lenc (X : Term) (k : Nat) :
    Prf (shapeUn X k ⇒ Formula.eq (lenc X) (numeralM 2)) := by
  refine prf_deduction ?_
  refine PrfH_eq_trans (PrfH_congr_lenc (prfH_hyp_self (shapeUn X k))) ?_
  refine PrfH_eq_trans (prf_to_prfH (prf_lenc_cons _ _) _) ?_
  refine prf_to_prfH ?_ _
  exact prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _) (prf_eq_congr_succ prf_lenc_nil))

theorem prf_shapeUn_consOk (X : Term) (k : Nat) : Prf (shapeUn X k ⇒ consOk X) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (shapeUn X k)
  have hc : PrfH _ (carc X =eq numeralM k) :=
    PrfH_eq_trans (PrfH_congr_carc h) (prf_to_prfH (prf_carc_cons _ _) _)
  have hd : PrfH _ (cdrc X =eq cons (nthc X (numeralM 1)) nil) :=
    PrfH_eq_trans (PrfH_congr_cdrc h) (prf_to_prfH (prf_cdrc_cons _ _) _)
  exact PrfH_eq_symm (PrfH_eq_trans
    (PrfH_eq_trans (PrfH_congr_cons_head hc) (PrfH_congr_cons_tail hd) : PrfH _ _)
    (PrfH_eq_symm h))

theorem prf_shapeBin_carc (X : Term) (k : Nat) :
    Prf (shapeBin X k ⇒ Formula.eq (carc X) (numeralM k)) := by
  refine prf_deduction ?_
  exact PrfH_eq_trans (PrfH_congr_carc (prfH_hyp_self (shapeBin X k)))
    (prf_to_prfH (prf_carc_cons _ _) _)

theorem prf_shapeBin_lenc (X : Term) (k : Nat) :
    Prf (shapeBin X k ⇒ Formula.eq (lenc X) (numeralM 3)) := by
  refine prf_deduction ?_
  refine PrfH_eq_trans (PrfH_congr_lenc (prfH_hyp_self (shapeBin X k))) ?_
  refine prf_to_prfH ?_ _
  refine prf_eq_trans (prf_lenc_cons _ _) (prf_eq_congr_succ ?_)
  exact prf_eq_trans (prf_lenc_cons _ _)
    (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _) (prf_eq_congr_succ prf_lenc_nil)))

theorem prf_shapeBin_consOk (X : Term) (k : Nat) : Prf (shapeBin X k ⇒ consOk X) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (shapeBin X k)
  have hc : PrfH _ (carc X =eq numeralM k) :=
    PrfH_eq_trans (PrfH_congr_carc h) (prf_to_prfH (prf_carc_cons _ _) _)
  have hd : PrfH _ (cdrc X =eq cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)) :=
    PrfH_eq_trans (PrfH_congr_cdrc h) (prf_to_prfH (prf_cdrc_cons _ _) _)
  exact PrfH_eq_symm (PrfH_eq_trans
    (PrfH_eq_trans (PrfH_congr_cons_head hc) (PrfH_congr_cons_tail hd) : PrfH _ _)
    (PrfH_eq_symm h))

/-! ## 6 · Los puentes `carcT` y la reflexión de la FORMA (copia de A3 §5‑§6) -/

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

theorem pcc_shape_tracked (X : Term) (k n : Nat) :
    Prf (consOk X ⇒ (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))
      ⇒ provFromCode (shapeDot (tcFn X) k n))) := by
  refine prf_deduction (deduction_aux ?_
    (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)))
    [consOk X] rfl)
  let Γ : List Formula :=
    [land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)), consOk X]
  show PrfH Γ (provFromCode (shapeDot (tcFn X) k n))
  have hsh : PrfH Γ
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH Γ (consOk X) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcarc : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have hcarc2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (carc X)) (tcFn (numeralM k)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (carc X) (numeralM k)) _)
      (PrfH_and_elim_left hsh)
  have hA : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (numeralM k)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hcarc hcarc2
  have hlen : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (lenc X)))) :=
    prf_to_prfH (pcc_eval_lenc X) Γ
  have hlen2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (lenc X)) (tcFn (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM n)) _)
      (PrfH_and_elim_right hsh)
  have hB : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (numeralM n)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_lencT (substtc_inv_tcFn X)) hlen hlen2
  exact PrfH_and_intro_code _ _ hA hB

theorem pcc_shapeUn_tracked (X : Term) (k : Nat) :
    Prf (shapeUn X k ⇒ provFromCode (shapeDot (tcFn X) k 2)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (shapeUn X k)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 2) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeUn_consOk X k) _) h))
    (PrfH_and_intro (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeUn_carc X k) _) h)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeUn_lenc X k) _) h))

theorem pcc_shapeBin_tracked (X : Term) (k : Nat) :
    Prf (shapeBin X k ⇒ provFromCode (shapeDot (tcFn X) k 3)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (shapeBin X k)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 3) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_consOk X k) _) h))
    (PrfH_and_intro (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_carc X k) _) h)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_lenc X k) _) h))

/-! ## 7 · El reflector del átomo `In` — COPIA LITERAL de `sondeos/A3IsFCBTracked.lean` §4
    (se necesita dos veces: para el conjunto `In c w` y dentro del reflector de `allIn`). -/

theorem prf_substfc_inDot (s A A' W : Term)
    (hA : Prf (substtc zero s A =eq A')) (hW : ∀ V, Prf (substtc zero V W =eq W)) :
    Prf (substfc zero s (inFormCodeFn A W) =eq inFormCodeFn A' W) := by
  show Prf (substfc zero s (atomc (strCode in_sym) (cons A (cons W nil)))
    =eq atomc (strCode in_sym) (cons A' (cons W nil)))
  refine prf_eq_trans (prf_substfc_atom zero s (strCode in_sym) (cons A (cons W nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero s A (cons W nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head hA) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons zero s W nil)
    (prf_eq_trans (prf_congr_cons_head (hW s)) (prf_congr_cons_tail (prf_substtsc_nil zero s)))

noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))
noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))
noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

theorem substtc_inv_bdInB (w : Term) : ∀ W, Prf (substtc zero W (bdInB w) =eq bdInB w) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn w)

theorem liftTerm_bdInDot (c : Nat) (x w : Term) :
    liftTerm c (bdInDot x w) = bdInDot (liftTerm c x) (liftTerm c w) := by
  unfold bdInDot bdInB bdInPhic bdExCode
  simp only [exc, andc, ltCodeFn, atom2CodeFn, eqCodeFn, lencT, nthcT, funcc, varc, liftc, tcFn,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem pcc_boundedIn_tracked (x w : Term) :
    Prf (boundedIn x w ⇒ provFromCode (bdInDot x w)) := by
  refine prf_deduction ?_
  have hex : PrfH [boundedIn x w] (boundedIn x w) := prfH_hyp_self _
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open, liftTerm_bdInDot]
  let X : Term := liftTerm 0 x
  let W : Term := liftTerm 0 w
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 (lenc w)))
    (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))
  let Γ' : List Formula := [exBody, liftFormula 0 (boundedIn x w)]
  show PrfH Γ' (provFromCode (bdInDot X W))
  have hC : PrfH Γ' exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Γ' (lt (.var 0) (lenc W)) := PrfH_and_elim_left hC
  have hbody : PrfH Γ' (Formula.eq (nthc W (.var 0)) X) := PrfH_and_elim_right hC
  have hlt1 : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (lenc W)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (lenc W)) _) hlt
  have hBeq : Prf (provFromCode (eqc (bdInB W) (tcFn (lenc W)))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_lencT (prf_eq_symm (prf_liftc_tcFn W))) (prf_refl _)))
      (pcc_eval_lenc W)
  have hBsym : PrfH Γ' (provFromCode (eqc (tcFn (lenc W)) (bdInB W))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_bdInB W) (prf_to_prfH hBeq _)
  have hcompLt : ∀ t : Term, Prf (substfc zero t (ltCodeFn (tcFn (.var 0)) (varc (numeral 0)))
      =eq ltCodeFn (tcFn (.var 0)) t) := fun t =>
    prf_substfc_ltCodeFn_snd (tcFn (.var 0)) t (substtc_inv_tcFn (.var 0))
  have hA1 : PrfH Γ' (provFromCode (substfc zero (tcFn (lenc W))
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcompLt _))) _) hlt1
  have hA2 : PrfH Γ' (provFromCode (substfc zero (bdInB W)
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hBsym hA1
  have hltB : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (bdInB W))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcompLt _)) _) hA2
  have hev : PrfH Γ' (provFromCode (eqCodeFn (nthcT (tcFn W) (tcFn (.var 0)))
      (tcFn (nthc W (.var 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc W (.var 0)) _) hlt
  have hcodeq : PrfH Γ' (eqCodeFn (nthcT (tcFn W) (tcFn (.var 0))) (tcFn (nthc W (.var 0)))
      =eq eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0))) (liftc zero (tcFn X))) :=
    PrfH_congr_eqCodeFn
      (prf_to_prfH (prf_congr_nthcT (prf_eq_symm (prf_liftc_tcFn W)) (prf_refl _)) _)
      (PrfH_eq_trans (PrfH_congr_tcFn hbody) (prf_to_prfH (prf_eq_symm (prf_liftc_tcFn X)) _))
  have hphi0 : PrfH Γ' (provFromCode (eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0)))
      (liftc zero (tcFn X)))) := PrfH_provCode_congr hcodeq hev
  have hcompPhi : Prf (substfc zero (tcFn (.var 0)) (bdInPhic X W)
      =eq eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0))) (liftc zero (tcFn X))) := by
    unfold bdInPhic
    refine prf_eq_trans (prf_substfc_eq zero (tcFn (.var 0)) _ _) ?_
    refine prf_congr_eqCodeFn ?_ (substtc_inv_liftc_tcFn X (tcFn (.var 0)))
    refine prf_eq_trans (prf_substtc_nthcT zero (tcFn (.var 0)) _ _) ?_
    exact prf_congr_nthcT (substtc_inv_liftc_tcFn W (tcFn (.var 0)))
      (prf_substtc_varc0 (tcFn (.var 0)))
  have hphi : PrfH Γ' (provFromCode (substfc zero (tcFn (.var 0)) (bdInPhic X W))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hcompPhi)) _) hphi0
  exact PrfH_bdEx_intro_open (bdInB W) (bdInPhic X W) (tcFn (.var 0))
    (substtc_inv_bdInB W) hltB hphi

def phiInBwd : Formula := Formula.impl (boundedIn (.var 1) (.var 0)) (In (.var 1) (.var 0))

theorem InBwd : Prf (forall_2 phiInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_In_of_boundedIn (.var 1) (.var 0)))

theorem substtc_inv_tcFn_at1 (w : Term) : ∀ V, Prf (substtc (succ zero) V (tcFn w) =eq tcFn w) :=
  fun V => prf_substtc_tcFn_at 1 V w

theorem prf_substtc_varc0_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 0)) =eq varc (numeral 0)) :=
  prf_mp (prf_substtc_var_lt (succ zero) V (numeral 0)) (prf_gnum_lt (by omega : 0 < 1))

theorem pcc_InBwd_computed (x w : Term) :
    Prf (provFromCode (implc (bdInDot x w) (inFormCodeFn (tcFn x) (tcFn w)))) := by
  let A : Term := tcFn x
  let B : Term := tcFn w
  let W : Term := liftc zero A
  have h0 : Prf (provFromCode (substfc zero B (substfc (succ zero) W (formCode phiInBwd)))) :=
    pcc_thm_inst2 phiInBwd InBwd A B
  have hin : Prf (substfc (succ zero) W (formCode phiInBwd)
      =eq implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                           (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                     (liftc zero W))))
                (inFormCodeFn W (varc (numeral 0)))) :=
    prf_substfc_arith_open 1 W phiInBwd
  have h1 := prf_mp (prf_provCode_congr (prf_congr_substfc3 hin)) h0
  have hv1 : ∀ t : Term, Prf (substtc (succ zero) t (varc (numeral 1)) =eq t) := fun t =>
    prf_mp (prf_substtc_var_eq (succ zero) t (numeral 1)) (prf_refl _)
  have hWnorm : ∀ t : Term, Prf (substtc (succ zero) t (liftc zero W) =eq liftc zero A) := by
    intro t
    refine prf_eq_trans (prf_congr_substtc3 (prf_congr_liftc (prf_liftc_tcFn x))) ?_
    refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_tcFn x)) ?_
    exact prf_eq_trans (prf_substtc_tcFn_at 1 t x) (prf_eq_symm (prf_liftc_tcFn x))
  have hout : Prf (substfc zero B
      (implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                        (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                  (liftc zero W))))
             (inFormCodeFn W (varc (numeral 0))))
      =eq implc (bdInDot x w) (inFormCodeFn A B)) := by
    refine prf_eq_trans (prf_substfc_impl zero B _ _) (prf_congr_implc ?_ ?_)
    · refine prf_eq_trans (prf_substfc_ex zero B _) (prf_congr_exc ?_)
      refine prf_eq_trans (prf_substfc_and (succ zero) (liftc zero B) _ _)
        (prf_congr_andc ?_ ?_)
      · show Prf (substfc (succ zero) (liftc zero B)
            (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT (varc (numeral 1))) nil)))
          =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (bdInB w) nil)))
        refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero B) (strCode lt_sym) _) ?_
        refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
        have hlen : Prf (substtc (succ zero) (liftc zero B) (lencT (varc (numeral 1)))
            =eq bdInB w) :=
          prf_eq_trans (prf_substtc_lencT (succ zero) (liftc zero B) (varc (numeral 1)))
            (prf_congr_lencT (hv1 (liftc zero B)))
        refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _) ?_
        refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0_at1 (liftc zero B))) ?_
        refine prf_congr_cons_tail ?_
        exact prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _)
          (prf_eq_trans (prf_congr_cons_head hlen)
            (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero B))))
      · refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero B) _ _)
          (prf_congr_eqCodeFn ?_ (hWnorm (liftc zero B)))
        exact prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero B) _ _)
          (prf_congr_nthcT (hv1 (liftc zero B)) (prf_substtc_varc0_at1 (liftc zero B)))
    · show Prf (substfc zero B (atomc (strCode in_sym) (cons W (cons (varc (numeral 0)) nil)))
        =eq atomc (strCode in_sym) (cons A (cons B nil)))
      refine prf_eq_trans (prf_substfc_atom zero B (strCode in_sym) _) ?_
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      refine prf_eq_trans (prf_substtsc_cons zero B W (cons (varc (numeral 0)) nil)) ?_
      refine prf_eq_trans (prf_congr_cons_head
        (prf_eq_trans (substtc_inv_liftc_tcFn x B) (prf_liftc_tcFn x))) ?_
      refine prf_congr_cons_tail ?_
      exact prf_eq_trans (prf_substtsc_cons zero B (varc (numeral 0)) nil)
        (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 B))
          (prf_congr_cons_tail (prf_substtsc_nil zero B)))
  exact prf_mp (prf_provCode_congr hout) h1

/-- **Reflexión del `In` como ÁTOMO**, con `x` y `w` ABSTRACTOS (A3). -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

/-! ## 8 · ENSAMBLAJE EXTERNO, **MÓDULO** el reflector del átomo `allIn`

    `AllInReflector` aísla EXACTAMENTE lo único que este frente añade sobre A3. -/

/-- La hipótesis que aísla el `∀` anidado. -/
abbrev AllInReflector : Prop :=
  ∀ c L : Term, Prf (allIn c L ⇒ provFromCode (allInFn (tcFn c) (tcFn L)))

/-- Transporte interno dentro del **2º** argumento del átomo `allIn`. -/
theorem PrfH_allIn_transport {Γ : List Formula} (u v W : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W))
    (heq : PrfH Γ (provFromCode (eqc u v)))
    (h : PrfH Γ (provFromCode (allInFn W u))) :
    PrfH Γ (provFromCode (allInFn W v)) := by
  let Cal : Term := allInFn W (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Cal =eq allInFn W t) := fun t =>
    prf_substfc_allInDot t W (varc (numeral 0)) t hW (prf_substtc_varc0 t)
  have h1 : PrfH Γ (provFromCode (substfc zero u Cal)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp u))) _) h
  have h2 : PrfH Γ (provFromCode (substfc zero v Cal)) := PrfH_leibniz_apply Cal u v heq h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp v)) _) h2

theorem pcc_allIn_child_tracked (hR : AllInReflector) (q X : Term) :
    Prf (Formula.eq (lenc X) (numeralM 3) ⇒ (allIn q (nthc X (numeralM 2)) ⇒
      provFromCode (allInFn (tcFn q) (nthcT (tcFn X) (tcFn (numeralM 2)))))) := by
  refine prf_deduction (deduction_aux ?_ (allIn q (nthc X (numeralM 2)))
    [Formula.eq (lenc X) (numeralM 3)] rfl)
  have hin : PrfH [allIn q (nthc X (numeralM 2)), Formula.eq (lenc X) (numeralM 3)]
      (allIn q (nthc X (numeralM 2))) := PrfH.hyp _ _ (List.Mem.head _)
  have hlen : PrfH [allIn q (nthc X (numeralM 2)), Formula.eq (lenc X) (numeralM 3)]
      (Formula.eq (lenc X) (numeralM 3)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH _ (lt (numeralM 2) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (prf_to_prfH (prf_lt_numeralM (by omega : 2 < 3)) _)
  have hev : PrfH _ (provFromCode (eqCodeFn (nthcT (tcFn X) (tcFn (numeralM 2)))
      (tcFn (nthc X (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM 2)) _) hlt
  have hevS : PrfH _ (provFromCode (eqCodeFn (tcFn (nthc X (numeralM 2)))
      (nthcT (tcFn X) (tcFn (numeralM 2))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM 2))) hev
  have hat : PrfH _ (provFromCode (allInFn (tcFn q) (tcFn (nthc X (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hR q (nthc X (numeralM 2))) _) hin
  exact PrfH_allIn_transport _ _ _ (substtc_inv_tcFn q) hevS hat

/-- Los DOS disyuntos, reflejados sobre el nodo `X` ABSTRACTO. -/
theorem pcc_isTCE1_pure (hR : AllInReflector) (q X : Term) :
    Prf (isTermCodeE1' q X ⇒ provFromCode (isTCE1Dot (tcFn q) (tcFn X))) := by
  unfold isTermCodeE1' isTCE1Dot
  refine prf_or_elim_imp (impT (pcc_shapeUn_tracked X 0) (prf_orL_imp _ _)) ?_
  refine impT ?_ (prf_orR_imp (shapeDot (tcFn X) 0 2) _)
  refine prf_deduction ?_
  have h := prfH_hyp_self (land (shapeBin X 1) (allIn q (nthc X (numeralM 2))))
  have hb := PrfH_and_elim_left h
  have ha := PrfH_and_elim_right h
  have h1 := PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeBin_tracked X 1) _) hb
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_allIn_child_tracked hR q X) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_lenc X 1) _) hb)) ha
  exact PrfH_and_intro_code _ _ h1 h2

theorem hbody_ok (hR : AllInReflector) : ∀ q i : Term, Prf (wfAll1' q ⇒ (lt i (lenc q)
    ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll1' q] rfl)
  have hlt : PrfH [lt i (lenc q), wfAll1' q] (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (lenc q), wfAll1' q] (wfAll1' q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (wfAll1'Body q)
      = Formula.impl (lt i (lenc q)) (isTermCodeE1' q (nthc q i)) := by
    simp only [wfAll1'Body, isTermCodeE1', shapeUn, shapeBin, lor, land, allIn, lt, lenc, nthc,
      cons, nil, zero, substFormula, substTerm, substTerms, substTerm_numeralM,
      FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (lenc q), wfAll1' q] _
    (Prf₀.q1 (wfAll1'Body q) i)) hwf
  rw [hsubst] at h0
  have hnode : PrfH [lt i (lenc q), wfAll1' q] (isTermCodeE1' q (nthc q i)) :=
    PrfH.mp _ _ _ h0 hlt
  have hpure : PrfH [lt i (lenc q), wfAll1' q]
      (provFromCode (isTCE1Dot (tcFn q) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_isTCE1_pure hR q (nthc q i)) _) hnode
  have hev : PrfH [lt i (lenc q), wfAll1' q]
      (provFromCode (eqCodeFn (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hevS : PrfH [lt i (lenc q), wfAll1' q]
      (provFromCode (eqCodeFn (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  have hC : ∀ t : Term,
      Prf (substfc zero t (isTCE1Dot (tcFn q) (varc (numeral 0))) =eq isTCE1Dot (tcFn q) t) :=
    fun t => prf_substfc_isTCE1Dot_gen t (tcFn q) (varc (numeral 0)) t
      (substtc_inv_tcFn q) (prf_substtc_varc0 t)
  have h1 : PrfH [lt i (lenc q), wfAll1' q]
      (provFromCode (substfc zero (tcFn (nthc q i)) (isTCE1Dot (tcFn q) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hC _))) _) hpure
  have h2 : PrfH [lt i (lenc q), wfAll1' q]
      (provFromCode (substfc zero (nthcT (tcFn q) (tcFn i))
        (isTCE1Dot (tcFn q) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hevS h1
  have h3 : PrfH [lt i (lenc q), wfAll1' q]
      (provFromCode (isTCE1Dot (tcFn q) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hC _)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF q (tcFn i)))) _) h3

/-- **EL PUNTO DE LA MEDIDA**: con `allIn` DOTADO COMO ÁTOMO, el `∀` externo sale en
    UNA LÍNEA por `pcc_bdAll_intro`, exactamente igual que en A3. -/
theorem pcc_wfAll_tracked (hR : AllInReflector) (w : Term) :
    Prf (wfAll1' w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_bdAll_intro wfAll1' lenc PsiF w hCl_ok hCs_ok hbl_ok hbs_ok hPl_ok hPs_ok hPsiId_ok
    (hbody_ok hR)

theorem pcc_isTC1_tracked (hR : AllInReflector) (w c : Term) :
    Prf (isTC1' w c ⇒ provFromCode (isTC1Dot w c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTC1' w c)
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll_tracked hR w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! ## 9 · EL RELECTOR DEL ÁTOMO `allIn` — (a) el PUENTE COMPUTADO

    Gemelo de `pcc_InBwd_computed`, con un `forallc` de más: la forma acotada de `allIn`
    es un `∀` (no un `∃`), pero se instancia igual desde el TEOREMA OBJETO
    `prf_allIn_of_boundedAllIn`, que YA ESTÁ EN PRODUCCIÓN. -/

theorem prf_congr_forallc {a a' : Term} (h : Prf (a =eq a')) :
    Prf (forallc a =eq forallc a') := by
  unfold forallc
  exact prf_congr_cons_tail (prf_congr_cons_head h)

/-- `substfc` sobre el código del átomo `allIn`, a NIVEL ARBITRARIO y con los dos
    argumentos moviéndose. -/
theorem prf_substfc_allIn_at (v s W W' A A' : Term)
    (hW : Prf (substtc v s W =eq W')) (hA : Prf (substtc v s A =eq A')) :
    Prf (substfc v s (allInFn W A) =eq allInFn W' A') := by
  show Prf (substfc v s (atomc (strCode "allIn") (cons W (cons A nil)))
    =eq atomc (strCode "allIn") (cons W' (cons A' nil)))
  refine prf_eq_trans (prf_substfc_atom v s (strCode "allIn") (cons W (cons A nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v s W (cons A nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head hW) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons v s A nil)
    (prf_eq_trans (prf_congr_cons_head hA) (prf_congr_cons_tail (prf_substtsc_nil v s)))

/-- Ídem para el átomo `In` (nivel arbitrario, los dos argumentos). -/
theorem prf_substfc_in_at (v s A A' W W' : Term)
    (hA : Prf (substtc v s A =eq A')) (hW : Prf (substtc v s W =eq W')) :
    Prf (substfc v s (inFormCodeFn A W) =eq inFormCodeFn A' W') := by
  show Prf (substfc v s (atomc (strCode in_sym) (cons A (cons W nil)))
    =eq atomc (strCode in_sym) (cons A' (cons W' nil)))
  refine prf_eq_trans (prf_substfc_atom v s (strCode in_sym) (cons A (cons W nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v s A (cons W nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head hA) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons v s W nil)
    (prf_eq_trans (prf_congr_cons_head hW) (prf_congr_cons_tail (prf_substtsc_nil v s)))

def phiAllInBwd : Formula :=
  Formula.impl (boundedAllIn (.var 1) (.var 0)) (allIn (.var 1) (.var 0))

/-- El teorema OBJETO, en UNA línea: ya está en producción
    (`Meta/ChainOkBoundedPrf.lean:386`). -/
theorem AllInBwd : Prf (forall_2 phiAllInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_allIn_of_boundedAllIn (.var 1) (.var 0)))

/-- El cuerpo dotado del `∀` acotado INTERNO: átomo `In`, hueco en el índice. -/
noncomputable def PsiIn (c L : Term) : Term :=
  inFormCodeFn (nthcT (tcFn L) (varc (numeral 0))) (tcFn c)

/-- La forma acotada dotada de `allIn`, con la cota **COMPUTADA** (`lencT L̇`). -/
noncomputable def bdAllInDot (c L : Term) : Term := bdAllCode (lencT (tcFn L)) (PsiIn c L)

/-- **EL PUENTE**: `⊢ Prov(⌜ (∀i<lenc(L̇). nthc(L̇,i) ∈ ċ) ⇒ allIn(ċ, L̇) ⌝)`, `c`,`L` ABSTRACTOS. -/
theorem pcc_AllInBwd_computed (c L : Term) :
    Prf (provFromCode (implc (bdAllInDot c L) (allInFn (tcFn c) (tcFn L)))) := by
  let A : Term := tcFn c
  let B : Term := tcFn L
  let W : Term := liftc zero A
  have h0 : Prf (provFromCode (substfc zero B (substfc (succ zero) W (formCode phiAllInBwd)))) :=
    pcc_thm_inst2 phiAllInBwd AllInBwd A B
  have hin : Prf (substfc (succ zero) W (formCode phiAllInBwd)
      =eq implc (forallc (implc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                  (inFormCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0))) (liftc zero W))))
                (allInFn W (varc (numeral 0)))) :=
    prf_substfc_arith_open 1 W phiAllInBwd
  have h1 := prf_mp (prf_provCode_congr (prf_congr_substfc3 hin)) h0
  have hv1 : ∀ t : Term, Prf (substtc (succ zero) t (varc (numeral 1)) =eq t) := fun t =>
    prf_mp (prf_substtc_var_eq (succ zero) t (numeral 1)) (prf_refl _)
  have hBnorm : Prf (substtc (succ zero) (liftc zero B) (varc (numeral 1)) =eq B) :=
    prf_eq_trans (hv1 (liftc zero B)) (prf_liftc_tcFn L)
  have hWnorm : ∀ t : Term, Prf (substtc (succ zero) t (liftc zero W) =eq A) := by
    intro t
    refine prf_eq_trans (prf_congr_substtc3 (prf_congr_liftc (prf_liftc_tcFn c))) ?_
    refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_tcFn c)) ?_
    exact prf_substtc_tcFn_at 1 t c
  have hout : Prf (substfc zero B
      (implc (forallc (implc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                (inFormCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0))) (liftc zero W))))
             (allInFn W (varc (numeral 0))))
      =eq implc (bdAllInDot c L) (allInFn A B)) := by
    refine prf_eq_trans (prf_substfc_impl zero B _ _) (prf_congr_implc ?_ ?_)
    · refine prf_eq_trans (prf_substfc_forall zero B _) (prf_congr_forallc ?_)
      refine prf_eq_trans (prf_substfc_impl (succ zero) (liftc zero B) _ _)
        (prf_congr_implc ?_ ?_)
      · show Prf (substfc (succ zero) (liftc zero B)
            (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT (varc (numeral 1))) nil)))
          =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT B) nil)))
        refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero B) (strCode lt_sym) _) ?_
        refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
        have hlen : Prf (substtc (succ zero) (liftc zero B) (lencT (varc (numeral 1)))
            =eq lencT B) :=
          prf_eq_trans (prf_substtc_lencT (succ zero) (liftc zero B) (varc (numeral 1)))
            (prf_congr_lencT hBnorm)
        refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _) ?_
        refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0_at1 (liftc zero B))) ?_
        refine prf_congr_cons_tail ?_
        exact prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _)
          (prf_eq_trans (prf_congr_cons_head hlen)
            (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero B))))
      · refine prf_substfc_in_at (succ zero) (liftc zero B) _ _ _ _ ?_ (hWnorm (liftc zero B))
        exact prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero B) _ _)
          (prf_congr_nthcT hBnorm (prf_substtc_varc0_at1 (liftc zero B)))
    · refine prf_substfc_allIn_at zero B _ _ _ _ ?_ (prf_substtc_varc0 B)
      exact prf_eq_trans (substtc_inv_liftc_tcFn c B) (prf_liftc_tcFn c)
  exact prf_mp (prf_provCode_congr hout) h1

/-! ## 10 · (b) La reflexión de la forma ACOTADA de `allIn`, por `pcc_bdAll_intro`

    ⚠️ `pcc_bdAll_intro` está parametrizado sobre **UN** término `p`; `boundedAllIn` tiene
    DOS argumentos ⇒ se pasa el par `p = cons c L` y se recupera con `carc`/`cdrc`. -/

theorem prf_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) :=
  prfH_nil_to_prf (PrfH_congr_lenc (prf_to_prfH h [])) rfl

theorem prf_mp_code {Ac Bc : Term} (h1 : Prf (provFromCode (implc Ac Bc)))
    (h2 : Prf (provFromCode Ac)) : Prf (provFromCode Bc) :=
  prfH_nil_to_prf (PrfH_mp_code_apply (prf_to_prfH h1 []) (prf_to_prfH h2 [])) rfl

/-- Transporte interno dentro del 1er argumento del átomo `In` (A3 §5). -/
theorem PrfH_in_transport {Γ : List Formula} (u v W : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W))
    (heq : PrfH Γ (provFromCode (eqc u v)))
    (h : PrfH Γ (provFromCode (inFormCodeFn u W))) :
    PrfH Γ (provFromCode (inFormCodeFn v W)) := by
  let Cin : Term := inFormCodeFn (varc (numeral 0)) W
  have hcomp : ∀ t : Term, Prf (substfc zero t Cin =eq inFormCodeFn t W) := fun t =>
    prf_substfc_inDot t (varc (numeral 0)) t W (prf_substtc_varc0 t) hW
  have h1 : PrfH Γ (provFromCode (substfc zero u Cin)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp u))) _) h
  have h2 : PrfH Γ (provFromCode (substfc zero v Cin)) := PrfH_leibniz_apply Cin u v heq h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp v)) _) h2

/-- Especialización del `∀` acotado de `boundedAllIn` en un índice `i` arbitrario. -/
theorem prf_boundedAllIn_spec (c L i : Term) :
    Prf (boundedAllIn c L ⇒ (lt i (lenc L) ⇒ In (nthc L i) c)) := by
  refine prf_deduction ?_
  have hwf := prfH_hyp_self (boundedAllIn c L)
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
      (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 c)))
      = Formula.impl (lt i (lenc L)) (In (nthc L i) c) := by
    simp only [lt, lenc, nthc, In, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [boundedAllIn c L] _
    (Prf₀.q1 (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
      (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 c))) i)) hwf
  rw [hsubst] at h0
  exact h0

noncomputable def CFin (p : Term) : Formula := boundedAllIn (carc p) (cdrc p)
def bndFin (p : Term) : Term := lenc (cdrc p)
noncomputable def PsiFin (p : Term) : Term :=
  inFormCodeFn (nthcT (tcFn (cdrc p)) (varc (numeral 0))) (tcFn (carc p))

theorem hCl_in : ∀ (k : Nat) (q : Term), liftFormula k (CFin q) = CFin (liftTerm k q) := by
  intro k q
  simp only [CFin, liftFormula_boundedAllIn_gen, carc, cdrc, liftTerm, liftTerms]

theorem hCs_in : ∀ (v : Nat) (t q : Term),
    substFormula v t (CFin q) = CFin (substTerm v t q) := by
  intro v t q
  simp only [CFin, substFormula_boundedAllIn, carc, cdrc, substTerm, substTerms]

theorem hbl_in : ∀ (k : Nat) (q : Term), liftTerm k (bndFin q) = bndFin (liftTerm k q) := by
  intro k q; simp only [bndFin, lenc, cdrc, liftTerm, liftTerms]

theorem hbs_in : ∀ (v : Nat) (t q : Term),
    substTerm v t (bndFin q) = bndFin (substTerm v t q) := by
  intro v t q; simp only [bndFin, lenc, cdrc, substTerm, substTerms]

theorem hPl_in : ∀ (k : Nat) (q : Term), liftTerm k (PsiFin q) = PsiFin (liftTerm k q) := by
  intro k q
  simp only [PsiFin, inFormCodeFn, nthcT, funcc, varc, tcFn, carc, cdrc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem hPs_in : ∀ (v : Nat) (t q : Term),
    substTerm v t (PsiFin q) = PsiFin (substTerm v t q) := by
  intro v t q
  simp only [PsiFin, inFormCodeFn, nthcT, funcc, varc, tcFn, carc, cdrc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

/-- El descenso del cuerpo `PsiFin` (átomo `In`, hueco en el índice). -/
theorem prf_substfc_PsiFin (p s : Term) :
    Prf (substfc zero s (PsiFin p)
      =eq inFormCodeFn (nthcT (tcFn (cdrc p)) s) (tcFn (carc p))) :=
  prf_substfc_inDot s _ _ _
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn (cdrc p)) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn (cdrc p) s) (prf_substtc_varc0 s)))
    (substtc_inv_tcFn (carc p))

theorem hPsiId_in : ∀ q : Term,
    Prf (substfc zero (varc (numeral 0)) (PsiFin q) =eq PsiFin q) :=
  fun q => prf_substfc_PsiFin q (varc (numeral 0))

theorem hbody_in : ∀ q i : Term, Prf (CFin q ⇒ (lt i (bndFin q)
    ⇒ provFromCode (substfc zero (tcFn i) (PsiFin q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (bndFin q)) [CFin q] rfl)
  have hlt : PrfH [lt i (bndFin q), CFin q] (lt i (lenc (cdrc q))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (bndFin q), CFin q] (CFin q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hin : PrfH _ (In (nthc (cdrc q) i) (carc q)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_boundedAllIn_spec (carc q) (cdrc q) i) _) hwf) hlt
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (nthc (cdrc q) i)) (tcFn (carc q)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc (cdrc q) i) (carc q)) _) hin
  have hev : PrfH _ (provFromCode (eqCodeFn (nthcT (tcFn (cdrc q)) (tcFn i))
      (tcFn (nthc (cdrc q) i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc (cdrc q) i) _) hlt
  have hevS : PrfH _ (provFromCode (eqCodeFn (tcFn (nthc (cdrc q) i))
      (nthcT (tcFn (cdrc q)) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn (cdrc q)) (substtc_inv_tcFn i)) hev
  have hgoal : PrfH _ (provFromCode (inFormCodeFn (nthcT (tcFn (cdrc q)) (tcFn i))
      (tcFn (carc q)))) :=
    PrfH_in_transport _ _ _ (substtc_inv_tcFn (carc q)) hevS hat
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiFin q (tcFn i)))) _) hgoal

/-- La reflexión de la forma acotada, sobre el PAR. -/
theorem pcc_bdAllIn_pair (p : Term) :
    Prf (CFin p ⇒ provFromCode (bdAllCode (tcFn (bndFin p)) (PsiFin p))) :=
  pcc_bdAll_intro CFin bndFin PsiFin p hCl_in hCs_in hbl_in hbs_in hPl_in hPs_in
    hPsiId_in hbody_in

/-! ## 11 · (c) EL CAMBIO DE COTA — la única fricción real

    `pcc_bdAll_intro` entrega la cota en forma de **reflexión pura** `tcFn (lenc L)`, y el
    PUENTE (que viene de instanciar un teorema objeto) la pide **COMPUTADA** `lencT (tcFn L)`.
    Se salva con **UNA** Leibniz interna cuyo contexto tiene el hueco en `⌜v₁⌝` (bajo el
    binder de código): `pcc_leibniz_code` basta, no hace falta ninguna Leibniz de nivel 1. -/

theorem prf_congr_bdAllCode {B B' P P' : Term} (hB : Prf (B =eq B')) (hP : Prf (P =eq P')) :
    Prf (bdAllCode B P =eq bdAllCode B' P') := by
  unfold bdAllCode
  refine prf_congr_forallc (prf_congr_implc ?_ hP)
  show Prf (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons B nil))
    =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons B' nil)))
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_congr_cons_tail (prf_congr_cons_head hB))))

/-- El contexto de la Leibniz: el hueco es la COTA, que bajo el `forallc` es `⌜v₁⌝`. -/
noncomputable def Cbnd (Psi : Term) : Term :=
  forallc (implc (ltCodeFn (varc (numeral 0)) (varc (numeral 1))) Psi)

theorem prf_substfc_Cbnd (s Psi : Term)
    (hPsi : Prf (substfc (succ zero) (liftc zero s) Psi =eq Psi)) :
    Prf (substfc zero s (Cbnd Psi) =eq bdAllCode (liftc zero s) Psi) := by
  refine prf_eq_trans (prf_substfc_forall zero s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl (succ zero) (liftc zero s) _ _)
    (prf_congr_implc ?_ hPsi)
  show Prf (substfc (succ zero) (liftc zero s)
      (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (varc (numeral 1)) nil)))
    =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (liftc zero s) nil)))
  refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero s) (strCode lt_sym) _) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero s) _ _) ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0_at1 (liftc zero s))) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero s) _ _)
    (prf_eq_trans (prf_congr_cons_head
        (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (numeral 1)) (prf_refl _)))
      (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero s))))

theorem prf_substfc_PsiIn_at1 (c L V : Term) :
    Prf (substfc (succ zero) V (PsiIn c L) =eq PsiIn c L) :=
  prf_substfc_in_at (succ zero) V _ _ _ _
    (prf_eq_trans (prf_substtc_nthcT (succ zero) V (tcFn L) (varc (numeral 0)))
      (prf_congr_nthcT (prf_substtc_tcFn_at 1 V L) (prf_substtc_varc0_at1 V)))
    (prf_substtc_tcFn_at 1 V c)

theorem prf_liftc_lencT (t : Term) : Prf (liftc zero (lencT t) =eq lencT (liftc zero t)) := by
  unfold lencT
  refine prf_eq_trans (prf_liftc_func zero (strCode "lenc") (cons t nil)) ?_
  refine prf_congr_funcc2 ?_
  exact prf_eq_trans (prf_liftsc_cons zero t nil) (prf_congr_cons_tail (prf_liftsc_nil zero))

theorem hlift_B2 (L : Term) : Prf (liftc zero (lencT (tcFn L)) =eq lencT (tcFn L)) :=
  prf_eq_trans (prf_liftc_lencT (tcFn L)) (prf_congr_lencT (prf_liftc_tcFn L))

/-- **EL CAMBIO DE COTA**, dentro de `Prov`. -/
theorem pcc_bdAll_bound_swap (B1 B2 Psi : Term)
    (h1 : Prf (liftc zero B1 =eq B1)) (h2 : Prf (liftc zero B2 =eq B2))
    (hPsi : ∀ V, Prf (substfc (succ zero) V Psi =eq Psi))
    (heq : Prf (provFromCode (eqc B1 B2))) :
    Prf (provFromCode (bdAllCode B1 Psi) ⇒ provFromCode (bdAllCode B2 Psi)) := by
  have hc : ∀ s, Prf (liftc zero s =eq s) →
      Prf (substfc zero s (Cbnd Psi) =eq bdAllCode s Psi) := fun s hs =>
    prf_eq_trans (prf_substfc_Cbnd s Psi (hPsi (liftc zero s)))
      (prf_congr_bdAllCode hs (prf_refl _))
  have hL := prf_mp_code (pcc_leibniz_code (Cbnd Psi) B1 B2) heq
  have hL2 : Prf (provFromCode (implc (bdAllCode B1 Psi) (bdAllCode B2 Psi))) :=
    prf_mp (prf_provCode_congr (prf_congr_implc (hc B1 h1) (hc B2 h2))) hL
  exact prf_mp (pcc_mp_code_open _ _) hL2

/-! ## 12 · Del PAR a los dos argumentos, y EL RELECTOR CERRADO -/

theorem PrfH_congr_boundedAllIn1 {Γ : List Formula} {c₁ c₂ L : Term} (h : PrfH Γ (c₁ =eq c₂))
    (hb : PrfH Γ (boundedAllIn c₁ L)) : PrfH Γ (boundedAllIn c₂ L) := by
  let f : Formula := boundedAllIn (.var 0) (liftTerm 0 L)
  have hS : ∀ s : Term, substFormula 0 s f = boundedAllIn s L := by
    intro s
    simp only [f, substFormula_boundedAllIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS c₂) ▸ PrfH_leibniz_subst (A := f) h ((hS c₁) ▸ hb)

theorem PrfH_congr_boundedAllIn2 {Γ : List Formula} {c L₁ L₂ : Term} (h : PrfH Γ (L₁ =eq L₂))
    (hb : PrfH Γ (boundedAllIn c L₁)) : PrfH Γ (boundedAllIn c L₂) := by
  let f : Formula := boundedAllIn (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = boundedAllIn c s := by
    intro s
    simp only [f, substFormula_boundedAllIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS L₂) ▸ PrfH_leibniz_subst (A := f) h ((hS L₁) ▸ hb)

theorem pcc_boundedAllIn_tracked (c L : Term) :
    Prf (boundedAllIn c L ⇒ provFromCode (bdAllCode (tcFn (lenc L)) (PsiIn c L))) := by
  refine prf_deduction ?_
  have hcar : Prf (carc (cons c L) =eq c) := prf_carc_cons c L
  have hcdr : Prf (cdrc (cons c L) =eq L) := prf_cdrc_cons c L
  have hb : PrfH [boundedAllIn c L] (CFin (cons c L)) :=
    PrfH_congr_boundedAllIn1 (prf_to_prfH (prf_eq_symm hcar) _)
      (PrfH_congr_boundedAllIn2 (prf_to_prfH (prf_eq_symm hcdr) _) (prfH_hyp_self _))
  have h1 : PrfH [boundedAllIn c L]
      (provFromCode (bdAllCode (tcFn (bndFin (cons c L))) (PsiFin (cons c L)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_bdAllIn_pair (cons c L)) _) hb
  refine PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr ?_) _) h1
  refine prf_congr_bdAllCode (prf_congr_tcFn (prf_congr_lenc hcdr)) ?_
  exact prf_congr_inFormCodeFn (prf_congr_nthcT (prf_congr_tcFn hcdr) (prf_refl _))
    (prf_congr_tcFn hcar)

/-- **EL RELECTOR DEL ÁTOMO `allIn`**, con `c` y `L` ABSTRACTOS. CERO axiomas nuevos. -/
theorem pcc_allIn_atom_tracked (c L : Term) :
    Prf (allIn c L ⇒ provFromCode (allInFn (tcFn c) (tcFn L))) := by
  refine prf_deduction ?_
  have hb : PrfH [allIn c L] (boundedAllIn c L) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedAllIn_of_allIn c L) _) (prfH_hyp_self _)
  have h1 : PrfH [allIn c L] (provFromCode (bdAllCode (tcFn (lenc L)) (PsiIn c L))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedAllIn_tracked c L) _) hb
  have heq : Prf (provFromCode (eqc (tcFn (lenc L)) (lencT (tcFn L)))) :=
    prfH_nil_to_prf (PrfH_eq_symm_code _ _ (substtc_inv_lencT (substtc_inv_tcFn L))
      (prf_to_prfH (pcc_eval_lenc L) [])) rfl
  have hswap := pcc_bdAll_bound_swap (tcFn (lenc L)) (lencT (tcFn L)) (PsiIn c L)
    (prf_liftc_tcFn _) (hlift_B2 L) (prf_substfc_PsiIn_at1 c L) heq
  have h2 : PrfH [allIn c L] (provFromCode (bdAllInDot c L)) :=
    PrfH.mp _ _ _ (prf_to_prfH hswap _) h1
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_AllInBwd_computed c L) _) h2

/-! ## 13 · CIERRE: la hipótesis se descarga -/

theorem AllInReflector_ok : AllInReflector := pcc_allIn_atom_tracked

/-- **A3 PARA EL PREDICADO SIN `wTs`**, con `allIn` dotado COMO ÁTOMO. SIN hipótesis. -/
theorem pcc_wfAll_tracked_closed (w : Term) :
    Prf (wfAll1' w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_wfAll_tracked AllInReflector_ok w

theorem pcc_isTC1_tracked_closed (w c : Term) :
    Prf (isTC1' w c ⇒ provFromCode (isTC1Dot w c)) :=
  pcc_isTC1_tracked AllInReflector_ok w c

/-! ## 14 · SIN NINGUNA DESVIACIÓN: el predicado OBJETO **literal** de
       `sondeos/ClausuraLiftSinWTs.lean` (con `argsIn`, no con `allIn`)

    El átomo `allIn` NO hace falta en el objeto: basta en la IMAGEN PUNTEADA. El objeto se
    queda exactamente como estaba (y por tanto sigue valiendo la clausura bajo `liftc 0`
    probada ayer); el paso `argsIn ⇒ allIn` es `prf_allIn_of_boundedAllIn`, de producción. -/

/-- Copia LITERAL de `sondeos/ClausuraLiftSinWTs.lean:109` — y `= boundedAllIn` por `rfl`. -/
def argsIn (wT Y : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT)))

theorem argsIn_eq_boundedAllIn (wT Y : Term) : argsIn wT Y = boundedAllIn wT Y := rfl

/-- Copia LITERAL de `sondeos/ClausuraLiftSinWTs.lean:134`. -/
def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prf₀.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prf₀.j2 A B)

theorem prf_and_mono_right {A B B' : Formula} (h : Prf (B ⇒ B')) :
    Prf (land A B ⇒ land A B') := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land A B)
  exact PrfH_and_intro (PrfH_and_elim_left hh)
    (PrfH.mp _ _ _ (prf_to_prfH h _) (PrfH_and_elim_right hh))

/-- Las DOS formas del disyunto son provablemente EQUIVALENTES: nada se ha reforzado. -/
theorem prf_isTCE1_of_literal (wT X : Term) :
    Prf (isTermCodeE1 wT X ⇒ isTermCodeE1' wT X) :=
  prf_or_elim_imp (prf_lorL _ _)
    (impT (prf_and_mono_right (prf_allIn_of_boundedAllIn wT (nthc X (numeralM 2))))
      (prf_lorR _ _))

theorem prf_literal_of_isTCE1 (wT X : Term) :
    Prf (isTermCodeE1' wT X ⇒ isTermCodeE1 wT X) :=
  prf_or_elim_imp (prf_lorL _ _)
    (impT (prf_and_mono_right (prf_boundedAllIn_of_allIn wT (nthc X (numeralM 2))))
      (prf_lorR _ _))

theorem hCl_lit : ∀ (k : Nat) (q : Term), liftFormula k (wfAll1 q) = wfAll1 (liftTerm k q) := by
  intro k q
  simp only [wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn_eq_boundedAllIn,
    liftFormula_boundedAllIn_gen, lor, land, lt, lenc, nthc, cons, nil, zero,
    liftFormula, liftTerm, liftTerms, liftTerm_numeralM,
    if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCs_lit : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAll1 q) = wfAll1 (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn_eq_boundedAllIn,
    substFormula_boundedAllIn, lor, land, lt, lenc, nthc, cons, nil, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

theorem hbody_lit : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q)
    ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll1 q] rfl)
  have hlt : PrfH [lt i (lenc q), wfAll1 q] (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (lenc q), wfAll1 q] (wfAll1 q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (wfAll1Body q)
      = Formula.impl (lt i (lenc q)) (isTermCodeE1 q (nthc q i)) := by
    simp only [wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn_eq_boundedAllIn,
      substFormula_boundedAllIn, lor, land, lt, lenc, nthc, cons, nil, zero,
      substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (lenc q), wfAll1 q] _
    (Prf₀.q1 (wfAll1Body q) i)) hwf
  rw [hsubst] at h0
  have hnode : PrfH [lt i (lenc q), wfAll1 q] (isTermCodeE1' q (nthc q i)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_isTCE1_of_literal q (nthc q i)) _)
      (PrfH.mp _ _ _ h0 hlt)
  have hpure : PrfH [lt i (lenc q), wfAll1 q]
      (provFromCode (isTCE1Dot (tcFn q) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_isTCE1_pure AllInReflector_ok q (nthc q i)) _) hnode
  have hev : PrfH [lt i (lenc q), wfAll1 q]
      (provFromCode (eqCodeFn (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hevS : PrfH [lt i (lenc q), wfAll1 q]
      (provFromCode (eqCodeFn (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  have hC : ∀ t : Term,
      Prf (substfc zero t (isTCE1Dot (tcFn q) (varc (numeral 0))) =eq isTCE1Dot (tcFn q) t) :=
    fun t => prf_substfc_isTCE1Dot_gen t (tcFn q) (varc (numeral 0)) t
      (substtc_inv_tcFn q) (prf_substtc_varc0 t)
  have h1 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hC _))) _) hpure
  have h2 := PrfH_leibniz_apply _ _ _ hevS h1
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hC _)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF q (tcFn i)))) _) h3

/-- **EL RESULTADO**, sobre el predicado objeto LITERAL de la vía sin `wTs`:
    `pcc_wfAll_tracked` sale en UNA LÍNEA, como en A3. -/
theorem pcc_wfAll_tracked_lit (w : Term) :
    Prf (wfAll1 w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_bdAll_intro wfAll1 lenc PsiF w hCl_lit hCs_lit hbl_ok hbs_ok hPl_ok hPs_ok hPsiId_ok
    hbody_lit

/-- Y el reconocedor entero. -/
theorem pcc_isTC1_tracked_lit (w c : Term) :
    Prf (isTC1 w c ⇒ provFromCode (isTC1Dot w c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTC1 w c)
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll_tracked_lit w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! ## 14bis · BONUS — la COTA en forma COMPUTADA

    A3 declaró como «DESVIACIÓN 2» que la cota sale en reflexión pura `tcFn (lenc w)` y no
    evaluada `lencT (tcFn w)`, y difirió el arreglo («cuesta un lema entero: una segunda
    travesía estructural de `PsiF` a nivel 1»). **`pcc_bdAll_bound_swap` lo cierra**: la
    travesía a nivel 1 son 12 líneas y la conversión, una línea. -/

theorem prf_substfc_isTCE1Dot_at1 (V W X : Term)
    (hW : Prf (substtc (succ zero) V W =eq W)) (hX : Prf (substtc (succ zero) V X =eq X)) :
    Prf (substfc (succ zero) V (isTCE1Dot W X) =eq isTCE1Dot W X) := by
  have hshape : ∀ k n : Nat,
      Prf (substfc (succ zero) V (shapeDot X k n) =eq shapeDot X k n) := by
    intro k n
    unfold shapeDot
    refine prf_eq_trans (prf_substfc_and (succ zero) V _ _) (prf_congr_andc ?_ ?_)
    · refine prf_eq_trans (prf_substfc_eq (succ zero) V _ _) (prf_congr_eqCodeFn ?_ ?_)
      · exact prf_eq_trans (prf_substtc_carcT (succ zero) V X) (prf_congr_carcT hX)
      · exact prf_substtc_tcFn_at 1 V (numeralM k)
    · refine prf_eq_trans (prf_substfc_eq (succ zero) V _ _) (prf_congr_eqCodeFn ?_ ?_)
      · exact prf_eq_trans (prf_substtc_lencT (succ zero) V X) (prf_congr_lencT hX)
      · exact prf_substtc_tcFn_at 1 V (numeralM n)
  unfold isTCE1Dot
  refine prf_eq_trans (prf_substfc_or (succ zero) V _ _) (prf_congr_orc (hshape 0 2) ?_)
  refine prf_eq_trans (prf_substfc_and (succ zero) V _ _) (prf_congr_andc (hshape 1 3) ?_)
  exact prf_substfc_allIn_at (succ zero) V W W _ _ hW
    (prf_eq_trans (prf_substtc_nthcT (succ zero) V X (tcFn (numeralM 2)))
      (prf_congr_nthcT hX (prf_substtc_tcFn_at 1 V (numeralM 2))))

theorem prf_substfc_PsiF_at1 (w V : Term) :
    Prf (substfc (succ zero) V (PsiF w) =eq PsiF w) :=
  prf_substfc_isTCE1Dot_at1 V (tcFn w) _ (prf_substtc_tcFn_at 1 V w)
    (prf_eq_trans (prf_substtc_nthcT (succ zero) V (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (prf_substtc_tcFn_at 1 V w) (prf_substtc_varc0_at1 V)))

/-- La imagen punteada con la cota **evaluada**. -/
noncomputable def wfAll1DotC (w : Term) : Term := bdAllCode (lencT (tcFn w)) (PsiF w)

theorem pcc_wfAll_tracked_lit_computed (w : Term) :
    Prf (wfAll1 w ⇒ provFromCode (wfAll1DotC w)) :=
  impT (pcc_wfAll_tracked_lit w)
    (pcc_bdAll_bound_swap (tcFn (lenc w)) (lencT (tcFn w)) (PsiF w)
      (prf_liftc_tcFn _) (hlift_B2 w) (prf_substfc_PsiF_at1 w)
      (prfH_nil_to_prf (PrfH_eq_symm_code _ _ (substtc_inv_lencT (substtc_inv_tcFn w))
        (prf_to_prfH (pcc_eval_lenc w) [])) rfl))

/-! ## 15 · NO VACUIDAD — instancia CERRADA extremo a extremo

    (La lección de A3: un antecedente reforzado puede dejar el teorema VERDADERO Y VACÍO.
    Aquí no se ha reforzado nada — §14 lo prueba —, pero se comprueba igualmente que hay
    testigo real: el código de la variable `#0`, `varc 0 = ⟨0,0⟩`.) -/

def Xv : Term := varc zero
def wV : Term := cons Xv nil

theorem prf_nthc_one_Xv : Prf (nthc Xv (numeralM 1) =eq zero) :=
  prf_eq_trans (prf_nthc_succ zero (cons zero nil) zero) (prf_nthc_zero zero nil)

theorem prf_shapeUn_Xv : Prf (shapeUn Xv 0) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head prf_nthc_one_Xv))

theorem prf_isTermCodeE1_Xv (w : Term) : Prf (isTermCodeE1 w Xv) :=
  prf_mp (prf_lorL _ _) prf_shapeUn_Xv

theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula :=
    Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (isTermCodeE1 w X₁)) : PrfH Γ (isTermCodeE1 w X₂) := by
  let f : Formula := isTermCodeE1 (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermCodeE1 w s := by
    intro s
    simp only [f, isTermCodeE1, shapeUn, shapeBin, argsIn_eq_boundedAllIn,
      substFormula_boundedAllIn, lor, land, lt, lenc, nthc, cons, nil, zero,
      substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_isTC1_Xv : Prf (isTC1 wV Xv) := by
  refine prf_and_intro ?_ (prf_in_cons_head Xv nil)
  refine Prf.gen _ (prf_deduction ?_)
  have hlift : liftTerm 0 wV = wV := by
    simp only [wV, Xv, varc, cons, nil, zero, liftTerm, liftTerms]
  rw [hlift]
  have hlen : Prf (Formula.eq (lenc wV) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons Xv nil) (prf_eq_congr_succ prf_lenc_nil)
  have hlt1 : PrfH [lt (.var 0) (lenc wV)] (lt (.var 0) (succ zero)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH hlen _)
      (PrfH.hyp _ _ (List.Mem.head _))
  have hsplit : PrfH [lt (.var 0) (lenc wV)]
      (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) hlt1
  refine PrfH_or_elim hsplit ?brA ?brB
  case brA =>
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) (PrfH.hyp _ _ (List.Mem.head _)))
  case brB =>
    have hi : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (lenc wV)])
        (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (lenc wV)])
        (Formula.eq (nthc wV (.var 0)) Xv) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := wV) hi)
        (prf_to_prfH (prf_nthc_zero Xv nil) _)
    exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hX) (prf_to_prfH (prf_isTermCodeE1_Xv wV) _)

/-- **INSTANCIA CERRADA**: `⊢ Prov(⌜ isTC1(⟨⌜v₀⌝⟩, ⌜v₀⌝) ⌝)`. El teorema NO es vacío. -/
theorem pcc_isTC1_Xv : Prf (provFromCode (isTC1Dot wV Xv)) :=
  prf_mp (pcc_isTC1_tracked_lit wV Xv) prf_isTC1_Xv

end ReflAtomo

set_option pp.explicit false in
#check @ReflAtomo.pcc_wfAll_tracked_lit
#check @ReflAtomo.pcc_isTC1_tracked_lit
#check @ReflAtomo.pcc_allIn_atom_tracked
#check @ReflAtomo.pcc_wfAll_tracked_closed
#check @ReflAtomo.pcc_isTC1_tracked_closed

#print axioms ReflAtomo.pcc_wfAll_tracked_lit
#print axioms ReflAtomo.pcc_isTC1_tracked_lit
#print axioms ReflAtomo.pcc_wfAll_tracked_lit_computed
#print axioms ReflAtomo.prf_isTC1_Xv
#print axioms ReflAtomo.pcc_isTC1_Xv
#print axioms ReflAtomo.prf_isTCE1_of_literal
#print axioms ReflAtomo.prf_literal_of_isTCE1
#print axioms ReflAtomo.pcc_allIn_atom_tracked
#print axioms ReflAtomo.pcc_boundedAllIn_tracked
#print axioms ReflAtomo.pcc_bdAll_bound_swap
#print axioms ReflAtomo.pcc_wfAll_tracked_closed
#print axioms ReflAtomo.pcc_isTC1_tracked_closed
#print axioms ReflAtomo.pcc_bdAllIn_pair
#print axioms ReflAtomo.pcc_AllInBwd_computed
#print axioms ReflAtomo.pcc_In_atom_tracked
#print axioms ReflAtomo.hbody_ok
#print axioms ReflAtomo.pcc_wfAll_tracked
#print axioms ReflAtomo.pcc_isTC1_tracked
#print axioms ReflAtomo.pcc_shapeUn_tracked
#print axioms ReflAtomo.pcc_shapeBin_tracked
#print axioms ReflAtomo.hPl_ok
#print axioms ReflAtomo.hCl_ok
#print axioms ReflAtomo.hCs_ok
#print axioms ReflAtomo.hPsiId_ok

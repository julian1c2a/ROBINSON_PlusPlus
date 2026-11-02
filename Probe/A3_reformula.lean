/-
A3 — ESTRATEGIA 4: REFORMULAR PARA ESQUIVAR EL BINDER.

Objetivo:  pcc_isFCB_tracked (w c) : Prf (isFCB w c ⇒ provFromCode (isFCBDot w c))
con `w` y `c` ABSTRACTOS y footprint sancionado.

    lake env lean Probe/A3_reformula.lean
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
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf

namespace A3Reformula

/-! # 1 · EL OBJETO REFORMULADO

    Frente a `sondeos/ParseWitness.lean` hay UNA sola enmienda: el conjunto `consOk X`
    («el nodo es un `cons`»). Es OBJETO puro y NO aparece en la imagen punteada. -/

def nulOk (X : Term) (k : Nat) : Formula :=
  land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 1))

def unOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

def binOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w))

def strBinOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

def varOk (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- **ENMIENDA**: el nodo es un `cons`. Desbloquea los puentes `carcT`/`cdrcT`. -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def nodeOk (w X : Term) : Formula :=
  land (consOk X)
    (lorAll (nulOk X 2)
      [ strBinOk w X 3, binOk w X 4, binOk w X 5, unOk w X 6, binOk w X 7, binOk w X 8
      , unOk w X 9, varOk X, strBinOk w X 1
      , Formula.eq X nil
      , land (In (carc X) w) (In (cdrc X) w) ])

def wfAll (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCB (w c : Term) : Formula := land (wfAll w) (In c w)

/-! # 2 · LA IMAGEN PUNTEADA — **SIN NI UN BINDER**

    La reformulación decisiva: `In` se dota como su **ÁTOMO** (`inFormCodeFn`, que ya existe
    en producción), no como su despliegue `∃`-acotado. Con eso el cuerpo del `∀` acotado
    NO contiene ningún `exc`, y todo el descenso de `substfc` vive a NIVEL 0. -/

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

noncomputable def unDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 2) (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)

noncomputable def binDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3)
    (andc (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)
          (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W))

noncomputable def strBinDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3) (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W)

noncomputable def varDot (X : Term) : Term := shapeDot X 0 2

def lorAllc : Term → List Term → Term
  | a, []      => a
  | a, b :: bs => orc a (lorAllc b bs)

/-- **El nodo dotado, 12 casos, CERO binders.** -/
noncomputable def nodeOkDot (W X : Term) : Term :=
  lorAllc (shapeDot X 2 1)
    [ strBinDot W X 3
    , binDot W X 4
    , binDot W X 5
    , unDot  W X 6
    , binDot W X 7
    , binDot W X 8
    , unDot  W X 9
    , varDot X
    , strBinDot W X 1
    , eqCodeFn X (tcFn nil)
    , andc (inFormCodeFn (carcT X) W) (inFormCodeFn (cdrcT X) W) ]

/-- El cuerpo del `∀` acotado, con el hueco `⌜v₀⌝` en el ÍNDICE. -/
noncomputable def PsiF (w : Term) : Term :=
  nodeOkDot (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

noncomputable def wfAllDot (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiF w)

noncomputable def isFCBDot (w c : Term) : Term :=
  andc (wfAllDot w) (inFormCodeFn (tcFn c) (tcFn w))

/-! # 3 · EL DESCENSO GENÉRICO de `substfc zero s` — íntegramente a NIVEL 0 -/

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

theorem prf_substfc_unDot (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (unDot W X k) =eq unDot W X' k) := by
  unfold unDot
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 2 hX)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 1 hX) hW))

theorem prf_substfc_binDot (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (binDot W X k) =eq binDot W X' k) := by
  unfold binDot
  refine prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 3 hX) ?_)
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 1 hX) hW)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 2 hX) hW))

theorem prf_substfc_strBinDot (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (strBinDot W X k) =eq strBinDot W X' k) := by
  unfold strBinDot
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 3 hX)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 2 hX) hW))

/-- **EL DESCENSO**: `substfc zero s` atraviesa los 12 disyuntos y sólo toca el hueco de `X`. -/
theorem prf_substfc_nodeOkDot_gen (s W X X' : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (nodeOkDot W X) =eq nodeOkDot W X') := by
  unfold nodeOkDot lorAllc
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 2 1 hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_strBinDot s W X X' 3 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 4 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 5 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_unDot s W X X' 6 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 7 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 8 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_unDot s W X X' 9 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 0 2 hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_strBinDot s W X X' 1 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _) (prf_congr_orc ?_ ?_)
  · exact prf_eq_trans (prf_substfc_eq zero s _ _)
      (prf_congr_eqCodeFn hX (substtc_inv_tcFn nil s))
  · refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
    · exact prf_substfc_inDot s _ _ W
        (prf_eq_trans (prf_substtc_carcT zero s X) (prf_congr_carcT hX)) hW
    · exact prf_substfc_inDot s _ _ W
        (prf_eq_trans (prf_substtc_cdrcT zero s X) (prf_congr_cdrcT hX)) hW

/-- El descenso instanciado en el cuerpo real. -/
theorem prf_substfc_PsiF (w s : Term) :
    Prf (substfc zero s (PsiF w) =eq nodeOkDot (tcFn w) (nthcT (tcFn w) s)) :=
  prf_substfc_nodeOkDot_gen s (tcFn w) _ _ (substtc_inv_tcFn w)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s)))

/-- **`hPsiId`, GRATIS**: el RHS del descenso en `s := ⌜v₀⌝` es DEFINICIONALMENTE `PsiF w`.
    Esto es exactamente lo que un `exc` en el cuerpo impediría. -/
theorem hPsiId_ok (q : Term) :
    Prf (substfc zero (varc (numeral 0)) (PsiF q) =eq PsiF q) :=
  prf_substfc_PsiF q (varc (numeral 0))

/-! # 4 · Las obligaciones MECÁNICAS de `pcc_bdAll_intro` -/

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hPl_ok : ∀ (k : Nat) (q : Term), liftTerm k (PsiF q) = PsiF (liftTerm k q) := by
  intro k q
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, atomc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral,
    liftTerm_strCode]

theorem hPs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (PsiF q) = PsiF (substTerm v t q) := by
  intro v t q
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, atomc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral,
    substTerm_strCode]

theorem substTerm_numeralM (v : Nat) (s : Term) : ∀ n : Nat,
    substTerm v s (numeralM n) = numeralM n
  | 0     => by simp only [numeralM, zero, substTerm, substTerms]
  | n + 1 => by
      simp only [numeralM, succ, substTerm, substTerms, substTerm_numeralM v s n]

theorem liftTerm_numeralM (c : Nat) : ∀ n : Nat, liftTerm c (numeralM n) = numeralM n
  | 0     => by simp only [numeralM, zero, liftTerm, liftTerms]
  | n + 1 => by simp only [numeralM, succ, liftTerm, liftTerms, liftTerm_numeralM c n]

theorem hCl_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAll q) = wfAll (liftTerm k q) := by
  intro k q
  simp only [wfAll, nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
    lt, carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCs_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAll q) = wfAll (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAll, nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
    lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

/-! # 5 · EL REFLECTOR DEL ÁTOMO `In`, con `x` y `w` ABSTRACTOS

    A1 (`sondeos/InTracked.lean`) da la forma `∃`-acotada; el puente `pcc_InBwd_computed`
    la convierte DENTRO de `Prov` al átomo. Es el gemelo de `pcc_ltBwd_computed`. -/

noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))
noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))
noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

def phiInBwd : Formula := Formula.impl (boundedIn (.var 1) (.var 0)) (In (.var 1) (.var 0))

theorem InBwd : Prf (forall_2 phiInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_In_of_boundedIn (.var 1) (.var 0)))

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

theorem substtc_inv_bdInB (w : Term) : ∀ W, Prf (substtc zero W (bdInB w) =eq bdInB w) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn w)

theorem liftTerm_bdInDot (c : Nat) (x w : Term) :
    liftTerm c (bdInDot x w) = bdInDot (liftTerm c x) (liftTerm c w) := by
  unfold bdInDot bdInB bdInPhic bdExCode
  simp only [exc, andc, ltCodeFn, atom2CodeFn, eqCodeFn, lencT, nthcT, funcc, varc, liftc, tcFn,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- **A1** (copia literal de `sondeos/InTracked.lean`). -/
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

/-- **El reflector del ÁTOMO `In`**, con `x` y `w` ABSTRACTOS. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

/-! # 6 · Los puentes `carcT` / `cdrcT`, desgatillados por `consOk` -/

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons : PrfH [consOk X] (X =eq cons (carc X) (cdrc X)) := prfH_hyp_self _
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

theorem PrfH_congr_cdrcT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (cdrcT x =eq cdrcT y) := by
  unfold cdrcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_congr_cons_head h)))

theorem pcc_cdrcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (cdrcT (tcFn X)) (tcFn (cdrc X)))) := by
  refine prf_deduction ?_
  have hcons : PrfH [consOk X] (X =eq cons (carc X) (cdrc X)) := prfH_hyp_self _
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_cdrcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_cdrc (carc X) (cdrc X)) _)

/-! # 7 · Herramientas `PrfH` sobre códigos -/

/-- Reescritura interna con hueco `⌜v₀⌝` — versión `PrfH` de `pcc_rw`. -/
theorem PrfH_rw {Γ : List Formula} (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : PrfH Γ (provFromCode (eqc X Y)))
    (hbase : PrfH Γ (provFromCode (G X))) : PrfH Γ (provFromCode (G Y)) := by
  have h1 : PrfH Γ (provFromCode (substfc zero X (G (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hG X))) _) hbase
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hG Y)) _)
    (PrfH_leibniz_apply _ X Y heq h1)

theorem PrfH_or_introL_code {Γ : List Formula} {Ac Bc : Term}
    (h : PrfH Γ (provFromCode Ac)) : PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH_mp_code_apply (prf_to_prfH (pcc_j1_code Ac Bc) _) h

theorem PrfH_or_introR_code {Γ : List Formula} {Ac Bc : Term}
    (h : PrfH Γ (provFromCode Bc)) : PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH_mp_code_apply (prf_to_prfH (pcc_j2_code Ac Bc) _) h

/-- De un PUENTE `Prov(T = ṫ)` y un hecho OBJETO `t = u` sale `Prov(T = u̇)`. -/
theorem PrfH_eqDot_via {Γ : List Formula} (T t u : Term)
    (hinv : ∀ V, Prf (substtc zero V T =eq T))
    (hbr : PrfH Γ (provFromCode (eqc T (tcFn t))))
    (hobj : PrfH Γ (t =eq u)) :
    PrfH Γ (provFromCode (eqCodeFn T (tcFn u))) :=
  PrfH_eq_trans_code T (tcFn t) (tcFn u) hinv hbr
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked t u) _) hobj)

/-- De un PUENTE `Prov(T = ṫ)` y un hecho OBJETO `In t w` sale `Prov(⌜T ∈ ẇ⌝)`.
    ⚠️ Aquí se ve la ganancia de la reformulación: el hueco NO está bajo ningún binder,
    así que `PrfH_rw` (un `substfc zero`) lo alcanza. -/
theorem PrfH_inDot_via {Γ : List Formula} (T t w : Term)
    (hinv : ∀ V, Prf (substtc zero V T =eq T))
    (hbr : PrfH Γ (provFromCode (eqc T (tcFn t))))
    (hobj : PrfH Γ (In t w)) :
    PrfH Γ (provFromCode (inFormCodeFn T (tcFn w))) := by
  have hbase : PrfH Γ (provFromCode (inFormCodeFn (tcFn t) (tcFn w))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked t w) _) hobj
  have hsym : PrfH Γ (provFromCode (eqc (tcFn t) T)) := PrfH_eq_symm_code T (tcFn t) hinv hbr
  refine PrfH_rw (fun s => inFormCodeFn s (tcFn w)) (fun s => ?_) (tcFn t) T hsym hbase
  exact prf_substfc_inDot s (varc (numeral 0)) s (tcFn w) (prf_substtc_varc0 s)
    (substtc_inv_tcFn w)

/-! # 8 · LOS 12 CASOS DE `nodeOk`, reflejados en forma COMPUTADA -/

/-- Los dos `=eq` de todo nodo (tag + longitud), ya en forma computada `carcT Ẋ` / `lencT Ẋ`. -/
theorem PrfH_shapeDot_tracked {Γ : List Formula} (X : Term) (k n : Nat)
    (hcarcBr : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))))
    (hk : PrfH Γ (carc X =eq numeralM k))
    (hn : PrfH Γ (lenc X =eq numeralM n)) :
    PrfH Γ (provFromCode (shapeDot (tcFn X) k n)) :=
  PrfH_and_intro_code _ _
    (PrfH_eqDot_via _ _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hcarcBr hk)
    (PrfH_eqDot_via _ _ _ (substtc_inv_lencT (substtc_inv_tcFn X))
      (prf_to_prfH (pcc_eval_lenc X) _) hn)

/-- Un HIJO: de `In (nthc X j̄) w` sale `Prov(⌜nthc(Ẋ, j̇) ∈ ẇ⌝)`.
    La cota `j < lenc X` la da la longitud del nodo (`lenc X = n̄`, `j < n`). -/
theorem PrfH_child_tracked {Γ : List Formula} (w X : Term) (j n : Nat) (hjn : j < n)
    (hn : PrfH Γ (lenc X =eq numeralM n))
    (hin : PrfH Γ (In (nthc X (numeralM j)) w)) :
    PrfH Γ (provFromCode (inFormCodeFn (nthcT (tcFn X) (tcFn (numeralM j))) (tcFn w))) := by
  have hltN : Prf (lt (numeralM j) (numeralM n)) := by
    rw [numeralM_eq, numeralM_eq]; exact prf_gnum_lt hjn
  have hlt : PrfH Γ (lt (numeralM j) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hn) (prf_to_prfH hltN _)
  have hbr : PrfH Γ (provFromCode (evalNthcCode X (numeralM j))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hlt
  exact PrfH_inDot_via _ _ w
    (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM j))) hbr hin

theorem PrfH_nulDot_tracked {Γ : List Formula} (X : Term) (k : Nat)
    (hcarcBr : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))))
    (h : PrfH Γ (nulOk X k)) : PrfH Γ (provFromCode (shapeDot (tcFn X) k 1)) :=
  PrfH_shapeDot_tracked X k 1 hcarcBr (PrfH_and_elim_left h) (PrfH_and_elim_right h)

theorem PrfH_varDot_tracked {Γ : List Formula} (X : Term)
    (hcarcBr : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))))
    (h : PrfH Γ (varOk X)) : PrfH Γ (provFromCode (varDot (tcFn X))) :=
  PrfH_shapeDot_tracked X 0 2 hcarcBr (PrfH_and_elim_left h) (PrfH_and_elim_right h)

theorem PrfH_unDot_tracked {Γ : List Formula} (w X : Term) (k : Nat)
    (hcarcBr : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))))
    (h : PrfH Γ (unOk w X k)) : PrfH Γ (provFromCode (unDot (tcFn w) (tcFn X) k)) :=
  PrfH_and_intro_code _ _
    (PrfH_shapeDot_tracked X k 2 hcarcBr
      (PrfH_and_elim_left (PrfH_and_elim_left h)) (PrfH_and_elim_right (PrfH_and_elim_left h)))
    (PrfH_child_tracked w X 1 2 (by omega)
      (PrfH_and_elim_right (PrfH_and_elim_left h)) (PrfH_and_elim_right h))

theorem PrfH_binDot_tracked {Γ : List Formula} (w X : Term) (k : Nat)
    (hcarcBr : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))))
    (h : PrfH Γ (binOk w X k)) : PrfH Γ (provFromCode (binDot (tcFn w) (tcFn X) k)) :=
  PrfH_and_intro_code _ _
    (PrfH_shapeDot_tracked X k 3 hcarcBr
      (PrfH_and_elim_left (PrfH_and_elim_left h)) (PrfH_and_elim_right (PrfH_and_elim_left h)))
    (PrfH_and_intro_code _ _
      (PrfH_child_tracked w X 1 3 (by omega)
        (PrfH_and_elim_right (PrfH_and_elim_left h))
        (PrfH_and_elim_left (PrfH_and_elim_right h)))
      (PrfH_child_tracked w X 2 3 (by omega)
        (PrfH_and_elim_right (PrfH_and_elim_left h))
        (PrfH_and_elim_right (PrfH_and_elim_right h))))

theorem PrfH_strBinDot_tracked {Γ : List Formula} (w X : Term) (k : Nat)
    (hcarcBr : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))))
    (h : PrfH Γ (strBinOk w X k)) : PrfH Γ (provFromCode (strBinDot (tcFn w) (tcFn X) k)) :=
  PrfH_and_intro_code _ _
    (PrfH_shapeDot_tracked X k 3 hcarcBr
      (PrfH_and_elim_left (PrfH_and_elim_left h)) (PrfH_and_elim_right (PrfH_and_elim_left h)))
    (PrfH_child_tracked w X 2 3 (by omega)
      (PrfH_and_elim_right (PrfH_and_elim_left h)) (PrfH_and_elim_right h))

/-- ⚠️ Trampa: `simp` NO cierra `List.Mem A Δ` (su cabeza es `List.Mem`, no `Membership.mem`,
    y con `Minimal.Axioms` abierto `∈` es el `In` OBJETO). Con estos dos combinadores la
    pertenencia se escribe a mano y sin ruido. -/
theorem memH {A : Formula} {Δ : List Formula} : List.Mem A (A :: Δ) := List.Mem.head _
theorem memT {A B : Formula} {Δ : List Formula} (h : List.Mem A Δ) : List.Mem A (B :: Δ) :=
  List.Mem.tail _ h

/-- **A2 COMPLETA**: los 12 casos, con `w` y `X` ABSTRACTOS, en la forma COMPUTADA. -/
theorem pcc_nodeOk_tracked (w X : Term) :
    Prf (nodeOk w X ⇒ provFromCode (nodeOkDot (tcFn w) (tcFn X))) := by
  refine prf_deduction ?_
  have hcarc : ∀ Δ : List Formula, List.Mem (nodeOk w X) Δ →
      PrfH Δ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := fun Δ hm =>
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) Δ)
      (PrfH_and_elim_left (PrfH.hyp _ _ hm))
  have hcdrc : ∀ Δ : List Formula, List.Mem (nodeOk w X) Δ →
      PrfH Δ (provFromCode (eqCodeFn (cdrcT (tcFn X)) (tcFn (cdrc X)))) := fun Δ hm =>
    PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcD_bridge_cons X) Δ)
      (PrfH_and_elim_left (PrfH.hyp _ _ hm))
  have hdis : PrfH [nodeOk w X]
      (lorAll (nulOk X 2)
        [ strBinOk w X 3, binOk w X 4, binOk w X 5, unOk w X 6, binOk w X 7, binOk w X 8
        , unOk w X 9, varOk X, strBinOk w X 1
        , Formula.eq X nil
        , land (In (carc X) w) (In (cdrc X) w) ]) :=
    PrfH_and_elim_right (prfH_hyp_self _)
  refine PrfH_or_elim hdis ?_ ?_
  · refine PrfH_or_introL_code
      (PrfH_nulDot_tracked X 2 ?_ (PrfH.hyp _ _ (List.Mem.head _)))
    exact hcarc _ (memT (memH))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introL_code
      (PrfH_strBinDot_tracked w X 3 ?_ (PrfH.hyp _ _ (List.Mem.head _))))
    exact hcarc _ (memT (memT (memH)))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introL_code
      (PrfH_binDot_tracked w X 4 ?_ (PrfH.hyp _ _ (List.Mem.head _)))))
    exact hcarc _ (memT (memT (memT (memH))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introL_code
      (PrfH_binDot_tracked w X 5 ?_ (PrfH.hyp _ _ (List.Mem.head _))))))
    exact hcarc _ (memT (memT (memT (memT (memH)))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introL_code
        (PrfH_unDot_tracked w X 6 ?_ (PrfH.hyp _ _ (List.Mem.head _)))))))
    exact hcarc _ (memT (memT (memT (memT (memT (memH))))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introL_code
        (PrfH_binDot_tracked w X 7 ?_ (PrfH.hyp _ _ (List.Mem.head _))))))))
    exact hcarc _ (memT (memT (memT (memT (memT (memT (memH)))))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introL_code
        (PrfH_binDot_tracked w X 8 ?_ (PrfH.hyp _ _ (List.Mem.head _)))))))))
    exact hcarc _ (memT (memT (memT (memT (memT (memT (memT (memH))))))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introL_code
        (PrfH_unDot_tracked w X 9 ?_ (PrfH.hyp _ _ (List.Mem.head _))))))))))
    exact hcarc _ (memT (memT (memT (memT (memT (memT (memT (memT (memH)))))))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
        (PrfH_or_introL_code
          (PrfH_varDot_tracked X ?_ (PrfH.hyp _ _ (List.Mem.head _)))))))))))
    exact hcarc _ (memT (memT (memT (memT (memT (memT (memT (memT (memT (memH))))))))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
        (PrfH_or_introR_code (PrfH_or_introL_code
          (PrfH_strBinDot_tracked w X 1 ?_ (PrfH.hyp _ _ (List.Mem.head _))))))))))))
    exact hcarc _ (memT (memT (memT (memT (memT (memT (memT (memT (memT (memT (memH)))))))))))
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
        (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introL_code
          (PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked X nil) _)
            (PrfH.hyp _ _ (List.Mem.head _)))))))))))))
  · refine PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
      (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
        (PrfH_or_introR_code (PrfH_or_introR_code (PrfH_or_introR_code
          (PrfH_and_intro_code _ _
            (PrfH_inDot_via (carcT (tcFn X)) (carc X) w
              (substtc_inv_carcT (substtc_inv_tcFn X)) ?_
              (PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))))
            (PrfH_inDot_via (cdrcT (tcFn X)) (cdrc X) w
              (substtc_inv_cdrcT (substtc_inv_tcFn X)) ?_
              (PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _)))))))))))))))
    · exact hcarc _ (memT (memT (memT (memT (memT (memT (memT (memT (memT (memT (memT (memH))))))))))))
    · exact hcdrc _ (memT (memT (memT (memT (memT (memT (memT (memT (memT (memT (memT (memH))))))))))))

/-! # 9 · `hbody` y el ENSAMBLAJE -/

theorem hbody_ok (q i : Term) :
    Prf (wfAll q ⇒ (lt i (lenc q) ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll q] rfl)
  let Γ : List Formula := [lt i (lenc q), wfAll q]
  show PrfH Γ (provFromCode (substfc zero (tcFn i) (PsiF q)))
  have hw : PrfH Γ (wfAll q) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Γ (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hsub : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (nodeOk (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))
      = Formula.impl (lt i (lenc q)) (nodeOk q (nthc q i)) := by
    simp only [nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have hspec := PrfH_spec hw i
  rw [hsub] at hspec
  have hnode : PrfH Γ (nodeOk q (nthc q i)) := PrfH.mp _ _ _ hspec hlt
  have hpure : PrfH Γ (provFromCode (nodeOkDot (tcFn q) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_nodeOk_tracked q (nthc q i)) _) hnode
  -- transporte «reflexión pura ⇝ forma computada»: SIN binder, `PrfH_rw` alcanza el hueco
  have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hevs : PrfH Γ (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  have hcomp : PrfH Γ (provFromCode (nodeOkDot (tcFn q) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_rw (fun s => nodeOkDot (tcFn q) s)
      (fun s => prf_substfc_nodeOkDot_gen s (tcFn q) (varc (numeral 0)) s
        (substtc_inv_tcFn q) (prf_substtc_varc0 s))
      _ _ hevs hpure
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF q (tcFn i)))) _) hcomp

/-- **`wfAll` REFLEJADA**, con `w` ABSTRACTO. -/
theorem pcc_wfAll_tracked (w : Term) : Prf (wfAll w ⇒ provFromCode (wfAllDot w)) :=
  pcc_bdAll_intro wfAll lenc PsiF w hCl_ok hCs_ok hbl_ok hbs_ok hPl_ok hPs_ok
    hPsiId_ok hbody_ok

/-- **A3 — EL OBJETIVO**: `isFCB` reflejada, con `w` y `c` ABSTRACTOS. -/
theorem pcc_isFCB_tracked (w c : Term) :
    Prf (isFCB w c ⇒ provFromCode (isFCBDot w c)) := by
  refine prf_deduction ?_
  have h : PrfH [isFCB w c] (isFCB w c) := prfH_hyp_self _
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll_tracked w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! # 10 · ¿ROMPE la enmienda `consOk` el lado CONSTRUCTOR (`prf_wfAll_objList`)?

    **NO.** Aquí se MIDE: los tres lemas de `sondeos/ParseWitness.lean` que tocan `nodeOk`
    se re-demuestran con la enmienda, y el único cambio es añadir `consOk` a los `simp only`
    y un conjunto extra (`prf_consOk_cons`, 3 líneas) por nodo. `prf_bdAll_numeral`,
    `prf_lenc_objList`, `prf_nthc_objList`, `prf_In_objList` quedan **intactos**
    (no mencionan `nodeOk`), así que ni se copian modificados. -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_cdrc ∈ axioms by simp [axioms])) h) t
  simp [ax_cdrc, substFormula, substTerm, substTerms, cdrc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Para un nodo LITERAL (`cons a b`) el conjunto `consOk` es trivial. -/
theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_symm (prf_eq_trans (prf_congr_cons_head (prf_carc_cons a b))
    (prf_congr_cons_tail (prf_cdrc_cons a b)))

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq Φ))
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

theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

/-- ⚠️ ÚNICO cambio frente a `ParseWitness`: `consOk` en el `simp only`. -/
theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, nil, zero, cons, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_congr_nodeOk {w X₁ X₂ : Term} (h : Prf (X₁ =eq X₂)) (hN : Prf (nodeOk w X₁)) :
    Prf (nodeOk w X₂) :=
  prfH_nil_to_prf (PrfH_congr_nodeOk (prf_to_prfH h []) (prf_to_prfH hN [])) rfl

/-- **EL ENSAMBLAJE, INTACTO**: mismo enunciado que en `sondeos/ParseWitness.lean`,
    mismo esqueleto de prueba; sólo `consOk`/`cons` añadidos al `simp only` de `hsub`. -/
theorem prf_wfAll_objList (L : List Term)
    (hcl : ∀ s : Term, substTerm 0 s (objList L) = objList L)
    (hlift : liftTerm 0 (objList L) = objList L)
    (h : ∀ (k : Nat) (x : Term), L[k]? = some x → Prf (nodeOk (objList L) x)) :
    Prf (wfAll (objList L)) := by
  let w : Term := objList L
  let Φ : Formula := nodeOk w (nthc w (.var 0))
  have hsub : ∀ s : Term, substFormula 0 s Φ = nodeOk w (nthc w s) := by
    intro s
    simp only [Φ, w, nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, nil, zero, cons, substFormula, substTerm, substTerms,
      substTerm_numeralM, hcl, if_true]
  have hΦ : substFormula 0 (.var 0) Φ = Φ := hsub (.var 0)
  have hinst : ∀ k : Nat, k < L.length → Prf (substFormula 0 (numeralM k) Φ) := by
    intro k hk
    rw [hsub]
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    exact prf_congr_nodeOk (prf_eq_symm (prf_nthc_objList L k x hx)) (h k x hx)
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM L.length)) Φ)) :=
    prf_bdAll_numeral Φ hΦ L.length hinst
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM L.length)) Φ)
      = Formula.impl (lt (.var 0) (numeralM L.length)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  have hlift2 : liftTerm 0 (lenc (objList L)) = lenc (objList L) := by
    simp only [lenc, liftTerm, liftTerms, hlift]
  refine Prf.gen _ (prf_deduction ?_)
  rw [hlift2, hlift]
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_lenc_objList L) _) (PrfH.hyp _ _ (List.Mem.head _)))

/-! ## 10.1 · El caso base `⊥`, extremo a extremo, con la enmienda -/

def wBot : Term := objList [formCodeM Formula.bottom]

theorem prf_nodeOk_bot (w : Term) : Prf (nodeOk w (formCodeM Formula.bottom)) := by
  have htag : Prf (Formula.eq (carc (formCodeM Formula.bottom)) (numeralM 2)) :=
    prf_carc_cons (numeralM 2) nil
  have hlen : Prf (Formula.eq (lenc (formCodeM Formula.bottom)) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons (numeralM 2) nil) (prf_eq_congr_succ prf_lenc_nil)
  have hnul : Prf (nulOk (formCodeM Formula.bottom) 2) := prf_and_intro htag hlen
  refine prf_and_intro (prf_consOk_cons (numeralM 2) nil) ?_
  unfold lorAll
  exact prf_mp (Prf.incl (Prfᵢ.j1 _ _)) hnul

theorem prf_isFCB_bottom : Prf (isFCB wBot (formCodeM Formula.bottom)) := by
  refine prf_and_intro ?_ (prf_In_objList _ _ (List.Mem.head _))
  refine Prf.gen _ (prf_deduction ?_)
  have hlift : liftTerm 0 wBot = wBot := by
    simp only [wBot, objList, formCodeM, cons, nil, zero, numeralM, succ, liftTerm, liftTerms]
  rw [hlift]
  have hlen : Prf (Formula.eq (lenc wBot) (numeralM 1)) := prf_lenc_objList _
  have hlt1 : PrfH [lt (.var 0) (lenc wBot)] (lt (.var 0) (succ zero)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH hlen _)
      (PrfH.hyp _ _ (List.Mem.head _))
  have hsplit : PrfH [lt (.var 0) (lenc wBot)]
      (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) hlt1
  refine PrfH_or_elim hsplit ?brA ?brB
  case brA =>
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) (PrfH.hyp _ _ (List.Mem.head _)))
  case brB =>
    let Δ : List Formula := Formula.eq (.var 0) zero :: [lt (.var 0) (lenc wBot)]
    have hi : PrfH Δ (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH Δ (Formula.eq (nthc wBot (.var 0)) (formCodeM Formula.bottom)) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := wBot) hi)
        (prf_to_prfH (prf_nthc_zero (formCodeM Formula.bottom) nil) Δ)
    exact PrfH_congr_nodeOk (PrfH_eq_symm hX) (prf_to_prfH (prf_nodeOk_bot wBot) Δ)

/-- **CIERRE EXTREMO A EXTREMO**: hay un testigo CONCRETO cuyo `isFCB` es demostrable
    y cuya imagen punteada es demostrable DENTRO de `Prov`. -/
theorem pcc_isFCB_bottom_tracked :
    Prf (provFromCode (isFCBDot wBot (formCodeM Formula.bottom))) :=
  prf_mp (pcc_isFCB_tracked wBot (formCodeM Formula.bottom)) prf_isFCB_bottom

end A3Reformula

#print axioms A3Reformula.pcc_isFCB_tracked
#print axioms A3Reformula.pcc_wfAll_tracked
#print axioms A3Reformula.pcc_nodeOk_tracked
#print axioms A3Reformula.hbody_ok
#print axioms A3Reformula.pcc_In_atom_tracked
#print axioms A3Reformula.pcc_carcD_bridge_cons
#print axioms A3Reformula.pcc_cdrcD_bridge_cons
#print axioms A3Reformula.PrfH_inDot_via
#print axioms A3Reformula.prf_substfc_nodeOkDot_gen
#print axioms A3Reformula.hPsiId_ok
#print axioms A3Reformula.hCl_ok
#print axioms A3Reformula.hCs_ok
#print axioms A3Reformula.hPl_ok
#print axioms A3Reformula.hPs_ok
#print axioms A3Reformula.prf_wfAll_objList
#print axioms A3Reformula.prf_isFCB_bottom
#print axioms A3Reformula.pcc_isFCB_bottom_tracked
#check @A3Reformula.pcc_isFCB_tracked

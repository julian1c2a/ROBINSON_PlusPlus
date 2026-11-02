/-
A3 — BOTTOM-UP.  `pcc_isFCB_tracked (w c) : Prf (isFCB w c ⇒ provFromCode (isFCBDot w c))`.

Estrategia 2: primero TODA el álgebra de `nodeOkDot` como resultados autónomos, y sólo al final
`pcc_bdAll_intro`.

Formulación elegida: la (d) del SCOUT (`Probe/A3Scout.lean`) — el `In` dotado va como su ÁTOMO
(`inFormCodeFn`), NO como su despliegue `∃`-acotado (`bdInDot`). Con eso el cuerpo dotado NO tiene
ningún binder y todo el descenso de `substfc` vive en NIVEL 0.

⚠️ ENMIENDA R-A3-1' (corrección de la R-A3-1 de `Probe/A3Spec.lean`): `consOk X` NO puede ir como
conjunto de CABECERA de `nodeOk`, porque el disyunto `X = nil` (el nodo `termsCode []`) lo haría
REFUTABLE (`lenc nil = 0` vs `lenc (cons a b) = succ …`), y ese nodo aparece en el testigo de
CUALQUIER fórmula con un átomo. Va conjuntado a cada uno de los ONCE disyuntos que sí necesitan
evaluar `carc`/`cdrc`; el disyunto `nil` se queda sin él.

    lake env lean Probe\A3_bottomup.lean
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
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

namespace A3BottomUp

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 0 · EL OBJETO (de `sondeos/ParseWitness.lean`) + la enmienda R-A3-1'
    ══════════════════════════════════════════════════════════════════════════════════════ -/

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

/-- **ENMIENDA R-A3-1'**: el nodo es un `cons`. Sin esto no hay puente `carcT Ẋ → (carc X)˙`
    para `X` ABSTRACTO. Es OBJETO puro y NO aparece en la imagen punteada. -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

/-- El disyunto, con la enmienda pegada. -/
def cns (X : Term) (F : Formula) : Formula := land (consOk X) F

/-- Los 12 casos. ⚠️ El disyunto `X = nil` va SIN `consOk` (con él sería refutable). -/
def nodeOk (w X : Term) : Formula :=
  lorAll (cns X (nulOk X 2))
    [ cns X (strBinOk w X 3)
    , cns X (binOk w X 4)
    , cns X (binOk w X 5)
    , cns X (unOk  w X 6)
    , cns X (binOk w X 7)
    , cns X (binOk w X 8)
    , cns X (unOk  w X 9)
    , cns X (varOk X)
    , cns X (strBinOk w X 1)
    , Formula.eq X nil
    , cns X (land (In (carc X) w) (In (cdrc X) w)) ]

def wfAll (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCB (w c : Term) : Formula := land (wfAll w) (In c w)

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 1 · LA IMAGEN PUNTEADA (SIN binders)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- `carc X = k̄ ∧ lenc X = n̄`, dotado y EVALUADO. -/
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

/-- **El nodo dotado, 12 casos.** Ni un solo `exc`. -/
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

/-- **`PsiF`**: el cuerpo del `∀` acotado, con el hueco `⌜v₀⌝` en el ÍNDICE. -/
noncomputable def PsiF (w : Term) : Term :=
  nodeOkDot (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

/-- Imagen punteada de `wfAll` (la que entrega `pcc_bdAll_intro`, literalmente). -/
noncomputable def wfAllDot (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiF w)

/-- **Imagen punteada de `isFCB`.** -/
noncomputable def isFCBDot (w c : Term) : Term :=
  andc (wfAllDot w) (inFormCodeFn (tcFn c) (tcFn w))

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 2 · ÁLGEBRA (a) — el descenso de `substfc zero s`, todo a NIVEL 0
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- `substfc 0 s` sobre el código del átomo `In`, con hueco ANIDADO en el 1er argumento. -/
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

/-- **`hPsiId`**: el RHS del descenso en `s := ⌜v₀⌝` es DEFINICIONALMENTE `PsiF w`. -/
theorem hPsiId_ok (w : Term) :
    Prf (substfc zero (varc (numeral 0)) (PsiF w) =eq PsiF w) :=
  prf_substfc_PsiF w (varc (numeral 0))

/-- Descenso con el hueco DIRECTO sobre el nodo (contexto de Leibniz del transporte final). -/
theorem prf_substfc_nodeOkHole (w s : Term) :
    Prf (substfc zero s (nodeOkDot (tcFn w) (varc (numeral 0))) =eq nodeOkDot (tcFn w) s) :=
  prf_substfc_nodeOkDot_gen s (tcFn w) _ _ (substtc_inv_tcFn w) (prf_substtc_varc0 s)

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 3 · ÁLGEBRA (b) — `liftTerm` / `substTerm` (las 6 obligaciones mecánicas)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

theorem liftTerm_PsiF (c : Nat) (w : Term) : liftTerm c (PsiF w) = PsiF (liftTerm c w) := by
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral,
    liftTerm_strCode]

theorem substTerm_PsiF (v : Nat) (t w : Term) :
    substTerm v t (PsiF w) = PsiF (substTerm v t w) := by
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral,
    substTerm_strCode]

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hCl_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAll q) = wfAll (liftTerm k q) := by
  intro k q
  simp only [wfAll, nodeOk, cns, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCs_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAll q) = wfAll (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAll, nodeOk, cns, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 4 · A1 y el reflector del ÁTOMO `In` (de `sondeos/InTracked.lean` + `Probe/A3Scout.lean`)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

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

theorem prf_substtc_varc0_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 0)) =eq varc (numeral 0)) :=
  prf_mp (prf_substtc_var_lt (succ zero) V (numeral 0)) (prf_gnum_lt (by omega : 0 < 1))

/-- **EL PUENTE**: `⊢ Prov(⌜ (∃i<lenc(ẇ). nthc(ẇ,i)=ẋ) ⇒ ẋ ∈ ẇ ⌝)`, `x`, `w` ABSTRACTOS. -/
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

/-- **Reflector del ÁTOMO `In`**, con `x` y `w` ABSTRACTOS. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 5 · R-A3-1' — los puentes `carc` / `cdrc` DESGATILLADOS (sin `lineWF` ni `chainOk`)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

theorem PrfH_congr_cdrcT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (cdrcT x =eq cdrcT y) := by
  unfold cdrcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_congr_cons_head h)))

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

theorem pcc_cdrcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (cdrcT (tcFn X)) (tcFn (cdrc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_cdrcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_cdrc (carc X) (cdrc X)) _)

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 6 · ÁLGEBRA (c) — combinadores internos que faltaban
    ══════════════════════════════════════════════════════════════════════════════════════ -/

theorem PrfH_or_introL_code {Γ : List Formula} {Ac Bc : Term}
    (h : PrfH Γ (provFromCode Ac)) : PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH_mp_code_apply (prf_to_prfH (pcc_j1_code Ac Bc) _) h

theorem PrfH_or_introR_code {Γ : List Formula} {Ac Bc : Term}
    (h : PrfH Γ (provFromCode Bc)) : PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH_mp_code_apply (prf_to_prfH (pcc_j2_code Ac Bc) _) h

/-- **Transporte de un `In` dotado por su primer argumento**, dentro de `Prov`.
    De `Prov(⌜A = B⌝)` y `Prov(⌜B ∈ W⌝)` sale `Prov(⌜A ∈ W⌝)`. -/
theorem PrfH_in_transport {Γ : List Formula} (W A B : Term)
    (hAinv : ∀ V, Prf (substtc zero V A =eq A))
    (hWinv : ∀ V, Prf (substtc zero V W =eq W))
    (heq : PrfH Γ (provFromCode (eqc A B)))
    (hin : PrfH Γ (provFromCode (inFormCodeFn B W))) :
    PrfH Γ (provFromCode (inFormCodeFn A W)) := by
  let Ac : Term := inFormCodeFn (varc (numeral 0)) W
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq inFormCodeFn t W) := fun t =>
    prf_substfc_inFormCode_hole1 t W hWinv
  have hsym : PrfH Γ (provFromCode (eqc B A)) := PrfH_eq_symm_code A B hAinv heq
  have hB : PrfH Γ (provFromCode (substfc zero B Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp B))) _) hin
  have hA : PrfH Γ (provFromCode (substfc zero A Ac)) := PrfH_leibniz_apply Ac B A hsym hB
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp A)) _) hA

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 7 · LOS REFLECTORES DE LOS 12 DISYUNTOS (`X` objeto ABSTRACTO, forma `tcFn X`)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- Invariancias que se usan una y otra vez. -/
theorem inv_carcT_tc (X : Term) : ∀ V, Prf (substtc zero V (carcT (tcFn X)) =eq carcT (tcFn X)) :=
  substtc_inv_carcT (substtc_inv_tcFn X)
theorem inv_cdrcT_tc (X : Term) : ∀ V, Prf (substtc zero V (cdrcT (tcFn X)) =eq cdrcT (tcFn X)) :=
  substtc_inv_cdrcT (substtc_inv_tcFn X)
theorem inv_lencT_tc (X : Term) : ∀ V, Prf (substtc zero V (lencT (tcFn X)) =eq lencT (tcFn X)) :=
  substtc_inv_lencT (substtc_inv_tcFn X)
theorem inv_nthcT_tc (X i : Term) :
    ∀ V, Prf (substtc zero V (nthcT (tcFn X) (tcFn i)) =eq nthcT (tcFn X) (tcFn i)) :=
  substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn i)

/-- **La FORMA (`carc`, `lenc`) reflejada**, evaluada. Aquí es donde entra R-A3-1'. -/
theorem PrfH_shapeDot_tracked {Γ : List Formula} (X : Term) (k n : Nat)
    (hc : PrfH Γ (consOk X))
    (hk : PrfH Γ (Formula.eq (carc X) (numeralM k)))
    (hn : PrfH Γ (Formula.eq (lenc X) (numeralM n))) :
    PrfH Γ (provFromCode (shapeDot (tcFn X) k n)) := by
  have hc1 : PrfH Γ (provFromCode (eqc (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hc
  have hc2 : PrfH Γ (provFromCode (eqc (tcFn (carc X)) (tcFn (numeralM k)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (carc X) (numeralM k)) _) hk
  have hcarc : PrfH Γ (provFromCode (eqc (carcT (tcFn X)) (tcFn (numeralM k)))) :=
    PrfH_eq_trans_code _ _ _ (inv_carcT_tc X) hc1 hc2
  have hl1 : PrfH Γ (provFromCode (eqc (lencT (tcFn X)) (tcFn (lenc X)))) :=
    prf_to_prfH (pcc_eval_lenc X) _
  have hl2 : PrfH Γ (provFromCode (eqc (tcFn (lenc X)) (tcFn (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM n)) _) hn
  have hlen : PrfH Γ (provFromCode (eqc (lencT (tcFn X)) (tcFn (numeralM n)))) :=
    PrfH_eq_trans_code _ _ _ (inv_lencT_tc X) hl1 hl2
  exact PrfH_and_intro_code _ _ hcarc hlen

/-- **Un HIJO reflejado**: `In (nthc X j̄) w` ⇝ `Prov(⌜nthc(Ẋ,j̇) ∈ ẇ⌝)`.
    La cota `j < lenc X` sale de la longitud canónica (`hn`); `pcc_eval_nthc` NO pide más. -/
theorem PrfH_child_tracked {Γ : List Formula} (w X : Term) (j n : Nat) (hjn : j < n)
    (hn : PrfH Γ (Formula.eq (lenc X) (numeralM n)))
    (hin : PrfH Γ (In (nthc X (numeralM j)) w)) :
    PrfH Γ (provFromCode (inFormCodeFn (nthcT (tcFn X) (tcFn (numeralM j))) (tcFn w))) := by
  have hb : PrfH Γ (lt (numeralM j) (lenc X)) := PrfH_lt_of_lenc_eq hjn hn
  have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn X) (tcFn (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hb
  have hat : PrfH Γ (provFromCode (inFormCodeFn (tcFn (nthc X (numeralM j))) (tcFn w))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc X (numeralM j)) w) _) hin
  exact PrfH_in_transport _ _ _ (inv_nthcT_tc X (numeralM j)) (substtc_inv_tcFn w) hev hat

theorem PrfH_inCarc_tracked {Γ : List Formula} (w X : Term)
    (hc : PrfH Γ (consOk X)) (hin : PrfH Γ (In (carc X) w)) :
    PrfH Γ (provFromCode (inFormCodeFn (carcT (tcFn X)) (tcFn w))) := by
  have hev : PrfH Γ (provFromCode (eqc (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hc
  have hat : PrfH Γ (provFromCode (inFormCodeFn (tcFn (carc X)) (tcFn w))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (carc X) w) _) hin
  exact PrfH_in_transport _ _ _ (inv_carcT_tc X) (substtc_inv_tcFn w) hev hat

theorem PrfH_inCdrc_tracked {Γ : List Formula} (w X : Term)
    (hc : PrfH Γ (consOk X)) (hin : PrfH Γ (In (cdrc X) w)) :
    PrfH Γ (provFromCode (inFormCodeFn (cdrcT (tcFn X)) (tcFn w))) := by
  have hev : PrfH Γ (provFromCode (eqc (cdrcT (tcFn X)) (tcFn (cdrc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcD_bridge_cons X) _) hc
  have hat : PrfH Γ (provFromCode (inFormCodeFn (tcFn (cdrc X)) (tcFn w))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (cdrc X) w) _) hin
  exact PrfH_in_transport _ _ _ (inv_cdrcT_tc X) (substtc_inv_tcFn w) hev hat

/-! ### Los cinco reflectores de familia -/

theorem PrfH_nulOk_tracked {Γ : List Formula} (X : Term) (k : Nat)
    (h : PrfH Γ (cns X (nulOk X k))) : PrfH Γ (provFromCode (shapeDot (tcFn X) k 1)) := by
  have hc : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hs : PrfH Γ (nulOk X k) := PrfH_and_elim_right h
  exact PrfH_shapeDot_tracked X k 1 hc (PrfH_and_elim_left hs) (PrfH_and_elim_right hs)

theorem PrfH_varOk_tracked {Γ : List Formula} (X : Term)
    (h : PrfH Γ (cns X (varOk X))) : PrfH Γ (provFromCode (varDot (tcFn X))) := by
  have hc : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hs : PrfH Γ (varOk X) := PrfH_and_elim_right h
  exact PrfH_shapeDot_tracked X 0 2 hc (PrfH_and_elim_left hs) (PrfH_and_elim_right hs)

theorem PrfH_unOk_tracked {Γ : List Formula} (w X : Term) (k : Nat)
    (h : PrfH Γ (cns X (unOk w X k))) :
    PrfH Γ (provFromCode (unDot (tcFn w) (tcFn X) k)) := by
  have hc : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hs : PrfH Γ (unOk w X k) := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hs
  have hn : PrfH Γ (Formula.eq (lenc X) (numeralM 2)) := PrfH_and_elim_right hsh
  refine PrfH_and_intro_code _ _
    (PrfH_shapeDot_tracked X k 2 hc (PrfH_and_elim_left hsh) hn) ?_
  exact PrfH_child_tracked w X 1 2 (by omega) hn (PrfH_and_elim_right hs)

theorem PrfH_binOk_tracked {Γ : List Formula} (w X : Term) (k : Nat)
    (h : PrfH Γ (cns X (binOk w X k))) :
    PrfH Γ (provFromCode (binDot (tcFn w) (tcFn X) k)) := by
  have hc : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hs : PrfH Γ (binOk w X k) := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hs
  have hmem := PrfH_and_elim_right hs
  have hn : PrfH Γ (Formula.eq (lenc X) (numeralM 3)) := PrfH_and_elim_right hsh
  refine PrfH_and_intro_code _ _
    (PrfH_shapeDot_tracked X k 3 hc (PrfH_and_elim_left hsh) hn) ?_
  exact PrfH_and_intro_code _ _
    (PrfH_child_tracked w X 1 3 (by omega) hn (PrfH_and_elim_left hmem))
    (PrfH_child_tracked w X 2 3 (by omega) hn (PrfH_and_elim_right hmem))

theorem PrfH_strBinOk_tracked {Γ : List Formula} (w X : Term) (k : Nat)
    (h : PrfH Γ (cns X (strBinOk w X k))) :
    PrfH Γ (provFromCode (strBinDot (tcFn w) (tcFn X) k)) := by
  have hc : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hs : PrfH Γ (strBinOk w X k) := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hs
  have hn : PrfH Γ (Formula.eq (lenc X) (numeralM 3)) := PrfH_and_elim_right hsh
  refine PrfH_and_intro_code _ _
    (PrfH_shapeDot_tracked X k 3 hc (PrfH_and_elim_left hsh) hn) ?_
  exact PrfH_child_tracked w X 2 3 (by omega) hn (PrfH_and_elim_right hs)

theorem PrfH_consCase_tracked {Γ : List Formula} (w X : Term)
    (h : PrfH Γ (cns X (land (In (carc X) w) (In (cdrc X) w)))) :
    PrfH Γ (provFromCode (andc (inFormCodeFn (carcT (tcFn X)) (tcFn w))
                               (inFormCodeFn (cdrcT (tcFn X)) (tcFn w)))) := by
  have hc : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hs := PrfH_and_elim_right h
  exact PrfH_and_intro_code _ _
    (PrfH_inCarc_tracked w X hc (PrfH_and_elim_left hs))
    (PrfH_inCdrc_tracked w X hc (PrfH_and_elim_right hs))

theorem PrfH_nilCase_tracked {Γ : List Formula} (X : Term)
    (h : PrfH Γ (Formula.eq X nil)) : PrfH Γ (provFromCode (eqCodeFn (tcFn X) (tcFn nil))) :=
  PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked X nil) _) h

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 8 · EL REFLECTOR DEL NODO — or-elim de 12 ramas
    ══════════════════════════════════════════════════════════════════════════════════════ -/

theorem PrfH_nodeOk_tracked {Γ : List Formula} (w X : Term)
    (h : PrfH Γ (nodeOk w X)) :
    PrfH Γ (provFromCode (nodeOkDot (tcFn w) (tcFn X))) := by
  unfold nodeOk lorAll at h
  unfold nodeOkDot lorAllc
  refine PrfH_or_elim h ?_ ?_
  · exact PrfH_or_introL_code (PrfH_nulOk_tracked X 2 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_strBinOk_tracked w X 3 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_binOk_tracked w X 4 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_binOk_tracked w X 5 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_unOk_tracked w X 6 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_binOk_tracked w X 7 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_binOk_tracked w X 8 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_unOk_tracked w X 9 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_varOk_tracked X (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_strBinOk_tracked w X 1 (PrfH.hyp _ _ (List.Mem.head _)))
  refine PrfH_or_introR_code ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact PrfH_or_introL_code (PrfH_nilCase_tracked X (PrfH.hyp _ _ (List.Mem.head _)))
  · exact PrfH_or_introR_code (PrfH_consCase_tracked w X (PrfH.hyp _ _ (List.Mem.head _)))

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 9 · `hbody` — el transporte `Ẋ ↦ nthc(ẇ, ı̇)` y el ensamblaje
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- La instancia del `∀` acotado, computada. -/
theorem substFormula_wfAllBody (q s : Term) :
    substFormula 0 s (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (nodeOk (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))
      = Formula.impl (lt s (lenc q)) (nodeOk q (nthc q s)) := by
  simp only [nodeOk, cns, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
    lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_liftTerm, if_true]

/-- **`hbody`**: la obligación grande de `pcc_bdAll_intro`. -/
theorem hbody_ok (q i : Term) :
    Prf (wfAll q ⇒ (lt i (lenc q) ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll q] rfl)
  let Γ : List Formula := [lt i (lenc q), wfAll q]
  show PrfH Γ (provFromCode (substfc zero (tcFn i) (PsiF q)))
  have hbnd : PrfH Γ (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hall : PrfH Γ (wfAll q) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  -- (1) el nodo OBJETO
  have hspec := PrfH_spec hall i
  rw [substFormula_wfAllBody] at hspec
  have hnode : PrfH Γ (nodeOk q (nthc q i)) := PrfH.mp _ _ _ hspec hbnd
  -- (2) su reflexión, con el nodo en forma `tcFn`
  have hdot : PrfH Γ (provFromCode (nodeOkDot (tcFn q) (tcFn (nthc q i)))) :=
    PrfH_nodeOk_tracked q (nthc q i) hnode
  -- (3) transporte `(nthc q i)˙ ↦ nthc(q̇, ı̇)` — UNA Leibniz interna
  have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hbnd
  have hsym : PrfH Γ (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _ (inv_nthcT_tc q i) hev
  let Ac : Term := nodeOkDot (tcFn q) (varc (numeral 0))
  have hA : PrfH Γ (provFromCode (substfc zero (tcFn (nthc q i)) Ac)) :=
    PrfH.mp _ _ _
      (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_nodeOkHole q _))) _) hdot
  have hB : PrfH Γ (provFromCode (substfc zero (nthcT (tcFn q) (tcFn i)) Ac)) :=
    PrfH_leibniz_apply Ac _ _ hsym hA
  have hC : PrfH Γ (provFromCode (nodeOkDot (tcFn q) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_substfc_nodeOkHole q _)) _) hB
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF q (tcFn i)))) _) hC

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 10 · A3
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- **A3, mitad dura**: `wfAll w ⇒ Prov(⌜∀i<(lenc w)˙. nodeOkDot(ẇ, nthc(ẇ,i))⌝)`,
    con `w` ABSTRACTO. -/
theorem pcc_wfAll_tracked (w : Term) : Prf (wfAll w ⇒ provFromCode (wfAllDot w)) :=
  pcc_bdAll_intro wfAll lenc PsiF w hCl_ok hCs_ok hbl_ok hbs_ok liftTerm_PsiF substTerm_PsiF
    hPsiId_ok hbody_ok

/-- **A3**: `isFCB w c ⇒ Prov(⌜isFCBDot w c⌝)`, con `w` y `c` ABSTRACTOS. -/
theorem pcc_isFCB_tracked (w c : Term) :
    Prf (isFCB w c ⇒ provFromCode (isFCBDot w c)) := by
  refine prf_deduction ?_
  have h : PrfH [isFCB w c] (isFCB w c) := prfH_hyp_self _
  have h1 : PrfH [isFCB w c] (provFromCode (wfAllDot w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll_tracked w) _) (PrfH_and_elim_left h)
  have h2 : PrfH [isFCB w c] (provFromCode (inFormCodeFn (tcFn c) (tcFn w))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h)
  exact PrfH_and_intro_code _ _ h1 h2

/-! ══════════════════════════════════════════════════════════════════════════════════════
    § 11 · JUSTIFICACIÓN DE LA ENMIENDA R-A3-1' + PRUEBA EXTREMO A EXTREMO

    Aquí se **compila** (no se argumenta) que:
      (i)  `consOk` de un `cons` es gratis  ⇒ la fase A no se encarece;
      (ii) `consOk nil` es **REFUTABLE**    ⇒ ponerlo de CABECERA (como hace `Probe/A3Spec.lean`)
           haría `nodeOk w nil` inalcanzable, y ese nodo (`termsCode []`) aparece en el testigo
           de CUALQUIER fórmula con un átomo;
      (iii) con la colocación correcta, `isFCB` sigue siendo satisfacible: `⊢ isFCB wBot ⌜⊥⌝`,
           y componiendo con A3 sale la reflexión CERRADA.
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- `cdrc (cons h t) = t` (gemelo de `prf_carc_cons`, que sí está en `ReprPrf`). -/
theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_cdrc ∈ axioms by simp [axioms])) h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-- (i) **Todo `cons` literal cumple `consOk`** — el coste de la enmienda en la fase A es nulo. -/
theorem prf_consOk_cons (h t : Term) : Prf (consOk (cons h t)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons h t)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons h t)))

theorem PrfH_congr_lenc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) Γ)

/-- (ii) **`consOk nil` es REFUTABLE**: `lenc nil = 0` contra `lenc (cons a b) = σ(lenc b)`.
    ⇒ la R-A3-1 de `Probe/A3Spec.lean` (que conjunta `consOk` en CABECERA de `nodeOk`) deja
    `nodeOk w nil` sin demostración posible. Ésa es la corrección R-A3-1'. -/
theorem prf_consOk_nil_refuted : Prf (neg (consOk nil)) := by
  refine prf_deduction ?_
  have hc : PrfH [consOk nil] (consOk nil) := prfH_hyp_self _
  have h1 : PrfH [consOk nil] (lenc nil =eq lenc (cons (carc nil) (cdrc nil))) :=
    PrfH_congr_lenc hc
  have h2 : PrfH [consOk nil] (succ (lenc (cdrc nil)) =eq zero) :=
    PrfH_eq_symm (PrfH_eq_trans (prf_to_prfH (prf_eq_symm prf_lenc_nil) _)
      (PrfH_eq_trans h1 (prf_to_prfH (prf_lenc_cons (carc nil) (cdrc nil)) _)))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (lenc (cdrc nil))) _) h2

/-! ### (iii) El testigo de `⊥`, extremo a extremo (copia de `sondeos/ParseWitness.lean` §5) -/

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

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

/-- Leibniz sobre el nodo — UNA aplicación, no 12 (el hueco cubre todas sus ocurrencias). -/
theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, cns, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

def wBot : Term := objList [formCodeM Formula.bottom]

theorem prf_nodeOk_bot (w : Term) : Prf (nodeOk w (formCodeM Formula.bottom)) := by
  have htag : Prf (Formula.eq (carc (formCodeM Formula.bottom)) (numeralM 2)) :=
    prf_carc_cons (numeralM 2) nil
  have hlen : Prf (Formula.eq (lenc (formCodeM Formula.bottom)) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons (numeralM 2) nil) (prf_eq_congr_succ prf_lenc_nil)
  have hnul : Prf (cns (formCodeM Formula.bottom) (nulOk (formCodeM Formula.bottom) 2)) :=
    prf_and_intro (prf_consOk_cons (numeralM 2) nil) (prf_and_intro htag hlen)
  unfold nodeOk lorAll
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

/-- **EXTREMO A EXTREMO**: A3 aplicada a un testigo REAL da una reflexión CERRADA. -/
theorem pcc_isFCB_bottom_tracked :
    Prf (provFromCode (isFCBDot wBot (formCodeM Formula.bottom))) :=
  prf_mp (pcc_isFCB_tracked wBot (formCodeM Formula.bottom)) prf_isFCB_bottom

end A3BottomUp

#print axioms A3BottomUp.pcc_isFCB_tracked
#print axioms A3BottomUp.pcc_wfAll_tracked
#print axioms A3BottomUp.hbody_ok
#print axioms A3BottomUp.PrfH_nodeOk_tracked
#print axioms A3BottomUp.prf_substfc_nodeOkDot_gen
#print axioms A3BottomUp.hPsiId_ok
#print axioms A3BottomUp.pcc_In_atom_tracked
#print axioms A3BottomUp.prf_consOk_nil_refuted
#print axioms A3BottomUp.prf_isFCB_bottom
#print axioms A3BottomUp.pcc_isFCB_bottom_tracked

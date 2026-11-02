/-
A3 — ESTRATEGIA «FRAGMENTO PRIMERO».

`nodeOk` RECORTADO a DOS disyuntos:
  * `nulOk X 2`   — dos `=eq`, ningún `In`;
  * `unOk q X 6`  — dos `=eq` + UN `In`.
y `pcc_isFCB_tracked` cerrado ENTERO para ese `nodeOk` recortado.

Formulación de la imagen punteada: la (d) del SCOUT — el `In` se dota como su **ÁTOMO**
(`inFormCodeFn`), no como su despliegue `∃`-acotado ⇒ el cuerpo del `∀` acotado NO tiene binders
y todo el descenso de `substfc` vive a nivel 0.

    lake env lean Probe/A3_fragmento.lean
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
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf

namespace A3Frag

/-! ## 0 · EL OBJETO (fragmento de `sondeos/ParseWitness.lean` + enmienda R‑A3‑1) -/

/-- ⚠️ **ENMIENDA R‑A3‑1**: el nodo es un `cons`. Sin esto no hay puente
    `carcT ẋ → (carc x)˙` para `x` ABSTRACTO. Es OBJETO puro; NO aparece en la imagen punteada. -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def nulOk (X : Term) (k : Nat) : Formula :=
  land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 1))

def unOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

/-- El nodo RECORTADO: sólo dos disyuntos (uno sin `In`, otro con `In`). -/
def nodeOk2 (w X : Term) : Formula := land (consOk X) (lor (nulOk X 2) (unOk w X 6))

def wfAll2 (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk2 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCB2 (w c : Term) : Formula := land (wfAll2 w) (In c w)

/-! ## 1 · LA IMAGEN PUNTEADA (formulación (d): `In` como ÁTOMO ⇒ CERO binders) -/

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

noncomputable def unDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 2) (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)

noncomputable def nodeOkDot2 (W X : Term) : Term := orc (shapeDot X 2 1) (unDot W X 6)

/-- **`PsiF`**: el cuerpo dotado, hueco `⌜v₀⌝` en el ÍNDICE. -/
noncomputable def PsiF (w : Term) : Term :=
  nodeOkDot2 (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

noncomputable def wfAllDot2 (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiF w)

/-- **La imagen punteada de `isFCB`**. -/
noncomputable def isFCBDot2 (w c : Term) : Term :=
  andc (wfAllDot2 w) (inFormCodeFn (tcFn c) (tcFn w))

/-! ## 2 · Combinadores `PrfH` que faltaban -/

theorem PrfH_or_introL_code {Γ : List Formula} {Ac Bc : Term}
    (h : PrfH Γ (provFromCode Ac)) : PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH_mp_code_apply (prf_to_prfH (pcc_j1_code Ac Bc) _) h

theorem PrfH_or_introR_code {Γ : List Formula} {Ac Bc : Term}
    (h : PrfH Γ (provFromCode Bc)) : PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH_mp_code_apply (prf_to_prfH (pcc_j2_code Ac Bc) _) h

/-- `pcc_rw` bajo contexto (`pcc_rw` es sólo `Prf`). -/
theorem PrfH_rw {Γ : List Formula} (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : PrfH Γ (provFromCode (eqc X Y)))
    (hbase : PrfH Γ (provFromCode (G X))) : PrfH Γ (provFromCode (G Y)) := by
  have h1 : PrfH Γ (provFromCode (substfc zero X (G (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hG X))) _) hbase
  have h2 : PrfH Γ (provFromCode (substfc zero Y (G (varc (numeral 0))))) :=
    PrfH_leibniz_apply (G (varc (numeral 0))) X Y heq h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hG Y)) _) h2

/-! ## 3 · EL DESCENSO de `substfc zero s` — todo a NIVEL 0 (copiado de `Probe/A3Scout.lean`) -/

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

/-- **EL DESCENSO** por los dos disyuntos: sólo toca el hueco de `X`. -/
theorem prf_substfc_nodeOkDot2_gen (s W X X' : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (nodeOkDot2 W X) =eq nodeOkDot2 W X') := by
  unfold nodeOkDot2
  exact prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 2 1 hX)
      (prf_substfc_unDot s W X X' 6 hW hX))

/-- Contexto de reescritura para el nodo entero. -/
theorem hG_node (q : Term) : ∀ s : Term,
    Prf (substfc zero s (nodeOkDot2 (tcFn q) (varc (numeral 0))) =eq nodeOkDot2 (tcFn q) s) :=
  fun s => prf_substfc_nodeOkDot2_gen s (tcFn q) (varc (numeral 0)) s
    (substtc_inv_tcFn q) (prf_substtc_varc0 s)

/-- Contexto de reescritura para el 1er argumento del átomo `In`. -/
theorem hG_in (q : Term) : ∀ s : Term,
    Prf (substfc zero s (inFormCodeFn (varc (numeral 0)) (tcFn q)) =eq inFormCodeFn s (tcFn q)) :=
  fun s => prf_substfc_inDot s (varc (numeral 0)) s (tcFn q)
    (prf_substtc_varc0 s) (substtc_inv_tcFn q)

theorem prf_substfc_PsiF (w s : Term) :
    Prf (substfc zero s (PsiF w) =eq nodeOkDot2 (tcFn w) (nthcT (tcFn w) s)) :=
  prf_substfc_nodeOkDot2_gen s (tcFn w) _ _ (substtc_inv_tcFn w)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s)))

/-- **`hPsiId`**: el RHS del descenso en `s := ⌜v₀⌝` es DEFINICIONALMENTE `PsiF w`. -/
theorem hPsiId_ok (q : Term) :
    Prf (substfc zero (varc (numeral 0)) (PsiF q) =eq PsiF q) :=
  prf_substfc_PsiF q (varc (numeral 0))

/-! ## 4 · A1 y el reflector del ÁTOMO `In` (copiado de `Probe/A3Scout.lean`) -/

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

/-- El puente `bdInDot ⇒ ⌜In⌝` DENTRO de `Prov`. -/
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

/-- Reflector del ÁTOMO `In`, argumentos ABSTRACTOS. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

/-! ## 5 · R‑A3‑1: el puente `carc` desgatillado (sólo pide que el nodo sea `cons`) -/

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf ((X =eq cons (carc X) (cdrc X))
      ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (X =eq cons (carc X) (cdrc X))
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

/-! ## 6 · Los tres reflectores atómicos de la forma del nodo -/

/-- `carc X = k̄` (+ el nodo es `cons`)  ⇒  `Prov(⌜carcT Ẋ = k̄˙⌝)`. -/
theorem PrfH_shape_carc {Γ : List Formula} (X : Term) (k : Nat)
    (hcons : PrfH Γ (X =eq cons (carc X) (cdrc X)))
    (hk : PrfH Γ (Formula.eq (carc X) (numeralM k))) :
    PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (numeralM k)))) := by
  have h1 : PrfH Γ (provFromCode (eqc (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have h2 : PrfH Γ (provFromCode (eqc (tcFn (carc X)) (tcFn (numeralM k)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (carc X) (numeralM k)) _) hk
  exact PrfH_eq_trans_code _ _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) h1 h2

/-- `lenc X = n̄`  ⇒  `Prov(⌜lencT Ẋ = n̄˙⌝)`. **INCONDICIONAL** (`pcc_eval_lenc` lo es). -/
theorem PrfH_shape_lenc {Γ : List Formula} (X : Term) (n : Nat)
    (hn : PrfH Γ (Formula.eq (lenc X) (numeralM n))) :
    PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (numeralM n)))) := by
  have h1 : PrfH Γ (provFromCode (eqc (lencT (tcFn X)) (tcFn (lenc X)))) :=
    prf_to_prfH (pcc_eval_lenc X) _
  have h2 : PrfH Γ (provFromCode (eqc (tcFn (lenc X)) (tcFn (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM n)) _) hn
  exact PrfH_eq_trans_code _ _ _ (substtc_inv_lencT (substtc_inv_tcFn X)) h1 h2

/-- `In (nthc X j̄) q` (+ `j̄ < lenc X`)  ⇒  `Prov(⌜ nthcT Ẋ j̄˙ ∈ q̇ ⌝)`. -/
theorem PrfH_child_in {Γ : List Formula} (q X : Term) (j : Nat)
    (hlt : PrfH Γ (lt (numeralM j) (lenc X)))
    (hin : PrfH Γ (In (nthc X (numeralM j)) q)) :
    PrfH Γ (provFromCode (inFormCodeFn (nthcT (tcFn X) (tcFn (numeralM j))) (tcFn q))) := by
  have hA : PrfH Γ (provFromCode (inFormCodeFn (tcFn (nthc X (numeralM j))) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc X (numeralM j)) q) _) hin
  have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn X) (tcFn (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hlt
  have hsym : PrfH Γ (provFromCode (eqc (tcFn (nthc X (numeralM j)))
      (nthcT (tcFn X) (tcFn (numeralM j))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM j))) hev
  exact PrfH_rw (fun s => inFormCodeFn s (tcFn q)) (hG_in q) _ _ hsym hA

/-! ## 7 · A2 (fragmento): reflexión del nodo con el código PURO `Ẋ` -/

theorem pcc_nodeOk2_tracked (q X : Term) :
    Prf (nodeOk2 q X ⇒ provFromCode (nodeOkDot2 (tcFn q) (tcFn X))) := by
  refine prf_deduction ?_
  have h : PrfH [nodeOk2 q X] (nodeOk2 q X) := prfH_hyp_self _
  have hdisj : PrfH [nodeOk2 q X] (lor (nulOk X 2) (unOk q X 6)) := PrfH_and_elim_right h
  refine PrfH_or_elim hdisj ?bl ?br
  case bl =>
    have hn : PrfH (nulOk X 2 :: [nodeOk2 q X]) (nulOk X 2) := PrfH.hyp _ _ (List.Mem.head _)
    have hcons : PrfH (nulOk X 2 :: [nodeOk2 q X]) (X =eq cons (carc X) (cdrc X)) :=
      PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    have hc := PrfH_shape_carc X 2 hcons (PrfH_and_elim_left hn)
    have hl := PrfH_shape_lenc X 1 (PrfH_and_elim_right hn)
    exact PrfH_or_introL_code (PrfH_and_intro_code _ _ hc hl)
  case br =>
    have hu : PrfH (unOk q X 6 :: [nodeOk2 q X]) (unOk q X 6) := PrfH.hyp _ _ (List.Mem.head _)
    have hcons : PrfH (unOk q X 6 :: [nodeOk2 q X]) (X =eq cons (carc X) (cdrc X)) :=
      PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    have hsh : PrfH (unOk q X 6 :: [nodeOk2 q X])
        (land (Formula.eq (carc X) (numeralM 6)) (Formula.eq (lenc X) (numeralM 2))) :=
      PrfH_and_elim_left hu
    have hin : PrfH (unOk q X 6 :: [nodeOk2 q X]) (In (nthc X (numeralM 1)) q) :=
      PrfH_and_elim_right hu
    have hlen : PrfH (unOk q X 6 :: [nodeOk2 q X]) (Formula.eq (lenc X) (numeralM 2)) :=
      PrfH_and_elim_right hsh
    have h12 : PrfH (unOk q X 6 :: [nodeOk2 q X]) (lt (numeralM 1) (numeralM 2)) :=
      prf_to_prfH (prf_lt_succ_self (numeralM 1)) _
    have hlt : PrfH (unOk q X 6 :: [nodeOk2 q X]) (lt (numeralM 1) (lenc X)) :=
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen) h12
    have hc := PrfH_shape_carc X 6 hcons (PrfH_and_elim_left hsh)
    have hl := PrfH_shape_lenc X 2 hlen
    have hch := PrfH_child_in q X 1 hlt hin
    exact PrfH_or_introR_code (PrfH_and_intro_code _ _ (PrfH_and_intro_code _ _ hc hl) hch)

/-! ## 8 · `hbody`: `wfAll2 q` + `i < lenc q`  ⇒  `Prov(substfc 0 ı̇ (PsiF q))` -/

theorem hbody_ok (q i : Term) :
    Prf (wfAll2 q ⇒ (lt i (lenc q) ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll2 q] rfl)
  let Γ : List Formula := [lt i (lenc q), wfAll2 q]
  show PrfH Γ (provFromCode (substfc zero (tcFn i) (PsiF q)))
  have hlt : PrfH Γ (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH Γ (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (nodeOk2 (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  -- (1) el nodo, a nivel OBJETO
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (nodeOk2 (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))
      = Formula.impl (lt i (lenc q)) (nodeOk2 q (nthc q i)) := by
    simp only [nodeOk2, consOk, nulOk, unOk, land, lor, In, lt, carc, cdrc, lenc, nthc,
      cons, nil, zero, substFormula, substTerm, substTerms, substTerm_numeralM,
      FOL.substTerm_liftTerm, reduceIte, if_true]
  have hq1 : PrfH Γ (Formula.impl (lt i (lenc q)) (nodeOk2 q (nthc q i))) := by
    have hh := PrfH.mp _ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q1
      (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (nodeOk2 (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0)))) i)) hwf
    rwa [hsubst] at hh
  have hnode : PrfH Γ (nodeOk2 q (nthc q i)) := PrfH.mp _ _ _ hq1 hlt
  -- (2) su reflexión PURA
  have hpure : PrfH Γ (provFromCode (nodeOkDot2 (tcFn q) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_nodeOk2_tracked q (nthc q i)) _) hnode
  -- (3) transporte `Ẋ ↦ nthcT q̇ ı̇` — UNA Leibniz interna, el hueco cubre TODAS las ocurrencias
  have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hsym : PrfH Γ (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  have hcomp : PrfH Γ (provFromCode (nodeOkDot2 (tcFn q) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_rw (fun s => nodeOkDot2 (tcFn q) s) (hG_node q) _ _ hsym hpure
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF q (tcFn i)))) _) hcomp

/-! ## 9 · Las cuatro obligaciones MECÁNICAS -/

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hPl_ok : ∀ (k : Nat) (q : Term), liftTerm k (PsiF q) = PsiF (liftTerm k q) := by
  intro k q
  simp only [PsiF, nodeOkDot2, shapeDot, unDot, inFormCodeFn, eqCodeFn, andc, orc, atomc,
    carcT, lencT, nthcT, funcc, varc, tcFn, cons, nil, zero, succ, numeralM,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem hPs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (PsiF q) = PsiF (substTerm v t q) := by
  intro v t q
  simp only [PsiF, nodeOkDot2, shapeDot, unDot, inFormCodeFn, eqCodeFn, andc, orc, atomc,
    carcT, lencT, nthcT, funcc, varc, tcFn, cons, nil, zero, succ, numeralM,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem hCl_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAll2 q) = wfAll2 (liftTerm k q) := by
  intro k q
  simp only [wfAll2, nodeOk2, consOk, nulOk, unOk, land, lor, In, lt, carc, cdrc, lenc, nthc,
    cons, nil, zero, liftFormula, liftTerm, liftTerms, liftTerm_numeralM,
    if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCs_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAll2 q) = wfAll2 (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAll2, nodeOk2, consOk, nulOk, unOk, land, lor, In, lt, carc, cdrc, lenc, nthc,
    cons, nil, zero, substFormula, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

/-! ## 10 · EL RESULTADO -/

theorem pcc_wfAll2_tracked (w : Term) : Prf (wfAll2 w ⇒ provFromCode (wfAllDot2 w)) :=
  pcc_bdAll_intro wfAll2 lenc PsiF w hCl_ok hCs_ok hbl_ok hbs_ok hPl_ok hPs_ok hPsiId_ok hbody_ok

/-- **A3 (fragmento), CERRADA**: `w` y `c` ABSTRACTOS. -/
theorem pcc_isFCB_tracked (w c : Term) :
    Prf (isFCB2 w c ⇒ provFromCode (isFCBDot2 w c)) := by
  refine prf_deduction ?_
  have h : PrfH [isFCB2 w c] (isFCB2 w c) := prfH_hyp_self _
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll2_tracked w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! ## 11 · GENERALIZACIÓN a los 12 disyuntos (`nodeOk` COMPLETO de `sondeos/ParseWitness.lean`)

    Nada nuevo: los mismos tres reflectores atómicos (§6), el mismo chasis (§8‑§10). Lo único
    que hay que añadir es el **combinador `prf_or_step`**, que hace `∨`‑elim OBJETO y `∨`‑intro
    CÓDIGO **a la vez** ⇒ los 12 casos se pliegan a la derecha exactamente como `lorAll`. -/

/-! ### 11.1 · El objeto completo -/

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

/-- Los 12 disyuntos, en el orden de `sondeos/ParseWitness.lean`. -/
def nodeDisj (w X : Term) : List Formula :=
  [ strBinOk w X 3, binOk w X 4, binOk w X 5, unOk w X 6, binOk w X 7, binOk w X 8
  , unOk w X 9, varOk X, strBinOk w X 1
  , Formula.eq X nil
  , land (In (carc X) w) (In (cdrc X) w) ]

/-- `nodeOk` COMPLETO (+ enmienda R‑A3‑1). -/
def nodeOkF (w X : Term) : Formula := land (consOk X) (lorAll (nulOk X 2) (nodeDisj w X))

def wfAllF (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOkF (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCBF (w c : Term) : Formula := land (wfAllF w) (In c w)

/-! ### 11.2 · La imagen punteada completa -/

noncomputable def binDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3)
    (andc (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)
          (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W))

noncomputable def strBinDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3) (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W)

def lorAllc : Term → List Term → Term
  | a, []      => a
  | a, b :: bs => orc a (lorAllc b bs)

noncomputable def nodeDisjDot (W X : Term) : List Term :=
  [ strBinDot W X 3, binDot W X 4, binDot W X 5, unDot W X 6, binDot W X 7, binDot W X 8
  , unDot W X 9, shapeDot X 0 2, strBinDot W X 1
  , eqCodeFn X (tcFn nil)
  , andc (inFormCodeFn (carcT X) W) (inFormCodeFn (cdrcT X) W) ]

noncomputable def nodeOkDotF (W X : Term) : Term := lorAllc (shapeDot X 2 1) (nodeDisjDot W X)

noncomputable def PsiFF (w : Term) : Term :=
  nodeOkDotF (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

noncomputable def wfAllDotF (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiFF w)

noncomputable def isFCBDotF (w c : Term) : Term :=
  andc (wfAllDotF w) (inFormCodeFn (tcFn c) (tcFn w))

/-! ### 11.3 · El descenso de `substfc zero s` por los 12 (nivel 0, sin binders) -/

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

theorem prf_substfc_nodeOkDotF_gen (s W X X' : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (nodeOkDotF W X) =eq nodeOkDotF W X') := by
  unfold nodeOkDotF nodeDisjDot lorAllc
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

theorem hG_nodeF (q : Term) : ∀ s : Term,
    Prf (substfc zero s (nodeOkDotF (tcFn q) (varc (numeral 0))) =eq nodeOkDotF (tcFn q) s) :=
  fun s => prf_substfc_nodeOkDotF_gen s (tcFn q) (varc (numeral 0)) s
    (substtc_inv_tcFn q) (prf_substtc_varc0 s)

theorem prf_substfc_PsiFF (w s : Term) :
    Prf (substfc zero s (PsiFF w) =eq nodeOkDotF (tcFn w) (nthcT (tcFn w) s)) :=
  prf_substfc_nodeOkDotF_gen s (tcFn w) _ _ (substtc_inv_tcFn w)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s)))

theorem hPsiIdF_ok (q : Term) :
    Prf (substfc zero (varc (numeral 0)) (PsiFF q) =eq PsiFF q) :=
  prf_substfc_PsiFF q (varc (numeral 0))

/-! ### 11.4 · El puente `cdrc` desgatillado -/

theorem PrfH_congr_cdrcT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (cdrcT x =eq cdrcT y) := by
  unfold cdrcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_congr_cons_head h)))

theorem pcc_cdrcD_bridge_cons (X : Term) :
    Prf ((X =eq cons (carc X) (cdrc X))
      ⇒ provFromCode (eqCodeFn (cdrcT (tcFn X)) (tcFn (cdrc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (X =eq cons (carc X) (cdrc X))
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_cdrcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_cdrc (carc X) (cdrc X)) _)

/-! ### 11.5 · EL COMBINADOR: `∨`-elim OBJETO y `∨`-intro CÓDIGO de una vez -/

theorem prf_or_step {A B1 B2 : Formula} {C1 C2 : Term}
    (h1 : Prf (A ⇒ (B1 ⇒ provFromCode C1)))
    (h2 : Prf (A ⇒ (B2 ⇒ provFromCode C2))) :
    Prf (A ⇒ (lor B1 B2 ⇒ provFromCode (orc C1 C2))) := by
  refine prf_deduction (deduction_aux ?_ (lor B1 B2) [A] rfl)
  have hor : PrfH [lor B1 B2, A] (lor B1 B2) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_or_elim hor ?_ ?_
  · exact PrfH_or_introL_code (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h1 _)
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      (PrfH.hyp _ _ (List.Mem.head _)))
  · exact PrfH_or_introR_code (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h2 _)
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      (PrfH.hyp _ _ (List.Mem.head _)))

/-! ### 11.6 · Los 6 patrones de caso -/

theorem pcc_case_shape (X : Term) (k n : Nat) :
    Prf (consOk X ⇒ (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))
      ⇒ provFromCode (shapeDot (tcFn X) k n))) := by
  refine prf_deduction (deduction_aux ?_
    (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))) [consOk X] rfl)
  have hsh := PrfH.hyp
    (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)) :: [consOk X])
    _ (List.Mem.head _)
  have hcons : PrfH
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)) :: [consOk X])
      (X =eq cons (carc X) (cdrc X)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  exact PrfH_and_intro_code _ _ (PrfH_shape_carc X k hcons (PrfH_and_elim_left hsh))
    (PrfH_shape_lenc X n (PrfH_and_elim_right hsh))

theorem pcc_case_un (q X : Term) (k : Nat) :
    Prf (consOk X ⇒ (unOk q X k ⇒ provFromCode (unDot (tcFn q) (tcFn X) k))) := by
  refine prf_deduction (deduction_aux ?_ (unOk q X k) [consOk X] rfl)
  have hu := PrfH.hyp (unOk q X k :: [consOk X]) _ (List.Mem.head _)
  have hcons : PrfH (unOk q X k :: [consOk X]) (X =eq cons (carc X) (cdrc X)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsh : PrfH (unOk q X k :: [consOk X])
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2))) :=
    PrfH_and_elim_left hu
  have hlen := PrfH_and_elim_right hsh
  have h12 : PrfH (unOk q X k :: [consOk X]) (lt (numeralM 1) (numeralM 2)) :=
    prf_to_prfH (prf_lt_succ_self (numeralM 1)) _
  have hlt : PrfH (unOk q X k :: [consOk X]) (lt (numeralM 1) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen) h12
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _ (PrfH_shape_carc X k hcons (PrfH_and_elim_left hsh))
      (PrfH_shape_lenc X 2 hlen))
    (PrfH_child_in q X 1 hlt (PrfH_and_elim_right hu))

theorem pcc_case_bin (q X : Term) (k : Nat) :
    Prf (consOk X ⇒ (binOk q X k ⇒ provFromCode (binDot (tcFn q) (tcFn X) k))) := by
  refine prf_deduction (deduction_aux ?_ (binOk q X k) [consOk X] rfl)
  have hb := PrfH.hyp (binOk q X k :: [consOk X]) _ (List.Mem.head _)
  have hcons : PrfH (binOk q X k :: [consOk X]) (X =eq cons (carc X) (cdrc X)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsh : PrfH (binOk q X k :: [consOk X])
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3))) :=
    PrfH_and_elim_left hb
  have hmem : PrfH (binOk q X k :: [consOk X])
      (land (In (nthc X (numeralM 1)) q) (In (nthc X (numeralM 2)) q)) :=
    PrfH_and_elim_right hb
  have hlen := PrfH_and_elim_right hsh
  have h23 : PrfH (binOk q X k :: [consOk X]) (lt (numeralM 2) (numeralM 3)) :=
    prf_to_prfH (prf_lt_succ_self (numeralM 2)) _
  have h13 : PrfH (binOk q X k :: [consOk X]) (lt (numeralM 1) (numeralM 3)) :=
    prf_to_prfH (prf_mp (prf_lt_succ_of_lt (numeralM 1) (numeralM 2))
      (prf_lt_succ_self (numeralM 1))) _
  have hlt1 : PrfH (binOk q X k :: [consOk X]) (lt (numeralM 1) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen) h13
  have hlt2 : PrfH (binOk q X k :: [consOk X]) (lt (numeralM 2) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen) h23
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _ (PrfH_shape_carc X k hcons (PrfH_and_elim_left hsh))
      (PrfH_shape_lenc X 3 hlen))
    (PrfH_and_intro_code _ _ (PrfH_child_in q X 1 hlt1 (PrfH_and_elim_left hmem))
      (PrfH_child_in q X 2 hlt2 (PrfH_and_elim_right hmem)))

theorem pcc_case_strBin (q X : Term) (k : Nat) :
    Prf (consOk X ⇒ (strBinOk q X k ⇒ provFromCode (strBinDot (tcFn q) (tcFn X) k))) := by
  refine prf_deduction (deduction_aux ?_ (strBinOk q X k) [consOk X] rfl)
  have hb := PrfH.hyp (strBinOk q X k :: [consOk X]) _ (List.Mem.head _)
  have hcons : PrfH (strBinOk q X k :: [consOk X]) (X =eq cons (carc X) (cdrc X)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsh : PrfH (strBinOk q X k :: [consOk X])
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3))) :=
    PrfH_and_elim_left hb
  have hlen := PrfH_and_elim_right hsh
  have h23 : PrfH (strBinOk q X k :: [consOk X]) (lt (numeralM 2) (numeralM 3)) :=
    prf_to_prfH (prf_lt_succ_self (numeralM 2)) _
  have hlt2 : PrfH (strBinOk q X k :: [consOk X]) (lt (numeralM 2) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen) h23
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _ (PrfH_shape_carc X k hcons (PrfH_and_elim_left hsh))
      (PrfH_shape_lenc X 3 hlen))
    (PrfH_child_in q X 2 hlt2 (PrfH_and_elim_right hb))

theorem pcc_case_nil (X : Term) :
    Prf (consOk X ⇒ (Formula.eq X nil ⇒ provFromCode (eqCodeFn (tcFn X) (tcFn nil)))) := by
  refine prf_deduction (deduction_aux ?_ (Formula.eq X nil) [consOk X] rfl)
  exact PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked X nil) _)
    (PrfH.hyp (Formula.eq X nil :: [consOk X]) _ (List.Mem.head _))

theorem pcc_case_cons (q X : Term) :
    Prf (consOk X ⇒ (land (In (carc X) q) (In (cdrc X) q)
      ⇒ provFromCode (andc (inFormCodeFn (carcT (tcFn X)) (tcFn q))
                           (inFormCodeFn (cdrcT (tcFn X)) (tcFn q))))) := by
  refine prf_deduction (deduction_aux ?_ (land (In (carc X) q) (In (cdrc X) q)) [consOk X] rfl)
  have hm := PrfH.hyp (land (In (carc X) q) (In (cdrc X) q) :: [consOk X]) _ (List.Mem.head _)
  have hcons : PrfH (land (In (carc X) q) (In (cdrc X) q) :: [consOk X])
      (X =eq cons (carc X) (cdrc X)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  -- `carc`: A1' sobre `(carc X)˙` y transporte a `carcT Ẋ` con el puente R‑A3‑1 (simetrizado)
  have hA : PrfH _ (provFromCode (inFormCodeFn (tcFn (carc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (carc X) q) _) (PrfH_and_elim_left hm)
  have hbc : PrfH _ (provFromCode (eqc (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have hbcs : PrfH _ (provFromCode (eqc (tcFn (carc X)) (carcT (tcFn X)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hbc
  have hC : PrfH _ (provFromCode (inFormCodeFn (carcT (tcFn X)) (tcFn q))) :=
    PrfH_rw (fun s => inFormCodeFn s (tcFn q)) (hG_in q) _ _ hbcs hA
  -- `cdrc`: idem
  have hB : PrfH _ (provFromCode (inFormCodeFn (tcFn (cdrc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (cdrc X) q) _) (PrfH_and_elim_right hm)
  have hbd : PrfH _ (provFromCode (eqc (cdrcT (tcFn X)) (tcFn (cdrc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcD_bridge_cons X) _) hcons
  have hbds : PrfH _ (provFromCode (eqc (tcFn (cdrc X)) (cdrcT (tcFn X)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_cdrcT (substtc_inv_tcFn X)) hbd
  have hD : PrfH _ (provFromCode (inFormCodeFn (cdrcT (tcFn X)) (tcFn q))) :=
    PrfH_rw (fun s => inFormCodeFn s (tcFn q)) (hG_in q) _ _ hbds hB
  exact PrfH_and_intro_code _ _ hC hD

/-! ### 11.7 · A2 COMPLETO: los 12 plegados a la derecha -/

theorem pcc_nodeOkF_tracked (q X : Term) :
    Prf (nodeOkF q X ⇒ provFromCode (nodeOkDotF (tcFn q) (tcFn X))) := by
  have hall : Prf (consOk X ⇒ (lorAll (nulOk X 2) (nodeDisj q X)
      ⇒ provFromCode (nodeOkDotF (tcFn q) (tcFn X)))) :=
    prf_or_step (pcc_case_shape X 2 1)
      (prf_or_step (pcc_case_strBin q X 3)
        (prf_or_step (pcc_case_bin q X 4)
          (prf_or_step (pcc_case_bin q X 5)
            (prf_or_step (pcc_case_un q X 6)
              (prf_or_step (pcc_case_bin q X 7)
                (prf_or_step (pcc_case_bin q X 8)
                  (prf_or_step (pcc_case_un q X 9)
                    (prf_or_step (pcc_case_shape X 0 2)
                      (prf_or_step (pcc_case_strBin q X 1)
                        (prf_or_step (pcc_case_nil X) (pcc_case_cons q X)))))))))))
  refine prf_deduction ?_
  have h : PrfH [nodeOkF q X] (nodeOkF q X) := prfH_hyp_self _
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hall _) (PrfH_and_elim_left h))
    (PrfH_and_elim_right h)

/-! ### 11.8 · `hbody`, obligaciones mecánicas y RESULTADO COMPLETO -/

theorem hbodyF_ok (q i : Term) :
    Prf (wfAllF q ⇒ (lt i (lenc q) ⇒ provFromCode (substfc zero (tcFn i) (PsiFF q)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAllF q] rfl)
  let Γ : List Formula := [lt i (lenc q), wfAllF q]
  show PrfH Γ (provFromCode (substfc zero (tcFn i) (PsiFF q)))
  have hlt : PrfH Γ (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH Γ (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (nodeOkF (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (nodeOkF (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))
      = Formula.impl (lt i (lenc q)) (nodeOkF q (nthc q i)) := by
    simp only [nodeOkF, nodeDisj, lorAll, consOk, nulOk, unOk, binOk, strBinOk, varOk,
      land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero,
      substFormula, substTerm, substTerms,
      substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have hq1 : PrfH Γ (Formula.impl (lt i (lenc q)) (nodeOkF q (nthc q i))) := by
    have hh := PrfH.mp _ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q1
      (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (nodeOkF (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0)))) i)) hwf
    rwa [hsubst] at hh
  have hnode : PrfH Γ (nodeOkF q (nthc q i)) := PrfH.mp _ _ _ hq1 hlt
  have hpure : PrfH Γ (provFromCode (nodeOkDotF (tcFn q) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_nodeOkF_tracked q (nthc q i)) _) hnode
  have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hsym : PrfH Γ (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  have hcomp : PrfH Γ (provFromCode (nodeOkDotF (tcFn q) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_rw (fun s => nodeOkDotF (tcFn q) s) (hG_nodeF q) _ _ hsym hpure
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiFF q (tcFn i)))) _) hcomp

theorem hPlF_ok : ∀ (k : Nat) (q : Term), liftTerm k (PsiFF q) = PsiFF (liftTerm k q) := by
  intro k q
  simp only [PsiFF, nodeOkDotF, nodeDisjDot, lorAllc, shapeDot, unDot, binDot, strBinDot,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem hPsF_ok : ∀ (v : Nat) (t q : Term), substTerm v t (PsiFF q) = PsiFF (substTerm v t q) := by
  intro v t q
  simp only [PsiFF, nodeOkDotF, nodeDisjDot, lorAllc, shapeDot, unDot, binDot, strBinDot,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem hClF_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAllF q) = wfAllF (liftTerm k q) := by
  intro k q
  simp only [wfAllF, nodeOkF, nodeDisj, lorAll, consOk, nulOk, unOk, binOk, strBinOk, varOk,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero,
    liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCsF_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAllF q) = wfAllF (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAllF, nodeOkF, nodeDisj, lorAll, consOk, nulOk, unOk, binOk, strBinOk, varOk,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero,
    substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

theorem pcc_wfAllF_tracked (w : Term) : Prf (wfAllF w ⇒ provFromCode (wfAllDotF w)) :=
  pcc_bdAll_intro wfAllF lenc PsiFF w hClF_ok hCsF_ok hbl_ok hbs_ok hPlF_ok hPsF_ok
    hPsiIdF_ok hbodyF_ok

/-- **A3 COMPLETA (los 12 disyuntos)**, `w` y `c` ABSTRACTOS. -/
theorem pcc_isFCB_tracked_full (w c : Term) :
    Prf (isFCBF w c ⇒ provFromCode (isFCBDotF w c)) := by
  refine prf_deduction ?_
  have h : PrfH [isFCBF w c] (isFCBF w c) := prfH_hyp_self _
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllF_tracked w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

end A3Frag

#print axioms A3Frag.pcc_isFCB_tracked_full
#print axioms A3Frag.pcc_wfAllF_tracked
#print axioms A3Frag.pcc_nodeOkF_tracked
#print axioms A3Frag.hbodyF_ok
#print axioms A3Frag.pcc_isFCB_tracked
#print axioms A3Frag.pcc_wfAll2_tracked
#print axioms A3Frag.hbody_ok
#print axioms A3Frag.pcc_nodeOk2_tracked
#print axioms A3Frag.hPsiId_ok
#print axioms A3Frag.pcc_In_atom_tracked

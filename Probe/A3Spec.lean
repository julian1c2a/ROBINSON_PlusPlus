/-
ESPECIFICACIÓN A3 — instanciación EXACTA de `pcc_bdAll_intro` sobre `wfAll`.
Sólo comprueba tipos: reduce A3 a las 8 obligaciones. No prueba `hbody`.
    lake env lean Probe/A3Spec.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

namespace A3Spec

/-! ## 0 · Copia literal de `sondeos/ParseWitness.lean` (el OBJETO) -/

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

/-- ⚠️ **ENMIENDA R‑A3‑1** (no está en `sondeos/ParseWitness.lean`): el nodo es un `cons`.
    Sin esto NO hay puente `carcT ẋ → (carc x)˙` para `x` abstracto: los tres que existen
    (`pcc_eval_carc`, `pcc_carcD_bridge`, `pcc_eval_carc_nthc`) piden un `cons` literal, `lineWF`
    o `chainOk`. Es OBJETO puro: NO aparece en la imagen punteada. -/
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

/-! ## 1 · Copia literal de `sondeos/InTracked.lean` (A1) -/

noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))
noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))
noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

/-! ## 2 · LA IMAGEN PUNTEADA de `nodeOk` — evaluada, y con los `liftc` YA NORMALIZADOS.

    `W`   = código del testigo (`tcFn w`, CERRADO ⇒ `liftc 0 W =eq W`, no se escribe el `liftc`);
    `I`   = código del índice al nivel del `∀` acotado (para `PsiF`: `⌜v₀⌝`);
    `Iup` = el MISMO índice bajo UN binder `exc` (para `PsiF`: `⌜v₁⌝`).                       -/

/-- El nodo, dotado: `nthcT(Ẇ, I)`. -/
noncomputable def nodeC (W I : Term) : Term := nthcT W I

/-- `In (nthc X j) w` dotado (`X` = el nodo, ya bajo el `exc` ⇒ `Iup`). -/
noncomputable def inNthDot (W Iup : Term) (j : Nat) : Term :=
  bdExCode (lencT W)
    (eqCodeFn (nthcT W (varc (numeral 0))) (nthcT (nodeC W Iup) (tcFn (numeralM j))))

/-- `In (carc X) w` dotado. -/
noncomputable def inCarcDot (W Iup : Term) : Term :=
  bdExCode (lencT W) (eqCodeFn (nthcT W (varc (numeral 0))) (carcT (nodeC W Iup)))

/-- `In (cdrc X) w` dotado. -/
noncomputable def inCdrcDot (W Iup : Term) : Term :=
  bdExCode (lencT W) (eqCodeFn (nthcT W (varc (numeral 0))) (cdrcT (nodeC W Iup)))

noncomputable def nulOkDot (W I : Term) (k : Nat) : Term :=
  andc (eqCodeFn (carcT (nodeC W I)) (tcFn (numeralM k)))
       (eqCodeFn (lencT (nodeC W I)) (tcFn (numeralM 1)))

noncomputable def unOkDot (W I Iup : Term) (k : Nat) : Term :=
  andc (andc (eqCodeFn (carcT (nodeC W I)) (tcFn (numeralM k)))
             (eqCodeFn (lencT (nodeC W I)) (tcFn (numeralM 2))))
       (inNthDot W Iup 1)

noncomputable def binOkDot (W I Iup : Term) (k : Nat) : Term :=
  andc (andc (eqCodeFn (carcT (nodeC W I)) (tcFn (numeralM k)))
             (eqCodeFn (lencT (nodeC W I)) (tcFn (numeralM 3))))
       (andc (inNthDot W Iup 1) (inNthDot W Iup 2))

noncomputable def strBinOkDot (W I Iup : Term) (k : Nat) : Term :=
  andc (andc (eqCodeFn (carcT (nodeC W I)) (tcFn (numeralM k)))
             (eqCodeFn (lencT (nodeC W I)) (tcFn (numeralM 3))))
       (inNthDot W Iup 2)

noncomputable def varOkDot (W I : Term) : Term :=
  andc (eqCodeFn (carcT (nodeC W I)) (tcFn (numeralM 0)))
       (eqCodeFn (lencT (nodeC W I)) (tcFn (numeralM 2)))

noncomputable def orcAll : Term → List Term → Term
  | a, []      => a
  | a, b :: bs => orc a (orcAll b bs)

/-- La disyunción DOTADA, los 12 casos en el mismo orden que `nodeOk`. -/
noncomputable def nodeOkDotAt (W I Iup : Term) : Term :=
  orcAll (nulOkDot W I 2)
    [ strBinOkDot W I Iup 3, binOkDot W I Iup 4, binOkDot W I Iup 5, unOkDot W I Iup 6
    , binOkDot W I Iup 7, binOkDot W I Iup 8, unOkDot W I Iup 9, varOkDot W I
    , strBinOkDot W I Iup 1
    , eqCodeFn (nodeC W I) (tcFn nil)
    , andc (inCarcDot W Iup) (inCdrcDot W Iup) ]

/-- **`PsiF` de A3**: el cuerpo dotado con el hueco `⌜v₀⌝` (y `⌜v₁⌝` bajo el `exc`). -/
noncomputable def nodeOkDot (q : Term) : Term :=
  nodeOkDotAt (tcFn q) (varc (numeral 0)) (varc (numeral 1))

/-- **Imagen punteada de `wfAll`** = lo que `pcc_bdAll_intro` entrega, literalmente. -/
noncomputable def wfAllDot (q : Term) : Term := bdAllCode (tcFn (lenc q)) (nodeOkDot q)

/-- **Imagen punteada de `isFCB`**. -/
noncomputable def isFCBDot (w c : Term) : Term := andc (wfAllDot w) (bdInDot c w)

/-! ## 3 · LA REDUCCIÓN: A3 ⇐ las 8 obligaciones (sólo type-checking) -/

theorem pcc_wfAll_tracked_of_obligations (w : Term)
    (hCl : ∀ (k : Nat) (q : Term), liftFormula k (wfAll q) = wfAll (liftTerm k q))
    (hCs : ∀ (v : Nat) (t q : Term), substFormula v t (wfAll q) = wfAll (substTerm v t q))
    (hbl : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q))
    (hbs : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q))
    (hPl : ∀ (k : Nat) (q : Term), liftTerm k (nodeOkDot q) = nodeOkDot (liftTerm k q))
    (hPs : ∀ (v : Nat) (t q : Term),
      substTerm v t (nodeOkDot q) = nodeOkDot (substTerm v t q))
    (hPsiId : ∀ q : Term,
      Prf (substfc zero (varc (numeral 0)) (nodeOkDot q) =eq nodeOkDot q))
    (hbody : ∀ q i : Term, Prf (wfAll q ⇒ (lt i (lenc q)
      ⇒ provFromCode (substfc zero (tcFn i) (nodeOkDot q))))) :
    Prf (wfAll w ⇒ provFromCode (wfAllDot w)) :=
  pcc_bdAll_intro wfAll lenc nodeOkDot w hCl hCs hbl hbs hPl hPs hPsiId hbody

/-! ## 4 · Las 6 obligaciones MECÁNICAS, descargadas -/

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hPl_ok : ∀ (k : Nat) (q : Term),
    liftTerm k (nodeOkDot q) = nodeOkDot (liftTerm k q) := by
  intro k q
  simp only [nodeOkDot, nodeOkDotAt, orcAll, nulOkDot, unOkDot, binOkDot, strBinOkDot, varOkDot,
    inNthDot, inCarcDot, inCdrcDot, nodeC, bdExCode, exc, andc, orc, ltCodeFn, atom2CodeFn,
    eqCodeFn, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn, nil, cons, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_numeralM, liftTerm_strCode]

theorem hPs_ok : ∀ (v : Nat) (t q : Term),
    substTerm v t (nodeOkDot q) = nodeOkDot (substTerm v t q) := by
  intro v t q
  simp only [nodeOkDot, nodeOkDotAt, orcAll, nulOkDot, unOkDot, binOkDot, strBinOkDot, varOkDot,
    inNthDot, inCarcDot, inCdrcDot, nodeC, bdExCode, exc, andc, orc, ltCodeFn, atom2CodeFn,
    eqCodeFn, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn, nil, cons, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_numeralM, substTerm_strCode]

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

/-! ## 5 · A3 REDUCIDA a DOS obligaciones -/

theorem pcc_wfAll_tracked_of_2 (w : Term)
    (hPsiId : ∀ q : Term,
      Prf (substfc zero (varc (numeral 0)) (nodeOkDot q) =eq nodeOkDot q))
    (hbody : ∀ q i : Term, Prf (wfAll q ⇒ (lt i (lenc q)
      ⇒ provFromCode (substfc zero (tcFn i) (nodeOkDot q))))) :
    Prf (wfAll w ⇒ provFromCode (wfAllDot w)) :=
  pcc_wfAll_tracked_of_obligations w hCl_ok hCs_ok hbl_ok hbs_ok hPl_ok hPs_ok hPsiId hbody

/-- Y A3 entera, dado además A1. -/
theorem pcc_isFCB_tracked_of_2 (w c : Term)
    (hPsiId : ∀ q : Term,
      Prf (substfc zero (varc (numeral 0)) (nodeOkDot q) =eq nodeOkDot q))
    (hbody : ∀ q i : Term, Prf (wfAll q ⇒ (lt i (lenc q)
      ⇒ provFromCode (substfc zero (tcFn i) (nodeOkDot q)))))
    (hA1 : Prf (In c w ⇒ provFromCode (bdInDot c w))) :
    Prf (isFCB w c ⇒ provFromCode (isFCBDot w c)) := by
  refine prf_deduction ?_
  have h : PrfH [isFCB w c] (isFCB w c) := prfH_hyp_self _
  have h1 : PrfH [isFCB w c] (provFromCode (wfAllDot w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll_tracked_of_2 w hPsiId hbody) _) (PrfH_and_elim_left h)
  have h2 : PrfH [isFCB w c] (provFromCode (bdInDot c w)) :=
    PrfH.mp _ _ _ (prf_to_prfH hA1 _) (PrfH_and_elim_right h)
  exact PrfH_and_intro_code _ _ h1 h2

/-! ## 6 · R‑A3‑1: el puente `carc`/`cdrc` SIN `lineWF` ni `chainOk` -/

/-- Puente `carc` degatillado: sólo pide que el nodo sea un `cons`.
    (`pcc_carcD_bridge` pide `lineWF`; `pcc_eval_carc_nthc` pide `chainOk`. Ninguno sirve aquí.) -/
theorem pcc_carcD_bridge_cons (X : Term) :
    Prf ((X =eq cons (carc X) (cdrc X))
      ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (X =eq cons (carc X) (cdrc X))
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

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

end A3Spec

#print axioms A3Spec.pcc_carcD_bridge_cons
#print axioms A3Spec.pcc_cdrcD_bridge_cons
#print axioms A3Spec.pcc_wfAll_tracked_of_obligations
#print axioms A3Spec.pcc_wfAll_tracked_of_2
#print axioms A3Spec.pcc_isFCB_tracked_of_2

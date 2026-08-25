/-
# CRITICO DE COMPLETITUD del hito (i) -- Probe/CritCompleto.lean

SS1-SS15 = copia MECANICA de Probe/SubC_mutua.lean (para construir encima sin tocar el
fichero de otro agente). SS16 es lo nuevo.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace SubCMutua

/-! ## 1 · EL OBJETO — copia LITERAL de `sondeos/A3IsFCBTracked.lean` §1 -/

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

/-- Disyunción asociada a la derecha de una lista NO vacía. -/
def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- El nodo es un `cons` (enmienda R‑A3‑1). -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

/-- Envoltorio: «además de `F`, el nodo es un `cons`». -/
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def nodeOk (w X : Term) : Formula :=
  lorAll (cOk X (nulOk X 2))                        -- ⊥                       (tag 2)
    [ cOk X (strBinOk w X 3)                        -- atom p ts               (tag 3)
    , cOk X (binOk w X 4)                           -- eq t u                  (tag 4)
    , cOk X (binOk w X 5)                           -- impl a b                (tag 5)
    , cOk X (unOk  w X 6)                           -- ∀ a                     (tag 6)
    , cOk X (binOk w X 7)                           -- ∧ a b                   (tag 7)
    , cOk X (binOk w X 8)                           -- ∨ a b                   (tag 8)
    , cOk X (unOk  w X 9)                           -- ∃ a                     (tag 9)
    , cOk X (varOk X)                               -- var n                   (tag 0)
    , cOk X (strBinOk w X 1)                        -- func s ts               (tag 1)
    , Formula.eq X nil                              -- termsCodeM []   ⚠️ DESNUDO
    , cOk X (land (In (carc X) w) (In (cdrc X) w)) ]-- termsCodeM (t :: ts)

def wfAll (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCB (w c : Term) : Formula := land (wfAll w) (In c w)

/-! ## 2 · `prf_cdrc_cons` -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-! ## 3 · `consOk` sobre un `cons` LITERAL -/

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

/-! ## 4 · EL TESTIGO `subCodes` -/

mutual
def subCodesT : Term → List Term
  | .var n     => [termCodeM (.var n)]
  | .func s ts => termCodeM (.func s ts) :: subCodesTs ts
def subCodesTs : List Term → List Term
  | []      => [nil]
  | t :: ts => termsCodeM (t :: ts) :: (subCodesT t ++ subCodesTs ts)
end

def subCodes : Formula → List Term
  | .bottom          => [formCodeM Formula.bottom]
  | .atom p ts       => formCodeM (.atom p ts) :: subCodesTs ts
  | .eq t u          => formCodeM (.eq t u) :: (subCodesT t ++ subCodesT u)
  | .impl a b        => formCodeM (.impl a b) :: (subCodes a ++ subCodes b)
  | Formula.forall a => formCodeM (Formula.forall a) :: subCodes a
  | .and a b         => formCodeM (.and a b) :: (subCodes a ++ subCodes b)
  | .or a b          => formCodeM (.or a b) :: (subCodes a ++ subCodes b)
  | .ex a            => formCodeM (.ex a) :: subCodes a

theorem mem_self_subCodesT (t : Term) : List.Mem (termCodeM t) (subCodesT t) := by
  cases t with
  | var n     => simp only [subCodesT]; exact List.Mem.head _
  | func s ts => simp only [subCodesT]; exact List.Mem.head _

theorem mem_self_subCodesTs : ∀ ts : List Term, List.Mem (termsCodeM ts) (subCodesTs ts)
  | []      => by simp only [subCodesTs, termsCodeM]; exact List.Mem.head _
  | _ :: _  => by simp only [subCodesTs]; exact List.Mem.head _

theorem mem_self_subCodes (φ : Formula) : List.Mem (formCodeM φ) (subCodes φ) := by
  cases φ <;> (simp only [subCodes]; exact List.Mem.head _)

/-! ## 5 · CLAUSURA -/

def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_formCodeM (φ : Formula) : CodeClosed (formCodeM φ) :=
  ⟨fun c => liftTerm_formCodeM c φ, fun v s => substTerm_formCodeM v s φ⟩

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

theorem closed_termsCodeM (ts : List Term) : CodeClosed (termsCodeM ts) :=
  ⟨fun c => liftTerm_termsCodeM c ts, fun v s => substTerm_termsCodeM v s ts⟩

theorem closed_nil : CodeClosed nil :=
  ⟨fun c => liftTerm_nil c, fun v s => substTerm_nil v s⟩

mutual
theorem closed_mem_subCodesT : ∀ (t x : Term), List.Mem x (subCodesT t) → CodeClosed x
  | .var n, x, h => by
      simp only [subCodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.var n)
      · cases h'
  | .func s ts, x, h => by
      simp only [subCodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.func s ts)
      · exact closed_mem_subCodesTs ts x h'
theorem closed_mem_subCodesTs : ∀ (ts : List Term) (x : Term),
    List.Mem x (subCodesTs ts) → CodeClosed x
  | [], x, h => by
      simp only [subCodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_nil
      · cases h'
  | t :: ts, x, h => by
      simp only [subCodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termsCodeM (t :: ts)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodesT t x hA
        · exact closed_mem_subCodesTs ts x hB
end

theorem closed_mem_subCodes : ∀ (φ : Formula) (x : Term), List.Mem x (subCodes φ) → CodeClosed x
  | .bottom, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM Formula.bottom
      · cases h'
  | .atom p ts, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.atom p ts)
      · exact closed_mem_subCodesTs ts x h'
  | .eq t u, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.eq t u)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodesT t x hA
        · exact closed_mem_subCodesT u x hB
  | .impl a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.impl a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodes a x hA
        · exact closed_mem_subCodes b x hB
  | Formula.forall a, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (Formula.forall a)
      · exact closed_mem_subCodes a x h'
  | .and a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.and a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodes a x hA
        · exact closed_mem_subCodes b x hB
  | .or a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.or a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodes a x hA
        · exact closed_mem_subCodes b x hB
  | .ex a, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.ex a)
      · exact closed_mem_subCodes a x h'

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

theorem liftTerm_objList_subCodes (c : Nat) (φ : Formula) :
    liftTerm c (objList (subCodes φ)) = objList (subCodes φ) :=
  liftTerm_objList c (subCodes φ) (fun x hx => (closed_mem_subCodes φ x hx).1 c)

theorem substTerm_objList_subCodes (v : Nat) (s : Term) (φ : Formula) :
    substTerm v s (objList (subCodes φ)) = objList (subCodes φ) :=
  substTerm_objList v s (subCodes φ) (fun x hx => (closed_mem_subCodes φ x hx).2 v s)

/-! ## 6 · El puente `objList` ⇄ meta -/

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

/-! ## 7 · `prf_bdAll_numeral` -/

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

/-! ## 8 · `PrfH_congr_nodeOk` y `prf_wfAll_objList` para el `nodeOk` NUEVO -/

theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula :=
    Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_congr_nodeOk {w X₁ X₂ : Term} (h : Prf (X₁ =eq X₂)) (hN : Prf (nodeOk w X₁)) :
    Prf (nodeOk w X₂) :=
  prfH_nil_to_prf (PrfH_congr_nodeOk (prf_to_prfH h []) (prf_to_prfH hN [])) rfl

theorem prf_wfAll_objList (L : List Term)
    (hcl : ∀ s : Term, substTerm 0 s (objList L) = objList L)
    (hlift : liftTerm 0 (objList L) = objList L)
    (h : ∀ (k : Nat) (x : Term), L[k]? = some x → Prf (nodeOk (objList L) x)) :
    Prf (wfAll (objList L)) := by
  let w : Term := objList L
  let Φ : Formula := nodeOk w (nthc w (.var 0))
  have hsub : ∀ s : Term, substFormula 0 s Φ = nodeOk w (nthc w s) := by
    intro s
    simp only [Φ, w, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor,
      In, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
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

theorem prf_wfAll_subCodes (φ : Formula)
    (h : ∀ (k : Nat) (x : Term), (subCodes φ)[k]? = some x →
      Prf (nodeOk (objList (subCodes φ)) x)) :
    Prf (wfAll (objList (subCodes φ))) :=
  prf_wfAll_objList (subCodes φ)
    (fun s => substTerm_objList_subCodes 0 s φ) (liftTerm_objList_subCodes 0 φ) h

theorem prf_isFCB_of_wfAll (φ : Formula) (hwf : Prf (wfAll (objList (subCodes φ)))) :
    Prf (isFCB (objList (subCodes φ)) (formCodeM φ)) :=
  prf_and_intro hwf (prf_In_objList _ _ (mem_self_subCodes φ))

/-! ## 10 · LO NUEVO — combinadores para elegir disyunto -/

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j1 A B)) h

theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j2 A B)) h

theorem prf_lorAll_head : ∀ (a : Formula) (bs : List Formula), Prf a → Prf (lorAll a bs)
  | _, [],     h => h
  | _, _ :: _, h => prf_orL h

theorem prf_lorAll_tail (a b : Formula) (bs : List Formula) (h : Prf (lorAll b bs)) :
    Prf (lorAll a (b :: bs)) := prf_orR h

/-- Los 12 inyectores de disyunto. `iⱼ` mete el disyunto `j` (0‑based) en `nodeOk`. -/
theorem nodeOk_i0 (w X : Term) (h : Prf (cOk X (nulOk X 2))) : Prf (nodeOk w X) :=
  prf_lorAll_head _ _ h
theorem nodeOk_i1 (w X : Term) (h : Prf (cOk X (strBinOk w X 3))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)
theorem nodeOk_i2 (w X : Term) (h : Prf (cOk X (binOk w X 4))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h))
theorem nodeOk_i3 (w X : Term) (h : Prf (cOk X (binOk w X 5))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_head _ _ h)))
theorem nodeOk_i4 (w X : Term) (h : Prf (cOk X (unOk w X 6))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h))))
theorem nodeOk_i5 (w X : Term) (h : Prf (cOk X (binOk w X 7))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)))))
theorem nodeOk_i6 (w X : Term) (h : Prf (cOk X (binOk w X 8))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_head _ _ h))))))
theorem nodeOk_i7 (w X : Term) (h : Prf (cOk X (unOk w X 9))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)))))))
theorem nodeOk_i8 (w X : Term) (h : Prf (cOk X (varOk X))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h))))))))
theorem nodeOk_i9 (w X : Term) (h : Prf (cOk X (strBinOk w X 1))) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
        (prf_lorAll_head _ _ h)))))))))
theorem nodeOk_i10 (w X : Term) (h : Prf (Formula.eq X nil)) : Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
        (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h))))))))))
theorem nodeOk_i11 (w X : Term) (h : Prf (cOk X (land (In (carc X) w) (In (cdrc X) w)))) :
    Prf (nodeOk w X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
        (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)))))))))))

/-! ## 11 · Aritmética de listas concretas: `lenc` y `nthc` sobre `cons` LITERALES -/

theorem prf_lenc_c1 (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc_c2 (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc_c1 b))

theorem prf_lenc_c3 (a b c : Term) :
    Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil))) (prf_eq_congr_succ (prf_lenc_c2 b c))

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

/-! ## 12 · Leibniz sobre el 1er argumento de `In` -/

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := f) h ((hS u) ▸ hin)

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) :=
  prfH_nil_to_prf (PrfH_congr_In_left (prf_to_prfH h []) (prf_to_prfH hin [])) rfl

/-! ## 13 · Los CINCO MOLDES de nodo (todos sobre `cons` LITERAL ⇒ `consOk` sale sola) -/

theorem prf_cOk_nulOk (k : Nat) :
    Prf (cOk (cons (numeralM k) nil) (nulOk (cons (numeralM k) nil) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro (prf_carc_cons (numeralM k) nil) (prf_lenc_c1 (numeralM k)))

theorem prf_cOk_varOk (a : Term) :
    Prf (cOk (cons (numeralM 0) (cons a nil)) (varOk (cons (numeralM 0) (cons a nil)))) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro (prf_carc_cons (numeralM 0) (cons a nil)) (prf_lenc_c2 (numeralM 0) a))

theorem prf_cOk_unOk (w : Term) (k : Nat) (A : Term) (hA : Prf (In A w)) :
    Prf (cOk (cons (numeralM k) (cons A nil))
             (unOk w (cons (numeralM k) (cons A nil)) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons A nil)) (prf_lenc_c2 (numeralM k) A))
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM k) A nil)) hA))

theorem prf_cOk_binOk (w : Term) (k : Nat) (A B : Term)
    (hA : Prf (In A w)) (hB : Prf (In B w)) :
    Prf (cOk (cons (numeralM k) (cons A (cons B nil)))
             (binOk w (cons (numeralM k) (cons A (cons B nil))) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons A (cons B nil)))
        (prf_lenc_c3 (numeralM k) A B))
      (prf_and_intro
        (prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM k) A (cons B nil))) hA)
        (prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM k) A B nil)) hB)))

theorem prf_cOk_strBinOk (w : Term) (k : Nat) (S C : Term) (hC : Prf (In C w)) :
    Prf (cOk (cons (numeralM k) (cons S (cons C nil)))
             (strBinOk w (cons (numeralM k) (cons S (cons C nil))) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons S (cons C nil)))
        (prf_lenc_c3 (numeralM k) S C))
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM k) S C nil)) hC))

theorem prf_cOk_consCase (w A B : Term) (hA : Prf (In A w)) (hB : Prf (In B w)) :
    Prf (cOk (cons A B) (land (In (carc (cons A B)) w) (In (cdrc (cons A B)) w))) :=
  prf_and_intro (prf_consOk_cons A B)
    (prf_and_intro
      (prf_congr_In_left (prf_eq_symm (prf_carc_cons A B)) hA)
      (prf_congr_In_left (prf_eq_symm (prf_cdrc_cons A B)) hB))

/-! ## 14 · LA INDUCCIÓN MUTUA

    Se generaliza sobre un SUPERCONJUNTO `W ⊇ subCodes …` y cada nodo se prueba contra la
    lista COMPLETA `objList W`. Así nunca hace falta transportar `nodeOk w X` a
    `nodeOk (cons y w) X` (que costaría un or‑elim de 12 casos por composición). -/

mutual
theorem nodeOk_subCodesT : ∀ (t : Term) (W : List Term),
    (∀ y : Term, List.Mem y (subCodesT t) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodesT t) → Prf (nodeOk (objList W) x)
  | .var n, W, _, x, hx => by
      simp only [subCodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i8 _ _ (prf_cOk_varOk (numeralM n))
      · cases h'
  | .func s ts, W, hsub, x, hx => by
      have hts : Prf (In (termsCodeM ts) (objList W)) :=
        prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodesTs ts)))
      simp only [subCodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i9 _ _ (prf_cOk_strBinOk (objList W) 1 (strCodeM s) (termsCodeM ts) hts)
      · exact nodeOk_subCodesTs ts W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'

theorem nodeOk_subCodesTs : ∀ (ts : List Term) (W : List Term),
    (∀ y : Term, List.Mem y (subCodesTs ts) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodesTs ts) → Prf (nodeOk (objList W) x)
  | [], W, _, x, hx => by
      simp only [subCodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i10 _ _ (prf_refl nil)
      · cases h'
  | t :: ts, W, hsub, x, hx => by
      have ht : Prf (In (termCodeM t) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_subCodesT t)))))
      have hts : Prf (In (termsCodeM ts) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_subCodesTs ts)))))
      simp only [subCodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i11 _ _
          (prf_cOk_consCase (objList W) (termCodeM t) (termsCodeM ts) ht hts)
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_subCodesT t W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_subCodesTs ts W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
end

theorem nodeOk_subCodes : ∀ (φ : Formula) (W : List Term),
    (∀ y : Term, List.Mem y (subCodes φ) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodes φ) → Prf (nodeOk (objList W) x)
  | .bottom, W, _, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i0 _ _ (prf_cOk_nulOk 2)
      · cases h'
  | .atom p ts, W, hsub, x, hx => by
      have hts : Prf (In (termsCodeM ts) (objList W)) :=
        prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodesTs ts)))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i1 _ _ (prf_cOk_strBinOk (objList W) 3 (strCodeM p) (termsCodeM ts) hts)
      · exact nodeOk_subCodesTs ts W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'
  | .eq t u, W, hsub, x, hx => by
      have ht : Prf (In (termCodeM t) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_subCodesT t)))))
      have hu : Prf (In (termCodeM u) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_subCodesT u)))))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i2 _ _ (prf_cOk_binOk (objList W) 4 (termCodeM t) (termCodeM u) ht hu)
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_subCodesT t W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_subCodesT u W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .impl a b, W, hsub, x, hx => by
      have ha : Prf (In (formCodeM a) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_subCodes a)))))
      have hb : Prf (In (formCodeM b) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_subCodes b)))))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i3 _ _ (prf_cOk_binOk (objList W) 5 (formCodeM a) (formCodeM b) ha hb)
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_subCodes a W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_subCodes b W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | Formula.forall a, W, hsub, x, hx => by
      have ha : Prf (In (formCodeM a) (objList W)) :=
        prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodes a)))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i4 _ _ (prf_cOk_unOk (objList W) 6 (formCodeM a) ha)
      · exact nodeOk_subCodes a W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'
  | .and a b, W, hsub, x, hx => by
      have ha : Prf (In (formCodeM a) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_subCodes a)))))
      have hb : Prf (In (formCodeM b) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_subCodes b)))))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i5 _ _ (prf_cOk_binOk (objList W) 7 (formCodeM a) (formCodeM b) ha hb)
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_subCodes a W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_subCodes b W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .or a b, W, hsub, x, hx => by
      have ha : Prf (In (formCodeM a) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_subCodes a)))))
      have hb : Prf (In (formCodeM b) (objList W)) :=
        prf_In_objList W _
          (hsub _ (List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_subCodes b)))))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i6 _ _ (prf_cOk_binOk (objList W) 8 (formCodeM a) (formCodeM b) ha hb)
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_subCodes a W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_subCodes b W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .ex a, W, hsub, x, hx => by
      have ha : Prf (In (formCodeM a) (objList W)) :=
        prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodes a)))
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact nodeOk_i7 _ _ (prf_cOk_unOk (objList W) 9 (formCodeM a) ha)
      · exact nodeOk_subCodes a W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'

/-! ## 15 · LOS DOS TEOREMAS DEL HITO -/

theorem mem_of_getElem? : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x → List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? es k x h)

/-- **HITO (i), primera mitad**: `subCodes φ` ES un testigo de parseo válido de `⌜φ⌝`. -/
theorem prf_isFCB_subCodes (φ : Formula) :
    Prf (isFCB (objList (subCodes φ)) (formCodeM φ)) := by
  refine prf_isFCB_of_wfAll φ (prf_wfAll_subCodes φ ?_)
  intro k x hk
  exact nodeOk_subCodes φ (subCodes φ) (fun _ hy => hy) x (mem_of_getElem? _ k x hk)

/-- `substFormula` atraviesa `nodeOk`: con `A`, `B` ABSTRACTOS no queda ningún `if` que
    reducir (las únicas constantes son `numeralM k` y `nil`, ambas cerradas). -/
theorem substF_nodeOk (v : Nat) (s A B : Term) :
    substFormula v s (nodeOk A B) = nodeOk (substTerm v s A) (substTerm v s B) := by
  simp only [nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

/-- Normalización de la sustitución en el cuerpo Σ₁ (`W` y `c` CERRADOS). -/
theorem substF_isFCB (W c : Term)
    (hWl : liftTerm 0 W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (hcl : liftTerm 0 c = c) (hcs : ∀ (v : Nat) (s : Term), substTerm v s c = c) :
    substFormula 0 W (isFCB (.var 0) (liftTerm 0 c)) = isFCB W c := by
  -- forma normal del LHS: `liftTerm 0 #0 = #1` sale por cómputo puro
  have hlhs : isFCB (Term.var 0) c
      = land (Formula.forall (Formula.impl (lt (.var 0) (lenc (.var 1)))
          (nodeOk (.var 1) (nthc (.var 1) (.var 0))))) (In c (.var 0)) := rfl
  -- forma normal del RHS: aquí sí hace falta la clausura de `W`
  have hrhs : isFCB W c
      = land (Formula.forall (Formula.impl (lt (.var 0) (lenc W))
          (nodeOk W (nthc W (.var 0))))) (In c W) := by
    simp only [isFCB, wfAll, lenc, nthc, liftTerm, liftTerms, hWl]
  have hs0 : substTerm (0 + 1) W (Term.var 0) = Term.var 0 := rfl
  have hs1 : substTerm (0 + 1) W (Term.var 1) = W := rfl
  have hs00 : substTerm 0 W (Term.var 0) = W := rfl
  have hlenc : substTerm (0 + 1) W (lenc (Term.var 1)) = lenc W := rfl
  have hnthc : substTerm (0 + 1) W (nthc (Term.var 1) (Term.var 0)) = nthc W (Term.var 0) := rfl
  rw [hcl, hlhs, hrhs]
  simp only [land, In, lt, substFormula, substTerms, hWl, substF_nodeOk,
    hs0, hs1, hs00, hlenc, hnthc, hcs]

/-- **HITO (i), segunda mitad**: el Σ₁ `∃w. isFCB w ⌜φ⌝` es demostrable para toda `φ`. -/
theorem prf_isFC (φ : Formula) :
    Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 (formCodeM φ)))) := by
  refine prf_ex_intro (objList (subCodes φ)) ?_
  rw [substF_isFCB (objList (subCodes φ)) (formCodeM φ)
    (liftTerm_objList_subCodes 0 φ) (fun v s => substTerm_objList_subCodes v s φ)
    (liftTerm_formCodeM 0 φ) (fun v s => substTerm_formCodeM v s φ)]
  exact prf_isFCB_subCodes φ

/-! # ══════════════════════════════════════════════════════════════════════
    ## 16 · CRÍTICO DE COMPLETITUD — lo que se ha quedado FUERA
    ══════════════════════════════════════════════════════════════════════ -/

/-- Abreviatura del Σ₁ entregado por el hito (i): «`c` tiene testigo de parseo». -/
def isFC (c : Term) : Formula := Formula.ex (isFCB (.var 0) (liftTerm 0 c))

theorem prf_isFC_form (φ : Formula) : Prf (isFC (formCodeM φ)) := prf_isFC φ

/-! ### 16.1 · EL GEMELO DE TÉRMINOS — **no existía** (y es BARATO)

    Los esquemas `q1`(9), `q2`(10) y `leibniz`(13) llevan un código de **TÉRMINO** en la
    casilla 3 (y 4). La enmienda pide ahí la obligación análoga, y `prf_isFC` sólo cubre
    fórmulas. Aquí se cierra el hueco reusando LA MISMA inducción mutua. -/

theorem liftTerm_objList_subCodesT (c : Nat) (t : Term) :
    liftTerm c (objList (subCodesT t)) = objList (subCodesT t) :=
  liftTerm_objList c _ (fun x hx => (closed_mem_subCodesT t x hx).1 c)

theorem substTerm_objList_subCodesT (v : Nat) (s : Term) (t : Term) :
    substTerm v s (objList (subCodesT t)) = objList (subCodesT t) :=
  substTerm_objList v s _ (fun x hx => (closed_mem_subCodesT t x hx).2 v s)

theorem liftTerm_objList_subCodesTs (c : Nat) (ts : List Term) :
    liftTerm c (objList (subCodesTs ts)) = objList (subCodesTs ts) :=
  liftTerm_objList c _ (fun x hx => (closed_mem_subCodesTs ts x hx).1 c)

theorem substTerm_objList_subCodesTs (v : Nat) (s : Term) (ts : List Term) :
    substTerm v s (objList (subCodesTs ts)) = objList (subCodesTs ts) :=
  substTerm_objList v s _ (fun x hx => (closed_mem_subCodesTs ts x hx).2 v s)

theorem prf_isFCB_subCodesT (t : Term) :
    Prf (isFCB (objList (subCodesT t)) (termCodeM t)) := by
  refine prf_and_intro
    (prf_wfAll_objList (subCodesT t)
      (fun s => substTerm_objList_subCodesT 0 s t) (liftTerm_objList_subCodesT 0 t) ?_)
    (prf_In_objList _ _ (mem_self_subCodesT t))
  intro k x hk
  exact nodeOk_subCodesT t (subCodesT t) (fun _ hy => hy) x (mem_of_getElem? _ k x hk)

theorem prf_isFCB_subCodesTs (ts : List Term) :
    Prf (isFCB (objList (subCodesTs ts)) (termsCodeM ts)) := by
  refine prf_and_intro
    (prf_wfAll_objList (subCodesTs ts)
      (fun s => substTerm_objList_subCodesTs 0 s ts) (liftTerm_objList_subCodesTs 0 ts) ?_)
    (prf_In_objList _ _ (mem_self_subCodesTs ts))
  intro k x hk
  exact nodeOk_subCodesTs ts (subCodesTs ts) (fun _ hy => hy) x (mem_of_getElem? _ k x hk)

/-- **PIEZA QUE FALTABA (1/2)**: el gemelo de `prf_isFC` para códigos de TÉRMINO. -/
theorem prf_isTC (t : Term) : Prf (isFC (termCodeM t)) := by
  show Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 (termCodeM t))))
  refine prf_ex_intro (objList (subCodesT t)) ?_
  rw [substF_isFCB (objList (subCodesT t)) (termCodeM t)
    (liftTerm_objList_subCodesT 0 t) (fun v s => substTerm_objList_subCodesT v s t)
    (liftTerm_termCodeM 0 t) (fun v s => substTerm_termCodeM v s t)]
  exact prf_isFCB_subCodesT t

/-- Y el de listas de términos (la casilla 2 de `atom`/`func`). -/
theorem prf_isTsC (ts : List Term) : Prf (isFC (termsCodeM ts)) := by
  show Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 (termsCodeM ts))))
  refine prf_ex_intro (objList (subCodesTs ts)) ?_
  rw [substF_isFCB (objList (subCodesTs ts)) (termsCodeM ts)
    (liftTerm_objList_subCodesTs 0 ts) (fun v s => substTerm_objList_subCodesTs v s ts)
    (liftTerm_termsCodeM 0 ts) (fun v s => substTerm_termsCodeM v s ts)]
  exact prf_isFCB_subCodesTs ts

/-! ### 16.2 · ⚠️ `isFC` **NO DISCRIMINA** fórmulas de términos

    Éste es el hallazgo. `nodeOk` es un predicado **FUSIONADO**: sus 12 disyuntos mezclan
    las formas de código de FÓRMULA (tags 2,3,4,5,6,7,8,9) con las de TÉRMINO (tag 0 =
    `varc`, tag 1 = `funcc`), más `nil` y el `cons` genérico. Luego `isFC X` **no dice**
    que `X` sea un código de fórmula. Se compila el contraejemplo. -/

/-- `nil` (= `termsCodeM []` = `zero`) satisface `isFC`. -/
theorem prf_isFC_nil : Prf (isFC nil) := prf_isTsC []

/-- Un código de VARIABLE satisface `isFC` (tag 0, que no es tag de fórmula). -/
theorem prf_isFC_varc (n : Nat) : Prf (isFC (termCodeM (Term.var n))) := prf_isTC (Term.var n)

/-- El testigo BASURA: la lista `[⌜x₀⌝ₜ, implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ]`. -/
def junkW : List Term :=
  [termCodeM (Term.var 0), implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))]

/-- «⌜x₀ ⇒ x₀⌝» donde `x₀` es un **TÉRMINO**: un error de categoría puro. -/
def junkImp : Term := implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))

theorem junk_lift (c : Nat) : ∀ x : Term, List.Mem x junkW → liftTerm c x = x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact liftTerm_termCodeM c (Term.var 0)
  · rcases List.mem_cons.mp h with rfl | h2
    · simp only [implc, cons, succ, zero, liftTerm, liftTerms, liftTerm_termCodeM, liftTerm_nil]
    · cases h2

theorem junk_subst (v : Nat) (s : Term) : ∀ x : Term, List.Mem x junkW → substTerm v s x = x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact substTerm_termCodeM v s (Term.var 0)
  · rcases List.mem_cons.mp h with rfl | h2
    · simp only [implc, cons, succ, zero, substTerm, substTerms, substTerm_termCodeM, substTerm_nil]
    · cases h2

theorem junk_lift_obj (c : Nat) : liftTerm c (objList junkW) = objList junkW :=
  liftTerm_objList c junkW (junk_lift c)

theorem junk_subst_obj (v : Nat) (s : Term) : substTerm v s (objList junkW) = objList junkW :=
  substTerm_objList v s junkW (junk_subst v s)

theorem junk_lift_imp (c : Nat) : liftTerm c junkImp = junkImp := by
  simp only [junkImp, implc, cons, succ, zero, liftTerm, liftTerms, liftTerm_termCodeM,
    liftTerm_nil]

theorem junk_subst_imp (v : Nat) (s : Term) : substTerm v s junkImp = junkImp := by
  simp only [junkImp, implc, cons, succ, zero, substTerm, substTerms, substTerm_termCodeM,
    substTerm_nil]

theorem prf_isFCB_junk : Prf (isFCB (objList junkW) junkImp) := by
  have hvar : Prf (In (termCodeM (Term.var 0)) (objList junkW)) :=
    prf_In_objList junkW _ (List.Mem.head _)
  refine prf_and_intro
    (prf_wfAll_objList junkW (fun s => junk_subst_obj 0 s) (junk_lift_obj 0) ?_)
    (prf_In_objList junkW _ (List.Mem.tail _ (List.Mem.head _)))
  intro k x hk
  match k with
  | 0 =>
      simp only [junkW, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact nodeOk_i8 _ _ (prf_cOk_varOk (numeralM 0))
  | 1 =>
      simp only [junkW, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hk
      subst hk
      exact nodeOk_i3 _ _
        (prf_cOk_binOk (objList junkW) 5 (termCodeM (Term.var 0)) (termCodeM (Term.var 0))
          hvar hvar)
  | (n + 2) => simp [junkW] at hk

/-- **CONTRAEJEMPLO COMPILADO**: la teoría certifica como «bien formado» un código cuyos
    dos subnodos son códigos de TÉRMINO, no de fórmula. `substfc` NO tiene ecuación para
    un `varc`, así que la inducción de `pcc_eval_substfc` se atasca justo aquí. -/
theorem prf_isFC_junk : Prf (isFC junkImp) := by
  show Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 junkImp)))
  refine prf_ex_intro (objList junkW) ?_
  rw [substF_isFCB (objList junkW) junkImp
    (junk_lift_obj 0) (fun v s => junk_subst_obj v s)
    (junk_lift_imp 0) (fun v s => junk_subst_imp v s)]
  exact prf_isFCB_junk

/-! ### 16.3 · TRANSPORTE — `isFC` a lo largo de una igualdad OBJETO

    D1 consume la dirección ⇐ de los bicondicionales con la línea CONCRETA, y ahí la
    obligación aparece como `isFC (nthc line 2̇)`, no como `isFC ⌜A⌝`. Hace falta mover
    `isFC` por `nthc line 2̇ =eq ⌜A⌝`, o sea Leibniz **bajo el binder ∃**. Es barato. -/

theorem prf_congr_isFC {X Y : Term} (h : Prf (X =eq Y)) (hX : Prf (isFC X)) : Prf (isFC Y) := by
  let A : Formula := Formula.ex (isFCB (.var 0) (.var 1))
  -- Todo es computacional: el hueco `#1` está en el 1er argumento del átomo `In`, y bajo el
  -- `∀` de `wfAll` sólo hay `#0`/`#1`, que la sustitución en nivel 2 deja fijos.
  have hS : ∀ s : Term, substFormula 0 s A = isFC s := fun _ => rfl
  exact prfH_nil_to_prf
    ((hS Y) ▸ PrfH_leibniz_subst (A := A) (prf_to_prfH h []) ((hS X) ▸ prf_to_prfH hX [])) rfl

/-! ### 16.4 · SIN BASURA — todo miembro de `subCodes` es un código REAL -/

def IsRealCode (x : Term) : Prop :=
  (∃ ψ : Formula, x = formCodeM ψ) ∨ (∃ t : Term, x = termCodeM t) ∨
  (∃ ts : List Term, x = termsCodeM ts)

mutual
theorem real_mem_subCodesT : ∀ (t x : Term), List.Mem x (subCodesT t) → IsRealCode x
  | .var n, x, h => by
      simp only [subCodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr (Or.inl ⟨Term.var n, rfl⟩)
      · cases h'
  | .func s ts, x, h => by
      simp only [subCodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr (Or.inl ⟨Term.func s ts, rfl⟩)
      · exact real_mem_subCodesTs ts x h'

theorem real_mem_subCodesTs : ∀ (ts : List Term) (x : Term), List.Mem x (subCodesTs ts) →
    IsRealCode x
  | [],      x, h => by
      simp only [subCodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr (Or.inr ⟨[], rfl⟩)
      · cases h'
  | t :: ts, x, h => by
      simp only [subCodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr (Or.inr ⟨t :: ts, rfl⟩)
      · rcases List.mem_append.mp h' with hA | hB
        · exact real_mem_subCodesT t x hA
        · exact real_mem_subCodesTs ts x hB
end

theorem real_mem_subCodes : ∀ (φ : Formula) (x : Term), List.Mem x (subCodes φ) → IsRealCode x
  | .bottom, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.bottom, rfl⟩
      · cases h'
  | .atom p ts, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.atom p ts, rfl⟩
      · exact real_mem_subCodesTs ts x h'
  | .eq t u, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.eq t u, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact real_mem_subCodesT t x hA
        · exact real_mem_subCodesT u x hB
  | .impl a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.impl a b, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact real_mem_subCodes a x hA
        · exact real_mem_subCodes b x hB
  | Formula.forall a, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.forall a, rfl⟩
      · exact real_mem_subCodes a x h'
  | .and a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.and a b, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact real_mem_subCodes a x hA
        · exact real_mem_subCodes b x hB
  | .or a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.or a b, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact real_mem_subCodes a x hA
        · exact real_mem_subCodes b x hB
  | .ex a, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl ⟨Formula.ex a, rfl⟩
      · exact real_mem_subCodes a x h'

/-! ### 16.5 · LAS FORMAS SOSPECHOSAS — el testigo, DESPLEGADO por `rfl` -/

-- átomo 0‑ario: el testigo es [⌜P()⌝, nil]; `nil` es OBLIGATORIO
example : subCodes (Formula.atom "P" []) = [formCodeM (Formula.atom "P" []), nil] := rfl

-- función 0‑aria: idem
example : subCodesT (Term.func "c" []) = [termCodeM (Term.func "c" []), nil] := rfl

-- ⊥ dentro de cuantificadores anidados: un nodo por nivel, sin `nil`
example :
    subCodes (Formula.forall (Formula.forall (Formula.ex Formula.bottom)))
      = [ formCodeM (Formula.forall (Formula.forall (Formula.ex Formula.bottom)))
        , formCodeM (Formula.forall (Formula.ex Formula.bottom))
        , formCodeM (Formula.ex Formula.bottom)
        , formCodeM Formula.bottom ] := rfl

-- término profundo f(f(f(x))): 3 nodos por nivel de anidamiento + la hoja
example : (subCodesT (Term.func "f" [.func "f" [.func "f" [.var 0]]])).length = 10 := rfl

-- ecuación entre variables: NO aparece `nil` en el testigo (y no hace falta)
example : subCodes (Formula.eq (.var 0) (.var 1))
    = [formCodeM (Formula.eq (.var 0) (.var 1)), termCodeM (.var 0), termCodeM (.var 1)] := rfl

/-! ### 16.6 · DUPLICADOS y TAMAÑO -/

#eval (subCodes (Formula.atom "P" [])).length                                   -- 2
#eval (subCodes (Formula.impl Formula.bottom Formula.bottom)).length             -- 3 (⌜⊥⌝ x2)
#eval (subCodes (Formula.atom "P" [.var 0, .var 1, .var 2])).length              -- nil 1 vez
#eval (subCodes ax_lineWF_q1).length
#eval (subCodes ax_lineWF_listInd).length
#eval (subCodes ax_lineWF_leibniz).length
#eval (subCodes (Formula.impl ax_lineWF_q1 ax_lineWF_q1)).length

-- tamaño del TÉRMINO testigo (nodos de sintaxis), que es lo que D1 tendría que embarcar
mutual
def tSize : Term → Nat
  | .var _     => 1
  | .func _ ts => 1 + tsSize ts
def tsSize : List Term → Nat
  | []      => 1
  | t :: ts => tSize t + tsSize ts
end

#eval tSize (objList (subCodes ax_lineWF_q1))
#eval tSize (objList (subCodes ax_lineWF_listInd))
-- y el numeral UNARIO de la cota que `wfAll` obliga a escribir:
#eval tSize (numeralM (subCodes ax_lineWF_listInd).length)
-- duplicados: cuántas veces se repite `nil` en el testigo
#eval ((subCodes ax_lineWF_listInd).filter (fun x => decide (x = nil))).length
#eval ((subCodes ax_lineWF_listInd).eraseDups).length

/-! ### 16.7 · ¿CUESTA CARO en Lean? NO — la obligación es O(1) a nivel META

    `prf_isFC` es un teorema UNIVERSAL: aplicarlo a una fórmula gigante es una simple
    aplicación, y Lean nunca desarrolla `subCodes`. El coste medido arriba es del TÉRMINO
    OBJETO (lo que la teoría tendría que escribir), no del elaborador. Sobrevive, pues,
    la instanciación de D1 sobre los axiomas más grandes de la teoría. -/

theorem costo_q1 : Prf (isFC (formCodeM ax_lineWF_q1)) := prf_isFC_form ax_lineWF_q1
theorem costo_listInd : Prf (isFC (formCodeM ax_lineWF_listInd)) := prf_isFC_form ax_lineWF_listInd
theorem costo_t : Prf (isFC (termCodeM (Term.func "f" [.func "g" [.var 0]]))) :=
  prf_isTC (Term.func "f" [.func "g" [.var 0]])

/-! ### 16.8 · LA OBLIGACIÓN QUE NADIE REGISTRÓ — el puente ÍNDICE ⇄ PERTENENCIA

    `isFCB w c = wfAll w ∧ In c w` indexa el testigo de **DOS maneras incompatibles**:

    * `wfAll w` = `∀i < lenc w. nodeOk w (nthc w i)` — por ÍNDICE (`nthc`, `lenc`);
    * `In c w`  — por RECURSIÓN nil/cons (`ax_L1_in_nil`, `ax_L2_in_cons`); `In` es un
      ÁTOMO primitivo, no el despliegue ∃‑acotado.

    Para pasar de `isFCB w c` a `nodeOk w c` (el PRIMER paso de cualquier inducción sobre
    el testigo, y otra vez en CADA paso recursivo, porque los disyuntos entregan
    `In (nthc X 1̇) w` y no un índice) hace falta el puente de abajo. **No existe** en el
    árbol (0 ocurrencias). Se enuncia aquí como `Prop` de Lean — NO como `axiom`. -/

def ObligacionPuenteInNth : Prop :=
  ∀ w x : Term, Prf (In x w) →
    Prf (Formula.ex (land (lt (.var 0) (liftTerm 0 (lenc w)))
      (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))))

/-- Y su consecuencia inmediata, que es lo que la inducción necesita de verdad. -/
def ObligacionNodeOkOfIsFCB : Prop :=
  ∀ w c : Term, Prf (isFCB w c) → Prf (nodeOk w c)

#print axioms costo_listInd
#print axioms prf_isTC
#print axioms prf_isTsC
#print axioms prf_isFC_nil
#print axioms prf_isFC_junk
#print axioms prf_congr_isFC
#print axioms real_mem_subCodes

end SubCMutua

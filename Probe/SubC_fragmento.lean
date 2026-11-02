/-
# HITO (i) — ESTRATEGIA 3 (FRAGMENTO PRIMERO)

Cierra el hito (i) para el fragmento SIN términos: `⊥`, `⇒`, `∀`, `∧`, `∨`, `∃`
(o sea, sin `atom` ni `eq`, y por tanto sin `subCodesT`/`subCodesTs`).

    lake env lean Probe\SubC_fragmento.lean

§§1‑8 son COPIA LITERAL de `Probe\SubCodesPrelude.lean` (el fichero debe ser autocontenido:
`Probe/` no está en el lean path). Lo NUEVO empieza en §9.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace SubCFragmento

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

/-! ## 8 · `PrfH_congr_nodeOk` y `prf_wfAll_objList` -/

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

theorem prf_nodeOk_bot (w : Term) : Prf (nodeOk w (formCodeM Formula.bottom)) := by
  have htag : Prf (Formula.eq (carc (formCodeM Formula.bottom)) (numeralM 2)) :=
    prf_carc_cons (numeralM 2) nil
  have hlen : Prf (Formula.eq (lenc (formCodeM Formula.bottom)) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons (numeralM 2) nil) (prf_eq_congr_succ prf_lenc_nil)
  have hnul : Prf (cOk (formCodeM Formula.bottom) (nulOk (formCodeM Formula.bottom) 2)) :=
    prf_and_intro (prf_consOk_cons (numeralM 2) nil) (prf_and_intro htag hlen)
  unfold nodeOk lorAll
  exact prf_mp (Prf.incl (Prfᵢ.j1 _ _)) hnul

/-! ═══════════════════════════════════════════════════════════════════════════════════════
    ## 9 · NUEVO — combinadores para inyectar en el disyunto que toca
    ═══════════════════════════════════════════════════════════════════════════════════════ -/

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j1 A B)) h

theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j2 A B)) h

/-- Congruencia del átomo `In` en su PRIMER argumento. -/
theorem PrfH_congr_In_left {Γ : List Formula} {x y w : Term} (h : PrfH Γ (x =eq y))
    (hin : PrfH Γ (In x w)) : PrfH Γ (In y w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ PrfH_leibniz_subst (A := f) h ((hS x) ▸ hin)

theorem prf_congr_In_left {x y w : Term} (h : Prf (x =eq y)) (hin : Prf (In x w)) :
    Prf (In y w) :=
  prfH_nil_to_prf (PrfH_congr_In_left (prf_to_prfH h []) (prf_to_prfH hin [])) rfl

/-! ### Longitudes e índices de listas objeto EXPLÍCITAS -/

theorem prf_lenc1 (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc2 (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc1 b))

theorem prf_lenc3 (a b c : Term) : Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil))) (prf_eq_congr_succ (prf_lenc2 b c))

theorem prf_nthc1_2 (a b : Term) :
    Prf (nthc (cons a (cons b nil)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b nil) zero) (prf_nthc_zero b nil)

theorem prf_nthc1_3 (a b c : Term) :
    Prf (nthc (cons a (cons b (cons c nil))) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c nil)) zero) (prf_nthc_zero b (cons c nil))

theorem prf_nthc2_3 (a b c : Term) :
    Prf (nthc (cons a (cons b (cons c nil))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c nil)) (succ zero))
    (prf_eq_trans (prf_nthc_succ b (cons c nil) zero) (prf_nthc_zero c nil))

/-! ### Los dos moldes de disyunto que usa el fragmento -/

/-- Nodo BINARIO `X = cons k̄ (cons A (cons B nil))`, disyunto `cOk X (binOk w X k)`. -/
theorem prf_cOk_bin (w A B : Term) (k : Nat) (hA : Prf (In A w)) (hB : Prf (In B w)) :
    Prf (cOk (cons (numeralM k) (cons A (cons B nil)))
             (binOk w (cons (numeralM k) (cons A (cons B nil))) k)) := by
  unfold cOk binOk
  refine prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro (prf_and_intro ?_ ?_) (prf_and_intro ?_ ?_))
  · exact prf_carc_cons (numeralM k) (cons A (cons B nil))
  · exact prf_lenc3 (numeralM k) A B
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc1_3 (numeralM k) A B)) hA
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc2_3 (numeralM k) A B)) hB

/-- Nodo UNARIO `X = cons k̄ (cons A nil)`, disyunto `cOk X (unOk w X k)`. -/
theorem prf_cOk_un (w A : Term) (k : Nat) (hA : Prf (In A w)) :
    Prf (cOk (cons (numeralM k) (cons A nil))
             (unOk w (cons (numeralM k) (cons A nil)) k)) := by
  unfold cOk unOk
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro (prf_and_intro ?_ ?_) ?_)
  · exact prf_carc_cons (numeralM k) (cons A nil)
  · exact prf_lenc2 (numeralM k) A
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc1_2 (numeralM k) A)) hA

/-! ## 10 · `nodeOk` para cada constructor del FRAGMENTO -/

theorem prf_nodeOk_impl (w : Term) (a b : Formula)
    (ha : Prf (In (formCodeM a) w)) (hb : Prf (In (formCodeM b) w)) :
    Prf (nodeOk w (formCodeM (Formula.impl a b))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orL (prf_cOk_bin w (formCodeM a) (formCodeM b) 5 ha hb))))

theorem prf_nodeOk_forall (w : Term) (a : Formula) (ha : Prf (In (formCodeM a) w)) :
    Prf (nodeOk w (formCodeM (Formula.forall a))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orL (prf_cOk_un w (formCodeM a) 6 ha)))))

theorem prf_nodeOk_and (w : Term) (a b : Formula)
    (ha : Prf (In (formCodeM a) w)) (hb : Prf (In (formCodeM b) w)) :
    Prf (nodeOk w (formCodeM (Formula.and a b))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orL (prf_cOk_bin w (formCodeM a) (formCodeM b) 7 ha hb))))))

theorem prf_nodeOk_or (w : Term) (a b : Formula)
    (ha : Prf (In (formCodeM a) w)) (hb : Prf (In (formCodeM b) w)) :
    Prf (nodeOk w (formCodeM (Formula.or a b))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orL (prf_cOk_bin w (formCodeM a) (formCodeM b) 8 ha hb)))))))

theorem prf_nodeOk_ex (w : Term) (a : Formula) (ha : Prf (In (formCodeM a) w)) :
    Prf (nodeOk w (formCodeM (Formula.ex a))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orL (prf_cOk_un w (formCodeM a) 9 ha))))))))

/-! ## 11 · EL FRAGMENTO y la INDUCCIÓN PRINCIPAL

    Se generaliza sobre un SUPERCONJUNTO `W` y se prueba cada nodo contra la lista COMPLETA.
    Así NUNCA hay que transportar `nodeOk w X` a `nodeOk (cons y w) X`. -/

/-- El fragmento SIN términos: `⊥`, `⇒`, `∀`, `∧`, `∨`, `∃`. -/
inductive FragOk : Formula → Prop
  | bot  : FragOk Formula.bottom
  | impl (a b : Formula) : FragOk a → FragOk b → FragOk (Formula.impl a b)
  | all  (a : Formula)   : FragOk a → FragOk (Formula.forall a)
  | conj (a b : Formula) : FragOk a → FragOk b → FragOk (Formula.and a b)
  | disj (a b : Formula) : FragOk a → FragOk b → FragOk (Formula.or a b)
  | ex   (a : Formula)   : FragOk a → FragOk (Formula.ex a)

theorem nodeOk_of_mem_subCodes_frag {φ : Formula} (hφ : FragOk φ) : ∀ (W : List Term),
    (∀ y : Term, List.Mem y (subCodes φ) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodes φ) → Prf (nodeOk (objList W) x) := by
  induction hφ with
  | bot =>
      intro W _ x hx
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_bot _
      · cases h'
  | impl a b _ _ iha ihb =>
      intro W hsub x hx
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodes b) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_impl (objList W) a b
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
          (prf_In_objList W _ (hB _ (mem_self_subCodes b)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact iha W hA x hxa
        · exact ihb W hB x hxb
  | all a _ iha =>
      intro W hsub x hx
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ hy)
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_forall (objList W) a
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
      · exact iha W hA x h'
  | conj a b _ _ iha ihb =>
      intro W hsub x hx
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodes b) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_and (objList W) a b
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
          (prf_In_objList W _ (hB _ (mem_self_subCodes b)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact iha W hA x hxa
        · exact ihb W hB x hxb
  | disj a b _ _ iha ihb =>
      intro W hsub x hx
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodes b) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_or (objList W) a b
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
          (prf_In_objList W _ (hB _ (mem_self_subCodes b)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact iha W hA x hxa
        · exact ihb W hB x hxb
  | ex a _ iha =>
      intro W hsub x hx
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ hy)
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_ex (objList W) a
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
      · exact iha W hA x h'

/-! ## 12 · EL HITO (i) PARA EL FRAGMENTO -/

theorem mem_of_getElem? : ∀ {L : List Term} {k : Nat} {x : Term}, L[k]? = some x → List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? h)

/-- **EL TESTIGO ES VÁLIDO** (fragmento): `⊢ isFCB (objList (subCodes φ)) ⌜φ⌝`. -/
theorem prf_isFCB_subCodes_frag {φ : Formula} (hφ : FragOk φ) :
    Prf (isFCB (objList (subCodes φ)) (formCodeM φ)) := by
  refine prf_isFCB_of_wfAll φ (prf_wfAll_subCodes φ ?_)
  intro k x hk
  exact nodeOk_of_mem_subCodes_frag hφ (subCodes φ) (fun _ hy => hy) x (mem_of_getElem? hk)

/-! ### El Σ₁: `⊢ ∃w. isFCB w ⌜φ⌝` -/

/-- La sustitución del testigo en `wfAll (#0)`. Toda la aritmética De Bruijn es `rfl`;
    lo único que hay que aportar es que el testigo es CERRADO. -/
theorem subst_wfAll (W : Term) (hlift : ∀ c : Nat, liftTerm c W = W) :
    substFormula 0 W (wfAll (.var 0)) = wfAll W := by
  have hl : liftTerm 0 (lenc W) = lenc W := by simp only [lenc, liftTerm, liftTerms, hlift]
  show Formula.forall (substFormula 1 (liftTerm 0 W)
      (Formula.impl (lt (.var 0) (lenc (.var 1))) (nodeOk (.var 1) (nthc (.var 1) (.var 0)))))
    = Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc W)))
        (nodeOk (liftTerm 0 W) (nthc (liftTerm 0 W) (.var 0))))
  rw [hlift 0, hl]
  rfl

theorem subst_isFCB_var0 (W c : Term) (hlift : ∀ cc : Nat, liftTerm cc W = W) :
    substFormula 0 W (isFCB (.var 0) (liftTerm 0 c)) = isFCB W c := by
  show land (substFormula 0 W (wfAll (.var 0))) (In (substTerm 0 W (liftTerm 0 c)) W)
    = land (wfAll W) (In c W)
  rw [subst_wfAll W hlift, FOL.substTerm_liftTerm]

/-- **EL Σ₁** (fragmento): `⊢ ∃w. isFCB w ⌜φ⌝`. -/
theorem prf_isFC_frag {φ : Formula} (hφ : FragOk φ) :
    Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 (formCodeM φ)))) :=
  prf_ex_intro (A := isFCB (.var 0) (liftTerm 0 (formCodeM φ))) (objList (subCodes φ))
    ((subst_isFCB_var0 (objList (subCodes φ)) (formCodeM φ)
        (fun c => liftTerm_objList_subCodes c φ)) ▸ prf_isFCB_subCodes_frag hφ)

/-! ═══════════════════════════════════════════════════════════════════════════════════════
    ## 13 · LA EXTENSIÓN A TÉRMINOS — los 6 disyuntos que faltaban y la MUTUA
    ═══════════════════════════════════════════════════════════════════════════════════════

    El chasis de §9‑§12 no cambia. Sólo hacen falta tres moldes de disyunto más
    (`strBin`, `var`, el disyunto 12 del `cons`) y la inducción MUTUA sobre
    `subCodesT` / `subCodesTs`. -/

/-- Nodo `strBin` `X = cons k̄ (cons S (cons A nil))`: la casilla 1 (`S`) es carga OPACA
    (una cadena), sólo la casilla 2 lleva sub‑código. -/
theorem prf_cOk_strBin (w S A : Term) (k : Nat) (hA : Prf (In A w)) :
    Prf (cOk (cons (numeralM k) (cons S (cons A nil)))
             (strBinOk w (cons (numeralM k) (cons S (cons A nil))) k)) := by
  unfold cOk strBinOk
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro (prf_and_intro ?_ ?_) ?_)
  · exact prf_carc_cons (numeralM k) (cons S (cons A nil))
  · exact prf_lenc3 (numeralM k) S A
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc2_3 (numeralM k) S A)) hA

/-- Nodo `var` `X = cons 0̄ (cons N nil)`: la casilla 1 es un NUMERAL, no un sub‑código. -/
theorem prf_cOk_var (N : Term) :
    Prf (cOk (cons (numeralM 0) (cons N nil)) (varOk (cons (numeralM 0) (cons N nil)))) := by
  unfold cOk varOk
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro ?_ ?_)
  · exact prf_carc_cons (numeralM 0) (cons N nil)
  · exact prf_lenc2 (numeralM 0) N

/-- Disyunto 12 (`termsCodeM (t :: ts)`): `X = cons A B` con `A` y `B` en `w`. -/
theorem prf_cOk_consNode (w A B : Term) (hA : Prf (In A w)) (hB : Prf (In B w)) :
    Prf (cOk (cons A B) (land (In (carc (cons A B)) w) (In (cdrc (cons A B)) w))) := by
  unfold cOk
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro ?_ ?_)
  · exact prf_congr_In_left (prf_eq_symm (prf_carc_cons A B)) hA
  · exact prf_congr_In_left (prf_eq_symm (prf_cdrc_cons A B)) hB

/-! ### Los 6 `nodeOk` que faltaban -/

theorem prf_nodeOk_atom (w : Term) (p : String) (ts : List Term)
    (h : Prf (In (termsCodeM ts) w)) : Prf (nodeOk w (formCodeM (Formula.atom p ts))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orL (prf_cOk_strBin w (strCodeM p) (termsCodeM ts) 3 h))

theorem prf_nodeOk_eq (w t u : Term)
    (ht : Prf (In (termCodeM t) w)) (hu : Prf (In (termCodeM u) w)) :
    Prf (nodeOk w (formCodeM (Formula.eq t u))) := by
  simp only [nodeOk, lorAll, formCodeM]
  exact prf_orR (prf_orR (prf_orL (prf_cOk_bin w (termCodeM t) (termCodeM u) 4 ht hu)))

theorem prf_nodeOk_var (w : Term) (n : Nat) : Prf (nodeOk w (termCodeM (Term.var n))) := by
  simp only [nodeOk, lorAll, termCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orL (prf_cOk_var (numeralM n))))))))))

theorem prf_nodeOk_func (w : Term) (s : String) (ts : List Term)
    (h : Prf (In (termsCodeM ts) w)) : Prf (nodeOk w (termCodeM (Term.func s ts))) := by
  simp only [nodeOk, lorAll, termCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orL (prf_cOk_strBin w (strCodeM s) (termsCodeM ts) 1 h))))))))))

/-- ⚠️ El disyunto 10 va DESNUDO (sin `cOk`): `nil` NO es un `cons`. -/
theorem prf_nodeOk_nil (w : Term) : Prf (nodeOk w (termsCodeM [])) := by
  simp only [nodeOk, lorAll, termsCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orR (prf_orL (prf_refl nil)))))))))))

theorem prf_nodeOk_termsCons (w t : Term) (ts : List Term)
    (ht : Prf (In (termCodeM t) w)) (hts : Prf (In (termsCodeM ts) w)) :
    Prf (nodeOk w (termsCodeM (t :: ts))) := by
  simp only [nodeOk, lorAll, termsCodeM]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR
    (prf_orR (prf_orR (prf_cOk_consNode w (termCodeM t) (termsCodeM ts) ht hts)))))))))))

/-! ### La INDUCCIÓN MUTUA sobre términos y listas de términos -/

mutual
theorem nodeOk_of_mem_subCodesT : ∀ (t : Term) (W : List Term),
    (∀ y : Term, List.Mem y (subCodesT t) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodesT t) → Prf (nodeOk (objList W) x)
  | .var n, W, _, x, hx => by
      simp only [subCodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_var (objList W) n
      · cases h'
  | .func s ts, W, hsub, x, hx => by
      simp only [subCodesT] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodesTs ts) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ hy)
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_func (objList W) s ts
          (prf_In_objList W _ (hA _ (mem_self_subCodesTs ts)))
      · exact nodeOk_of_mem_subCodesTs ts W hA x h'
theorem nodeOk_of_mem_subCodesTs : ∀ (ts : List Term) (W : List Term),
    (∀ y : Term, List.Mem y (subCodesTs ts) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodesTs ts) → Prf (nodeOk (objList W) x)
  | [], W, _, x, hx => by
      simp only [subCodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_nil (objList W)
      · cases h'
  | t :: ts, W, hsub, x, hx => by
      simp only [subCodesTs] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodesT t) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodesTs ts) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_termsCons (objList W) t ts
          (prf_In_objList W _ (hA _ (mem_self_subCodesT t)))
          (prf_In_objList W _ (hB _ (mem_self_subCodesTs ts)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact nodeOk_of_mem_subCodesT t W hA x hxa
        · exact nodeOk_of_mem_subCodesTs ts W hB x hxb
end

/-! ### La inducción sobre fórmulas, ya SIN restricción de fragmento -/

theorem nodeOk_of_mem_subCodes : ∀ (φ : Formula) (W : List Term),
    (∀ y : Term, List.Mem y (subCodes φ) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodes φ) → Prf (nodeOk (objList W) x)
  | .bottom, W, _, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_bot _
      · cases h'
  | .atom p ts, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodesTs ts) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ hy)
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_atom (objList W) p ts
          (prf_In_objList W _ (hA _ (mem_self_subCodesTs ts)))
      · exact nodeOk_of_mem_subCodesTs ts W hA x h'
  | .eq t u, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodesT t) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodesT u) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_eq (objList W) t u
          (prf_In_objList W _ (hA _ (mem_self_subCodesT t)))
          (prf_In_objList W _ (hB _ (mem_self_subCodesT u)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact nodeOk_of_mem_subCodesT t W hA x hxa
        · exact nodeOk_of_mem_subCodesT u W hB x hxb
  | .impl a b, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodes b) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_impl (objList W) a b
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
          (prf_In_objList W _ (hB _ (mem_self_subCodes b)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact nodeOk_of_mem_subCodes a W hA x hxa
        · exact nodeOk_of_mem_subCodes b W hB x hxb
  | Formula.forall a, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ hy)
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_forall (objList W) a
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
      · exact nodeOk_of_mem_subCodes a W hA x h'
  | .and a b, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodes b) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_and (objList W) a b
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
          (prf_In_objList W _ (hB _ (mem_self_subCodes b)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact nodeOk_of_mem_subCodes a W hA x hxa
        · exact nodeOk_of_mem_subCodes b W hB x hxb
  | .or a b, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))
      have hB : ∀ y : Term, List.Mem y (subCodes b) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_or (objList W) a b
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
          (prf_In_objList W _ (hB _ (mem_self_subCodes b)))
      · rcases List.mem_append.mp h' with hxa | hxb
        · exact nodeOk_of_mem_subCodes a W hA x hxa
        · exact nodeOk_of_mem_subCodes b W hB x hxb
  | .ex a, W, hsub, x, hx => by
      simp only [subCodes] at hsub hx
      have hA : ∀ y : Term, List.Mem y (subCodes a) → List.Mem y W := fun y hy =>
        hsub y (List.Mem.tail _ hy)
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_ex (objList W) a
          (prf_In_objList W _ (hA _ (mem_self_subCodes a)))
      · exact nodeOk_of_mem_subCodes a W hA x h'

/-! ## 14 · EL HITO (i) COMPLETO — sin restricción de fragmento -/

/-- **EL TESTIGO DE PARSEO ES VÁLIDO**, para TODA fórmula. -/
theorem prf_isFCB_subCodes (φ : Formula) :
    Prf (isFCB (objList (subCodes φ)) (formCodeM φ)) := by
  refine prf_isFCB_of_wfAll φ (prf_wfAll_subCodes φ ?_)
  intro k x hk
  exact nodeOk_of_mem_subCodes φ (subCodes φ) (fun _ hy => hy) x (mem_of_getElem? hk)

/-- **EL Σ₁**: `⊢ ∃w. isFCB w ⌜φ⌝`, para TODA fórmula. -/
theorem prf_isFC (φ : Formula) :
    Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 (formCodeM φ)))) :=
  prf_ex_intro (A := isFCB (.var 0) (liftTerm 0 (formCodeM φ))) (objList (subCodes φ))
    ((subst_isFCB_var0 (objList (subCodes φ)) (formCodeM φ)
        (fun c => liftTerm_objList_subCodes c φ)) ▸ prf_isFCB_subCodes φ)

end SubCFragmento

#check @SubCFragmento.prf_isFCB_subCodes
#check @SubCFragmento.prf_isFC

-- ⚠️ NO‑VACUIDAD: el testigo se CONSTRUYE, y contiene `nil` (`subCodesTs [] = [nil]`),
-- que sólo es nodo válido porque el disyunto 10 va DESNUDO.
example : SubCFragmento.subCodesTs [] = [nil] := rfl
example (t : Term) (ts : List Term) :
    SubCFragmento.subCodesTs (t :: ts)
      = termsCodeM (t :: ts) :: (SubCFragmento.subCodesT t ++ SubCFragmento.subCodesTs ts) := rfl
example : Prf (SubCFragmento.isFCB
    (objList (SubCFragmento.subCodes (Formula.eq zero (succ zero))))
    (formCodeM (Formula.eq zero (succ zero)))) := SubCFragmento.prf_isFCB_subCodes _

#print axioms SubCFragmento.prf_isFCB_subCodes
#print axioms SubCFragmento.prf_isFC
#print axioms SubCFragmento.nodeOk_of_mem_subCodes
#print axioms SubCFragmento.nodeOk_of_mem_subCodesT
#print axioms SubCFragmento.nodeOk_of_mem_subCodesTs
#print axioms SubCFragmento.prf_isFCB_subCodes_frag
#print axioms SubCFragmento.prf_isFC_frag

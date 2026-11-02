/-
# Hito (i) por la ESTRATEGIA 2 — LEMAS POR FORMA PRIMERO

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más).

    lake env lean Probe/SubC_porforma.lean

Estructura:
 §A  el PRELUDE (copia literal de `Probe/SubCodesPrelude.lean`, que ya compilaba):
     definiciones OBJETO, `prf_cdrc_cons`, `prf_consOk_cons`, `subCodes`, clausura,
     puente `objList` ⇄ meta, `prf_bdAll_numeral`, `prf_wfAll_objList`.
 §B  ARITMÉTICA DE ACCESO sobre `cons` literales (`lenc` 1/2/3, `nthc` 1/2).
 §C  los SIETE LEMAS POR FORMA — todo ABSTRACTO (`w` cualquiera, `k` cualquiera).
 §D  los DOCE inyectores concretos `prf_nodeOk_*` (tag → disyunto).
 §E  la INDUCCIÓN MUTUA `nodeOk_mem_subCodes{,T,Ts}` (generalizando sobre un
     SUPERCONJUNTO `W`, sin monotonía).
 §F  `prf_isFCB_subCodes` y `prf_isFC`.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace SubCPorForma

/-! # §A · PRELUDE (copia literal de `Probe/SubCodesPrelude.lean`) -/

/-! ## A.1 · EL OBJETO -/

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

/-! ## A.2 · `prf_cdrc_cons` -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-! ## A.3 · `consOk` sobre un `cons` LITERAL -/

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

/-! ## A.4 · EL TESTIGO `subCodes` -/

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

/-! ## A.5 · CLAUSURA -/

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

/-! ## A.6 · El puente `objList` ⇄ meta -/

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

/-! ## A.7 · `prf_bdAll_numeral` -/

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

/-! ## A.8 · `PrfH_congr_nodeOk` y `prf_wfAll_objList` -/

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

/-! # §B · ARITMÉTICA DE ACCESO sobre `cons` LITERALES

    `lenc` de cadenas de 1, 2 y 3 elementos; `nthc` en las casillas 1 y 2. Todo
    ABSTRACTO en los elementos y en la cola. -/

theorem prf_lenc_one (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc_two (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc_one b))

theorem prf_lenc_three (a b c : Term) :
    Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil)))
    (prf_eq_congr_succ (prf_lenc_two b c))

theorem prf_nthc_one (a b tl : Term) :
    Prf (nthc (cons a (cons b tl)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b tl) (numeralM 0)) (prf_nthc_zero b tl)

theorem prf_nthc_two (a b c tl : Term) :
    Prf (nthc (cons a (cons b (cons c tl))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c tl)) (numeralM 1)) (prf_nthc_one b c tl)

/-- Congruencia de `In` en el PRIMER argumento (la de producción, `prf_eq_subst_in`,
    es en el segundo). -/
theorem prf_In_congr_left {x y w : Term} (h : Prf (x =eq y)) (hin : Prf (In x w)) :
    Prf (In y w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ prf_leibniz_subst (A := f) h ((hS x) ▸ hin)

/-! # §C · LOS SIETE LEMAS POR FORMA

    Cada uno construye el DISYUNTO que le toca a su forma de nodo, con `w` y el tag `k`
    completamente ABSTRACTOS. Son los reutilizables: la inducción de §E sólo elige lema
    y descarga pertenencias. -/

/-- **(1) NUL** — nodo `cons k̄ nil` (`lenc = 1`, sin sub‑códigos). -/
theorem prf_nulOk_cons (k : Nat) :
    Prf (cOk (cons (numeralM k) nil) (nulOk (cons (numeralM k) nil) k)) :=
  prf_and_intro (prf_consOk_cons (numeralM k) nil)
    (prf_and_intro (prf_carc_cons (numeralM k) nil) (prf_lenc_one (numeralM k)))

/-- **(2) UN** — nodo `cons k̄ (cons a nil)` (`lenc = 2`, sub‑código en la casilla 1). -/
theorem prf_unOk_cons (w a : Term) (k : Nat) (ha : Prf (In a w)) :
    Prf (cOk (cons (numeralM k) (cons a nil))
         (unOk w (cons (numeralM k) (cons a nil)) k)) :=
  prf_and_intro (prf_consOk_cons (numeralM k) (cons a nil))
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons a nil))
        (prf_lenc_two (numeralM k) a))
      (prf_In_congr_left (prf_eq_symm (prf_nthc_one (numeralM k) a nil)) ha))

/-- **(3) BIN** — nodo `cons k̄ (cons a (cons b nil))` (`lenc = 3`, dos sub‑códigos). -/
theorem prf_binOk_cons (w a b : Term) (k : Nat) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (cOk (cons (numeralM k) (cons a (cons b nil)))
         (binOk w (cons (numeralM k) (cons a (cons b nil))) k)) :=
  prf_and_intro (prf_consOk_cons (numeralM k) (cons a (cons b nil)))
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons a (cons b nil)))
        (prf_lenc_three (numeralM k) a b))
      (prf_and_intro
        (prf_In_congr_left (prf_eq_symm (prf_nthc_one (numeralM k) a (cons b nil))) ha)
        (prf_In_congr_left (prf_eq_symm (prf_nthc_two (numeralM k) a b nil)) hb)))

/-- **(4) STRBIN** — nodo `cons k̄ (cons s (cons b nil))`: la casilla 1 es carga OPACA
    (una cadena) y sólo la 2 lleva sub‑código. -/
theorem prf_strBinOk_cons (w s b : Term) (k : Nat) (hb : Prf (In b w)) :
    Prf (cOk (cons (numeralM k) (cons s (cons b nil)))
         (strBinOk w (cons (numeralM k) (cons s (cons b nil))) k)) :=
  prf_and_intro (prf_consOk_cons (numeralM k) (cons s (cons b nil)))
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons s (cons b nil)))
        (prf_lenc_three (numeralM k) s b))
      (prf_In_congr_left (prf_eq_symm (prf_nthc_two (numeralM k) s b nil)) hb))

/-- **(5) VAR** — nodo `cons 0̄ (cons m nil)`: la casilla 1 es un NUMERAL, no un sub‑código. -/
theorem prf_varOk_cons (m : Term) :
    Prf (cOk (cons (numeralM 0) (cons m nil)) (varOk (cons (numeralM 0) (cons m nil)))) :=
  prf_and_intro (prf_consOk_cons (numeralM 0) (cons m nil))
    (prf_and_intro (prf_carc_cons (numeralM 0) (cons m nil))
      (prf_lenc_two (numeralM 0) m))

/-- **(6) NIL** — el disyunto DESNUDO (`termsCodeM [] = nil`). ⚠️ Sin `cOk`: ponerle
    `consOk` encima dejaría el predicado sin testigos (`nil_ne_cons`). -/
theorem prf_nilOk : Prf (Formula.eq nil nil) := prf_refl nil

/-- **(7) CONS** — nodo `cons a b` de la CADENA de argumentos (`termsCodeM (t :: ts)`):
    cabeza y cola son ambas sub‑códigos. -/
theorem prf_consCase_cons (w a b : Term) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (cOk (cons a b) (land (In (carc (cons a b)) w) (In (cdrc (cons a b)) w))) :=
  prf_and_intro (prf_consOk_cons a b)
    (prf_and_intro
      (prf_In_congr_left (prf_eq_symm (prf_carc_cons a b)) ha)
      (prf_In_congr_left (prf_eq_symm (prf_cdrc_cons a b)) hb))

/-! # §D · LOS DOCE INYECTORES `prf_nodeOk_*`

    `nodeOk w X = lor D₀ (lor D₁ (… (lor D₁₀ D₁₁)))`. El disyunto `Dⱼ` se alcanza con
    `j` veces `prf_or_intro_right` y (salvo el último) un `prf_or_intro_left`. -/

theorem prf_nodeOk_nul2 (w : Term) : Prf (nodeOk w (cons (numeralM 2) nil)) := by
  simp only [nodeOk, lorAll]
  exact prf_or_intro_left (prf_nulOk_cons 2)

theorem prf_nodeOk_strBin3 (w s b : Term) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons (numeralM 3) (cons s (cons b nil)))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  exact prf_or_intro_left (prf_strBinOk_cons w s b 3 hb)

theorem prf_nodeOk_bin4 (w a b : Term) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons (numeralM 4) (cons a (cons b nil)))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  exact prf_or_intro_left (prf_binOk_cons w a b 4 ha hb)

theorem prf_nodeOk_bin5 (w a b : Term) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons (numeralM 5) (cons a (cons b nil)))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  exact prf_or_intro_left (prf_binOk_cons w a b 5 ha hb)

theorem prf_nodeOk_un6 (w a : Term) (ha : Prf (In a w)) :
    Prf (nodeOk w (cons (numeralM 6) (cons a nil))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  exact prf_or_intro_left (prf_unOk_cons w a 6 ha)

theorem prf_nodeOk_bin7 (w a b : Term) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons (numeralM 7) (cons a (cons b nil)))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  exact prf_or_intro_left (prf_binOk_cons w a b 7 ha hb)

theorem prf_nodeOk_bin8 (w a b : Term) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons (numeralM 8) (cons a (cons b nil)))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  refine prf_or_intro_right ?_                                   -- 6
  exact prf_or_intro_left (prf_binOk_cons w a b 8 ha hb)

theorem prf_nodeOk_un9 (w a : Term) (ha : Prf (In a w)) :
    Prf (nodeOk w (cons (numeralM 9) (cons a nil))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  refine prf_or_intro_right ?_                                   -- 6
  refine prf_or_intro_right ?_                                   -- 7
  exact prf_or_intro_left (prf_unOk_cons w a 9 ha)

theorem prf_nodeOk_var (w m : Term) :
    Prf (nodeOk w (cons (numeralM 0) (cons m nil))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  refine prf_or_intro_right ?_                                   -- 6
  refine prf_or_intro_right ?_                                   -- 7
  refine prf_or_intro_right ?_                                   -- 8
  exact prf_or_intro_left (prf_varOk_cons m)

theorem prf_nodeOk_strBin1 (w s b : Term) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons (numeralM 1) (cons s (cons b nil)))) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  refine prf_or_intro_right ?_                                   -- 6
  refine prf_or_intro_right ?_                                   -- 7
  refine prf_or_intro_right ?_                                   -- 8
  refine prf_or_intro_right ?_                                   -- 9
  exact prf_or_intro_left (prf_strBinOk_cons w s b 1 hb)

theorem prf_nodeOk_nil (w : Term) : Prf (nodeOk w nil) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  refine prf_or_intro_right ?_                                   -- 6
  refine prf_or_intro_right ?_                                   -- 7
  refine prf_or_intro_right ?_                                   -- 8
  refine prf_or_intro_right ?_                                   -- 9
  refine prf_or_intro_right ?_                                   -- 10
  exact prf_or_intro_left prf_nilOk

theorem prf_nodeOk_cons (w a b : Term) (ha : Prf (In a w)) (hb : Prf (In b w)) :
    Prf (nodeOk w (cons a b)) := by
  simp only [nodeOk, lorAll]
  refine prf_or_intro_right ?_                                   -- 1
  refine prf_or_intro_right ?_                                   -- 2
  refine prf_or_intro_right ?_                                   -- 3
  refine prf_or_intro_right ?_                                   -- 4
  refine prf_or_intro_right ?_                                   -- 5
  refine prf_or_intro_right ?_                                   -- 6
  refine prf_or_intro_right ?_                                   -- 7
  refine prf_or_intro_right ?_                                   -- 8
  refine prf_or_intro_right ?_                                   -- 9
  refine prf_or_intro_right ?_                                   -- 10
  exact prf_or_intro_right (prf_consCase_cons w a b ha hb)       -- 11

/-! # §E · LA INDUCCIÓN — cada nodo contra la lista COMPLETA `W`

    Se generaliza sobre un SUPERCONJUNTO `W ⊇ subCodes φ` y se prueba cada nodo contra
    `objList W`. Así nunca hace falta transportar `nodeOk w X` a `nodeOk (cons y w) X`
    (12 or‑elim por composición). -/

mutual
theorem nodeOk_mem_subCodesT : ∀ (t : Term) (W : List Term),
    (∀ y : Term, List.Mem y (subCodesT t) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodesT t) → Prf (nodeOk (objList W) x)
  | .var n, W, _, x, hx => by
      simp only [subCodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [termCodeM]
        exact prf_nodeOk_var (objList W) (numeralM n)
      · cases h'
  | .func s ts, W, hsub, x, hx => by
      simp only [subCodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [termCodeM]
        exact prf_nodeOk_strBin1 (objList W) (strCodeM s) (termsCodeM ts)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodesTs ts))))
      · exact nodeOk_mem_subCodesTs ts W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'
theorem nodeOk_mem_subCodesTs : ∀ (ts : List Term) (W : List Term),
    (∀ y : Term, List.Mem y (subCodesTs ts) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodesTs ts) → Prf (nodeOk (objList W) x)
  | [], W, _, x, hx => by
      simp only [subCodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact prf_nodeOk_nil (objList W)
      · cases h'
  | t :: ts, W, hsub, x, hx => by
      simp only [subCodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [termsCodeM]
        exact prf_nodeOk_cons (objList W) (termCodeM t) (termsCodeM ts)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inl (mem_self_subCodesT t))))))
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inr (mem_self_subCodesTs ts))))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_mem_subCodesT t W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_mem_subCodesTs ts W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
end

theorem nodeOk_mem_subCodes : ∀ (φ : Formula) (W : List Term),
    (∀ y : Term, List.Mem y (subCodes φ) → List.Mem y W) →
    ∀ x : Term, List.Mem x (subCodes φ) → Prf (nodeOk (objList W) x)
  | .bottom, W, _, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_nul2 (objList W)
      · cases h'
  | .atom p ts, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_strBin3 (objList W) (strCodeM p) (termsCodeM ts)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodesTs ts))))
      · exact nodeOk_mem_subCodesTs ts W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'
  | .eq t u, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_bin4 (objList W) (termCodeM t) (termCodeM u)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inl (mem_self_subCodesT t))))))
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inr (mem_self_subCodesT u))))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_mem_subCodesT t W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_mem_subCodesT u W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .impl a b, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_bin5 (objList W) (formCodeM a) (formCodeM b)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inl (mem_self_subCodes a))))))
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inr (mem_self_subCodes b))))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_mem_subCodes a W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_mem_subCodes b W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | Formula.forall a, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_un6 (objList W) (formCodeM a)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodes a))))
      · exact nodeOk_mem_subCodes a W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'
  | .and a b, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_bin7 (objList W) (formCodeM a) (formCodeM b)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inl (mem_self_subCodes a))))))
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inr (mem_self_subCodes b))))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_mem_subCodes a W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_mem_subCodes b W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .or a b, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_bin8 (objList W) (formCodeM a) (formCodeM b)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inl (mem_self_subCodes a))))))
          (prf_In_objList W _ (hsub _ (List.Mem.tail _
            (List.mem_append.mpr (Or.inr (mem_self_subCodes b))))))
      · rcases List.mem_append.mp h' with hA | hB
        · exact nodeOk_mem_subCodes a W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact nodeOk_mem_subCodes b W
            (fun y hy => hsub y (List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
  | .ex a, W, hsub, x, hx => by
      simp only [subCodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · simp only [formCodeM]
        exact prf_nodeOk_un9 (objList W) (formCodeM a)
          (prf_In_objList W _ (hsub _ (List.Mem.tail _ (mem_self_subCodes a))))
      · exact nodeOk_mem_subCodes a W (fun y hy => hsub y (List.Mem.tail _ hy)) x h'

/-! # §F · EL HITO (i) -/

theorem mem_of_getElem? : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? es k x h)

/-- **EL TESTIGO DE PARSEO, VALIDADO**: `⊢ isFCB (objList (subCodes φ)) ⌜φ⌝`. -/
theorem prf_isFCB_subCodes (φ : Formula) :
    Prf (isFCB (objList (subCodes φ)) (formCodeM φ)) :=
  prf_isFCB_of_wfAll φ (prf_wfAll_subCodes φ (fun k x hk =>
    nodeOk_mem_subCodes φ (subCodes φ) (fun _ hy => hy) x (mem_of_getElem? (subCodes φ) k x hk)))

/-! ### La sustitución `∃`‑testigo, hecha por DEFEQ

    Todo el descenso de `substFormula 0 L` por `isFCB (#0) c` es **definicional** (los
    índices son literales concretos, y `substTerm` sobre `numeralM k` con `k` concreto
    reduce). Lo único NO definicional son `liftTerm 0 W = W` (clausura del testigo) y
    `substTerm 0 W ⌜φ⌝ = ⌜φ⌝` (clausura del código): se aportan como reescrituras. -/

theorem subst_isFCB_gen (L c : Term) :
    substFormula 0 L (isFCB (.var 0) c)
      = land (Formula.forall (Formula.impl (lt (.var 0) (lenc (liftTerm 0 L)))
                (nodeOk (liftTerm 0 L) (nthc (liftTerm 0 L) (.var 0)))))
             (In (substTerm 0 L c) L) := rfl

theorem isFCB_unfold (W c : Term) :
    isFCB W c
      = land (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc W)))
                (nodeOk (liftTerm 0 W) (nthc (liftTerm 0 W) (.var 0)))))
             (In c W) := rfl

/-- **EL Σ₁**: `⊢ ∃w. isFCB w ⌜φ⌝`. -/
theorem prf_isFC (φ : Formula) :
    Prf (Formula.ex (isFCB (.var 0) (liftTerm 0 (formCodeM φ)))) := by
  have hlw : liftTerm 0 (objList (subCodes φ)) = objList (subCodes φ) :=
    liftTerm_objList_subCodes 0 φ
  have hlw2 : liftTerm 0 (lenc (objList (subCodes φ))) = lenc (objList (subCodes φ)) := by
    simp only [lenc, liftTerm, liftTerms, hlw]
  have hc : substTerm 0 (objList (subCodes φ)) (liftTerm 0 (formCodeM φ)) = formCodeM φ := by
    rw [liftTerm_formCodeM, substTerm_formCodeM]
  refine prf_ex_intro (objList (subCodes φ)) ?_
  have hs : substFormula 0 (objList (subCodes φ)) (isFCB (.var 0) (liftTerm 0 (formCodeM φ)))
      = isFCB (objList (subCodes φ)) (formCodeM φ) := by
    rw [subst_isFCB_gen, isFCB_unfold, hlw, hlw2, hc]
  rw [hs]
  exact prf_isFCB_subCodes φ

end SubCPorForma

#print axioms SubCPorForma.prf_nulOk_cons
#print axioms SubCPorForma.prf_unOk_cons
#print axioms SubCPorForma.prf_binOk_cons
#print axioms SubCPorForma.prf_strBinOk_cons
#print axioms SubCPorForma.prf_varOk_cons
#print axioms SubCPorForma.prf_nilOk
#print axioms SubCPorForma.prf_consCase_cons
#print axioms SubCPorForma.nodeOk_mem_subCodesT
#print axioms SubCPorForma.nodeOk_mem_subCodesTs
#print axioms SubCPorForma.nodeOk_mem_subCodes
#print axioms SubCPorForma.prf_isFCB_subCodes
#print axioms SubCPorForma.prf_isFC

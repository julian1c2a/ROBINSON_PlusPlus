/-
VERIFICACION ADVERSARIAL de Probe/A3_reformula.lean.

Tesis a comprobar: la ENMIENDA `consOk` que el fichero anade a `nodeOk` (frente a
`sondeos/ParseWitness.lean`) MATA el disyunto `X = nil` (= `termsCode []`), porque la
teoria objeto REFUTA `nil = cons h t` (`Meta/CodeDistinct.lean:67`).

    lake env lean Probe\VerifA3_JCadv.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open FOL

namespace VerifA3JC

/-! # 1 · COPIAS LITERALES de las definiciones de `Probe/A3_reformula.lean` -/

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

/-- LA ENMIENDA del fichero auditado. -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

/-- `nodeOk` **ENMENDADO** (el de `Probe/A3_reformula.lean`). -/
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

/-- `nodeOk` **ORIGINAL** (`sondeos/ParseWitness.lean:113`), SIN la enmienda. -/
def nodeOkOrig (w X : Term) : Formula :=
  lorAll (nulOk X 2)
    [ strBinOk w X 3, binOk w X 4, binOk w X 5, unOk w X 6, binOk w X 7, binOk w X 8
    , unOk w X 9, varOk X, strBinOk w X 1
    , Formula.eq X nil
    , land (In (carc X) w) (In (cdrc X) w) ]

/-! # 2 · EL CONTRASTE: el ORIGINAL PRUEBA `nodeOk w nil`; el ENMENDADO lo REFUTA. -/

/-- Con la definicion ORIGINAL, `nil` SI es un nodo valido (disyunto `X = nil`). -/
theorem prf_nodeOkOrig_nil (w : Term) : Prf (nodeOkOrig w nil) := by
  unfold nodeOkOrig lorAll
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  refine prf_mp (Prf.incl (Prf₀.j2 _ _)) ?_
  exact prf_mp (Prf.incl (Prf₀.j1 _ _)) (prf_refl nil)

theorem neg_consOk_nil : axioms ⊢ neg (consOk nil) :=
  nil_ne_cons (carc nil) (cdrc nil)

/-- **El disyunto `X = nil` esta MUERTO**: con la enmienda, `nil` NO puede ser nodo. -/
theorem neg_nodeOk_nil (w : Term) : axioms ⊢ neg (nodeOk w nil) :=
  Derives.elim_impl _ _ _
    (Derives.elim_impl _ _ _ (syllogism_impl (A := nodeOk w nil) (B := consOk nil)
      (C := Formula.bottom)) and_elim_left) neg_consOk_nil

/-! # 3 · Y `nil` es OBLIGATORIO en cualquier testigo real:
      el nodo de la constante `0` pide `In (nthc X 2) w`, y ahi `nthc X 2 = nil`. -/

/-- `termCodeM zero = cons 1̄ (cons ⌜"0"⌝ (cons nil nil))`; su casilla 2 es `nil`. -/
theorem nthc_termCodeM_zero_is_nil :
    Prf (nthc (termCodeM zero) (numeralM 2) =eq nil) := by
  show Prf (nthc (cons (numeralM 1) (cons (strCodeM zero_sym) (cons nil nil)))
    (succ (succ zero)) =eq nil)
  refine prf_eq_trans (prf_nthc_succ _ _ _) ?_
  refine prf_eq_trans (prf_nthc_succ _ _ _) ?_
  exact prf_nthc_zero _ _

/-! # 4 · LA CONSECUENCIA FUERTE: `wfAll w` + `In nil w` es REFUTABLE (w ABSTRACTO). -/

theorem liftFormula_nodeOk : ∀ (k : Nat) (q X : Term),
    liftFormula k (nodeOk q X) = nodeOk (liftTerm k q) (liftTerm k X) := by
  intro k q X
  simp only [nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM]

theorem liftFormula_wfAll : ∀ (k : Nat) (q : Term),
    liftFormula k (wfAll q) = wfAll (liftTerm k q) := by
  intro k q
  simp only [wfAll, nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
    lt, carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, nil, zero, cons, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

/-- De un testigo valido `w` que CONTIENE `nil` sale `nodeOk w nil`. -/
theorem prf_wfAll_In_nil (w : Term) : Prf (wfAll w ⇒ (In nil w ⇒ nodeOk w nil)) := by
  refine prf_deduction (deduction_aux ?_ (In nil w) [wfAll w] rfl)
  let Γ : List Formula := [In nil w, wfAll w]
  show PrfH Γ (nodeOk w nil)
  have hIn : PrfH Γ (In nil w) := PrfH.hyp _ _ (List.Mem.head _)
  have hbd : PrfH Γ (boundedIn nil w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In nil w) _) hIn
  refine PrfH_ex_elim hbd ?_
  rw [liftFormula_nodeOk]
  let W : Term := liftTerm 0 w
  let exBody : Formula := land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) nil)
  let Δ : List Formula := exBody :: (Γ.map (liftFormula 0))
  show PrfH Δ (nodeOk W nil)
  have hC : PrfH Δ exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Δ (lt (.var 0) (lenc W)) := PrfH_and_elim_left hC
  have heq : PrfH Δ (Formula.eq (nthc W (.var 0)) nil) := PrfH_and_elim_right hC
  have hw : PrfH Δ (wfAll W) := by
    have : PrfH Δ (liftFormula 0 (wfAll w)) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    rwa [liftFormula_wfAll] at this
  have hsub : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (liftTerm 0 (lenc W)))
        (nodeOk (liftTerm 0 W) (nthc (liftTerm 0 W) (.var 0))))
      = Formula.impl (lt (.var 0) (lenc W)) (nodeOk W (nthc W (.var 0))) := by
    simp only [nodeOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have hspec := PrfH_spec hw (.var 0)
  rw [hsub] at hspec
  exact PrfH_congr_nodeOk heq (PrfH.mp _ _ _ hspec hlt)

private theorem dtrans {A B C : Formula} (h1 : axioms ⊢ (A ⇒ B)) (h2 : axioms ⊢ (B ⇒ C)) :
    axioms ⊢ (A ⇒ C) :=
  Derives.elim_impl _ _ _ (Derives.elim_impl _ _ _ syllogism_impl h1) h2

/-- **NINGUN testigo valido puede contener `nil`** — con `w` ABSTRACTO.
    Como todo codigo de termino `func s ts` / de atomo pide `In (nthc X 2) w` y esa casilla
    acaba en `nil` (ver §3), esto deja `isFCB` sin testigos para cualquier formula que
    mencione un simbolo de funcion o de predicado. -/
theorem no_valid_witness_contains_nil (w : Term) :
    axioms ⊢ neg (land (wfAll w) (In nil w)) := by
  let A : Formula := land (wfAll w) (In nil w)
  have e1 : axioms ⊢ (A ⇒ wfAll w) := and_elim_left
  have e2 : axioms ⊢ (A ⇒ In nil w) := and_elim_right
  have h1 : axioms ⊢ (wfAll w ⇒ (In nil w ⇒ nodeOk w nil)) :=
    prf_to_derives (prf_wfAll_In_nil w)
  have h2 : axioms ⊢ (A ⇒ (In nil w ⇒ nodeOk w nil)) := dtrans e1 h1
  have h3 : axioms ⊢ (A ⇒ nodeOk w nil) :=
    Derives.elim_impl _ _ _ (Derives.elim_impl _ _ _ s_impl h2) e2
  exact dtrans h3 (neg_nodeOk_nil w)

end VerifA3JC

#print axioms VerifA3JC.prf_nodeOkOrig_nil
#print axioms VerifA3JC.neg_consOk_nil
#print axioms VerifA3JC.neg_nodeOk_nil
#print axioms VerifA3JC.nthc_termCodeM_zero_is_nil
#print axioms VerifA3JC.prf_wfAll_In_nil
#print axioms VerifA3JC.no_valid_witness_contains_nil
#check @VerifA3JC.no_valid_witness_contains_nil

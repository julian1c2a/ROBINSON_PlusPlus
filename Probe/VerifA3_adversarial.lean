/-
VERIFICACION ADVERSARIAL de Probe/A3_fragmento.lean.

Tesis a comprobar en el COMPILADOR: la «enmienda R-A3-1» (`consOk X` conjuntado
globalmente en `nodeOkF`) MATA el disyunto `Formula.eq X nil`, porque la teoria
objeto REFUTA `nil =eq cons h t` (`CodeDistinct.nil_ne_cons`).

Si esto compila, `nodeOkF w nil` es refutable ⇒ ninguna lista testigo `w` puede
contener `nil` como elemento satisfaciendo `wfAllF w`.
-/
import ROBINSON_PlusPlus.Meta
import ROBINSON_PlusPlus.Meta.CodeDistinct

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction

namespace VerifA3

/-- Copia LITERAL de las definiciones de `Probe/A3_fragmento.lean` (§0, §11.1). -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

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

def nodeDisj (w X : Term) : List Formula :=
  [ strBinOk w X 3, binOk w X 4, binOk w X 5, unOk w X 6, binOk w X 7, binOk w X 8
  , unOk w X 9, varOk X, strBinOk w X 1
  , Formula.eq X nil
  , land (In (carc X) w) (In (cdrc X) w) ]

/-- `nodeOk` de A3_fragmento (CON la enmienda R-A3-1). -/
def nodeOkF (w X : Term) : Formula := land (consOk X) (lorAll (nulOk X 2) (nodeDisj w X))

/-- `nodeOk` ORIGINAL de `sondeos/ParseWitness.lean` (SIN la enmienda). -/
def nodeOk_orig (w X : Term) : Formula := lorAll (nulOk X 2) (nodeDisj w X)

/-- Copia LITERAL de `wfAllF` / `isFCBF` de `Probe/A3_fragmento.lean` (§11.1). -/
def wfAllF (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOkF (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCBF (w c : Term) : Formula := land (wfAllF w) (In c w)

/-! ## LA REFUTACION -/

/-- La teoria REFUTA `consOk nil`. -/
theorem refuta_consOk_nil : axioms ⊢ neg (consOk nil) :=
  ROBINSON_PlusPlus.Meta.CodeDistinct.nil_ne_cons (carc nil) (cdrc nil)

/-- **EL PUNTO**: con la enmienda R-A3-1, el nodo `nil` es REFUTABLE.
    El disyunto `Formula.eq X nil` de `nodeDisj` queda MUERTO. -/
theorem refuta_nodeOkF_nil (w : Term) : axioms ⊢ neg (nodeOkF w nil) :=
  imp_intro (fun h => mp refuta_consOk_nil (mp FOL.Theorems.Derived.and_elim_left h))

/-- Y sin embargo el disyunto SI es alcanzable en el `nodeOk` ORIGINAL:
    `nodeOk_orig w nil` es DEMOSTRABLE (via el disyunto `X =eq nil`). -/
theorem alcanzable_nodeOk_orig_nil (w : Term) : axioms ⊢ nodeOk_orig w nil := by
  show axioms ⊢ lorAll (nulOk nil 2) (nodeDisj w nil)
  simp only [lorAll, nodeDisj]
  have hnil : axioms ⊢ (nil =eq nil) := Derives.refl _ _
  exact mp FOL.Theorems.Derived.or_intro_right
    (mp FOL.Theorems.Derived.or_intro_right (mp FOL.Theorems.Derived.or_intro_right
      (mp FOL.Theorems.Derived.or_intro_right (mp FOL.Theorems.Derived.or_intro_right
        (mp FOL.Theorems.Derived.or_intro_right (mp FOL.Theorems.Derived.or_intro_right
          (mp FOL.Theorems.Derived.or_intro_right (mp FOL.Theorems.Derived.or_intro_right
            (mp FOL.Theorems.Derived.or_intro_right
              (mp FOL.Theorems.Derived.or_intro_left hnil))))))))))

/-! ## LA CONSECUENCIA: ninguna casilla de un testigo valido puede valer `nil` -/

/-- Del `wfAllF` sale `consOk` en cada casilla (patron `hbodyF_ok` de A3_fragmento). -/
theorem consOk_of_wfAllF (w i : Term) :
    Prf (wfAllF w ⇒ (lt i (lenc w) ⇒ consOk (nthc w i))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc w)) [wfAllF w] rfl)
  let Γ : List Formula := [lt i (lenc w), wfAllF w]
  show PrfH Γ (consOk (nthc w i))
  have hlt : PrfH Γ (lt i (lenc w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH Γ (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
      (nodeOkF (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
      (nodeOkF (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))
      = Formula.impl (lt i (lenc w)) (nodeOkF w (nthc w i)) := by
    simp only [nodeOkF, nodeDisj, lorAll, consOk, nulOk, unOk, binOk, strBinOk, varOk,
      land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero,
      substFormula, substTerm, substTerms,
      substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have hq1 : PrfH Γ (Formula.impl (lt i (lenc w)) (nodeOkF w (nthc w i))) := by
    have hh := PrfH.mp _ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q1
      (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
        (nodeOkF (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))) i)) hwf
    rwa [hsubst] at hh
  exact PrfH_and_elim_left (PrfH.mp _ _ _ hq1 hlt)

/-- **EL GOLPE**: si `w` es un testigo valido segun A3_fragmento, ninguna de sus
    casillas puede ser `nil`. Es decir, `wfAllF w` REFUTA `nthc w i =eq nil`. -/
theorem wfAllF_refuta_casilla_nil (w i : Term) :
    axioms ⊢ neg (land (wfAllF w) (land (lt i (lenc w)) (nthc w i =eq nil))) := by
  refine imp_intro (fun h => ?_)
  have hwf := mp FOL.Theorems.Derived.and_elim_left h
  have hrest := mp FOL.Theorems.Derived.and_elim_right h
  have hlt := mp FOL.Theorems.Derived.and_elim_left hrest
  have hnil : _ ⊢ (nthc w i =eq nil) := mp FOL.Theorems.Derived.and_elim_right hrest
  have hcons : _ ⊢ consOk (nthc w i) :=
    mp (mp (prf_to_derives (consOk_of_wfAllF w i)) hwf) hlt
  -- `nil =eq cons (carc (nthc w i)) (cdrc (nthc w i))`, refutado por `nil_ne_cons`
  exact mp (ROBINSON_PlusPlus.Meta.CodeDistinct.nil_ne_cons
      (carc (nthc w i)) (cdrc (nthc w i)))
    (FOL.derive_eq_trans (FOL.derive_eq_symm hnil) hcons)

end VerifA3

#print axioms VerifA3.refuta_nodeOkF_nil
#print axioms VerifA3.alcanzable_nodeOk_orig_nil
#print axioms VerifA3.consOk_of_wfAllF
#print axioms VerifA3.wfAllF_refuta_casilla_nil
#check @VerifA3.wfAllF_refuta_casilla_nil
#check @VerifA3.refuta_nodeOkF_nil

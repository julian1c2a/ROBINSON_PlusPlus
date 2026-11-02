/-
# SONDEO — LA VIA SIN MAP: ¿se puede probar la CLAUSURA sin transportar el testigo?

    lake env lean Probe/SinMap.lean

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más). Copia LITERAL de las
definiciones de `Probe/PilotoParticion.lean` (§1, §12, §16, §19) y de los combinadores de
`Probe/CritPiloto.lean` que hacen falta — no se toca ninguno de los dos ficheros.
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
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace SinMap

/-! ## 0 · Combinadores (copia literal de `PilotoParticion` §0 y `CritPiloto` C1–C5) -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j1 A B)) h

theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j2 A B)) h

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

theorem PrfH_congr_In_right {Γ : List Formula} {u w w' : Term} (h : PrfH Γ (w =eq w'))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In u w') := by
  have hS : ∀ s : Term, substFormula 0 s (In (liftTerm 0 u) (.var 0)) = In u s := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS w') ▸ PrfH_leibniz_subst (A := In (liftTerm 0 u) (.var 0)) h ((hS w) ▸ hin)

theorem crit_num_ne : ∀ (m n : Nat), m ≠ n →
    Prf (Formula.impl (Formula.eq (numeralM m) (numeralM n)) Formula.bottom)
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ =>
      prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (numeralM _)) _)
        (PrfH_eq_symm (prfH_hyp_self _)))
  | m + 1, 0,     _ => prf_succ_ne_zero (numeralM m)
  | m + 1, n + 1, h =>
      impT (prf_succ_inj (numeralM m) (numeralM n)) (crit_num_ne m n (fun e => h (by omega)))

/-! ## 1 · Las definiciones de la PARTICIÓN (copia literal de `PilotoParticion` §1 y §12) -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))
def funcOkT (wTs X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) wTs)
def isTermCodeB (wT wTs X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT wTs X))
def isTermsCodeB (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))

def nulOkF (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 2)) (Formula.eq (lenc X) (numeralM 1))
def unOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)
def binOkF (wA wB X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) wA) (In (nthc X (numeralM 2)) wB))
def strBinOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

def isFormCodeB (wF wT wTs X : Term) : Formula :=
  lorAll (cOk X (nulOkF X))
    [ cOk X (strBinOkF wTs X 3)
    , cOk X (binOkF wT wT X 4)
    , cOk X (binOkF wF wF X 5)
    , cOk X (unOkF  wF X 6)
    , cOk X (binOkF wF wF X 7)
    , cOk X (binOkF wF wF X 8)
    , cOk X (unOkF  wF X 9) ]

def bndFF (aF : Term → Term) (p : Term) : Term := lenc (aF p)
def wfAllF (aF aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndFF aF p)))
    (isFormCodeB (liftTerm 0 (aF p)) (liftTerm 0 (aT p)) (liftTerm 0 (aTs p))
      (nthc (liftTerm 0 (aF p)) (.var 0))))

def bndTgen  (aT  : Term → Term) (p : Term) : Term := lenc (aT p)
def bndTsgen (aTs : Term → Term) (p : Term) : Term := lenc (aTs p)
def wfAllTgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTgen aT p)))
    (isTermCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aT p)) (.var 0))))
def wfAllTsgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTsgen aTs p)))
    (isTermsCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aTs p)) (.var 0))))

def acF  : Term → Term := carc
def acT  : Term → Term := fun p => carc (cdrc p)
def acTs : Term → Term := fun p => cdrc (cdrc p)

def tripleOk (p : Term) : Formula :=
  land (wfAllF acF acT acTs p)
       (land (wfAllTgen acT acTs p) (wfAllTsgen acT acTs p))

def isFCB3 (p c : Term) : Formula := land (tripleOk p) (In c (acF p))

theorem substF_isFormCodeB (v : Nat) (s A B C X : Term) :
    substFormula v s (isFormCodeB A B C X)
      = isFormCodeB (substTerm v s A) (substTerm v s B) (substTerm v s C) (substTerm v s X) := by
  simp only [isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

theorem PrfH_congr_isFormCodeB {Γ : List Formula} {wF wT wTs X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (hN : PrfH Γ (isFormCodeB wF wT wTs X₁)) :
    PrfH Γ (isFormCodeB wF wT wTs X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s
        (isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
        = isFormCodeB wF wT wTs s := by
    intro s
    simp only [substF_isFormCodeB, FOL.substTerm_liftTerm, substTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst
    (A := isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)) h ((hS X₁) ▸ hN)

theorem wfAllF_closed_at (p : Term) (h1 : liftTerm 0 (acF p) = acF p)
    (h2 : liftTerm 0 (acT p) = acT p) (h3 : liftTerm 0 (acTs p) = acTs p) :
    wfAllF acF acT acTs p = Formula.forall (Formula.impl (lt (.var 0) (bndFF acF p))
      (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) (.var 0)))) := by
  simp only [wfAllF, bndFF, lenc, nthc, liftTerm, liftTerms, h1, h2, h3]

theorem spec_bodyF (A B C : Term)
    (hAs : ∀ (v : Nat) (s : Term), substTerm v s A = A)
    (hBs : ∀ (v : Nat) (s : Term), substTerm v s B = B)
    (hCs : ∀ (v : Nat) (s : Term), substTerm v s C = C)
    (h : Prf (Formula.forall (Formula.impl (lt (.var 0) (lenc A))
              (isFormCodeB A B C (nthc A (.var 0)))))) (i : Term) :
    Prf (Formula.impl (lt i (lenc A)) (isFormCodeB A B C (nthc A i))) := by
  have hh := prf_spec h i
  simpa only [substFormula, lt, substF_isFormCodeB, nthc, lenc, substTerm, substTerms,
    hAs, hBs, hCs, if_true, reduceIte] using hh

/-! ################################################################################
    # E1 · EL «MAP» NO ES QUE NO EXISTA: ES QUE ES LA FUNCIÓN EQUIVOCADA
    ################################################################################

    La pista del encargo era que `substtsc` YA ES el map de `substtc` sobre listas de
    códigos de TÉRMINO (`ax_substtsc_nil/cons`, `Axioms.lean:454‑457`), luego «no existe
    map» es demasiado fuerte. Correcto — pero el diagnóstico correcto es PEOR:

    **aunque existiera `substfsc` (el map de `substfc` sobre listas de códigos de FÓRMULA),
    su imagen NO sería un testigo válido.**

    Razón: los dos binders desplazan los parámetros (`ax_substfc_forall` / `ax_substfc_ex`):

        substfc v t (forallc a) = forallc (substfc (succ v) (liftc zero t) a)

    ⇒ la hija del código imagen es `substfc (succ v) (liftc zero t) a`, mientras que el map
    con parámetros FIJOS `(v,t)` metería en la lista `substfc v t a`. Un testigo debe contener
    las hijas del nodo; luego el map produce la lista EQUIVOCADA. -/

/-- El desplazamiento de parámetros bajo `∀` — es el axioma, aquí sólo para tenerlo a la vista. -/
theorem e1_binder_shift (v t a : Term) :
    Prf (substfc v t (forallc a) =eq forallc (substfc (succ v) (liftc zero t) a)) :=
  prf_substfc_forall v t a

/-- Y lo mismo bajo `∃`. -/
theorem e1_binder_shift_ex (v t a : Term) :
    Prf (substfc v t (exc a) =eq exc (substfc (succ v) (liftc zero t) a)) :=
  prf_substfc_ex v t a

/-- **La testigo A**: a nivel META, `substFormula` bajo un binder cambia de nivel. -/
theorem e1_meta_forall (s : Term) (A : Formula) :
    substFormula 0 s (Formula.forall A) = Formula.forall (substFormula 1 (liftTerm 0 s) A) := rfl

/-- **La testigo B (refutación concreta)**: con `A := (#0 ≐ #1)` y `s := 0`, la hija que el
    testigo imagen NECESITA (`substFormula 1 ↑0 A`) y la que un map con `(v,t)` fijos
    PRODUCIRÍA (`substFormula 0 0 A`) son fórmulas DISTINTAS. -/
theorem e1_map_is_wrong :
    substFormula 1 (liftTerm 0 zero) (Formula.eq (.var 0) (.var 1))
      ≠ substFormula 0 zero (Formula.eq (.var 0) (.var 1)) := by
  simp only [substFormula, substTerm, liftTerm, zero, reduceIte]
  intro h
  exact absurd (Formula.eq.inj h).1 (by simp)

/-- Y por tanto sus CÓDIGOS son términos Lean distintos: la lista imagen del map no puede
    ser el testigo de `substfc v t (forallc ⌜A⌝)`. -/
theorem e1_map_is_wrong_codes :
    formCodeM (substFormula 1 (liftTerm 0 zero) (Formula.eq (.var 0) (.var 1)))
      ≠ formCodeM (substFormula 0 zero (Formula.eq (.var 0) (.var 1))) := by
  simp only [substFormula, substTerm, liftTerm, zero, reduceIte, formCodeM, termCodeM,
    numeralM, cons, nil, succ]
  intro h
  exact absurd h (by decide)

/-! ################################################################################
    # E2 · EL DESCENSO ES GRATIS — **el MISMO testigo sirve para todas las subfórmulas**
    ################################################################################

    Lo que la inducción de `pcc_eval_substfc` necesita NO es transportar el testigo:
    necesita BAJAR por él. Y el diseño «pertenencia SIN orden» (`In c w`, no «antes de la
    posición i») hace que bajar sea la identidad sobre el testigo:

        isFCB3 p (forallc a)  ⟹  isFCB3 p a          (MISMO `p`)

    Aquí queda COMPILADO con `a` ABSTRACTO. -/

theorem crit_tag_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (Formula.eq (carc X) (numeralM m)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne k m hkm) _)
    (PrfH_eq_trans (prf_to_prfH (prf_eq_symm hX) _) (prfH_hyp_self _)))

theorem crit_cOk2_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) (G : Formula) :
    Prf (Formula.impl (cOk X (land (Formula.eq (carc X) (numeralM m)) G)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_tag_absurd X k m hkm hX) _)
    (PrfH_and_elim_left (PrfH_and_elim_right (prfH_hyp_self _))))

theorem crit_cOk3_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) (G H : Formula) :
    Prf (Formula.impl (cOk X (land (land (Formula.eq (carc X) (numeralM m)) G) H))
      Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_tag_absurd X k m hkm hX) _)
    (PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_right (prfH_hyp_self _)))))

/-- La hija de un `forallc` (tag 6) está en la lista de FÓRMULAS. Espejo de
    `CritPiloto.crit_isFormCodeB_implc_child1`, para el caso UNARIO con binder. -/
theorem e2_child_forallc (wF wT wTs a : Term) :
    Prf (Formula.impl (isFormCodeB wF wT wTs (forallc a)) (In a wF)) := by
  have hc : Prf (carc (forallc a) =eq numeralM 6) := prf_carc_cons _ _
  have bad3 : ∀ (m : Nat), m ≠ 6 → ∀ G H : Formula,
      Prf (Formula.impl
        (cOk (forallc a) (land (land (Formula.eq (carc (forallc a)) (numeralM m)) G) H))
        (In a wF)) := fun m hm G H =>
    impT (crit_cOk3_absurd (forallc a) 6 m (fun e => hm e.symm) hc G H)
      (Prf.incl (Prfᵢ.efq (In a wF)))
  have bad2 : ∀ (m : Nat), m ≠ 6 → ∀ G : Formula,
      Prf (Formula.impl
        (cOk (forallc a) (land (Formula.eq (carc (forallc a)) (numeralM m)) G)) (In a wF)) :=
    fun m hm G =>
      impT (crit_cOk2_absurd (forallc a) 6 m (fun e => hm e.symm) hc G)
        (Prf.incl (Prfᵢ.efq (In a wF)))
  have good : Prf (Formula.impl (cOk (forallc a) (unOkF wF (forallc a) 6)) (In a wF)) := by
    refine prf_deduction ?_
    have hyp := prfH_hyp_self (cOk (forallc a) (unOkF wF (forallc a) 6))
    have hin := PrfH_and_elim_right (PrfH_and_elim_right hyp)
    have hnth : Prf (nthc (forallc a) (numeralM 1) =eq a) :=
      prf_nthc_c1 (numeralM 6) a nil
    exact PrfH_congr_In_left (prf_to_prfH hnth _) hin
  simp only [isFormCodeB, lorAll]
  exact prf_or_elim_imp (bad2 2 (by decide) _)
   (prf_or_elim_imp (bad3 3 (by decide) _ _)
    (prf_or_elim_imp (bad3 4 (by decide) _ _)
     (prf_or_elim_imp (bad3 5 (by decide) _ _)
      (prf_or_elim_imp good
       (prf_or_elim_imp (bad3 7 (by decide) _ _)
        (prf_or_elim_imp (bad3 8 (by decide) _ _) (bad3 9 (by decide) _ _)))))))

theorem liftF_isFormCodeB (k : Nat) (A B C X : Term) :
    liftFormula k (isFormCodeB A B C X)
      = isFormCodeB (liftTerm k A) (liftTerm k B) (liftTerm k C) (liftTerm k X) := by
  simp only [isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM]

/-- **La otra mitad del descenso**: `In c (acF p)` + `tripleOk p` ⟹ `c` ES un código de
    fórmula (positivo; `CritPiloto` sólo tenía la versión que concluye `⊥`). -/
theorem e2_memb_wf (p c : Term)
    (hpl : ∀ n : Nat, liftTerm n p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (hwf : Prf (tripleOk p)) :
    Prf (Formula.impl (In c (acF p)) (isFormCodeB (acF p) (acT p) (acTs p) c)) := by
  have l1 : ∀ n : Nat, liftTerm n (acF p) = acF p := by
    intro n; simp only [acF, carc, liftTerm, liftTerms, hpl]
  have l2 : ∀ n : Nat, liftTerm n (acT p) = acT p := by
    intro n; simp only [acT, carc, cdrc, liftTerm, liftTerms, hpl]
  have l3 : ∀ n : Nat, liftTerm n (acTs p) = acTs p := by
    intro n; simp only [acTs, cdrc, liftTerm, liftTerms, hpl]
  have e1 : ∀ (v : Nat) (s : Term), substTerm v s (acF p) = acF p := by
    intro v s; simp only [acF, carc, substTerm, substTerms, hps]
  have e2 : ∀ (v : Nat) (s : Term), substTerm v s (acT p) = acT p := by
    intro v s; simp only [acT, carc, cdrc, substTerm, substTerms, hps]
  have e3 : ∀ (v : Nat) (s : Term), substTerm v s (acTs p) = acTs p := by
    intro v s; simp only [acTs, cdrc, substTerm, substTerms, hps]
  have hwfF : Prf (Formula.forall (Formula.impl (lt (.var 0) (lenc (acF p)))
      (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) (.var 0))))) := by
    have h0 := prf_and_elim_left hwf
    rwa [wfAllF_closed_at p (l1 0) (l2 0) (l3 0)] at h0
  have hbdEq : boundedIn c (acF p)
      = Formula.ex (land (lt (.var 0) (lenc (acF p)))
          (Formula.eq (nthc (acF p) (.var 0)) c)) := by
    simp only [boundedIn, lenc, nthc, liftTerm, liftTerms, l1, hcl]
  have hlift : liftFormula 0 (isFormCodeB (acF p) (acT p) (acTs p) c)
      = isFormCodeB (acF p) (acT p) (acTs p) c := by
    simp only [liftF_isFormCodeB, l1, l2, l3, hcl]
  have hex : Prf (Formula.impl (Formula.ex (land (lt (.var 0) (lenc (acF p)))
          (Formula.eq (nthc (acF p) (.var 0)) c)))
        (isFormCodeB (acF p) (acT p) (acTs p) c)) := by
    refine prf_ex_elim_imp ?_
    rw [hlift]
    have hyp := prfH_hyp_self (land (lt (.var 0) (lenc (acF p)))
          (Formula.eq (nthc (acF p) (.var 0)) c))
    have hlt := PrfH_and_elim_left hyp
    have heq := PrfH_and_elim_right hyp
    have hifc := PrfH.mp _ _ _
      (prf_to_prfH (spec_bodyF (acF p) (acT p) (acTs p) e1 e2 e3 hwfF (.var 0)) _) hlt
    exact PrfH_congr_isFormCodeB heq hifc
  have hbd : Prf (Formula.impl (boundedIn c (acF p))
      (isFormCodeB (acF p) (acT p) (acTs p) c)) := by rw [hbdEq]; exact hex
  exact impT (prf_boundedIn_of_In c (acF p)) hbd

/-- ✅ **EL DESCENSO, con el MISMO TESTIGO `p`** — `a` ABSTRACTO.
    Ésta es la pieza que la inducción fuerte de `pcc_eval_substfc` necesita, y NO pide
    ningún map, ni transporte, ni testigo nuevo. -/
theorem e2_descent_forall (p a : Term)
    (hpl : ∀ n : Nat, liftTerm n p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hcl : ∀ n : Nat, liftTerm n (forallc a) = forallc a)
    (h : Prf (isFCB3 p (forallc a))) :
    Prf (isFCB3 p a) :=
  prf_and_intro (prf_and_elim_left h)
    (prf_mp (e2_child_forallc (acF p) (acT p) (acTs p) a)
      (prf_mp (e2_memb_wf p (forallc a) hpl hps hcl (prf_and_elim_left h))
        (prf_and_elim_right h)))

/-! ################################################################################
    # E3 · LA OBSTRUCCIÓN REAL NO ES EL MAP: ES LA **RECONSTRUCCIÓN DE FORMA**
    ################################################################################

    Para siquiera *aplicar* `ax_substfc_forall` a un código ABSTRACTO `X` hace falta
    `X = forallc a` para algún `a`. Y el predicado de la partición, tal y como está, da
    `consOk X`, `carc X = 6̄` y `lenc X = 2̄` — de ahí NO sale la reconstrucción:

    * `ax_lenc_nil`/`ax_lenc_cons` sólo dicen cuánto vale `lenc` sobre `nil`/`cons`;
      no hay inversión «`lenc y = σ n ⟹ y = cons (carc y) (cdrc y)`», ni
      «`lenc y = 0 ⟹ y = nil`» (`Axioms.lean:742‑751`);
    * `ax_carc`/`ax_cdrc` sólo actúan sobre `cons` (`Axioms.lean:725‑726`);
    * `cons` es `pair h (σ t)` de Cantor (`ax_L0_cons_def`), sin axioma de sobreyectividad.

    `e3_recon_from_unOkF` mide EXACTAMENTE lo que falta: dos hechos extra, `consOk (cdrc X)`
    y `cdrc (cdrc X) = nil`. -/

theorem prf_congr_nthc_lst {w₁ w₂ : Term} (i : Term) (h : Prf (w₁ =eq w₂)) :
    Prf (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) [])) rfl

/-- Sanidad: `forallc a` **ES** `cons 6̄ (cons a nil)` — los tags son numerales `σⁿ0`. -/
theorem e3_forallc_is_cons (a : Term) : forallc a = cons (numeralM 6) (cons a nil) := rfl

/-- **LO QUE FALTA, MEDIDO.** Con los dos hechos extra la reconstrucción sale en 4 líneas;
    sin ellos no hay por dónde. -/
theorem e3_recon_from_unOkF (X : Term)
    (h1 : Prf (consOk X)) (h2 : Prf (carc X =eq numeralM 6))
    (h3 : Prf (consOk (cdrc X))) (h4 : Prf (cdrc (cdrc X) =eq nil)) :
    Prf (X =eq forallc (nthc X (numeralM 1))) := by
  -- `nthc X 1 = carc (cdrc X)`
  have hn : Prf (nthc X (numeralM 1) =eq carc (cdrc X)) := by
    refine prf_eq_trans (prf_congr_nthc_lst (numeralM 1) h1) ?_
    refine prf_eq_trans (prf_nthc_succ (carc X) (cdrc X) (numeralM 0)) ?_
    refine prf_eq_trans (prf_congr_nthc_lst (numeralM 0) h3) ?_
    exact prf_nthc_zero (carc (cdrc X)) (cdrc (cdrc X))
  -- `cdrc X = cons (carc (cdrc X)) nil`
  have hc : Prf (cdrc X =eq cons (carc (cdrc X)) nil) :=
    prf_eq_trans h3 (prf_congr_cons_tail h4)
  -- ensamblado
  show Prf (X =eq cons (numeralM 6) (cons (nthc X (numeralM 1)) nil))
  refine prf_eq_trans h1 ?_
  refine prf_eq_trans (prf_congr_cons_head h2) ?_
  refine prf_congr_cons_tail (prf_eq_trans hc ?_)
  exact prf_congr_cons_head (prf_eq_symm hn)

/-! ### La REFORMULACIÓN (opción C): el disyunto como ECUACIÓN DE FORMA -/

/-- Variante `unOkF` **por ecuación de forma**: en vez de `carc X = k̄ ∧ lenc X = 2̄`,
    directamente `X = cons k̄ (cons (nthc X 1̄) nil)`. Mismo contenido para códigos reales,
    pero AHORA la reconstrucción es la propia hipótesis. -/
def unEqF (w X : Term) (k : Nat) : Formula :=
  land (Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil)))
       (In (nthc X (numeralM 1)) w)

/-- Los códigos REALES lo cumplen (lo que hace falta para D1: `prf_isFCB3_fcodes`). -/
theorem e3_unEqF_forallc (w a : Term) (h : Prf (In a w)) : Prf (unEqF w (forallc a) 6) := by
  have hnth : Prf (nthc (forallc a) (numeralM 1) =eq a) := prf_nthc_c1 (numeralM 6) a nil
  refine prf_and_intro ?_ (prf_congr_In_left (prf_eq_symm hnth) h)
  show Prf (forallc a =eq cons (numeralM 6) (cons (nthc (forallc a) (numeralM 1)) nil))
  exact prf_congr_cons_tail (prf_congr_cons_head (prf_eq_symm hnth))

/-- ✅ **EL PAYOFF**: con la forma ecuacional, el PASO DE EVALUACIÓN de `substfc` sale sobre
    argumento **ABSTRACTO** `X` — es exactamente el paso que la inducción fuerte de
    `pcc_eval_substfc` necesita en el caso `∀`, y que hoy está bloqueado. -/
theorem e3_eval_step_forall (w X v t : Term) (h : Prf (unEqF w X 6)) :
    Prf (substfc v t X =eq forallc (substfc (succ v) (liftc zero t) (nthc X (numeralM 1)))) := by
  have hX : Prf (X =eq forallc (nthc X (numeralM 1))) := prf_and_elim_left h
  exact prf_eq_trans (prf_congr_substfc_arg3 hX)
    (prf_substfc_forall v t (nthc X (numeralM 1)))

/-- Y el mismo paso para `∃` (tag 9). -/
theorem e3_eval_step_ex (w X v t : Term)
    (h : Prf (Formula.eq X (cons (numeralM 9) (cons (nthc X (numeralM 1)) nil)))) :
    Prf (substfc v t X =eq exc (substfc (succ v) (liftc zero t) (nthc X (numeralM 1)))) :=
  prf_eq_trans (prf_congr_substfc_arg3 h) (prf_substfc_ex v t (nthc X (numeralM 1)))

/-- Caso BINARIO (tag 5, `implc`) — la forma ecuacional también lo destraba. -/
theorem e3_eval_step_impl (X v t : Term)
    (h : Prf (Formula.eq X (cons (numeralM 5)
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))))) :
    Prf (substfc v t X =eq implc (substfc v t (nthc X (numeralM 1)))
                                 (substfc v t (nthc X (numeralM 2)))) :=
  prf_eq_trans (prf_congr_substfc_arg3 h)
    (prf_substfc_impl v t (nthc X (numeralM 1)) (nthc X (numeralM 2)))

/-! ################################################################################
    # E4 · EXTENDER el testigo SÍ se puede (monotonía) — la vía (A)/(B) no muere aquí
    ################################################################################

    Si en algún momento hiciera falta CONSTRUIR un testigo mayor (la clausura), el
    ingrediente básico es que `isFormCodeB` sea MONÓTONO en las listas testigo. Lo es, y
    sale de `ax_L2_in_cons` sin nada nuevo, con `X` ABSTRACTO. -/

theorem prf_imp_refl (A : Formula) : Prf (A ⇒ A) := prf_deduction (prfH_hyp_self A)

theorem prf_and_mono {A A' B B' : Formula} (hA : Prf (A ⇒ A')) (hB : Prf (B ⇒ B')) :
    Prf (land A B ⇒ land A' B') := by
  refine prf_deduction ?_
  have hyp := prfH_hyp_self (land A B)
  exact PrfH_and_intro (PrfH.mp _ _ _ (prf_to_prfH hA _) (PrfH_and_elim_left hyp))
    (PrfH.mp _ _ _ (prf_to_prfH hB _) (PrfH_and_elim_right hyp))

theorem prf_or_mono {A A' B B' : Formula} (hA : Prf (A ⇒ A')) (hB : Prf (B ⇒ B')) :
    Prf (lor A B ⇒ lor A' B') :=
  prf_or_elim_imp (impT hA (Prf.incl (Prfᵢ.j1 A' B')))
    (impT hB (Prf.incl (Prfᵢ.j2 A' B')))

/-- ✅ **MONOTONÍA de `isFormCodeB` en la lista de FÓRMULAS**, `X` ABSTRACTO.
    (Los disyuntos 2/3/4 no miran `wF`; los 5/6/7/8/9 sí.) -/
theorem e4_isFormCodeB_mono_F (y wF wT wTs X : Term) :
    Prf (isFormCodeB wF wT wTs X ⇒ isFormCodeB (cons y wF) wT wTs X) := by
  have mono : ∀ x : Term, Prf (In x wF ⇒ In x (cons y wF)) := fun x =>
    prf_in_cons_tail_imp y x wF
  have un : ∀ k : Nat, Prf (cOk X (unOkF wF X k) ⇒ cOk X (unOkF (cons y wF) X k)) := fun k =>
    prf_and_mono (prf_imp_refl _)
      (prf_and_mono (prf_imp_refl _) (mono (nthc X (numeralM 1))))
  have bin : ∀ k : Nat, Prf (cOk X (binOkF wF wF X k) ⇒ cOk X (binOkF (cons y wF) (cons y wF) X k)) :=
    fun k => prf_and_mono (prf_imp_refl _)
      (prf_and_mono (prf_imp_refl _)
        (prf_and_mono (mono (nthc X (numeralM 1))) (mono (nthc X (numeralM 2)))))
  simp only [isFormCodeB, lorAll]
  exact prf_or_mono (prf_imp_refl _)
   (prf_or_mono (prf_imp_refl _)
    (prf_or_mono (prf_imp_refl _)
     (prf_or_mono (bin 5)
      (prf_or_mono (un 6)
       (prf_or_mono (bin 7) (prf_or_mono (bin 8) (un 9)))))))

/-! ################################################################################
    # E5 · LA INDUCCIÓN FUERTE ACEPTA EL MOTIVO Σ₁ DE LA CLAUSURA
    ################################################################################

    `prf_strong_induction` (`Meta/StrongInductionPrf.lean:185`) sólo pide de `Φ` que
    `liftFormula 1 Φ = Φ` (sin libres por encima del índice de inducción). El motivo de la
    clausura —que lleva un `∃` OBJETO sobre el testigo, luego es Σ₁— lo cumple. -/

/-- `Φ(c) = ∀v ∀t ∃q. isFCB3 q (substfc v t c)`, con `c` en el índice 0. -/
def closurePred : Formula :=
  Formula.forall (Formula.forall (Formula.ex
    (isFCB3 (.var 0) (substfc (.var 2) (.var 1) (.var 3)))))

theorem e5_closurePred_ok : liftFormula 1 closurePred = closurePred := by
  simp [closurePred, isFCB3, tripleOk, wfAllF, wfAllTgen, wfAllTsgen, bndFF, bndTgen,
    bndTsgen, isFormCodeB, isTermCodeB, isTermsCodeB, lorAll, cOk, consOk, nulOkF, unOkF,
    binOkF, strBinOkF, varOkT, funcOkT, acF, acT, acTs, land, lor, In, lt, substfc,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM]

/-- ✅ La maquinaria **acepta** el motivo: `prf_strong_induction` tipa sobre `closurePred`.
    (No se cierra la clausura aquí; se mide que el eliminador no la rechaza por ser Σ₁.) -/
theorem e5_strong_induction_accepts
    (step : Prf (Formula.forall (Formula.impl (PSI closurePred) closurePred))) :
    ∀ c : Term, Prf (substFormula 0 c closurePred) :=
  prf_strong_induction closurePred e5_closurePred_ok step

/-- El motivo es, literalmente, el enunciado de la clausura: `∃q` OBJETO sobre el testigo,
    con el código `c` en el índice 0 y `v`/`t` cuantificados INTERNAMENTE (que es lo que
    permite aplicar la HI con los parámetros DESPLAZADOS `(σv, liftc 0 t)` en los binders). -/
theorem e5_motive_is_the_closure :
    closurePred = Formula.forall (Formula.forall (Formula.ex
      (isFCB3 (.var 0) (substfc (.var 2) (.var 1) (.var 3))))) := rfl

/-! ################################################################################
    # E6 · EL TESTIGO BAJO UN `∃` OBJETO: se puede eliminar, pero DEJA DE SER CERRADO
    ################################################################################

    La pregunta del encargo: «¿se puede hacer el `∃`-elim y trabajar con el testigo como
    término objeto abstracto?». **Sí** — `prf_ex_elim_imp` existe y es net‑0. Pero el
    testigo pasa a ser `#0`, y `#0` **no es cerrado**: rompe las hipótesis de cierre que
    piden hoy TODOS los lemas de descenso (`e2_memb_wf`, `crit_*`). -/

/-- El `∃`-elim objeto está disponible: basta que la conclusión no tenga `#0` libre. -/
theorem e6_ex_elim_available (c : Term) (C : Formula) (hC : liftFormula 0 C = C)
    (hstep : PrfH [isFCB3 (.var 0) c] C) :
    Prf (Formula.ex (isFCB3 (.var 0) c) ⇒ C) := by
  refine prf_ex_elim_imp ?_
  rw [hC]; exact hstep

/-- ⚠️ **PERO**: el testigo eliminado es `#0`, que NO cumple la hipótesis de cierre que
    `e2_memb_wf` (y toda la familia `crit_*`) exige de `p`. -/
theorem e6_var_not_closed : ¬ (∀ n : Nat, liftTerm n (Term.var 0) = Term.var 0) := by
  intro h
  have h0 := h 0
  simp [liftTerm] at h0

theorem e6_var_not_subst_invariant :
    ¬ (∀ (v : Nat) (s : Term), substTerm v s (Term.var 0) = Term.var 0) := by
  intro h
  have h0 := h 0 zero
  simp [substTerm, zero] at h0

/-! ⇒ Para usar un testigo bajo `∃` habría que reescribir el descenso SIN hipótesis de
    cierre (estilo `Nat1`, como hace `pcc_wfAllF_tracked` con los accesores), o bien
    **evitar el `∃`**: llevar el testigo en una CASILLA DE LA LÍNEA
    (`⟨concl, 9, A, t, p⟩`, `lenc = 5̄`), con lo que `p` vuelve a ser un parámetro META
    y toda la familia `crit_*` se aplica tal cual. -/

/-! ################################################################################
    # E7 · DÓNDE SÍ REAPARECE LA CLAUSURA — y ahí el MAP **SÍ EXISTE**
    ################################################################################

    La clausura NO la piden los 7 tags (su enmienda R‑6 cae sobre las CASILLAS
    `nthc #0 2` / `nthc #0 3`, nunca sobre un resultado de `substfc`).
    La pide `pcc_eval_substfc` **por dentro**, y del lado de los TÉRMINOS:

    en el caso `∀`, la HI se aplica en `(σv, liftc 0 t)`, luego hay que saber que
    `liftc 0 t` sigue siendo un código de TÉRMINO ⟹ **clausura de `isTermCode` bajo `liftc`**.

    Y ahí el panorama se invierte respecto de E1: en el lado de los TÉRMINOS **no hay
    binders**, luego el parámetro NO se desplaza y el transporte SÍ es un map — que además
    **ya es axioma**. -/

/-- `liftc` recurre con el nivel **INTACTO** (contrastar con `e1_binder_shift`). -/
theorem e7_liftc_no_shift (c sc tsc : Term) :
    Prf (liftc c (funcc sc tsc) =eq funcc sc (liftsc c tsc)) := prf_liftc_func c sc tsc

/-- Y `liftsc` **ES** el map de `liftc`: `ax_liftsc_nil`/`ax_liftsc_cons`. -/
theorem e7_liftsc_is_map_nil (c : Term) : Prf (liftsc c nil =eq nil) := prf_liftsc_nil c
theorem e7_liftsc_is_map_cons (c h t : Term) :
    Prf (liftsc c (cons h t) =eq cons (liftc c h) (liftsc c t)) := prf_liftsc_cons c h t

/-- Lo mismo para `substtc`/`substtsc`: nivel intacto y map ya axiomatizado. -/
theorem e7_substtc_no_shift (v s sc tsc : Term) :
    Prf (substtc v s (funcc sc tsc) =eq funcc sc (substtsc v s tsc)) := prf_substtc_func v s sc tsc
theorem e7_substtsc_is_map_cons (v s h t : Term) :
    Prf (substtsc v s (cons h t) =eq cons (substtc v s h) (substtsc v s t)) :=
  prf_substtsc_cons v s h t

/-- ⇒ La lista testigo de TÉRMINOS `wT` se transporta con `liftsc k` (resp. `substtsc v s`)
    **sin nada nuevo**: sus elementos son códigos de término y ésa es exactamente la
    ecuación de `liftsc`. El ÚNICO map que falta es sobre la lista testigo de LISTAS `wTs`
    (map de `liftsc` sobre una lista de códigos‑de‑lista), que no está axiomatizada. -/
theorem e7_the_only_missing_map : True := trivial

/-! ################################################################################
    # E8 · Y ese map tampoco hace falta: la INDUCCIÓN DE LISTAS objeto lo suple
    ################################################################################

    `prf_list_induction` (`Meta/ChainPrf.lean:29`, net‑0) prueba `⊢ ∀L. Φ(L)` a partir de
    `Φ(nil)` y `∀h∀t (Φ(t) ⇒ Φ(cons h t))`. Con `Φ(L) := ∃q. <L bien formada con testigo q>`
    el PASO CONS construye el testigo imagen `cons … q` **dentro del `∃`**: no hace falta
    ninguna función objeto de map, ni ninguna lista META. -/

/-- Motivo Σ₁ para la clausura del lado LISTA: `Φ(L) = ∀k ∃q. isTsCB‑style q (liftsc k L)`.
    (Aquí sólo se comprueba que el eliminador lo acepta: `liftFormula 1 Φ = Φ`.) -/
def liftClosurePred : Formula :=
  Formula.forall (Formula.ex (isFCB3 (.var 0) (liftsc (.var 1) (.var 2))))

theorem e8_liftClosurePred_ok : liftFormula 1 liftClosurePred = liftClosurePred := by
  simp [liftClosurePred, isFCB3, tripleOk, wfAllF, wfAllTgen, wfAllTsgen, bndFF, bndTgen,
    bndTsgen, isFormCodeB, isTermCodeB, isTermsCodeB, lorAll, cOk, consOk, nulOkF, unOkF,
    binOkF, strBinOkF, varOkT, funcOkT, acF, acT, acTs, land, lor, In, lt, liftsc,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM]

/-- ✅ El eliminador de listas **acepta** el motivo Σ₁: el `∃` objeto hace de map. -/
theorem e8_list_induction_accepts
    (base : Prf (substFormula 0 nil liftClosurePred))
    (step : Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 liftClosurePred)
              (substFormula 0 (cons (.var 1) (.var 0))
                (liftFormula 2 (liftFormula 1 liftClosurePred))))))) :
    Prf (Formula.forall liftClosurePred) :=
  prf_list_induction liftClosurePred base step

end SinMap

/-! ## FOOTPRINT -/

#print axioms SinMap.e1_map_is_wrong
#print axioms SinMap.e1_map_is_wrong_codes
#print axioms SinMap.e2_child_forallc
#print axioms SinMap.e2_memb_wf
#print axioms SinMap.e2_descent_forall
#print axioms SinMap.e3_recon_from_unOkF
#print axioms SinMap.e3_unEqF_forallc
#print axioms SinMap.e3_eval_step_forall
#print axioms SinMap.e3_eval_step_ex
#print axioms SinMap.e3_eval_step_impl
#print axioms SinMap.e4_isFormCodeB_mono_F
#print axioms SinMap.e5_closurePred_ok
#print axioms SinMap.e5_strong_induction_accepts
#print axioms SinMap.e6_ex_elim_available
#print axioms SinMap.e7_liftc_no_shift
#print axioms SinMap.e7_liftsc_is_map_cons
#print axioms SinMap.e8_liftClosurePred_ok
#print axioms SinMap.e8_list_induction_accepts

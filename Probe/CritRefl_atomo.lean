/-
# VERIFICACIÓN ADVERSARIAL de `Probe/Refl_atomo.lean`.

Se importa el fichero REAL (no copias) y se atacan los dos puntos que el informe deja sin medir:

  (A) **NO VACUIDAD DE LA RAMA QUE IMPORTA.** La instancia cerrada del informe
      (`prf_isTC1_Xv`) sólo pasa por `prf_lorL` — el disyunto `shapeUn` (VARIABLE).
      La rama `shapeBin ∧ argsIn`, que es donde vive el `∀` ANIDADO y por tanto TODO el
      frente de esta sesión, NUNCA se instancia. Aquí se construye una instancia CERRADA
      que SÍ pasa por ella, con lista de argumentos NO VACÍA.

  (B) **DISCRIMINACIÓN.** ¿El predicado ECUACIONAL `isTermCodeE1` sigue refutando códigos
      de FÓRMULA? (el informe no lo comprueba en ninguna de las dos versiones).

  (C) El reflector del átomo `allIn` sobre una lista CERRADA NO VACÍA.

    $env:LEAN_PATH="<raiz>"; lake env lean Probe/CritRefl_atomo.lean
-/
import Probe.Refl_atomo

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ReflAtomo

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace CritReflAtomo

/-! ## A · LA RAMA `shapeBin ∧ argsIn` — instancia CERRADA con argumentos NO VACÍOS.

    `Xf = ⟨1, ⌜f⌝, [Xv]⟩` es el código del término `f(v₀)`; su lista de argumentos
    tiene UN elemento, así que el `∀` acotado INTERNO (`argsIn`) NO es vacuo. -/

def sc : Term := strCode "f"
def argsL : Term := cons ReflAtomo.Xv nil          -- lista de argumentos [⌜v₀⌝]
def Xf : Term := funcc sc argsL                    -- ⟨1, ⌜f⌝, [⌜v₀⌝]⟩
def wF : Term := cons Xf (cons ReflAtomo.Xv nil)   -- testigo [Xf, Xv]

theorem prf_nthc_one_Xf : Prf (nthc Xf (numeralM 1) =eq sc) :=
  prf_eq_trans (prf_nthc_succ (succ zero) (cons sc (cons argsL nil)) zero)
    (prf_nthc_zero sc (cons argsL nil))

theorem prf_nthc_two_Xf : Prf (nthc Xf (numeralM 2) =eq argsL) :=
  prf_eq_trans (prf_nthc_succ (succ zero) (cons sc (cons argsL nil)) (succ zero))
    (prf_eq_trans (prf_nthc_succ sc (cons argsL nil) zero) (prf_nthc_zero argsL nil))

/-- El disyunto de FORMA, en su versión ECUACIONAL, para un código de FUNCIÓN real. -/
theorem prf_shapeBin_Xf : Prf (ReflAtomo.shapeBin Xf 1) :=
  prf_eq_symm (prf_congr_cons_tail
    (prf_eq_trans (prf_congr_cons_head prf_nthc_one_Xf)
      (prf_congr_cons_tail (prf_congr_cons_head prf_nthc_two_Xf))))

/-- Congruencia en el 2º argumento del átomo `allIn` (no estaba). -/
theorem prf_congr_allIn2 {c L₁ L₂ : Term} (h : Prf (L₁ =eq L₂)) (hA : Prf (allIn c L₁)) :
    Prf (allIn c L₂) := by
  let f : Formula := allIn (liftTerm 0 c) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = allIn c s := by
    intro s
    simp only [f, allIn, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS L₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS L₁) ▸ prf_to_prfH hA [])) rfl

theorem prf_In_Xv_wF : Prf (In ReflAtomo.Xv wF) :=
  prf_in_cons_tail Xf (prf_in_cons_head ReflAtomo.Xv nil)

theorem prf_In_Xf_wF : Prf (In Xf wF) := prf_in_cons_head Xf (cons ReflAtomo.Xv nil)

/-- **La carga NO ES VACUA**: la lista de argumentos tiene un elemento y hay que
    comprobar que está en el testigo. -/
theorem prf_allIn_wF_argsL : Prf (allIn wF argsL) :=
  prf_iff_mpr (prf_allIn_cons wF ReflAtomo.Xv nil)
    (prf_and_intro prf_In_Xv_wF (prf_allIn_nil wF))

theorem prf_argsIn_Xf : Prf (ReflAtomo.argsIn wF (nthc Xf (numeralM 2))) := by
  rw [ReflAtomo.argsIn_eq_boundedAllIn]
  exact prf_mp (prf_boundedAllIn_of_allIn wF (nthc Xf (numeralM 2)))
    (prf_congr_allIn2 (prf_eq_symm prf_nthc_two_Xf) prf_allIn_wF_argsL)

/-- **EL NODO POR LA RAMA `shapeBin`** — el disyunto DERECHO, el que el informe nunca toca. -/
theorem prf_isTermCodeE1_Xf : Prf (ReflAtomo.isTermCodeE1 wF Xf) :=
  prf_mp (ReflAtomo.prf_lorR _ _) (prf_and_intro prf_shapeBin_Xf prf_argsIn_Xf)

theorem prf_nthc_zero_wF : Prf (nthc wF zero =eq Xf) :=
  prf_nthc_zero Xf (cons ReflAtomo.Xv nil)

theorem prf_nthc_one_wF : Prf (nthc wF (succ zero) =eq ReflAtomo.Xv) :=
  prf_eq_trans (prf_nthc_succ Xf (cons ReflAtomo.Xv nil) zero)
    (prf_nthc_zero ReflAtomo.Xv nil)

theorem prf_lenc_wF : Prf (Formula.eq (lenc wF) (succ (succ zero))) :=
  prf_eq_trans (prf_lenc_cons Xf (cons ReflAtomo.Xv nil))
    (prf_eq_congr_succ
      (prf_eq_trans (prf_lenc_cons ReflAtomo.Xv nil) (prf_eq_congr_succ prf_lenc_nil)))

/-- **`wfAll1` con DOS posiciones: una por CADA rama** (posición 0 = `funcc`, posición 1 = `varc`). -/
theorem prf_wfAll1_wF : Prf (ReflAtomo.wfAll1 wF) := by
  refine Prf.gen _ (prf_deduction ?_)
  have hlift : liftTerm 0 wF = wF := by
    simp only [wF, Xf, sc, argsL, ReflAtomo.Xv, varc, funcc, cons, nil, zero, succ,
      liftTerm, liftTerms, ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_strCode]
  rw [hlift]
  have hlt2 : PrfH [lt (.var 0) (lenc wF)] (lt (.var 0) (succ (succ zero))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH prf_lenc_wF _)
      (PrfH.hyp _ _ (List.Mem.head _))
  have hsplit2 : PrfH [lt (.var 0) (lenc wF)]
      (lor (lt (.var 0) (succ zero)) (Formula.eq (.var 0) (succ zero))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (succ zero)) _) hlt2
  refine PrfH_or_elim hsplit2 ?brLow ?brOne
  case brOne =>
    -- posición 1: el código de VARIABLE (rama `shapeUn`)
    have hi : PrfH (Formula.eq (.var 0) (succ zero) :: [lt (.var 0) (lenc wF)])
        (Formula.eq (.var 0) (succ zero)) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH (Formula.eq (.var 0) (succ zero) :: [lt (.var 0) (lenc wF)])
        (Formula.eq (nthc wF (.var 0)) ReflAtomo.Xv) :=
      PrfH_eq_trans (ReflAtomo.PrfH_congr_nthc_idx (w := wF) hi)
        (prf_to_prfH prf_nthc_one_wF _)
    exact ReflAtomo.PrfH_congr_isTermCodeE1 (PrfH_eq_symm hX)
      (prf_to_prfH (ReflAtomo.prf_isTermCodeE1_Xv wF) _)
  case brLow =>
    have hsplit1 : PrfH (lt (.var 0) (succ zero) :: [lt (.var 0) (lenc wF)])
        (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    refine PrfH_or_elim hsplit1 ?brA ?brB
    case brA =>
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
    case brB =>
      -- posición 0: el código de FUNCIÓN — **la rama con el `∀` anidado**
      have hi : PrfH (Formula.eq (.var 0) zero :: lt (.var 0) (succ zero)
          :: [lt (.var 0) (lenc wF)]) (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
      have hX : PrfH (Formula.eq (.var 0) zero :: lt (.var 0) (succ zero)
          :: [lt (.var 0) (lenc wF)]) (Formula.eq (nthc wF (.var 0)) Xf) :=
        PrfH_eq_trans (ReflAtomo.PrfH_congr_nthc_idx (w := wF) hi)
          (prf_to_prfH prf_nthc_zero_wF _)
      exact ReflAtomo.PrfH_congr_isTermCodeE1 (PrfH_eq_symm hX)
        (prf_to_prfH prf_isTermCodeE1_Xf _)

/-- **NO VACUIDAD REAL**: el reconocedor acepta un testigo con un código de FUNCIÓN
    de aridad 1, o sea pasando por el `∀` ANIDADO. -/
theorem crit_isTC1_wF : Prf (ReflAtomo.isTC1 wF Xf) :=
  prf_and_intro prf_wfAll1_wF prf_In_Xf_wF

/-- Y el reflector REAL del informe, compuesto con ella. -/
theorem crit_pcc_isTC1_wF : Prf (provFromCode (ReflAtomo.isTC1Dot wF Xf)) :=
  prf_mp (ReflAtomo.pcc_isTC1_tracked_lit wF Xf) crit_isTC1_wF

/-- La rama derecha también en la versión con `allIn` en el OBJETO. -/
theorem crit_isTermCodeE1'_Xf : Prf (ReflAtomo.isTermCodeE1' wF Xf) :=
  prf_mp (ReflAtomo.prf_isTCE1_of_literal wF Xf) prf_isTermCodeE1_Xf

/-! ## B · ¿SOBREVIVE LA DISCRIMINACIÓN a la forma ECUACIONAL de ESTE predicado? -/

theorem crit_num_ne : ∀ (m n : Nat), m ≠ n →
    Prf (Formula.impl (Formula.eq (numeralM m) (numeralM n)) Formula.bottom)
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ =>
      prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (numeralM _)) _)
        (PrfH_eq_symm (prfH_hyp_self _)))
  | m + 1, 0,     _ => prf_succ_ne_zero (numeralM m)
  | m + 1, n + 1, h =>
      ReflAtomo.impT (prf_succ_inj (numeralM m) (numeralM n))
        (crit_num_ne m n (fun e => h (by omega)))

theorem crit_tag_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (Formula.eq (carc X) (numeralM m)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne k m hkm) _)
    (PrfH_eq_trans (prf_to_prfH (prf_eq_symm hX) _) (prfH_hyp_self _)))

/-- **LA DISCRIMINACIÓN SOBREVIVE**: `isTermCodeE1` refuta todo nodo con tag ∉ {0,1}. -/
theorem crit_isTermCodeE1_rejects (w X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1 w X) Formula.bottom) :=
  ReflAtomo.prf_or_elim_imp
    (ReflAtomo.impT (ReflAtomo.prf_shapeUn_carc X 0) (crit_tag_absurd X k 0 hk0 hX))
    (prf_deduction (PrfH.mp _ _ _
      (prf_to_prfH (ReflAtomo.impT (ReflAtomo.prf_shapeBin_carc X 1)
        (crit_tag_absurd X k 1 hk1 hX)) _)
      (PrfH_and_elim_left (prfH_hyp_self _))))

/-- Ídem para la versión con `allIn` en el objeto. -/
theorem crit_isTermCodeE1'_rejects (w X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1' w X) Formula.bottom) :=
  ReflAtomo.impT (ReflAtomo.prf_literal_of_isTCE1 w X)
    (crit_isTermCodeE1_rejects w X k hk0 hk1 hX)

/-- **CÓDIGOS DE FÓRMULA REFUTADOS** (los junk que el frente vigila). -/
theorem crit_rejects_atomc (w p ts : Term) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1 w (atomc p ts)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (atomc p ts) 3 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_rejects_implc (w a b : Term) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1 w (implc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (implc a b) 5 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_rejects_forallc (w a : Term) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1 w (forallc a)) Formula.bottom) :=
  crit_isTermCodeE1_rejects w (forallc a) 6 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_rejects_botc (w : Term) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1 w botc) Formula.bottom) :=
  crit_isTermCodeE1_rejects w botc 2 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_rejects_atomc' (w p ts : Term) :
    Prf (Formula.impl (ReflAtomo.isTermCodeE1' w (atomc p ts)) Formula.bottom) :=
  crit_isTermCodeE1'_rejects w (atomc p ts) 3 (by decide) (by decide) (prf_carc_cons _ _)

/-! ## C · El reflector del átomo `allIn` sobre una lista CERRADA NO VACÍA. -/

theorem crit_pcc_allIn_wF :
    Prf (provFromCode (ReflAtomo.allInFn (tcFn wF) (tcFn argsL))) :=
  prf_mp (ReflAtomo.pcc_allIn_atom_tracked wF argsL) prf_allIn_wF_argsL

/-! ## D · El átomo `allIn` codificado ES el `formCode` del átomo objeto (sanity). -/

example (c L : Term) : ReflAtomo.allInFn (termCode c) (termCode L) = formCode (allIn c L) := rfl

end CritReflAtomo

#check @CritReflAtomo.crit_isTC1_wF
#check @CritReflAtomo.crit_pcc_isTC1_wF
#check @CritReflAtomo.crit_isTermCodeE1_rejects
#check @CritReflAtomo.crit_pcc_allIn_wF

#print axioms CritReflAtomo.crit_isTC1_wF
#print axioms CritReflAtomo.crit_pcc_isTC1_wF
#print axioms CritReflAtomo.prf_argsIn_Xf
#print axioms CritReflAtomo.crit_isTermCodeE1'_Xf
#print axioms CritReflAtomo.crit_isTermCodeE1_rejects
#print axioms CritReflAtomo.crit_rejects_atomc
#print axioms CritReflAtomo.crit_pcc_allIn_wF

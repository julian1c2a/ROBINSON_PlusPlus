/-
ADV_B1_dup — PUENTE `rfl` ADVERSARIAL para los 8 DUPLICADOS declarados.

Re-declara las 8 copias del sondeo VERBATIM en namespace propio, bajo los `open` DEL SONDEO,
y las confronta con las de PRODUCCION por `:= rfl` (nombres COMPLETAMENTE cualificados).
Si alguna no fuese la misma constante, el `rfl` NO elabora.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace AdvSondeo

/-! COPIA VERBATIM del sondeo, lineas 693-697 -/
def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

/-! COPIA VERBATIM del sondeo, lineas 879-885 -/
def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

/-! COPIA VERBATIM del sondeo, lineas 887-896 -/
theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-! COPIA VERBATIM del sondeo, lineas 747-758 -/
theorem PrfH_eq_trans_code {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z))) :
    PrfH Γ (provFromCode (eqc X Z)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hY : PrfH Γ (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp Y))) _) h1
  have hZ : PrfH Γ (provFromCode (substfc zero Z Ac)) := PrfH_leibniz_apply Ac Y Z h2 hY
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Z)) _) hZ

end AdvSondeo

/-! ############################################################################
    ## LOS OCHO PUENTES `:= rfl` — nombres de PRODUCCION completamente cualificados
    ############################################################################ -/

namespace AdvPuente

theorem d1_shapeUn :
    @AdvSondeo.shapeUn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn := rfl
theorem d2_shapeBin :
    @AdvSondeo.shapeBin = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin := rfl
theorem d3_argsInBody :
    @AdvSondeo.argsInBody = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody := rfl
theorem d4_argsIn :
    @AdvSondeo.argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn := rfl
theorem d5_isTermCodeE1 :
    @AdvSondeo.isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 := rfl
theorem d6_impT :
    @AdvSondeo.impT = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT := rfl
theorem d7_prf_or_elim_imp :
    @AdvSondeo.prf_or_elim_imp
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp := rfl
theorem d8_PrfH_eq_trans_code :
    @AdvSondeo.PrfH_eq_trans_code
      = @ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code := rfl

/-! La TERCERA copia denunciada: `ENS.impT` / `ENS.prf_or_elim_imp` ya existen en produccion
    ADEMAS de las de `SinWTs`. Si esto compila, produccion YA lleva DOS copias. -/
theorem ens_impT_es_sinwts :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.impT
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT := rfl
theorem ens_orelim_es_sinwts :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.prf_or_elim_imp
      = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp := rfl

end AdvPuente

#print axioms AdvPuente.d1_shapeUn
#print axioms AdvPuente.d2_shapeBin
#print axioms AdvPuente.d3_argsInBody
#print axioms AdvPuente.d4_argsIn
#print axioms AdvPuente.d5_isTermCodeE1
#print axioms AdvPuente.d6_impT
#print axioms AdvPuente.d7_prf_or_elim_imp
#print axioms AdvPuente.d8_PrfH_eq_trans_code
#print axioms AdvPuente.ens_impT_es_sinwts
#print axioms AdvPuente.ens_orelim_es_sinwts

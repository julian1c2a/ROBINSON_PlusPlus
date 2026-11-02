/- ADVERSARIAL: ¿cabe el general de nivel `numeral n` en CodeCtorKit? Imports EXACTOS de CodeCtorKit. -/
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf

namespace ADVB3C

/- (1) `prf_substtc_termCode_closed` / `_zero` SI se pueden probar aqui: -/
theorem K_prf_substtc_termCode_closed (v : Nat) (W t : Term)
    (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem K_prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  K_prf_substtc_termCode_closed v W zero (fun _ => rfl)

/- (2) y EL GENERAL ENTERO, de nivel `numeral n`, con los imports de CodeCtorKit: -/
def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (K_prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (K_prf_substtc_termCode_zero n W)))

#print axioms prf_substtc_binK_at
end ADVB3C

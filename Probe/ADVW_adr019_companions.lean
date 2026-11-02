/- ADR-019: ¿puede `PrfH_congr_predcT` VIVIR al final de `Meta/EvalPredPrf.lean`?
   Importa SOLO EvalPredPrf (NO el barrel, NO nada aguas abajo). -/
import ROBINSON_PlusPlus.Meta.EvalPredPrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.ChainPrf  -- ⚠️ NO lo abre EvalPredPrf hoy: hay que ANADIRLO

namespace ROBINSON_PlusPlus.Meta.EvalPredPrf

theorem PrfH_congr_pred {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (pred a =eq pred b) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 a)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred a) (pred s) := by
    intro s
    simp only [f, pred, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (pred a)) Γ)

theorem PrfH_congr_predcT {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (predcT a =eq predcT b) := by
  let f : Formula := Formula.eq (predcT (liftTerm 0 a)) (predcT (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (predcT a) (predcT s) := by
    intro s
    simp only [f, predcT, funcc, cons, nil, zero, succ, substFormula, substTerm, substTerms,
      substTerm_strCode, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (predcT a)) Γ)

theorem liftT_predcode (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) := by
  simp only [eqc, predcT, funcc, tcFn, pred, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode]


/-- ★ HALLAZGO: el `pcc_pred_succ_code` del sondeo NO es nuevo: es
    `EvalPredPrf.pcc_ax26_computed` instanciado en `w := tcFn m`. Cerrado con la
    constante de produccion, TAL CUAL. -/
theorem ADVW_pcc_pred_succ_code_es_dup (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) :=
  pcc_ax26_computed (tcFn m)

/-- Y con eso, `PrfH_pred_dot_of_succ` baja SIN promover nada mas. -/
theorem ADVW_PrfH_pred_dot_of_succ {G : List Formula} (n m : Term) (h : PrfH G (n =eq succ m)) :
    PrfH G (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := by
  have e1 : PrfH G (predcT (tcFn n) =eq predcT (succcT (tcFn m))) :=
    PrfH_congr_predcT (PrfH_eq_trans (PrfH_congr_tcFn h) (prf_to_prfH (prf_tc_succ' m) _))
  have hpn : PrfH G (pred n =eq m) :=
    PrfH_eq_trans (PrfH_congr_pred h) (prf_to_prfH (prf_pred_succ m) _)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_eq_symm e1) (PrfH_congr_tcFn (PrfH_eq_symm hpn)))
    (prf_to_prfH (pcc_ax26_computed (tcFn m)) _)

end ROBINSON_PlusPlus.Meta.EvalPredPrf

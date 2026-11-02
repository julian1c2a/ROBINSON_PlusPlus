/- # DOC_significado — verificacion COMPILADA de afirmaciones de SIGNIFICADO
       lake env lean Probe/DOC_significado.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalPredPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.DerivCondPrf

namespace DOCsig

/-! ## CHECK 1 · «el enunciado de los CRIT_* ya lo tenia produccion SIN descenso»
    (`Meta/EvalLiftcPrf.lean:559-570`). Se comprueba componiendo `refl_termCode` /
    `refl_termsCode` con `termCodeM_eq` / `termsCodeM_eq`, sin tocar el descenso. -/

theorem check1_sin_descenso (t : Term) : Prf (targetLift (termCodeM t)) :=
  (termCodeM_eq t) ▸ ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode t

theorem check1b_sin_descenso (ts : List Term) : Prf (targetLiftsc (termsCodeM ts)) :=
  (termsCodeM_eq ts) ▸ ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode ts

-- y son EL MISMO enunciado que los controles del modulo del descenso:
example (t : Term) :
    (Prf (targetLift (termCodeM t))) = (Prf (targetLift (termCodeM t))) := rfl
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLiftsc_real
#print axioms check1_sin_descenso
#print axioms check1b_sin_descenso

/-! ## CHECK 2 · la sub-obligacion de `pred` que consume `pcc_eval_substtc` es la GUARDADA,
    y se descarga SIN `pcc_eval_pred` y SIN induccion.
    Copia literal de `sondeos/EvalSubstfcPrf.lean:5864-5931` (§13), con `predcT` tomado de
    PRODUCCION (`Meta/EvalPredPrf.lean`). -/

def PredHyp : Prop := ∀ v n : Term,
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))

def AX26_BODY' : Formula := pred (succ (.var 0)) =eq (.var 0)

theorem pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) := by
  have hin : Prf (substfc zero (tcFn m) (formCode AX26_BODY')
      =eq eqCodeFn (predcT (succcT (tcFn m))) (tcFn m)) :=
    prf_substfc_arith_open 0 (tcFn m) AX26_BODY'
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst AX26_BODY' (show ax26_pred_succ ∈ axioms by simp [axioms]) (tcFn m))

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

theorem PrfH_pred_dot_of_succ {Γ : List Formula} (n m : Term) (h : PrfH Γ (n =eq succ m)) :
    PrfH Γ (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := by
  have e1 : PrfH Γ (predcT (tcFn n) =eq predcT (succcT (tcFn m))) :=
    PrfH_congr_predcT (PrfH_eq_trans (PrfH_congr_tcFn h) (prf_to_prfH (prf_tc_succ' m) _))
  have hpn : PrfH Γ (pred n =eq m) :=
    PrfH_eq_trans (PrfH_congr_pred h) (prf_to_prfH (prf_pred_succ m) _)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_eq_symm e1) (PrfH_congr_tcFn (PrfH_eq_symm hpn)))
    (prf_to_prfH (pcc_pred_succ_code m) _)

theorem liftT_predcode (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) := by
  simp only [eqc, predcT, funcc, tcFn, pred, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode]

/-- **`PredHyp` DESCARGADA, sin `pcc_eval_pred` y sin induccion.** -/
theorem predHyp : PredHyp := by
  intro v n
  refine prf_deduction ?_
  have hiff : PrfH [lt v n]
      (Formula.ex (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_lt_iff v n)) _) (prfH_hyp_self _)
  refine PrfH_ex_elim hiff ?_
  rw [liftFormula_provFromCode_open, liftT_predcode]
  have hh : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsucc : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (liftTerm 0 n =eq succ (add (liftTerm 0 v) (.var 0))) :=
    PrfH_eq_trans (PrfH_eq_symm hh)
      (prf_to_prfH (prf_add_succ_t (liftTerm 0 v) (.var 0)) _)
  exact PrfH_pred_dot_of_succ (liftTerm 0 n) (add (liftTerm 0 v) (.var 0)) hsucc

#print axioms predHyp

end DOCsig

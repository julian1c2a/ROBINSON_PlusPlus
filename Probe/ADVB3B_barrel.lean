/- ADVERSARIAL: comprobaciones que los arneses del agente NO podian hacer (importan el barrel). -/
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
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ADVB3B

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero n W)))

/-! ## T1 · IDENTIDAD DE TIPO con las constantes REALES de produccion.
     `Eq` obliga a unificar los tipos: si el enunciado derivado no fuera EL de produccion,
     esto no elabora. -/

example : @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at =
    (fun (m v : Nat) (W a b : Term) =>
      prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) v W a b) := rfl

example : @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_funccT_at =
    (fun (v : Nat) (W a b : Term) =>
      prf_substtc_binK_at (numeralM 1) (fun c => liftTerm_numeralM c 1) v W a b) := rfl

example : @ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_congr_binT =
    (fun (m : Nat) (a a' b b' : Term) (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) =>
      prf_congr_binK (H := termCode (numeralM m)) ha hb) := rfl

example : @ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_substtc_binT =
    (fun (m : Nat) (W a b : Term) =>
      prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) 0 W a b) := rfl

/-! ## T2 · `prf_substtc_funccT_at` YA es hoy un corolario de UNA linea. -/
example : @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_funccT_at =
    (fun (v : Nat) (W a b : Term) =>
      ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at 1 v W a b) := rfl

/-! ## T3 · las DOS copias de las ocho que el agente NO demostro: liftcT / liftscT. -/

theorem pcc_congr_hole_code (F : Term → Term) (X Y : Term)
    (hinv : ∀ W, Prf (substtc zero W (F X) =eq F X))
    (hhole : ∀ w, Prf (substtc zero w (F (varc (numeral 0))) =eq F w)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (F X) (F Y))) := by
  let Ac : Term := eqc (F X) (F (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (F X) (F w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (F X) (F (varc (numeral 0)))) ?_
    exact prf_congr_eqCodeFn (hinv w) (hhole w)
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (F X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

example : @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_liftcT_arg2_code =
    (fun (A X Y : Term) (hA : ∀ W, Prf (substtc zero W A =eq A))
         (hX : ∀ W, Prf (substtc zero W X =eq X)) =>
      pcc_congr_hole_code (fun s => liftcT A s) X Y
        (substtc_inv_liftcT hA hX)
        (fun w => prf_eq_trans (prf_substtc_liftcT zero w A (varc (numeral 0)))
          (prf_congr_liftcT (hA w) (prf_substtc_varc0 w)))) := rfl

example : @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_liftscT_arg2_code =
    (fun (A X Y : Term) (hA : ∀ W, Prf (substtc zero W A =eq A))
         (hX : ∀ W, Prf (substtc zero W X =eq X)) =>
      pcc_congr_hole_code (fun s => liftscT A s) X Y
        (substtc_inv_liftscT hA hX)
        (fun w => prf_eq_trans (prf_substtc_liftscT zero w A (varc (numeral 0)))
          (prf_congr_liftscT (hA w) (prf_substtc_varc0 w)))) := rfl

#print axioms prf_substtc_binK_at
#print axioms pcc_congr_hole_code

end ADVB3B

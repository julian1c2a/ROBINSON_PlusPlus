/- ¿Basta `pcc_dot_cons` para devolver `pcc_eval_carc`, la pieza que abre el keystone
   `EvalListPrf`? El viejo cerraba con `prf_tc_cons'` (el puente que murió con la reparación);
   la sustitución debería ser un único `pcc_rw` con `pcc_dot_cons`. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf

namespace CarcPayoff

def carcT (x : Term) : Term := funcc (strCode "carc") (cons x nil)
theorem prf_congr_carcT {x y : Term} (h : Prf (x =eq y)) : Prf (carcT x =eq carcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)
theorem prf_substtc_carcT (v W x : Term) :
    Prf (substtc v W (carcT x) =eq carcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode "carc") x

/-- `⊢ Prov(⌜ carc((cons h t)˙) = ḣ ⌝)` — el §28 recuperado. -/
theorem pcc_eval_carc (h t : Term) :
    Prf (provFromCode (eqCodeFn (carcT (tcFn (cons h t))) (tcFn h))) := by
  let W1 : Term := liftc zero (tcFn h)
  let W2 : Term := tcFn t
  let φ : Formula := carc (cons (.var 1) (.var 0)) =eq (.var 1)
  have hin : Prf (substfc (succ zero) W1 (formCode φ)
      =eq eqCodeFn (carcT (consT W1 (varc (numeral 0)))) W1) :=
    prf_substfc_arith_open 1 W1 φ
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (carcT (consT W1 (varc (numeral 0)))) W1
      =eq eqCodeFn (carcT (consT (tcFn h) (varc (numeral 0)))) (tcFn h)) :=
    prf_congr_eqCodeFn (prf_congr_carcT (prf_congr_consT hA (prf_refl _))) hA
  have hout : Prf (substfc zero W2 (eqCodeFn (carcT (consT (tcFn h) (varc (numeral 0)))) (tcFn h))
      =eq eqCodeFn (carcT (consT (tcFn h) W2)) (tcFn h)) := by
    refine prf_eq_trans
      (prf_substfc_eq zero W2 (carcT (consT (tcFn h) (varc (numeral 0)))) (tcFn h)) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn W2 h)
    refine prf_eq_trans (prf_substtc_carcT zero W2 (consT (tcFn h) (varc (numeral 0)))) ?_
    refine prf_congr_carcT ?_
    exact prf_eq_trans (prf_substtc_consT zero W2 (tcFn h) (varc (numeral 0)))
      (prf_congr_consT (prf_substtc_tcFn W2 h) (prf_substtc_varc0 W2))
  have hchain : Prf (substfc zero W2 (substfc (succ zero) W1 (formCode φ))
      =eq eqCodeFn (carcT (consT (tcFn h) W2)) (tcFn h)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  have hbase : Prf (provFromCode (eqCodeFn (carcT (consT (tcFn h) (tcFn t))) (tcFn h))) :=
    prf_mp (prf_provCode_congr hchain)
      (pcc_axiom_inst2 φ (show ax_carc ∈ axioms by simp [axioms]) (tcFn h) (tcFn t))
  -- ⬇ AQUÍ estaba `prf_tc_cons'`. Ahora: reescritura INTERNA con `pcc_dot_cons`.
  refine pcc_rw (fun s => eqc (carcT s) (tcFn h)) ?_ _ _ (pcc_dot_cons h t) hbase
  intro s
  refine prf_eq_trans (prf_substfc_eq zero s (carcT (varc (numeral 0))) (tcFn h)) ?_
  exact prf_congr_eqCodeFn
    (prf_eq_trans (prf_substtc_carcT zero s (varc (numeral 0)))
      (prf_congr_carcT (prf_substtc_varc0 s)))
    (prf_substtc_tcFn s h)

end CarcPayoff

#print axioms CarcPayoff.pcc_eval_carc

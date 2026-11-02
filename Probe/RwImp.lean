/- La forma IMPLICACIÓN de `pcc_rw`: hace falta porque los sitios de `EvalNthcPrf`
   viven dentro de `PrfH` (con hipótesis), y allí no vale un `Prf → Prf`. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf

namespace RwImpDev

/-- **`pcc_rw` en forma IMPLICACIÓN.** Mismo contrato que `pcc_rw`, pero devolviendo la
    implicación en vez de consumir la base: eso es lo que permite usarlo **dentro de `PrfH`**
    (vía `PrfH.mp` + `prf_to_prfH`), donde la base lleva hipótesis y no es un `Prf` pelado. -/
theorem pcc_rw_imp (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (G X) ⇒ provFromCode (G Y)) := by
  let Ac : Term := G (varc (numeral 0))
  -- (1) Leibniz codificado, ya aplicado a la igualdad: `Prov(⌜Ac[X] ⇒ Ac[Y]⌝)`
  have himp : Prf (provFromCode (implc (substfc zero X Ac) (substfc zero Y Ac))) :=
    pcc_mp_code_apply (pcc_leibniz_code Ac X Y) heq
  -- (2) abrir el `implc` a implicación REAL
  have hopen : Prf (provFromCode (substfc zero X Ac) ⇒ provFromCode (substfc zero Y Ac)) :=
    prf_mp (pcc_mp_code_open _ _) himp
  -- (3) normalizar los dos `substfc` a `G X` / `G Y`
  refine prf_deduction ?_
  have h1 : PrfH [provFromCode (G X)] (provFromCode (substfc zero X Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hG X))) _)
      (prfH_hyp_self (provFromCode (G X)))
  have h2 : PrfH [provFromCode (G X)] (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH hopen _) h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hG Y)) _) h2

/-- Control: `pcc_rw` se recupera de `pcc_rw_imp` con un `prf_mp`. -/
theorem pcc_rw' (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : Prf (provFromCode (eqc X Y)))
    (hbase : Prf (provFromCode (G X))) :
    Prf (provFromCode (G Y)) :=
  prf_mp (pcc_rw_imp G hG X Y heq) hbase

end RwImpDev

#print axioms RwImpDev.pcc_rw_imp

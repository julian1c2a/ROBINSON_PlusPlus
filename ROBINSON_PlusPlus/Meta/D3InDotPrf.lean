/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.D3DottedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.D3DottedPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.D3InDotPrf

/-!
## META — NIVEL D real (§38): reflexión PUNTEADA del átomo `In` (`hI_dot`, ruta B)

Segundo de los dos átomos punteados del cuerpo Δ₀ de `provCodeC' φ` (tras `chainOk`): dado
`chainOk nil p` e `In ⌜φ⌝ (runFn nil p)` (con `p = #0` **libre**), producir
`provFromCode (inDot φ)` — el código del átomo `In ⌜φ⌝ (runFn nil ṗ)` con `p` dotado (`ṗ = tcFn #0`).

Estrategia (análoga a `pcc_lt_tracked`, pero con la implicación objeto **codificada**):

1. `In ⌜φ⌝ (runFn nil p) ⇒ boundedCarcIn ⌜φ⌝ p` (`prf_boundedCarcIn_of_In_runFn`): pasar al `∃`
   acotado `∃i<lenc p. carc(nthc p i) = ⌜φ⌝`.
2. Reflejar ese `∃` acotado DOTADO (`pcc_bdEx_intro_open`, testigo `tcFn i`), con la cota vía
   `pcc_lt_tracked`+`pcc_eval_lenc` y el cuerpo vía `pcc_eq_tracked`+`pcc_eval_carc_nthc`+`prf_tc_form`
   (aquí entra `chainOk`, que `pcc_eval_carc_nthc` necesita).
3. Codificar la implicación objeto `boundedCarcIn ⌜φ⌝ p ⇒ In ⌜φ⌝ (runFn nil p)` (`pcc_thm_inst` del
   teorema generalizado) y MP interno (`pcc_mp_code_open`) para llegar a `provFromCode (inDot φ)`.
-/

/-- **`∃i<B`-intro a nivel de código, versión OPEN** (sin clausura de `B`/`Phic`): admite cotas y
    cuerpos con variables objeto **libres** (necesario para `p` dotado, `B = lencT (liftc 0 ṗ)`).
    Sólo pide `hBinv` (`substtc`-invariancia de `B`); la `∃`-intro interna es la abierta
    (`pcc_exIntro_code_open`), que no requiere `liftTerm`-invariancia. -/
theorem pcc_bdEx_intro_open (B Phic K : Term)
    (hBinv : ∀ W, Prf (substtc zero W B =eq B))
    (hlt : Prf (provFromCode (ltCodeFn K B)))
    (hphi : Prf (provFromCode (substfc zero K Phic))) :
    Prf (provFromCode (bdExCode B Phic)) := by
  have hand : Prf (provFromCode (andc (ltCodeFn K B) (substfc zero K Phic))) :=
    pcc_and_intro_code hlt hphi
  have hsub : Prf (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic)
      =eq andc (ltCodeFn K B) (substfc zero K Phic)) :=
    prf_eq_trans (prf_substfc_and zero K _ _)
      (prf_congr_andc (prf_substfc_ltCodeFn_varc0 B K hBinv) (prf_refl _))
  have hant : Prf (provFromCode (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic))) :=
    prf_mp (prf_provCode_congr (prf_eq_symm hsub)) hand
  exact prf_mp (pcc_exIntro_code_open (andc (ltCodeFn (varc (numeral 0)) B) Phic) K) hant

end ROBINSON_PlusPlus.Meta.D3InDotPrf

export ROBINSON_PlusPlus.Meta.D3InDotPrf (
  pcc_bdEx_intro_open
)

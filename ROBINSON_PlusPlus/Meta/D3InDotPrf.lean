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
open ROBINSON_PlusPlus.Meta.DerivCondPrf
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

/-! ### Step A — la implicación ⇐ CODIFICADA (`boundedCarcIn ⌜φ⌝ ṗ ⇒ In ⌜φ⌝ (runFn nil ṗ)`)

El teorema objeto `prf_In_runFn_of_boundedCarcIn ⌜φ⌝ #0` se generaliza (`Prf.gen`) y se instancia
DOTADO (`pcc_thm_inst`, testigo `tcFn #0`). Distribuyendo `substfc` sobre el `implc`
(`prf_substfc_impl`), el consecuente es **exactamente `inDot φ`** (por definición de `inDot`) y el
antecedente es `bddCarcDot φ` (código dotado de `boundedCarcIn`). -/

/-- Cuerpo objeto de la implicación ⇐ (con `p = #0`): `boundedCarcIn ⌜φ⌝ #0 ⇒ In ⌜φ⌝ (runFn nil #0)`. -/
noncomputable def inBwdBody (φ : Formula) : Formula :=
  Formula.impl (boundedCarcIn (formCode φ) (.var 0)) (In (formCode φ) (runFn nil (.var 0)))

/-- Código DOTADO del antecedente `boundedCarcIn ⌜φ⌝ #0` (con `p = #0 ↦ tcFn #0`). -/
noncomputable def bddCarcDot (φ : Formula) : Term :=
  substfc zero (tcFn (.var 0)) (formCode (boundedCarcIn (formCode φ) (.var 0)))

/-- **Step A**: `⊢ Prov(⌜ bddCarcDot φ ⇒ inDot φ ⌝)`. Instancia dotada del teorema ⇐, con `substfc`
    distribuido sobre el `implc`; el consecuente coincide con `inDot φ` por definición. -/
theorem pcc_bddDot_imp_inDot (φ : Formula) :
    Prf (provFromCode (implc (bddCarcDot φ) (inDot φ))) := by
  have hthm : Prf (provFromCode (substfc zero (tcFn (.var 0)) (formCode (inBwdBody φ)))) :=
    pcc_thm_inst (inBwdBody φ) (Prf.gen _ (prf_In_runFn_of_boundedCarcIn (formCode φ) (.var 0)))
      (tcFn (.var 0))
  have hbridge : Prf (substfc zero (tcFn (.var 0)) (formCode (inBwdBody φ))
      =eq implc (bddCarcDot φ) (inDot φ)) :=
    prf_substfc_impl zero (tcFn (.var 0)) (formCode (boundedCarcIn (formCode φ) (.var 0)))
      (formCode (In (formCode φ) (runFn nil (.var 0))))
  exact prf_mp (prf_provCode_congr hbridge) hthm

/-! ### Step B (puente) — `bddCarcDot φ` como `bdExCode` con argumentos DOTADOS

El código dotado del antecedente `boundedCarcIn` es un `∃` acotado codificado (`bdExCode`) con:
* cota `bdCarcB = lencT (liftc 0 ṗ)` (el `liftc 0` viene del binder de `substfc`);
* cuerpo `bdCarcPhic φ = eqCodeFn (carcT (nthcT (liftc 0 ṗ) ⌜v₀⌝)) ⌜φ⌝` (con `⌜φ⌝ = termCode (formCode φ)`,
  reducido vía `substCodeT_closed`).

Establece `bddCarcDot φ =eq bdExCode bdCarcB (bdCarcPhic φ)`: `prf_substfc_arith_open` lleva la forma
`substfc` a `substCodeF`, y `substCodeF_boundedCarcIn` (ecuación META, rfl salvo la reducción del
`formCode φ` cerrado) la identifica con `bdExCode`. -/

/-- Cota (dotada, bajo el binder) del `∃` acotado de `boundedCarcIn`: `lencT (liftc 0 ṗ)`. -/
noncomputable def bdCarcB : Term := lencT (liftc zero (tcFn (.var 0)))

/-- Cuerpo (dotado) del `∃` acotado: `carcT (nthcT (liftc 0 ṗ) ⌜v₀⌝) = ⌜φ⌝`. -/
noncomputable def bdCarcPhic (φ : Formula) : Term :=
  eqCodeFn (carcT (nthcT (liftc zero (tcFn (.var 0))) (varc (numeral 0)))) (termCode (formCode φ))

/-- **Forma META del código dotado de `boundedCarcIn`** (rfl salvo `substCodeT_closed` sobre el
    `formCode φ` cerrado): `substCodeF 0 ṗ (boundedCarcIn ⌜φ⌝ #0) = bdExCode bdCarcB (bdCarcPhic φ)`. -/
theorem substCodeF_boundedCarcIn (φ : Formula) :
    substCodeF 0 (tcFn (.var 0)) (boundedCarcIn (formCode φ) (.var 0))
      = bdExCode bdCarcB (bdCarcPhic φ) := by
  have key : substCodeT 1 (liftc zero (tcFn (.var 0))) (liftTerm 0 (formCode φ))
      = termCode (formCode φ) := by
    rw [liftTerm_formCode]
    exact substCodeT_closed 1 (liftc zero (tcFn (.var 0))) (formCode φ)
      (fun c => liftTerm_formCode c φ)
  simp only [boundedCarcIn, land, lt, lenc, carc, nthc, liftTerm, liftTerms, Nat.lt_irrefl,
    reduceIte, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, substCodeF, substCodeT,
    substCodeTs, bdExCode, bdCarcB, bdCarcPhic, exc, andc, numeral, ltCodeFn, atom2CodeFn, eqCodeFn,
    lencT, carcT, nthcT, funcc, varc, key]

/-- **`bddCarcDot φ` es `bdExCode` con argumentos dotados** (versión `Prf`): compone
    `prf_substfc_arith_open` (forma `substfc` → `substCodeF`) con `substCodeF_boundedCarcIn`. -/
theorem prf_bddCarcDot_eq (φ : Formula) :
    Prf (bddCarcDot φ =eq bdExCode bdCarcB (bdCarcPhic φ)) := by
  have h := prf_substfc_arith_open 0 (tcFn (.var 0)) (boundedCarcIn (formCode φ) (.var 0))
  rwa [substCodeF_boundedCarcIn φ] at h

end ROBINSON_PlusPlus.Meta.D3InDotPrf

export ROBINSON_PlusPlus.Meta.D3InDotPrf (
  pcc_bdEx_intro_open inBwdBody bddCarcDot pcc_bddDot_imp_inDot
  bdCarcB bdCarcPhic substCodeF_boundedCarcIn prf_bddCarcDot_eq
)

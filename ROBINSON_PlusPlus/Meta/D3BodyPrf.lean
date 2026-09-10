/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.D3ChainDotPrf
import ROBINSON_PlusPlus.Meta.SubstTreeReflect

/-!
# D3 · el CUERPO del chasis, mitad (a) — la reflexión de `lineWF`

`Meta/D3ChainDotPrf.lean` §13 partió el `hbody` de `pcc_bdAll_intro` en sus dos mitades. Ésta es
la **(a)**: la reflexión del átomo `lineWF`, que quedó desbloqueada el 2026‑09‑10 al cerrarse los
**siete** reflectores de sustitución (`Meta/SubstTreeReflect.lean` §10bis, con
`prf_hasWitF_liftfc`).

⚠️ **Módulo aparte, y a propósito**: junta `D3ChainDotPrf` (que fija el destino) con
`SubstTreeReflect` (que prueba el reflector), y ninguno de los dos importa al otro. Meterlo en
cualquiera de ellos crearía una dependencia que hoy no existe.

## Las tres cosas que pasan aquí

1. **`chainOk → chainOkB`** y `∀`‑elim en `i`: de la cadena válida sale `lineWF (nthc q i)`.
2. **El reflector**, `pcc_lineWF_tracked_modulo_other`, que da `Prov(⌜lineWF (nthc q i)⌝)` con el
   código en forma de **reflexión pura** `(nthc q i)˙`.
3. ⚠️ **La MONEDA** (§3.55.2 otra vez): el destino pide el **ACCESOR dotado** `nthcT q̇ i̇`, no la
   reflexión pura. El salto lo paga `pcc_eval_nthc` **dentro de `Prov`**, con el Leibniz
   codificado; y el `liftc` que el binder impone **colapsa** (`prf_liftc_tcFn`).

**Footprint**: la base sancionada.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.SubstTreeReflect
open ROBINSON_PlusPlus.Meta.D3ChainDotPrf

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace ROBINSON_PlusPlus.Meta.D3BodyPrf


/-- El hueco de `lineWFCodeFn`, como pide `pcc_rw_imp`. -/
theorem hG_lineWF (s : Term) :
    Prf (substfc zero s (lineWFCodeFn (varc (numeral 0))) =eq lineWFCodeFn s) := by
  unfold lineWFCodeFn atom1CodeFn
  refine prf_eq_trans (prf_substfc_atom zero s (strCode "lineWF")
    (cons (varc (numeral 0)) nil)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  exact prf_eq_trans (prf_substtsc_cons zero s (varc (numeral 0)) nil)
    (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 s))
      (prf_congr_cons_tail (prf_substtsc_nil zero s)))

theorem hwG_lineWF : Prf (hasWitF (lineWFCodeFn (varc (numeral 0)))) :=
  prf_hasWitF_atom1 (strCode "lineWF") (varc (numeral 0)) (prf_hasWit_varc (numeral 0))

/-- ⭐ **`hbody`(a) de D3**: la reflexión del átomo `lineWF`, ya instanciada en el cuerpo. -/
theorem hA_lineWFDotAt (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ provFromCode (lineWFDotAt q i))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  -- (1) `chainOk → chainOkB`, y la línea `i` es buena
  have hB : PrfH [lt i (lenc q), chainOk nil q] (chainOkB nil q) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_chainOk_iff_chainOkB nil q)) _) hch
  have hB' : PrfH [lt i (lenc q), chainOk nil q]
      (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))) := hB
  have hspec := PrfH_spec hB' i
  have heq : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))
      = Formula.impl (lt i (lenc q)) (lineOkB nil q i) := by
    simp only [substFormula, substFormula_lineOkB, lt, lenc, nil, zero, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  rw [heq] at hspec
  have hline : PrfH [lt i (lenc q), chainOk nil q] (lineWF (nthc q i)) :=
    PrfH_and_elim_left (PrfH.mp _ _ _ hspec hlt)
  -- (2) el reflector de `lineWF`, ya cerrado para los SIETE tags
  have hprov : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (lineWFCodeFn (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (pcc_lineWF_tracked (nthc q i)) _) hline
  -- (3) la MONEDA: el destino pide el ACCESOR dotado, no la reflexión pura
  have hev : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hsym : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i))
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
      (prf_hasWit_tcFn (nthc q i))) _) hev
  -- el Leibniz codificado, aplicado DENTRO del contexto `PrfH`
  have hleib : Prf (provFromCode (implc
      (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))
      (implc (substfc zero (tcFn (nthc q i)) (lineWFCodeFn (varc (numeral 0))))
             (substfc zero (nthcT (tcFn q) (tcFn i)) (lineWFCodeFn (varc (numeral 0))))))) :=
    pcc_leibniz_code (lineWFCodeFn (varc (numeral 0)))
      (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)) hwG_lineWF
      (prf_hasWit_tcFn (nthc q i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
  have h2 := PrfH_mp_code_apply (prf_to_prfH hleib _) hsym
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_implc
    (hG_lineWF (tcFn (nthc q i))) (hG_lineWF (nthcT (tcFn q) (tcFn i))))) _) h2
  have hrw : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (lineWFCodeFn (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_mp_code_apply h3 hprov
  -- (4) y el `liftc` del binder COLAPSA
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_atom1CodeFn
    (prf_congr_nthcT (prf_eq_symm (prf_liftc_tcFn q)) (prf_refl _)))) _) hrw


end ROBINSON_PlusPlus.Meta.D3BodyPrf

/-! ## `export` — por CONSUMO

El consumidor previsto es el ensamblaje de D3: `d3_prf_of_halves` (`D3ChainDotPrf` §13) pide
exactamente `hA` y `hB`, y ésta es `hA`. -/
export ROBINSON_PlusPlus.Meta.D3BodyPrf (
  hG_lineWF hwG_lineWF hA_lineWFDotAt
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.D3BodyPrf.hA_lineWFDotAt

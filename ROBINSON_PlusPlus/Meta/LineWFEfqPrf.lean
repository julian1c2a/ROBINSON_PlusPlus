/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeCtorKit

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFEfqPrf

/-!
## META — NIVEL D real (B.3c): tag `efq` (8) — **PILOTO del chasis + kit**

Primer tag cerrado **a través** de `pcc_lineWF_tracked_of_schema` + `CodeCtorKit`, en vez de a mano.
Sirve de medida del coste real por tag antes del batch de los 17 restantes.

`efq` es el más simple de los estructurales: su árbol es `implc botc (nthc #0 2)`, o sea
`binT 5 (nulT 2) ·` — un binario cuyo primer argumento es un nulario **cerrado**, luego sólo hay
**un** hueco que reflejar.

Lo que este módulo tiene que aportar (y que el chasis no puede factorizar) es exactamente el
reflector `hcond` de esa condición: sus dos piezas son `prf_condDEfq_eq` (evaluación del código
punteado) y `pcc_condDEfq` (su producción dentro de `Prov`).
-/

/-- La condición estructural de `efq`: `carc #0 = implc ⊥ (nthc #0 2)`. -/
def condEfq : Formula :=
  carc (.var 0) =eq implc botc (nthc (.var 0) (numeralM 2))

/-- El esquema estricto de `efq`, reexpresado con las piezas del chasis (definicional). -/
theorem ax_lineWF_efq_eq :
    ax_lineWF_efq
      = Formula.forall (Formula.impl (tagF 8) (lwfVar ⇔ Formula.and (lencF 3) condEfq)) := rfl

/-- Obligación administrativa del chasis: la condición sólo menciona `#0`. -/
theorem substFormula_condEfq : substFormula 0 (.var 0) condEfq = condEfq := rfl

/-- La condición instanciada en una línea concreta `t`. -/
theorem substFormula_condEfq_at (t : Term) :
    substFormula 0 t condEfq = (carc t =eq implc botc (nthc t (numeralM 2))) := by
  simp only [condEfq, carc, nthc, implc, botc, numeralM, succ, zero, cons, nil,
    substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]

/-! ### La parte propia del tag (1): el código punteado, EVALUADO

`implc a b` es `⟨5,a,b⟩` y `botc` es `⟨2⟩`, luego el árbol de código es `binT 5 (nulT 2) ·` y toda
la distribución de `substtc` sale del kit. -/

/-- **`COND_dot` de `efq` evaluado**:
    `substfc 0 ṫ ⌜carc #0 = implc ⊥ (nthc #0 2)⌝ = ⌜carc ṫ = implc ⊥ (nthc ṫ 2̇)⌝`. -/
theorem prf_condDEfq_eq (t : Term) :
    Prf (condD condEfq t =eq
      eqCodeFn (carcT (tcFn t))
        (binT 5 (nulT 2) (nthcT (tcFn t) (termCode (numeralM 2))))) := by
  unfold condD condEfq
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ ?_
  · exact prf_eq_trans (prf_substtc_carcT zero (tcFn t) _)
      (prf_congr_carcT (prf_substtc_varc0 (tcFn t)))
  · refine prf_eq_trans (prf_substtc_binT 5 (tcFn t) _ _) ?_
    refine prf_congr_binT (prf_substtc_nulT 2 (tcFn t)) ?_
    exact prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _)
      (prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
        (substtc_inv_termCode_numeralM 2 (tcFn t)))

/-! ### La parte propia del tag (2): la PRODUCCIÓN dentro de `Prov`

Cadena: puente `carc` → reescritura del valor por la hipótesis (vía `prf_tc_bin`/`prf_tc_nul`) →
puente `nthc` bajo la cota → congruencia interna del kit → transitividad interna. -/

/-- **`Prov(COND_dot t)`** para `efq`. -/
theorem pcc_condDEfq (t : Term) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM 3) ⇒
      (substFormula 0 t condEfq ⇒ provFromCode (condD condEfq t)))) := by
  rw [substFormula_condEfq_at]
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (carc t =eq implc botc (nthc t (numeralM 2)))
    [lenc t =eq numeralM 3, lineWF t] rfl)
    (lenc t =eq numeralM 3) [lineWF t] rfl)
  let Γ : List Formula := [carc t =eq implc botc (nthc t (numeralM 2)),
    lenc t =eq numeralM 3, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hlenc : PrfH Γ (lenc t =eq numeralM 3) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hEQ : PrfH Γ (carc t =eq implc botc (nthc t (numeralM 2))) := PrfH.hyp _ _ (List.Mem.head _)
  -- abreviaturas
  let V : Term := tcFn (nthc t (numeralM 2))
  let N : Term := nthcT (tcFn t) (termCode (numeralM 2))
  -- (1) puente `carc`
  have hcarc : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (tcFn (carc t)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge t) _) hlw
  -- (2) la hipótesis reescribe el VALOR. Tres tramos: el `tcFn`-congruente sigue siendo de CÓDIGO,
  --     y los dos pasos del KIT (`bin` y `nul`) se cruzan DENTRO de `Prov`.
  have hCinv : ∀ W, Prf (substtc zero W (carcT (tcFn t)) =eq carcT (tcFn t)) := fun W =>
    prf_eq_trans (prf_substtc_carcT zero W (tcFn t))
      (prf_congr_carcT (substtc_inv_tcFn t W))
  have hG : ∀ s : Term, Prf (substfc zero s (eqCodeFn (carcT (tcFn t)) (varc (numeral 0)))
      =eq eqCodeFn (carcT (tcFn t)) s) := fun s =>
    prf_eq_trans (prf_substfc_eq zero s (carcT (tcFn t)) (varc (numeral 0)))
      (prf_congr_eqCodeFn (hCinv s) (prf_substtc_varc0 s))
  -- (2a) CÓDIGO: `(carc t)˙ = (implc botc (nthc t 2))˙`
  have hcarc1 : PrfH Γ (provFromCode (eqc (carcT (tcFn t))
      (tcFn (implc botc (nthc t (numeralM 2)))))) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn hEQ)) hcarc
  -- (2b) INTERNO: `(implc botc X)˙ ⟶ binT 5 (botc)˙ Ẋ`
  have hstep1 : Prf (provFromCode (eqc (carcT (tcFn t))
        (tcFn (implc botc (nthc t (numeralM 2)))))
      ⇒ provFromCode (eqc (carcT (tcFn t)) (binT 5 (tcFn botc) V))) :=
    pcc_rw_imp (fun s => eqCodeFn (carcT (tcFn t)) s) hG _ _
      (pcc_dot_bin_symm 5 botc (nthc t (numeralM 2)))
  have hcarc1b : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (binT 5 (tcFn botc) V))) :=
    PrfH.mp _ _ _ (prf_to_prfH hstep1 _) hcarc1
  -- (2c) INTERNO: `(botc)˙ ⟶ nulT 2`, con el hueco en el 1.er argumento de `binT`
  have hGb : ∀ s : Term, Prf (substfc zero s
      (eqCodeFn (carcT (tcFn t)) (binT 5 (varc (numeral 0)) V))
      =eq eqCodeFn (carcT (tcFn t)) (binT 5 s V)) := fun s =>
    prf_eq_trans (prf_substfc_eq zero s (carcT (tcFn t)) (binT 5 (varc (numeral 0)) V))
      (prf_congr_eqCodeFn (hCinv s)
        (prf_eq_trans (prf_substtc_binT 5 s (varc (numeral 0)) V)
          (prf_congr_binT (prf_substtc_varc0 s) (substtc_inv_tcFn _ s))))
  have hstep2 : Prf (provFromCode (eqc (carcT (tcFn t)) (binT 5 (tcFn botc) V))
      ⇒ provFromCode (eqc (carcT (tcFn t)) (binT 5 (nulT 2) V))) :=
    pcc_rw_imp (fun s => eqCodeFn (carcT (tcFn t)) (binT 5 s V)) hGb _ _
      (pcc_dot_nul_symm 2)
  have hcarc2 : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (binT 5 (nulT 2) V))) :=
    PrfH.mp _ _ _ (prf_to_prfH hstep2 _) hcarc1b
  -- (3) puente `nthc` bajo la cota derivada de la longitud canónica
  have hb2 : PrfH Γ (lt (numeralM 2) (lenc t)) :=
    PrfH_lt_of_lenc_eq (i := 2) (n := 3) (by omega) hlenc
  have hevN : PrfH Γ (provFromCode (eqc N V)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_nthcD_bridge t 2) _) hb2
  -- (4) congruencia interna del kit: `Prov(binT 5 (nulT 2) V = binT 5 (nulT 2) N)`
  have hNinv : ∀ W, Prf (substtc zero W N =eq N) := substtc_inv_nthcT_tcFn t 2
  have hcongr : PrfH Γ (provFromCode (eqc (binT 5 (nulT 2) V) (binT 5 (nulT 2) N))) :=
    PrfH.mp _ _ _
      (prf_to_prfH (pcc_congr_binT_2_code 5 (nulT 2) V N
        (substtc_inv_nulT 2) (substtc_inv_tcFn _)) _)
      (PrfH_eq_symm_code N V hNinv hevN)
  -- (5) transitividad interna + vuelta a la forma `substfc`
  have hfin : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (binT 5 (nulT 2) N))) :=
    PrfH_eq_trans_code (carcT (tcFn t)) (binT 5 (nulT 2) V) (binT 5 (nulT 2) N)
      (substtc_inv_carcT_tcFn t) hcarc2 hcongr
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_condDEfq_eq t))) _) hfin

/-! ### El tag, cerrado por el CHASIS -/

/-- **Reflector por rama, caso `efq`** — obtenido instanciando el chasis genérico. Compárese con
    `pcc_lineWF_tracked_eqrefl_imp` (≈ 45 líneas a mano): aquí el ensamblaje es **una llamada**. -/
theorem pcc_lineWF_tracked_efq_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 8) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t substFormula_condEfq
    (ax_lineWF_efq_eq ▸ prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms]))
    (pcc_condDEfq t) (by omega)

end ROBINSON_PlusPlus.Meta.LineWFEfqPrf

export ROBINSON_PlusPlus.Meta.LineWFEfqPrf (
  condEfq ax_lineWF_efq_eq substFormula_condEfq substFormula_condEfq_at
  prf_condDEfq_eq pcc_condDEfq pcc_lineWF_tracked_efq_imp
)

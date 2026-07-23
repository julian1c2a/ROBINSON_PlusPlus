/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.LineWFPropPrf
import ROBINSON_PlusPlus.Meta.LineWFThyPrf
import ROBINSON_PlusPlus.Meta.LineWFMpPrf
import ROBINSON_PlusPlus.Meta.LineWFEfqPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFThyPrf
open ROBINSON_PlusPlus.Meta.LineWFMpPrf
open ROBINSON_PlusPlus.Meta.LineWFEfqPrf
open ROBINSON_PlusPlus.Meta.LineWFPropPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFAssemblePrf

/-!
## META — NIVEL D real (B.3c): ENSAMBLAJE `or_elim` ×21 de `pcc_lineWF_tracked`

**Propósito: verificación de encaje.** Los 7 tags que faltan (`q1` `q2` `q3` `leibniz` `ind`
`qconf` `listInd`) están bloqueados tras una cadena larga (`pcc_eval_substfc` ⟵ inducción fuerte
⟵ monotonía de Cantor ⟵ aritmética de `·`). Antes de invertir en esa cadena conviene comprobar
que **todo lo demás encaja**: que con los 21 reflectores por rama se obtiene efectivamente
`pcc_lineWF_tracked`, y que su enunciado es el que `hC_dot` consume.

Este módulo lo hace: construye el ensamblaje **genérico** y lo instancia dejando los 7 pendientes
como **hipótesis explícitas**. Si compila (y compila), el único trabajo restante para cerrar
`pcc_lineWF_tracked` son esos 7 reflectores — nada más aguas abajo.

**La estructura.** `ax_lineWF_inv` da `lineWF L ⇒ tagDisj L 20`, con
`tagDisj L (n+1) = (lineTag L = ṅ₊₁) ∨ tagDisj L n` — una disyunción anidada a derecha, de 20 a 0.
El ensamblador recorre esa estructura **por recursión sobre `n`**, así que vale para cualquier
número de tags y no hay que escribir 21 `or_elim` a mano.
-/

/-- **Ensamblador genérico**: si cada disyunto `lineTag t = k̇` (para `k ≤ n`) implica `C`,
    entonces `tagDisj t n` implica `C`. Recursión sobre la estructura de `tagDisj`. -/
theorem prf_of_tagDisj (t : Term) (C : Formula)
    (hbranch : ∀ k : Nat, Prf ((lineTag t =eq numeralM k) ⇒ C)) :
    ∀ n : Nat, Prf (tagDisj t n ⇒ C)
  | 0 => hbranch 0
  | n + 1 => by
      -- `tagDisj t (n+1) = (lineTag t = ṅ₊₁) ∨ tagDisj t n`; `j3` pide la disyunción PRIMERO,
      -- así que se descarga por deducción y se aplica en contexto
      have hrec : Prf (tagDisj t n ⇒ C) := prf_of_tagDisj t C hbranch n
      show Prf (lor (lineTag t =eq numeralM (n + 1)) (tagDisj t n) ⇒ C)
      refine prf_deduction ?_
      exact PrfH.mp _ _ _
        (PrfH.mp _ _ _
          (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 (lineTag t =eq numeralM (n + 1))
            (tagDisj t n) C)) (prfH_hyp_self _))
          (prf_to_prfH (hbranch (n + 1)) _))
        (prf_to_prfH hrec _)

/-- Permuta los dos antecedentes de una implicación anidada. -/
theorem prf_swap_imp {A B C : Formula} (h : Prf (A ⇒ (B ⇒ C))) : Prf (B ⇒ (A ⇒ C)) := by
  refine prf_deduction (deduction_aux ?_ A [B] rfl)
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH h _) (PrfH.hyp _ _ (List.Mem.head _)))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

/-- **`pcc_lineWF_tracked` GENÉRICO**: dado un reflector para cada tag, la reflexión punteada del
    átomo `lineWF` sale por inversión + el ensamblador. Es el enunciado que consume `hC_dot`. -/
theorem pcc_lineWF_tracked_of_branches (t : Term)
    (hbranch : ∀ k : Nat, Prf (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t))))) :
    Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t))) := by
  -- se permutan los antecedentes para que el ensamblador (que va sobre el tag) quede fuera
  have hall : Prf (tagDisj t 20 ⇒
      (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
    prf_of_tagDisj t _ (fun k => prf_swap_imp (hbranch k)) 20
  refine prf_deduction ?_
  have hdisj : PrfH [lineWF t] (tagDisj t 20) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_inv t) _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hall _) hdisj) (prfH_hyp_self _)

/-! ### Instanciación: los 14 reflectores reales + los 7 pendientes como hipótesis

Los `k` fuera de `0..20` no ocurren en `tagDisj t 20`, pero el ensamblador los pide por
uniformidad; se cubren con la misma hipótesis genérica (`hOther`), que en la instanciación real
será vacua. -/

/-- **`pcc_lineWF_tracked`, MÓDULO los 7 tags pendientes.**

    Verifica el encaje: con los 14 reflectores ya construidos (`eqrefl` `thy` `mp` `efq` `gen`
    y los 9 proposicionales) **y** los 7 que faltan como hipótesis, el átomo `lineWF` queda
    reflejado. ⟹ cerrar `pcc_lineWF_tracked` es **exactamente** cerrar esos 7 reflectores;
    no hay ninguna otra pieza aguas abajo.

    Los 7 pendientes (`q1`=9, `q2`=10, `q3`=11, `leibniz`=13, `ind`=18, `qconf`=19, `listInd`=20)
    están bloqueados tras `pcc_eval_substfc` (ver `NEXT-STEPS.md`, ruta 1a). -/
theorem pcc_lineWF_tracked_modulo_7 (t : Term)
    (hq1 : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hq2 : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 10) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hq3 : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 11) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hleibniz : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 13) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hind : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 18) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hqconf : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 19) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hlistInd : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 20) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hOther : ∀ k : Nat, Prf (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t))))) :
    Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t))) := by
  refine pcc_lineWF_tracked_of_branches t (fun k => ?_)
  match k with
  | 0  => exact pcc_lineWF_tracked_p1_imp t
  | 1  => exact pcc_lineWF_tracked_p2_imp t
  | 2  => exact pcc_lineWF_tracked_c1_imp t
  | 3  => exact pcc_lineWF_tracked_c2_imp t
  | 4  => exact pcc_lineWF_tracked_c3_imp t
  | 5  => exact pcc_lineWF_tracked_j1_imp t
  | 6  => exact pcc_lineWF_tracked_j2_imp t
  | 7  => exact pcc_lineWF_tracked_j3_imp t
  | 8  => exact pcc_lineWF_tracked_efq_imp t
  | 9  => exact hq1
  | 10 => exact hq2
  | 11 => exact hq3
  | 12 => exact pcc_lineWF_tracked_eqrefl_imp t
  | 13 => exact hleibniz
  | 14 => exact pcc_lineWF_tracked_p3_imp t
  | 15 => exact pcc_lineWF_tracked_thy_imp t
  | 16 => exact pcc_lineWF_tracked_mp_imp t
  | 17 => exact pcc_lineWF_tracked_gen_imp t
  | 18 => exact hind
  | 19 => exact hqconf
  | 20 => exact hlistInd
  | n + 21 => exact hOther (n + 21)

end ROBINSON_PlusPlus.Meta.LineWFAssemblePrf

export ROBINSON_PlusPlus.Meta.LineWFAssemblePrf (
  prf_swap_imp prf_of_tagDisj pcc_lineWF_tracked_of_branches pcc_lineWF_tracked_modulo_7
)

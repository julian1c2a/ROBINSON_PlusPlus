/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.GodelTwo
import ROBINSON_PlusPlus.Meta.PremsBdAllPrf
import ROBINSON_PlusPlus.Meta.DiagonalNumeral
import ROBINSON_PlusPlus.Meta.DiagonalTwo
import ROBINSON_PlusPlus.Meta.LineWFCases
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.Representability2Prf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.ReprPrf

/-!
# 🏁🏁 GÖDEL II SOBRE EL CÁLCULO FINITARIO `Prf`

## Por qué este módulo existe: la auditoría del 2026‑09‑11, hallazgo **F‑1**

`Meta/GodelTwo.lean` tiene `goedel_second'`, y está **montado pero NO ensamblado**: su hipótesis
es `hgi : ¬ (axioms ⊢ G)` —el cálculo **ω**— mientras Gödel I entrega `¬ Prf godelCN` —el
**finitario**—. Por `prf_to_derives` la primera es **estrictamente más fuerte**, y **no existe** la
vuelta `⊢ → Prf`.

⛔⛔ **Y la medición posterior es peor que eso**: `axioms ⊢` es **sintácticamente COMPLETO**
(`Meta/OmegaStrength.lean`): decide toda sentencia, porque `raa` toma como premisa una **función de
Lean** y la no‑derivabilidad se convierte en derivabilidad de la negación. Un cálculo que decide
todo **no puede** ser el sujeto de un teorema de incompletitud ⇒ `goedel_second'` **no es** el
Segundo Teorema.

## ⇒ Lo que sí lo es, y está aquí

    goedel_second_prf (hcon : ConsistentOmega) : ¬ Prf consistencyFormula'

**Sobre `Prf`, el cálculo finitario, y con UNA sola hipótesis** — la misma consistencia que pide
Gödel I. **Ninguna hipótesis suelta**: el punto fijo y la necesitación se **descargan aquí**.

## Lo que hizo falta, y es poco porque el espejo `Prf` ya estaba

* **§1** la lógica proposicional que faltaba: `prf_subst_eq_iff` (Leibniz con `⇔`, directo del
  axioma `Prf₀.leibniz`), `prf_iff_trans`, `prf_neg_congr_iff`.
* **§2** el **punto fijo** sobre `Prf`: puerto directo de `diag_arith_num` usando las piezas que ya
  existían (`prf_congr_substfc_arg2/3`, `prf_tc_numeral`, `prf_substFormula_arith`,
  `prf_formCode_numeral`). ⭐ **`prf_godelCN_fixedpoint` es net‑0 PURO**: no usa **ningún** axioma
  del proyecto.
* **§3** `Con' ⇒ G` sobre `Prf`: el mismo argumento, con `prf_deduction`/`deduction_aux` en lugar
  del meta‑axioma `imp_intro`. Usa **D2** (`d2_prf`) y **D3** (`d3_prf_real`), las dos ya sobre `Prf`.
* **§4** el ensamblaje, con **D1** (`repr_pos'_prf`) descargando la necesitación.

**Footprint**: los tres de Lean + las ω‑reglas ambiente (entran por `goedel_first_numeral`, cuya
hipótesis `ConsistentOmega` habla de `⊢`) + `ax_induction_prim`, `ax_list_induction` y las dos
anclas de codificación. **Ningún postulado gödeliano.**
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.DiagonalNumeral
open ROBINSON_PlusPlus.Meta.DiagonalTwo
open ROBINSON_PlusPlus.Meta.GodelTwo
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.PremsBdAllPrf

namespace ROBINSON_PlusPlus.Meta.GodelTwoPrf


/-! ## §1 · Lógica proposicional que falta sobre `Prf` -/

theorem prf_subst_eq_iff {t₁ t₂ : Term} (φ : Formula) (h : Prf (t₁ =eq t₂)) :
    Prf (substFormula 0 t₁ φ ⇔ substFormula 0 t₂ φ) :=
  prf_and_intro
    (prf_mp (Prf.incl (Prf₀.leibniz φ t₁ t₂)) h)
    (prf_mp (Prf.incl (Prf₀.leibniz φ t₂ t₁)) (prf_eq_symm h))

theorem prf_iff_trans {A B C : Formula} (h₁ : Prf (A ⇔ B)) (h₂ : Prf (B ⇔ C)) :
    Prf (A ⇔ C) :=
  prf_and_intro
    (prf_imp_trans (prf_and_elim_left h₁) (prf_and_elim_left h₂))
    (prf_imp_trans (prf_and_elim_right h₂) (prf_and_elim_right h₁))

theorem prf_neg_congr_iff {B C : Formula} (h : Prf (B ⇔ C)) : Prf (neg B ⇔ neg C) :=
  prf_and_intro
    (prf_deduction (ROBINSON_PlusPlus.Meta.HilbertDeduction.deduction_aux
      (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_right h) _)
          (PrfH.hyp _ _ (List.Mem.head _))))
      C [neg B] rfl))
    (prf_deduction (ROBINSON_PlusPlus.Meta.HilbertDeduction.deduction_aux
      (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left h) _)
          (PrfH.hyp _ _ (List.Mem.head _))))
      B [neg C] rfl))

/-! ## §2 · El PUNTO FIJO sobre `Prf` -/

theorem prf_hFN (φ : Formula) : Prf (numeral (codeNat φ) =eq formCode φ) :=
  prf_eq_symm (prf_formCode_numeral φ)

theorem prf_diag_arith_num (ψ : Formula) :
    Prf (substTerm 0 (numeral (codeNat ψ)) diagTerm =eq numeral (codeNat (selfAppN ψ))) := by
  have p1 : Prf (substfc (numeral 0) (tcFn (numeral (codeNat ψ))) (numeral (codeNat ψ)) =eq
                 substfc (numeral 0) (termCode (numeral (codeNat ψ))) (numeral (codeNat ψ))) :=
    prf_congr_substfc_arg2 (prf_tc_numeral (codeNat ψ))
  have p2 : Prf (substfc (numeral 0) (termCode (numeral (codeNat ψ))) (numeral (codeNat ψ)) =eq
                 substfc (numeral 0) (termCode (numeral (codeNat ψ))) (formCode ψ)) :=
    prf_congr_substfc_arg3 (prf_hFN ψ)
  have p3 : Prf (substfc (numeral 0) (termCode (numeral (codeNat ψ))) (formCode ψ) =eq
                 formCode (substFormula 0 (numeral (codeNat ψ)) ψ)) :=
    prf_substFormula_arith 0 (numeral (codeNat ψ)) ψ
  have p4 : Prf (formCode (selfAppN ψ) =eq numeral (codeNat (selfAppN ψ))) :=
    prf_formCode_numeral (selfAppN ψ)
  exact prf_eq_trans p1 (prf_eq_trans p2 (prf_eq_trans p3 p4))

theorem prf_godelCN_fixedpoint_N : Prf (godelCN ⇔ neg (provCodeN godelCN)) := by
  have hiff := prf_subst_eq_iff godelPred' (prf_diag_arith_num godelBeta')
  rw [← godel_comp' (numeral (codeNat godelBeta'))] at hiff
  simpa only [godelCN, selfAppN, godelPred', provCodeN, neg, substFormula] using hiff

theorem prf_provCode_transfer (φ : Formula) : Prf (provCodeN φ ⇔ provCodeC' φ) :=
  prf_subst_eq_iff provFormulaC' (prf_hFN φ)

/-- 🏁 **EL PUNTO FIJO SOBRE EL CÁLCULO FINITARIO.** -/
theorem prf_godelCN_fixedpoint : Prf (godelCN ⇔ neg (provCodeC' godelCN)) :=
  prf_iff_trans prf_godelCN_fixedpoint_N (prf_neg_congr_iff (prf_provCode_transfer godelCN))

/-! ## §3 · `Con' ⇒ G` sobre `Prf` -/

theorem prf_con_imp_godel (G : Formula)
    (fp_bwd : Prf (neg (provCodeC' G) ⇒ G))
    (nec1 : Prf (provCodeC' (G ⇒ neg (provCodeC' G)))) :
    Prf (consistencyFormula' ⇒ G) := by
  have step_a : Prf (provCodeC' G ⇒ provCodeC' (neg (provCodeC' G))) :=
    prf_mp (d2_prf G (neg (provCodeC' G))) nec1
  have step_b : Prf
      (provCodeC' G ⇒ (provCodeC' (provCodeC' G) ⇒ provCodeC' Formula.bottom)) :=
    prf_deduction (PrfH.mp _ _ _
      (prf_to_prfH (d2_prf (provCodeC' G) Formula.bottom) _)
      (PrfH.mp _ _ _ (prf_to_prfH step_a _) (prfH_hyp_self _)))
  have pg_imp_pbot : Prf (provCodeC' G ⇒ provCodeC' Formula.bottom) :=
    prf_deduction (PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH step_b _) (prfH_hyp_self _))
      (PrfH.mp _ _ _ (prf_to_prfH (d3_prf_real G) _) (prfH_hyp_self _)))
  refine prf_deduction (PrfH.mp _ _ _ (prf_to_prfH fp_bwd _) ?_)
  exact ROBINSON_PlusPlus.Meta.HilbertDeduction.deduction_aux
    (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (PrfH.mp _ _ _ (prf_to_prfH pg_imp_pbot _) (PrfH.hyp _ _ (List.Mem.head _))))
    (provCodeC' G) [consistencyFormula'] rfl

/-! ## §4 · 🏁 GÖDEL II SOBRE EL CÁLCULO FINITARIO, sin hipótesis sueltas -/

theorem goedel_second_prf (hcon : ConsistentOmega) : ¬ Prf consistencyFormula' := by
  intro hC
  refine goedel_first_numeral hcon (prf_mp (prf_con_imp_godel godelCN ?_ ?_) hC)
  · exact prf_and_elim_right prf_godelCN_fixedpoint
  · exact repr_pos'_prf (prf_and_elim_left prf_godelCN_fixedpoint)

end ROBINSON_PlusPlus.Meta.GodelTwoPrf

/-! ## `export` — por CONSUMO -/
export ROBINSON_PlusPlus.Meta.GodelTwoPrf (
  prf_subst_eq_iff prf_iff_trans prf_neg_congr_iff
  prf_diag_arith_num prf_godelCN_fixedpoint
  prf_con_imp_godel goedel_second_prf
)

/-! ## FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint
#print axioms ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezVerificador
import ROBINSON_PlusPlus.Meta.PurezaComando

/-!
# `Meta/GodelCorolarios.lean` — los corolarios de libro de Gödel II (T78, ADR‑162)

**Qué.** Tres resultados clásicos que faltaban, con D1–D3 y el punto fijo de `G`:

* **`prf_godel_iff_con : Prf (G ⇔ Con')`** — la sentencia de Gödel y la consistencia son equivalentes EN la teoría.
  La mitad `Con' ⇒ G` ya era `prf_con_imp_godel`; la otra, `G ⇒ Con'`, sale de D1 sobre `⊥ ⇒ G`, D2 y el punto fijo
  (`prf_godel_imp_con`).
* **`goedel_second_formalizado : Prf (Con' ⇒ ¬Prov⌜Con'⌝)`** — Gödel II DENTRO de la teoría: de `Prov⌜Con'⌝` sale
  `Prov⌜G⌝` (D1 sobre `Con' ⇒ G`, y D2), y de `Con'`, `G`, que niega `Prov⌜G⌝`.
* **`con_indecidible`** — `Con'` es indecidible: `¬ Prf Con'` (`goedel_II`) y `¬ Prf ¬Con'`, porque `Con'` es
  VERDADERA en `MNV V₀` (`con_verdadera`) y `Prf` es sólida. Es de la clase (iii): usa la verdad en el modelo, no sólo
  la consistencia (T+¬Con es consistente y demuestra ¬Con').

**Controles.** `goedel_second_de_formalizado`: con D1, la versión formalizada da la de siempre (`goedel_second_prf`),
así que no es vacua. Y el `#pureza` del final: los dos primeros, PUROS; `con_indecidible`, IMPURO, como se espera.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.DiagonalNumeral
open ROBINSON_PlusPlus.Meta.GodelTwo ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf ROBINSON_PlusPlus.Meta.PremsBdAllPrf

namespace ROBINSON_PlusPlus.Meta.GodelCorolarios

/-- `G ⇒ Con'`: de `G`, `¬Prov⌜G⌝` (el punto fijo); y `Prov⌜⊥⌝ ⇒ Prov⌜G⌝` (D1 sobre `⊥ ⇒ G`, y D2). -/
theorem prf_godel_imp_con : Prf (godelCN ⇒ consistencyFormula') := by
  have h1 : Prf (provCodeC' Formula.bottom ⇒ provCodeC' godelCN) :=
    prf_mp (d2_prf Formula.bottom godelCN) (repr_pos'_prf (Prf.incl (Prfᵢ.efq godelCN)))
  refine prf_deduction ?_
  show PrfH [godelCN] (provCodeC' Formula.bottom ⇒ Formula.bottom)
  refine deduction_aux ?_ (provCodeC' Formula.bottom) [godelCN] rfl
  have hP : PrfH [provCodeC' Formula.bottom, godelCN] (provCodeC' Formula.bottom) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hG : PrfH [provCodeC' Formula.bottom, godelCN] godelCN :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left prf_godelCN_fixedpoint) _) hG)
    (PrfH.mp _ _ _ (prf_to_prfH h1 _) hP)

/-- 🏁 **`G ⇔ Con'` en la teoría.** -/
theorem prf_godel_iff_con : Prf (godelCN ⇔ consistencyFormula') :=
  prf_and_intro prf_godel_imp_con
    (prf_con_imp_godel godelCN (prf_and_elim_right prf_godelCN_fixedpoint)
      (repr_pos'_prf (prf_and_elim_left prf_godelCN_fixedpoint)))

/-- 🏁 **Gödel II formalizado**: la teoría demuestra que, si es consistente, no demuestra su consistencia. -/
theorem goedel_second_formalizado : Prf (consistencyFormula' ⇒ neg (provCodeC' consistencyFormula')) := by
  have hcg : Prf (consistencyFormula' ⇒ godelCN) := prf_and_elim_right prf_godel_iff_con
  have h1 : Prf (provCodeC' consistencyFormula' ⇒ provCodeC' godelCN) :=
    prf_mp (d2_prf consistencyFormula' godelCN) (repr_pos'_prf hcg)
  refine prf_deduction ?_
  show PrfH [consistencyFormula'] (provCodeC' consistencyFormula' ⇒ Formula.bottom)
  refine deduction_aux ?_ (provCodeC' consistencyFormula') [consistencyFormula'] rfl
  have hP : PrfH [provCodeC' consistencyFormula', consistencyFormula'] (provCodeC' consistencyFormula') :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hC : PrfH [provCodeC' consistencyFormula', consistencyFormula'] consistencyFormula' :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hG := PrfH.mp _ _ _ (prf_to_prfH hcg _) hC
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left prf_godelCN_fixedpoint) _) hG)
    (PrfH.mp _ _ _ (prf_to_prfH h1 _) hP)

/-- ✅ **El formalizado no es vacuo**: con D1, da el de siempre (el enunciado de `goedel_second_prf`). -/
theorem goedel_second_de_formalizado (hcon : ConsistentH) : ¬ Prf consistencyFormula' :=
  fun hC => hcon (prf_mp (prf_mp goedel_second_formalizado hC) (repr_pos'_prf hC))

/-- 🏁 **`Con'` es INDECIDIBLE**: `goedel_II`, y `¬ Prf ¬Con'` porque `Con'` es verdadera en `MNV V₀` y `Prf` es
    sólida. Clase (iii): la consistencia sola no basta (T+¬Con es consistente y demuestra ¬Con'). Desde ADR‑191, por la
    solidez doble‑negada: `Con'` es `¬Prov(⌜⊥⌝)`, tiene `P`, y lo verdadero con `P` no se refuta (`no_refuta`). -/
theorem con_indecidible : And (¬ Prf consistencyFormula') (¬ Prf (neg consistencyFormula')) := by
  refine ⟨ROBINSON_PlusPlus.Meta.Consistencia.goedel_II, ?_⟩
  have e : ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
      (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' Formula.bottom) =
      ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
        ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC' := by
    rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas_subst]
  have hP : (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
      consistencyFormula').1 = true := by
    rw [consistencyFormula', neg]
    simp only [ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas, e]
    rfl
  exact ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.no_refuta ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada hP
    (fun _ => 0) (ROBINSON_PlusPlus.Meta.SolidezVerificador.con_verdadera (fun _ => 0))

end ROBINSON_PlusPlus.Meta.GodelCorolarios

#print axioms ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_imp_con
#print axioms ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con
#print axioms ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado
#print axioms ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible

/-! T08 en el módulo: los corolarios sintácticos no nombran la semántica; `con_indecidible`, que usa la verdad en
    `MNV V₀`, sí. -/
#pureza ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_imp_con ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con
  ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado
  ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_de_formalizado
  | ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible

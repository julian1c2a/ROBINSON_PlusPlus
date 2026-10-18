/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.PurezaComando

/-!
# `Meta/Lob.lean` — 🏁 LÖB: si T demuestra Prov⌜φ⌝ ⇒ φ, demuestra φ (ADR‑140, T70, ADR‑159)

**Qué.** `lob φ : Prf (provCodeC' φ ⇒ φ) → Prf φ`, y su forma completa, `lob_iff`: T demuestra la reflexión
Prov⌜φ⌝ ⇒ φ exactamente para sus teoremas. Es el segundo consumidor de D1–D3, tras Gödel II.

* **§1** La sentencia de Löb de φ, `lobSent φ`: el punto fijo (`prf_diagonal`, ADR‑121) del predicado
  `Prov(#0) ⇒ φ`, con φ subida un nivel para que `#0` sea sólo el código. `prf_lob_fix`: L ⇔ (Prov⌜L⌝ ⇒ φ), con el
  código de `formCode` (el del numeral pasa por `prf_provCode_transfer`).
* **§2** El argumento de siempre, con D1 (`repr_pos'_prf`), D2 (`d2_prf`) y D3 (`d3_prf_real`): de L ⇒ (Prov⌜L⌝ ⇒ φ),
  por D1 y D2, Prov⌜L⌝ ⇒ Prov⌜Prov⌜L⌝ ⇒ φ⌝; por D2 y D3, Prov⌜L⌝ ⇒ Prov⌜φ⌝; con la hipótesis, Prov⌜L⌝ ⇒ φ; por el
  punto fijo, L; por D1, Prov⌜L⌝; y φ.
* **§3** Los controles: Gödel II sale de Löb con φ = ⊥ (`goedel_second_de_lob`, el mismo enunciado que
  `goedel_second_prf`); la hipótesis puede valer (los teoremas: `lob_iff`) y puede fallar (φ = ⊥ y φ = G, con
  `consistencia`).

⛔ Ningún numeral se evalúa: ⌜L⌝ = `numeral (codeNat (lobSent φ))` sólo se mueve por `rw` con lemas ∀.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.GodelTwoPrf
open ROBINSON_PlusPlus.Meta.TarskiPrf ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.PremsBdAllPrf

namespace ROBINSON_PlusPlus.Meta.Lob

/-! ## §1 · La sentencia de Löb -/

/-- El predicado de Löb de φ: `Prov(#0) ⇒ φ`, con φ subida un nivel (`liftFormula 0`), así que la sustitución de
    `#0` por un código la devuelve intacta. -/
def lobPred (φ : Formula) : Formula := Formula.impl provFormulaC' (liftFormula 0 φ)

/-- 🏁 **La sentencia de Löb de φ**: el punto fijo de `lobPred φ`. -/
noncomputable def lobSent (φ : Formula) : Formula := selfAppN (diagBeta (lobPred φ))

theorem subst_lobPred (φ : Formula) (c : Term) :
    substFormula 0 c (lobPred φ) = Formula.impl (substFormula 0 c provFormulaC') φ := by
  show Formula.impl (substFormula 0 c provFormulaC') (substFormula 0 c (liftFormula 0 φ)) = _
  rw [FOL.substFormula_liftFormula]

/-- Cambiar el antecedente de una implicación por otro equivalente en T. -/
theorem prf_imp_congr_left_iff {A A' B : Formula} (h : Prf (A ⇔ A')) : Prf ((A ⇒ B) ⇔ (A' ⇒ B)) := by
  refine prf_and_intro ?_ ?_
  · refine prf_deduction (deduction_aux ?_ A' [A ⇒ B] rfl)
    exact PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_right h) _) (PrfH.hyp _ _ (List.Mem.head _)))
  · refine prf_deduction (deduction_aux ?_ A [A' ⇒ B] rfl)
    exact PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left h) _) (PrfH.hyp _ _ (List.Mem.head _)))

/-- El punto fijo: `L ⇔ (Prov⌜L⌝ ⇒ φ)`, con el código de `formCode`, el de D1–D3. -/
theorem prf_lob_fix (φ : Formula) : Prf (lobSent φ ⇔ (provCodeC' (lobSent φ) ⇒ φ)) := by
  have fp : Prf (lobSent φ ⇔ substFormula 0 (numeral (codeNat (lobSent φ))) (lobPred φ)) :=
    prf_diagonal (lobPred φ)
  rw [subst_lobPred] at fp
  exact prf_iff_trans fp (prf_imp_congr_left_iff (prf_provCode_transfer (lobSent φ)))

/-! ## §2 · LÖB -/

/-- 🏁 **LÖB**: si T demuestra Prov⌜φ⌝ ⇒ φ, demuestra φ. -/
theorem lob (φ : Formula) (h : Prf (provCodeC' φ ⇒ φ)) : Prf φ := by
  have fp := prf_lob_fix φ
  -- D1 y D2 sobre la ida del punto fijo: Prov⌜L⌝ ⇒ Prov⌜Prov⌜L⌝ ⇒ φ⌝
  have a : Prf (provCodeC' (lobSent φ) ⇒ provCodeC' (provCodeC' (lobSent φ) ⇒ φ)) :=
    prf_mp (d2_prf (lobSent φ) (provCodeC' (lobSent φ) ⇒ φ)) (repr_pos'_prf (prf_and_elim_left fp))
  -- D2 y D3, y la hipótesis: Prov⌜L⌝ ⇒ φ
  have b : Prf (provCodeC' (lobSent φ) ⇒ φ) := by
    refine prf_deduction ?_
    have hL := prfH_hyp_self (provCodeC' (lobSent φ))
    have h1 := PrfH.mp _ _ _ (prf_to_prfH a _) hL
    have h2 := PrfH.mp _ _ _ (prf_to_prfH (d2_prf (provCodeC' (lobSent φ)) φ) _) h1
    have h3 := PrfH.mp _ _ _ (prf_to_prfH (d3_prf_real (lobSent φ)) _) hL
    exact PrfH.mp _ _ _ (prf_to_prfH h _) (PrfH.mp _ _ _ h2 h3)
  -- la vuelta del punto fijo da L; D1, Prov⌜L⌝; y φ
  exact prf_mp b (repr_pos'_prf (prf_mp (prf_and_elim_right fp) b))

/-- 🏁 **Löb, entero**: T demuestra la reflexión Prov⌜φ⌝ ⇒ φ exactamente para sus teoremas. -/
theorem lob_iff (φ : Formula) : Prf (provCodeC' φ ⇒ φ) ↔ Prf φ :=
  ⟨lob φ, fun h => prf_mp (Prf.incl (Prfᵢ.p1 φ (provCodeC' φ))) h⟩

/-! ## §3 · Los controles -/

/-- ✅ **El corolario de T70**: Gödel II sale de Löb con φ = ⊥, porque `consistencyFormula'` ES Prov⌜⊥⌝ ⇒ ⊥. Es el
    enunciado de `goedel_second_prf`, por otro camino. -/
theorem goedel_second_de_lob (hcon : ConsistentH) : ¬ Prf ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun hC => hcon (lob Formula.bottom hC)

/-- ✅ La hipótesis puede FALLAR: T no demuestra su reflexión para ⊥ (con `consistencia`; es Gödel II). -/
theorem control_reflexion_bot : ¬ Prf (provCodeC' Formula.bottom ⇒ Formula.bottom) :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (lob Formula.bottom h)

/-- ✅ Ni para la sentencia de Gödel: T no demuestra Prov⌜G⌝ ⇒ G (Löb y Gödel I). -/
theorem control_reflexion_godel : ¬ Prf (provCodeC' godelCN ⇒ godelCN) :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (lob godelCN h)

/-- ✅ Y puede VALER: para un teorema, la reflexión es teorema (la dirección fácil de `lob_iff`). -/
theorem control_reflexion_teorema :
    Prf (provCodeC' (Formula.bottom ⇒ Formula.bottom) ⇒ (Formula.bottom ⇒ Formula.bottom)) :=
  (lob_iff _).2 (Prf.incl (prfI_id Formula.bottom))

end ROBINSON_PlusPlus.Meta.Lob

#print axioms ROBINSON_PlusPlus.Meta.Lob.prf_lob_fix
#print axioms ROBINSON_PlusPlus.Meta.Lob.lob
#print axioms ROBINSON_PlusPlus.Meta.Lob.lob_iff
#print axioms ROBINSON_PlusPlus.Meta.Lob.goedel_second_de_lob

/-! T08 en el módulo: Löb no nombra la semántica; los dos controles que descargan la consistencia con
    `consistencia` (directamente, o por `goedel_I`), sí. -/
#pureza ROBINSON_PlusPlus.Meta.Lob.prf_lob_fix ROBINSON_PlusPlus.Meta.Lob.lob ROBINSON_PlusPlus.Meta.Lob.lob_iff
  ROBINSON_PlusPlus.Meta.Lob.goedel_second_de_lob ROBINSON_PlusPlus.Meta.Lob.control_reflexion_teorema
  | ROBINSON_PlusPlus.Meta.Lob.control_reflexion_bot ROBINSON_PlusPlus.Meta.Lob.control_reflexion_godel

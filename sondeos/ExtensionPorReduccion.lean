/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · T+E por REDUCCIÓN a T: el cálculo de una extensión finita y su predicado de prueba, sin tocar el verificador

**Fecha:** 2026‑10‑16 · **Por qué:** ADR‑144, el ADR de diseño de T62. ADR‑137 eligió para Rosser la teoría como
parámetro del VERIFICADOR (opción a‑ii): `lineWF g`, `chainOk g`, `PrfL Γ`. Este sondeo comprueba que lo que el
enunciado de Rosser necesita de una extensión finita T+E sale ya del árbol, sin parametrizar nada:

* **El cálculo de T+E** es `PrfH E`, el de `Meta/HilbertDeduction.lean`: `Prf` con las hipótesis E.
* **Por el teorema de deducción**, `PrfH E φ ↔ Prf (impChain E φ)`, con `impChain E φ` = E en implicaciones delante de
  φ (§1).
* **El código de `impChain E φ`** es el de φ con un término de `implc` delante (§2). Por eso el predicado de prueba de
  T+E puede DEFINIRSE con el de T: Pf_E(y, x) := Pf_T(y, `impChainC E x`), y un numeral es prueba de φ en T+E sii lo
  es de `impChain E φ` en T. Así PosNum y NegNum de T dan los de toda T+E. Esa parte NO está aquí: PosNum y NegNum
  todavía no existen.
* **Los controles de CRI‑02** (§3): la hipótesis «T+E es consistente» puede FALLAR (E = [⊥]) y puede VALER en una
  extensión NO sólida, T+¬Con, donde la solidez no puede sustituir a la consistencia.

**Ámbito.** Es un sondeo de viabilidad: no hay Rosser ni el predicado Pf_E como fórmula. El control de T+¬Con usa
`goedel_II`, que pasa por el modelo; es un CONTROL del enunciado, no un titular, y T08 no se le aplica.

**Resultado de la ejecución del 2026‑10‑16:** en ADR‑144 §3.

✏️ **2026‑10‑18 (ADR‑157):** todo, promovido a `Meta/Rosser.lean` (§1, §2 y §6), donde ya hay Rosser y el predicado
Pf_E (`PfE`). Este sondeo sigue de CONTROL, con sus copias en su propio espacio de nombres; qué se hace con él es T66.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Provability

namespace ExtensionPorReduccion

/-! ## §1 · El cálculo de T+E, por deducción -/

/-- E en implicaciones delante de φ, en el orden en que el teorema de deducción las descarga: la cabeza de E queda
    más ADENTRO. `impChain [e₁, e₂] φ = e₂ ⇒ (e₁ ⇒ φ)`. -/
def impChain : List Formula → Formula → Formula
  | [], φ => φ
  | e :: E, φ => impChain E (e ⇒ φ)

/-- De T+E a T: `PrfH E φ → Prf (impChain E φ)`, descargando las hipótesis una a una (`deduction_aux`). -/
theorem prf_impChain_of_prfH : ∀ (E : List Formula) {φ : Formula}, PrfH E φ → Prf (impChain E φ)
  | [], _, h => prfH_nil_to_prf h rfl
  | e :: E, _, h => prf_impChain_of_prfH E (deduction_aux h e E rfl)

/-- Y de vuelta, en cualquier contexto que contenga E: con las hipótesis y MP. -/
theorem prfH_of_impChain (Γ : List Formula) :
    ∀ (E : List Formula) {φ : Formula}, (∀ e, List.Mem e E → List.Mem e Γ) → PrfH Γ (impChain E φ) → PrfH Γ φ
  | [], _, _, h => h
  | e :: E, φ, hsub, h =>
      have h' : PrfH Γ (e ⇒ φ) :=
        prfH_of_impChain Γ E (fun x hx => hsub x (List.Mem.tail e hx)) h
      PrfH.mp Γ e φ h' (PrfH.hyp Γ e (hsub e (List.Mem.head E)))

/-- ⭐ **El cálculo de T+E ES el de T, por reducción:** `PrfH E φ ↔ Prf (impChain E φ)`. -/
theorem prfH_iff_prf_impChain (E : List Formula) (φ : Formula) : PrfH E φ ↔ Prf (impChain E φ) :=
  ⟨prf_impChain_of_prfH E, fun h => prfH_of_impChain E E (fun _ hx => hx) (prf_to_prfH h E)⟩

/-! ## §2 · El código: el de φ, con un término delante -/

/-- El código de `impChain E φ` como TÉRMINO con un hueco `x` en lugar del código de φ. -/
def impChainC : List Formula → Term → Term
  | [], x => x
  | e :: E, x => impChainC E (ROBINSON_PlusPlus.Minimal.Axioms.implc (formCode e) x)

/-- ⭐ `formCode (impChain E φ) = impChainC E (formCode φ)`, por definición. Es lo que deja DEFINIR el predicado de
    prueba de T+E con el de T: el hueco `x` es una variable de la fórmula, y al sustituir `⌜φ⌝` sale el código de
    `impChain E φ` sin calcular nada. -/
theorem formCode_impChain : ∀ (E : List Formula) (φ : Formula), formCode (impChain E φ) = impChainC E (formCode φ)
  | [], _ => rfl
  | e :: E, φ => by
      have hc : formCode (e ⇒ φ) = ROBINSON_PlusPlus.Minimal.Axioms.implc (formCode e) (formCode φ) := rfl
      show formCode (impChain E (e ⇒ φ)) = impChainC E (ROBINSON_PlusPlus.Minimal.Axioms.implc (formCode e) (formCode φ))
      rw [← hc]
      exact formCode_impChain E (e ⇒ φ)

/-! ## §3 · Los controles de CRI‑02: la hipótesis de Rosser para T+E puede fallar, y puede valer sin solidez -/

/-- T+[⊥] es INCONSISTENTE: la hipótesis «T+E es consistente» puede fallar. -/
theorem inconsistente_bottom : PrfH [Formula.bottom] Formula.bottom :=
  PrfH.hyp _ _ (List.Mem.head _)

/-- T+¬Con es CONSISTENTE, por Gödel II y el teorema de deducción: de `PrfH [¬Con] ⊥` saldría `Prf (¬¬Con)`, y
    con DNE `Prf Con`, contra `goedel_II`. No es sólida: demuestra ¬Con, que es FALSA en el modelo (`con_verdadera`).
    Así que en este miembro la solidez no puede sustituir a la consistencia. -/
theorem consistente_neg_con :
    ¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula'] Formula.bottom := by
  intro h
  have hnn : Prf (neg (neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula')) :=
    (prfH_iff_prf_impChain _ _).1 h
  exact ROBINSON_PlusPlus.Meta.Consistencia.goedel_II
    (Prf.mp _ _ (Prf.p3 ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula') hnn)

end ExtensionPorReduccion

#print axioms ExtensionPorReduccion.prfH_iff_prf_impChain
#print axioms ExtensionPorReduccion.formCode_impChain
#print axioms ExtensionPorReduccion.inconsistente_bottom
#print axioms ExtensionPorReduccion.consistente_neg_con

-- T08 (ADR‑143): la reducción es SINTÁCTICA; `consistente_neg_con`, el control, pasa por el modelo (`goedel_II`).
#pureza ExtensionPorReduccion.prfH_iff_prf_impChain ExtensionPorReduccion.formCode_impChain | ExtensionPorReduccion.consistente_neg_con

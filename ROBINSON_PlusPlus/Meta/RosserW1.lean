/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezVerificador
import ROBINSON_PlusPlus.Meta.PurezaTitulares

/-!
# `Meta/RosserW1.lean` — Rosser, etapa W1(ax): W1 SIN el modelo (ADR‑146, ADR‑147, ADR‑148)

**Qué.** `ProofN m y`, el espejo en ℕ del predicado de prueba de T: el verificador acepta la cadena `m` con el código
de los 142 —`codeNatList axioms`— y `y` es una de sus conclusiones. **`w1Ax`**: lo que concluye, decodificado, es
teorema de `Prf`.

**Por qué así.** W1 (`verificador_solido`, `Meta/SolidezVerificador.lean`) habla de `V₀`, el valor de `axiomsCodeT`
en el modelo, y de `V₀` sólo se sabe que es el código de los 142 por la solidez (`V₀_eq_codigo`): por eso W1 es
IMPURO para T08. La cadena es la misma para cualquier `V` cuyos miembros, decodificados, sean teoremas (`cadena_buena`,
paramétrica desde ADR‑148), y `codeNatList axioms` lo es por construcción (`bueno_codeNatList`). Rosser usa la
contrapositiva: si `¬ Prf ¬R`, ningún numeral es prueba de `¬R` (NegNum' = `negNum ∘ w1Ax`, ADR‑146 §1).

**Controles** (ADR‑146 §4). `proofN_axioma`: la hipótesis puede VALER, con la cadena de una línea `thy` que cita un
axioma; con `w1Ax` da el axioma (`w1Ax_axioma`). `not_proofN_zero`: puede FALLAR, porque la cadena vacía no concluye
nada. Y el `#pureza` del final: `w1Ax` y los controles no nombran la semántica, y `verificador_solido` —la misma
cadena, en `V₀`— SÍ la nombra.

⛔ Ningún código se evalúa: `codeNatList axioms` y `codeNat a` sólo se mueven por `rw` con lemas ∀ (ADR‑130).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.ModeloCodigo
open ROBINSON_PlusPlus.Meta.SolidezVerificador

namespace ROBINSON_PlusPlus.Meta.RosserW1

/-- El espejo en ℕ del predicado de prueba de T (ADR‑146 §1): la cadena `m` es correcta con el CÓDIGO de los 142
    —`codeNatList axioms`, no `V₀`— y concluye `y`. -/
def ProofN (m y : Nat) : Prop := And (chainOkN (codeNatList axioms) 0 m) (memN y (runFnN 0 m))

/-- 🏁 **W1(ax)**: lo que concluye una cadena correcta con el código de los 142, decodificado, es teorema de `Prf`.
    Sin el modelo: `cadena_buena` con `bueno_codeNatList`. -/
theorem w1Ax {m y : Nat} (h : ProofN m y) : Prf (dec y) :=
  cadena_buena bueno_codeNatList (decodeL m) 0 bueno_zero h.1 y h.2

/-! ## Los controles: la hipótesis de `w1Ax` puede valer y puede fallar -/

/-- La otra mitad de `memN_codeNatList`: el código de un miembro de `L` está en `codeNatList L`. -/
theorem memN_codeNatList_of_mem {a : Formula} :
    ∀ {L : List Formula}, List.Mem a L → memN (codeNat a) (codeNatList L)
  | _ :: _, List.Mem.head _ => (memN_consN _ _ _).mpr (Or.inl rfl)
  | _ :: _, List.Mem.tail _ h => (memN_consN _ _ _).mpr (Or.inr (memN_codeNatList_of_mem h))

/-- La línea `thy` que cita la fórmula `a`: `⟨⌜a⌝, 15⟩`. -/
def lineaThy (a : Formula) : Nat := consN (codeNat a) (consN 15 0)

/-- ✅ La hipótesis de `w1Ax` puede VALER: la cadena de una sola línea `thy` que cita un axioma. -/
theorem proofN_axioma {a : Formula} (ha : List.Mem a axioms) :
    ProofN (consN (lineaThy a) 0) (codeNat a) := by
  have hc : carN (lineaThy a) = codeNat a := carN_consN _ _
  have hk : nthN (lineaThy a) 1 = 15 := by rw [lineaThy, nthN_cs, nthN_cz]
  have hl : lenN (lineaThy a) = 2 := by rw [lineaThy, lenN_consN, lenN_consN, lenN_zero]
  have hp : premsOfN (lineaThy a) = 0 := by
    rw [premsOfN, if_neg (by rw [hk]; decide), if_neg (by rw [hk]; decide)]
  have hT : lineWFT (codeNatList axioms) 15 (lineaThy a) :=
    And.intro hl (by rw [hc]; exact memN_codeNatList_of_mem ha)
  refine And.intro ?_ ?_
  · rw [chainOkN_consN]
    refine And.intro (And.intro ((lineWFN_of_tag hk (by decide)).mpr hT) ?_) (chainOkN_zero _ _)
    rw [hp]
    exact allInN_zero _
  · rw [runFnN_consN, runFnN_zero, concatN_zero, hc]
    exact (memN_consN _ _ _).mpr (Or.inl rfl)

/-- ✅ Con `w1Ax`, esa cadena da el axioma: la conclusión de `w1Ax` dice algo. -/
theorem w1Ax_axioma {a : Formula} (ha : List.Mem a axioms) : Prf a := by
  have h := w1Ax (proofN_axioma ha)
  rw [dec_codeNat] at h
  exact h

/-- ✅ La hipótesis de `w1Ax` puede FALLAR: la cadena vacía no concluye nada. -/
theorem not_proofN_zero (y : Nat) : ¬ ProofN 0 y := by
  intro h
  have h2 := h.2
  rw [runFnN_zero] at h2
  exact memN_zero y h2

end ROBINSON_PlusPlus.Meta.RosserW1

#print axioms ROBINSON_PlusPlus.Meta.RosserW1.w1Ax
#print axioms ROBINSON_PlusPlus.Meta.RosserW1.proofN_axioma
#print axioms ROBINSON_PlusPlus.Meta.RosserW1.not_proofN_zero

/-! T08 en el módulo (ADR‑147): lo de esta etapa no nombra la semántica; `verificador_solido`, la misma cadena en `V₀`,
    sí. Si un paso de aquí pasara por el modelo, el build fallaría en este módulo. -/
#pureza ROBINSON_PlusPlus.Meta.RosserW1.w1Ax ROBINSON_PlusPlus.Meta.RosserW1.proofN_axioma
  ROBINSON_PlusPlus.Meta.RosserW1.w1Ax_axioma ROBINSON_PlusPlus.Meta.RosserW1.not_proofN_zero
  | ROBINSON_PlusPlus.Meta.SolidezVerificador.verificador_solido

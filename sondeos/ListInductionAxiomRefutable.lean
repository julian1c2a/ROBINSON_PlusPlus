/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · L1‑2 — `ax_list_induction` sola da `axioms ⊢ ⊥` (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1, L1‑2): ¿es explotable el `axiom ax_list_induction`
(`Full/Lists.lean:79-82`)? ADR‑029 lo dio por saneado («vacuidad explotable: no»).

## 🏁 Respuesta, COMPILADA: sí, con dos constructores

Su `φ : Term → Formula` es una FUNCIÓN de Lean, que puede mirar la sintaxis del término, y su `Γ` es libre.
Con `φ (.var _) := ⊥` y `φ (.func _ _) := ⊥ ⇒ ⊥`, la base y el paso salen con `intro_impl` + `hyp`, porque
`nil` y `cons h t` son aplicaciones; la conclusión en `L := #0` es `[] ⊢ ⊥`.

    theorem nil_bot : [] ⊢ ⊥
    theorem no_consistentOmega : ¬ ConsistentOmega      -- footprint [… , ax_list_induction]

⇒ `axioms ⊢ ⊥`, y con ello son vacuos todos los resultados que suponen `ConsistentOmega` (la cadena ω).
ADR‑113 no lo toca: no depende de la codificación de `cons`.

## Uso

Evidencia del estado del árbol el 2026‑10‑02. Se retira con la capa `⊢` (decisión del propietario del
2026‑10‑02). La refutación PERMANENTE del enunciado, sin usar el axioma, está en
`MetaReglasRefutables.lean` §2 (`ax_list_induction_refutable`).
-/

open FOL ROBINSON_PlusPlus.Minimal.Axioms

namespace Sondeos.ListInductionAxiomRefutable

/-- `φ` que mira la SINTAXIS del término: `⊥` en variables, `⊥ ⇒ ⊥` en aplicaciones. -/
def phiBad : Term → Formula
  | .var _ => Formula.bottom
  | .func _ _ => Formula.impl Formula.bottom Formula.bottom

theorem top_der (Γ : List Formula) : Γ ⊢ Formula.impl Formula.bottom Formula.bottom :=
  Derives.intro_impl _ _ _ (Derives.hyp _ _ (List.Mem.head _))

/-- ⛔⛔ `[] ⊢ ⊥` con el axioma y dos constructores. -/
theorem nil_bot : ([] : List Formula) ⊢ Formula.bottom :=
  ROBINSON_PlusPlus.Full.ax_list_induction (Γ := []) phiBad (top_der [])
    (fun _ t => Derives.intro_impl _ (phiBad t) _ (top_der _)) (.var 0)

theorem no_consistentOmega : Not ROBINSON_PlusPlus.Meta.Hilbert.ConsistentOmega := fun hc =>
  hc (Derives.weakening [] _ _ nil_bot (fun _ hx => absurd hx List.not_mem_nil))

end Sondeos.ListInductionAxiomRefutable

#print axioms Sondeos.ListInductionAxiomRefutable.nil_bot
#print axioms Sondeos.ListInductionAxiomRefutable.no_consistentOmega

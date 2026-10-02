/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · L1‑2 — `ax_list_induction` sola daba `axioms ⊢ ⊥` (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1, L1‑2): ¿es explotable el `axiom ax_list_induction`
(`Full/Lists.lean:79-82`)? ADR‑029 lo dio por saneado («vacuidad explotable: no»).

## 🏁 Respuesta, COMPILADA: sí, con dos constructores

Su `φ : Term → Formula` es una FUNCIÓN de Lean, que puede mirar la sintaxis del término, y su `Γ` es libre.
Con `φ (.var _) := ⊥` y `φ (.func _ _) := ⊥ ⇒ ⊥`, la base y el paso salen con `intro_impl` + `hyp`, porque
`nil` y `cons h t` son aplicaciones; la conclusión en `L := #0` es `[] ⊢ ⊥`. ADR‑113 no lo toca: no depende
de la codificación de `cons`.

## Registro (compilado el 2026‑10‑02 contra RPP `1dac85a`, antes de la retirada)

```lean
theorem nil_bot : ([] : List Formula) ⊢ Formula.bottom :=
  ROBINSON_PlusPlus.Full.ax_list_induction (Γ := []) phiBad (top_der [])
    (fun _ t => Derives.intro_impl _ (phiBad t) _ (top_der _)) (.var 0)
-- [propext, ROBINSON_PlusPlus.Full.ax_list_induction]

theorem no_consistentOmega : Not ROBINSON_PlusPlus.Meta.Hilbert.ConsistentOmega := fun hc =>
  hc (Derives.weakening [] _ _ nil_bot (fun _ hx => absurd hx List.not_mem_nil))
-- [propext, Classical.choice, Quot.sound, ROBINSON_PlusPlus.Full.ax_list_induction]
```

⇒ `axioms ⊢ ⊥`, y con ello eran vacuos todos los resultados que suponían `ConsistentOmega` (la cadena ω).

## Hoy (ADR‑115)

El axioma, `ConsistentOmega` y toda la capa `⊢` de RPP se retiraron el 2026‑10‑02 (decisión del
propietario). Lo que queda, y vale para siempre, es la REDUCCIÓN sin el axioma (`nil_bot_of`, abajo): quien
vuelva a postular ese enunciado obtiene `[] ⊢ ⊥`. Su refutación como enunciado, por solidez booleana, está en
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

/-- ⛔⛔ La REDUCCIÓN, sin el axioma: su enunciado, instanciado en `phiBad`, da `[] ⊢ ⊥`. -/
theorem nil_bot_of
    (H : ∀ {Γ : List Formula} (φ : Term → Formula), (Γ ⊢ φ nil) →
      (∀ h t : Term, Γ ⊢ (φ t ⇒ φ (cons h t))) → ∀ L : Term, Γ ⊢ φ L) :
    ([] : List Formula) ⊢ Formula.bottom :=
  H (Γ := []) phiBad (top_der []) (fun _ t => Derives.intro_impl _ (phiBad t) _ (top_der _)) (.var 0)

end Sondeos.ListInductionAxiomRefutable

#print axioms Sondeos.ListInductionAxiomRefutable.nil_bot_of

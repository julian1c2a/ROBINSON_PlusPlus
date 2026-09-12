/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.OmegaStrength
import FOL.Semantics

/-!
# SONDEO · `prf0_soundness` — la SOLIDEZ de `Prf₀`, y con ella el ancla se vuelve MEDIBLE

**Pregunta que contesta (2026‑09‑11):** *¿se puede decir algo SEMÁNTICO sobre los cálculos de este
proyecto?* De ella dependía la única pregunta abierta sobre `prf_axiomsCodeT_eq`: no «¿es
derivable?» —eso ya estaba medido que no— sino **«¿es siquiera VERDADERO?»**.

## 🏁 Respuesta: SÍ, y sobre `Prf₀` sale gratis

    theorem prf0_soundness {φ} (h : Prf₀ φ) : satisfies axioms φ
    footprint: [propext, Classical.choice, Quot.sound]     ← net‑0 PURO

Los 17 constructores, con la maquinaria semántica de `FOL/Semantics.lean` (`eval_substFormula_zero`,
`eval_liftFormula_zero`, `contextSatisfies_lift_zero`) y `axioms_lift_eq` para el caso `gen`.

⭐ **El hallazgo de método**: `FOL/Semantics.lean` existe desde **mayo**, con 0 `sorry`, y este
proyecto **no lo había importado nunca**. Cuatro agentes independientes midiendo este frente
afirmaron que el árbol no tenía semántica. La tenía. *Antes de construir, buscar.*

## ⛔⛔ Y por qué esto NO se puede hacer sobre `axioms ⊢`

Ésta es la mitad cara del sondeo, y hay que decirla antes que nada:

> **Un teorema de solidez para `Derives` demuestra `False`.** Sin hipótesis.

`Derives` es un `inductive` de 18 constructores, pero **DOCE `axiom`s lo HABITAN** (censo corregido
el 2026‑09‑12: 8 en la librería FOL + 4 en RPP). `FOL/MetaRules.lean` declara **seis `axiom`s
que lo HABITAN** (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) — y tienen que ser axiomas,
porque sus premisas son **funciones de Lean**, ocurrencias negativas que Lean rechazaría en un
`inductive`. ⇒ `Derives` tiene habitantes que **no son aplicaciones de constructor**, y cualquier
teorema probado por `induction` sobre él cubre 18 casos pero **se aplica a todos**.

`FOL` tenía ese teorema (`FOL/Soundness.lean`). Está **en cuarentena** desde el 2026‑09‑11, con la
evidencia compilada en `../../FOL/cuarentena/Inconsistencia.lean` — footprint
`[propext, FOL.MetaRules.raa]`.

🔑 **La regla que queda**: *un `axiom` que habita un tipo inductivo prohíbe demostrar nada sobre ese
tipo por inducción.* En este árbol eso afecta a `Derives` (9 axiomas) y a `Prf` (uno,
`prf_axiomsCodeT_eq`). **`Prf₀` es el único cálculo con CERO** — y por eso es el único del que se
puede decir algo semántico.

## Qué desbloquea (§3)

Con `prf0_soundness` en la mano, dos corolarios que antes no eran ni enunciables:

* `prf0_consistent` — **la primera consistencia SEMÁNTICA del proyecto**: un modelo de `axioms` da
  `¬ Prf₀ ⊥` directamente. (Hasta hoy, `ConsistentH` era siempre hipótesis.)
* `ancla_underivable_prf0` — si algún modelo de `axioms` interpreta `axiomsCodeT` distinto de
  `listFormCodeM axioms`, entonces el ancla **no es demostrable en `Prf₀`**.

## ⬜ Lo que sigue faltando, y es la mitad cara

**El modelo.** Ninguno de los dos corolarios dice nada hasta que exista

    def M0 : Model D    con    contextSatisfies M0 v axioms      (los 141)

Sin él, «el ancla no es derivable» sigue siendo **hipótesis**, no medida. ⚠️ Y ojo: `axiomsCodeT`
**no** es libre — aparece en dos de los 141 axiomas (`ax_vpf_thy`, `ax_lineWF_thy`), siempre como
segundo argumento de `In`. Así que un modelo no puede reinterpretarlo a capricho: hay que
comprobar que esos dos siguen valiendo.

## ⚠️ Lo que este sondeo NO dice

* **No** dice que `prf_axiomsCodeT_eq` sea falso. Dice que ahora es **medible**.
* **No** toca la cadena de Gödel: `goedel_first_prf`/`goedel_second_prf` viven sobre `Prf`, y
  `prf0_soundness` habla de `Prf₀`. `Prf.incl : Prf₀ φ → Prf φ` va **en un solo sentido**.
* **No** vale para `Prf`: ese cálculo ya está habitado por `prf_axiomsCodeT_eq`, luego un
  `prf_soundness` por inducción tendría el mismo defecto que el de `Derives`.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open FOL.Metamath.Semantics

namespace Sondeos.AnclaSoundness

/-! ## §1 · El caso `gen`: los axiomas son SENTENCIAS CERRADAS -/

/-- Desplazar el entorno no cambia el valor de los axiomas, porque son cerrados.
    Sale de `axioms_lift_eq` (`Meta/Hilbert.lean`), que ya existía. -/
theorem ctx_shift {D : Type} (M : Model D) (v : Nat → D) (d : D)
    (h : contextSatisfies M v axioms) : contextSatisfies M (shiftEnv v d) axioms := by
  have hx : contextSatisfies M (shiftEnv v d) (axioms.map (liftFormula 0)) :=
    (contextSatisfies_lift_zero M v d).mpr h
  rw [axioms_lift_eq] at hx
  exact hx

/-! ## §2 · 🏁 LA SOLIDEZ DE `Prf₀`, los 17 constructores -/

/-- 🏁 **`Prf₀` es SÓLIDO**: todo lo que demuestra es verdadero en todo modelo de `axioms`.
    Inducción sobre los 17 constructores. **Footprint net‑0 puro.** -/
theorem prf0_soundness {φ : Formula} (h : Prf₀ φ) : satisfies axioms φ := by
  induction h with
  | p1 A B => intro D M v _ hA _; exact hA
  | p2 A B C => intro D M v _ hABC hAB hA; exact hABC hA (hAB hA)
  | c1 A B => intro D M v _ hA hB; exact ⟨hA, hB⟩
  | c2 A B => intro D M v _ hAB; exact hAB.left
  | c3 A B => intro D M v _ hAB; exact hAB.right
  | j1 A B => intro D M v _ hA; exact Or.inl hA
  | j2 A B => intro D M v _ hB; exact Or.inr hB
  | j3 A B C =>
      intro D M v _ hAB hAC hBC
      cases hAB with
      | inl hA => exact hAC hA
      | inr hB => exact hBC hB
  | efq A => intro D M v _ hbot; exact False.elim hbot
  | q1 A t =>
      intro D M v _ hall
      exact (eval_substFormula_zero M v t A).mpr (hall (evalTerm M v t))
  | q2 A t =>
      intro D M v _ hsub
      exact ⟨evalTerm M v t, (eval_substFormula_zero M v t A).mp hsub⟩
  | q3 A B =>
      intro D M v _ hall hex
      obtain ⟨d, hd⟩ := hex
      exact (eval_liftFormula_zero M v d B).mp (hall d hd)
  | eqrefl t => intro D M v _; rfl
  | leibniz A t₁ t₂ =>
      intro D M v _ heq hs
      have h1 := (eval_substFormula_zero M v t₁ A).mp hs
      have he : evalTerm M v t₁ = evalTerm M v t₂ := heq
      rw [he] at h1
      exact (eval_substFormula_zero M v t₂ A).mpr h1
  | thy a ha => intro D M v hG; exact hG a ha
  | mp A B _ _ ihAB ihA => intro D M v hG; exact (ihAB D M v hG) (ihA D M v hG)
  | gen A _ ih => intro D M v hG d; exact ih D M (shiftEnv v d) (ctx_shift M v d hG)

/-! ## §3 · Lo que desbloquea -/

/-- ⭐ **La primera consistencia SEMÁNTICA del proyecto**: un modelo de `axioms` da `¬ Prf₀ ⊥`.
    Hasta hoy la consistencia era siempre **hipótesis** (`ConsistentH`, `ConsistentOmega`). -/
theorem prf0_consistent {D : Type} (M : Model D) (v : Nat → D)
    (hM : contextSatisfies M v axioms) : ¬ Prf₀ ⊥ :=
  fun h => prf0_soundness h D M v hM

/-- ⭐ **El ancla, vuelta MEDIBLE**: un modelo de `axioms` que separe los dos lados demuestra que
    `axiomsCodeT ≐ listFormCodeM axioms` **no es demostrable en `Prf₀`**.
    ⬜ Falta el modelo — ver §«Lo que sigue faltando» de la cabecera. -/
theorem ancla_underivable_prf0 {D : Type} (M : Model D) (v : Nat → D)
    (hM : contextSatisfies M v axioms)
    (hne : evalTerm M v axiomsCodeT ≠ evalTerm M v (listFormCodeM axioms)) :
    ¬ Prf₀ (axiomsCodeT =eq listFormCodeM axioms) :=
  fun h => hne (prf0_soundness h D M v hM)

/-- Y la recíproca, que dice **qué se estaría suponiendo** si el ancla se postulase en `Prf₀`:
    exactamente que es **válida en todo modelo** de `axioms`. -/
theorem ancla_valida_si_prf0 (h : Prf₀ (axiomsCodeT =eq listFormCodeM axioms)) :
    satisfies axioms (axiomsCodeT =eq listFormCodeM axioms) :=
  prf0_soundness h

end Sondeos.AnclaSoundness

/-! ## FOOTPRINT -/
#print axioms Sondeos.AnclaSoundness.prf0_soundness
#print axioms Sondeos.AnclaSoundness.prf0_consistent
#print axioms Sondeos.AnclaSoundness.ancla_underivable_prf0

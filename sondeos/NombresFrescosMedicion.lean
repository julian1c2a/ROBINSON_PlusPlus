/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL

/-!
# SONDEO · ¿cuánto cuesta el SUMINISTRO DE CONSTANTES FRESCAS?

**Fecha:** 2026‑09‑14 · **Encargo:** *«¿puedes medir 1, 2 y 3?»* — lo que queda del ensamblaje de
Henkin (`doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2, ADR‑037 §4).

## ⚠️⚠️ El resultado refuta lo que yo había publicado una hora antes

ADR‑036 §5 y ADR‑037 §1 decían que el suministro de nombres frescos era **«combinatoria de
nombres»** que **«pasa por `String`»** y sería el trozo caro. **Medido: es barato.** El núcleo de
Lean da las dos piezas que hacen falta, y la segunda de una manera que yo no esperaba.

| pregunta | medición |
|---|---|
| ¿`ρ s := "f" ++ s` es inyectiva? | ✅ **`String.append_right_inj` EXISTE** en el núcleo: `s ++ t₁ = s ++ t₂ ↔ t₁ = t₂` |
| ¿hay constantes fuera de la imagen de `ρ`? | ✅ `"g" ++ t ≠ "f" ++ s` **compila**, y por `rfl` sobre `beq` |
| ¿hay inversa COMPUTABLE de `++`? | ⛔ **No.** `String.drop` devuelve un **`String.Slice`**, no un `String`, y `(a ++ b).drop a.length = b` **no existe** |

⭐ **Y la tercera no importa**: `derives0_rename_conservative` (ADR‑035) pide **inyectividad**, no
la inversa, y fabrica la inversa con elección. La ruta cara estaba cerrada y la barata, abierta.

## ⚠️ Lo que de mi afirmación SÍ se sostiene

El suministro de nombres **sí** mete `Classical.choice` en el footprint — pero **no** por la
matemática: por la implementación de `String` en el núcleo (v4.31, UTF‑8 opaco). Es exactamente
[[feedback-footprint-no-es-constructividad]]: *el footprint no distingue la no‑constructividad
matemática de la deuda de implementación del núcleo*.

⇒ Lo refutado es el **coste** («caro», «combinatoria»), no la **constructividad**.

## ⭐ Y una lección de método, que es la razón de que este fichero exista

`exact?` propuso `not_eq_of_beq_eq_false rfl` para `"g" ++ t ≠ "f" ++ s`, **con `s` y `t`
libres**. Eso parecía imposible: `beq` no debería reducir con variables libres. **Lo comprobé
compilando, y con un control adversarial**: el enunciado FALSO de la misma forma
(`"f" ++ t ≠ "f" ++ s`) **no compila**.

🔑 *Una sugerencia de `exact?` no es una medición.* Y un control adversarial cuesta una línea.

(La razón, una vez visto: `String` es UTF‑8 sobre `ByteArray`, y `beq` compara byte a byte
**cortocircuitando** en el primero que difiere — que aquí es el literal.)
-/

namespace NombresFrescos

-- ── (a) `ρ` es inyectiva, en una línea ──────────────────────────────────────
def rho (s : String) : String := "f" ++ s

theorem rho_inj (s t : String) (h : rho s = rho t) : s = t :=
  (String.append_right_inj "f").mp h

-- ── (b) constantes FUERA de la imagen ───────────────────────────────────────
theorem g_not_in_image (s : String) : "g" ≠ rho s := not_eq_of_beq_eq_false rfl

theorem ga_not_in_image (s t : String) : "g" ++ t ≠ rho s := not_eq_of_beq_eq_false rfl

-- ⚠️ CONTROL ADVERSARIAL: si `rfl` cerrara cualquier cosa de esta forma, lo de arriba no
-- mediría nada. El enunciado FALSO análogo NO compila — comprobado al escribir este fichero:
--
--     theorem tFALSO (s t : String) : "f" ++ t ≠ "f" ++ s := not_eq_of_beq_eq_false rfl
--     ⇒ error: Application type mismatch … ("f" ++ t == "f" ++ s) = false

-- ── (c) una familia infinita e inyectiva de constantes frescas ──────────────
def cst : Nat → String
  | 0 => "g"
  | n + 1 => "a" ++ cst n

theorem cst_not_in_image : ∀ (n : Nat) (s : String), cst n ≠ rho s
  | 0, s => g_not_in_image s
  | _ + 1, s => not_eq_of_beq_eq_false rfl

#print axioms rho_inj
#print axioms g_not_in_image
#print axioms ga_not_in_image
#print axioms cst_not_in_image

end NombresFrescos

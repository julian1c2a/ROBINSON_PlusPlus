import ROBINSON_PlusPlus

/-!
# ⭐⭐ SONDEO · CÓMO SE CORRIGE LA BASURA — y está **medido**, no propuesto

**Fecha**: 2026‑09‑22. Contesta la pregunta que dejó abierta ADR‑092 §2.

## El problema, en una línea

`ax_L0_cons_def` dice **`cons a b = pair a (σb)`**. La función `λ a b. cantor(a, b+1)` **no es
sobreyectiva**: se deja fuera los números triangulares `T(1)=1`, `T(3)=3`… ⇒ el `1` no es ni
`nil` ni un `cons`, el dominio ℕ tiene **basura**, y el esquema de inducción de listas —que es un
constructor de `Prf`— resulta **falso en ℕ** (ADR‑088).

## La corrección, en una línea

El `σ` sólo está ahí para que `cons h t ≠ nil`. **Sáquese fuera**:

    cons a b = σ (pair a b)

* `pair` (Cantor pelado) **es sobreyectivo** sobre ℕ — probado abajo, `cantorN_surj`.
* luego `σ ∘ pair` es una **biyección ℕ² → ℕ≥1**, y `nil = 0` queda **fuera de la imagen**.
* ⇒ **todo número es `nil` o un `cons`** (`sin_basura`). **La basura desaparece.**
* ⇒ la inducción de listas pasa a ser **verdadera en ℕ**, y `carc`/`cdrc` a ser inversas
  **totales** en vez de parciales con un valor inventado sobre la basura.

⚠️ Y **la monotonía que sostiene la recursión sobre códigos sobrevive** (`cola_decrece`): la cola
sigue siendo estrictamente menor que el `cons`, que es lo que hace terminar a todo lo que recorre
un código. Era el riesgo obvio de mover el `σ`, y no se materializa.

## 📏 El radio, medido (ADR‑092 §3)

| | |
|---|---|
| `ax_L0_cons_def` | 18 menciones, ~**5 consumidores reales** |
| `consN` (el espejo numérico) | **5 ficheros, 86 ocurrencias** |

Frente a la otra salida —relativizar `listInd`, que toca **13 teoremas de carga** incluido
`prf_chainOk_iff_chainOkB`—, ésta es **más pequeña y más localizada**.

## ⛔ Lo que este sondeo **NO** decide

Cambiar `ax_L0_cons_def` **cambia la codificación**, y con ella **`G`**. Los puentes que hoy
cierran por `rfl` sobre la forma numérica habría que **re‑verificarlos uno a uno**. Eso es una
decisión sobre el sistema de axiomas, y es del propietario.

## Cómo re‑ejecutarlo

    lake env lean sondeos/CantorSobreyectivo.lean      # desde la raíz de RPP
-/

open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace CantorSobreyectivo

/-- El emparejamiento de Cantor **pelado**, sin el `+1` del `cons` actual. -/
def cantorN (x y : Nat) : Nat := triN (x + y) + y

theorem triN_succ (s : Nat) : triN (s + 1) = triN s + (s + 1) := rfl

theorem triN_mono : ∀ {a b : Nat}, a ≤ b → triN a ≤ triN b
  | a, 0, h => by have : a = 0 := by omega
                  subst this; exact Nat.le_refl _
  | a, b + 1, h => by
      rcases Nat.lt_or_ge a (b + 1) with h' | h'
      · have := triN_mono (a := a) (b := b) (by omega)
        rw [triN_succ]; omega
      · have : a = b + 1 := by omega
        subst this; exact Nat.le_refl _

/-- El mayor `s` con `triN s ≤ n`. Misma forma que `sqrtN`: recursión, sin división. -/
def wN : Nat → Nat
  | 0 => 0
  | n + 1 => if triN (wN n + 1) ≤ n + 1 then wN n + 1 else wN n

theorem wN_le : ∀ n : Nat, triN (wN n) ≤ n
  | 0 => by simp [wN, triN]
  | n + 1 => by
      have ih := wN_le n
      simp only [wN]
      by_cases h : triN (wN n + 1) ≤ n + 1
      · rw [if_pos h]; exact h
      · rw [if_neg h]; omega

theorem lt_wN_succ : ∀ n : Nat, n < triN (wN n + 1)
  | 0 => by simp [wN, triN]
  | n + 1 => by
      have ih := lt_wN_succ n
      simp only [wN]
      by_cases h : triN (wN n + 1) ≤ n + 1
      · rw [if_pos h]
        have := triN_succ (wN n + 1)
        omega
      · rw [if_neg h]; exact Nat.lt_of_not_le h

/-- ⭐⭐ **EL CANTOR PELADO ES SOBREYECTIVO SOBRE ℕ.** Es lo que hace viable la salida (5). -/
theorem cantorN_surj (n : Nat) : ∃ x y, cantorN x y = n := by
  have h1 := wN_le n
  have h2 := lt_wN_succ n
  have h3 := triN_succ (wN n)
  refine ⟨wN n - (n - triN (wN n)), n - triN (wN n), ?_⟩
  have hy : n - triN (wN n) ≤ wN n := by omega
  have hs : (wN n - (n - triN (wN n))) + (n - triN (wN n)) = wN n := by omega
  simp only [cantorN, hs]
  omega

/-- ⇒ con `cons a b := σ (cantor a b)` y `nil := 0`, **todo número es `nil` o un `cons`**. -/
theorem sin_basura (n : Nat) : Or (n = 0) (∃ x y, cantorN x y + 1 = n) := by
  cases n with
  | zero => exact Or.inl rfl
  | succ m => obtain ⟨x, y, hxy⟩ := cantorN_surj m; exact Or.inr ⟨x, y, by omega⟩

/-- ⚠️ Y la monotonía que sostiene la recursión sobre códigos **sobrevive**: la cola decrece. -/
theorem cola_decrece (x y : Nat) : y < cantorN x y + 1 := by
  simp only [cantorN]; omega

end CantorSobreyectivo

#print axioms CantorSobreyectivo.cantorN_surj
#print axioms CantorSobreyectivo.sin_basura
#print axioms CantorSobreyectivo.cola_decrece

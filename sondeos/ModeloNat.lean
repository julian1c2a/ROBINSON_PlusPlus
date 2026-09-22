import ROBINSON_PlusPlus
import FOL.Semantics

/-!
# EL MODELO ESTÁNDAR — capa ARITMÉTICA de los 34 `coreAxioms`

**Fecha**: 2026‑09‑22. Frente 1, paso ① y ② de ADR‑085 §5.

Objetivo último: un modelo de los **141** axiomas ⇒ `¬ Prf ⊥` = `ConsistentH`, que es lo que
retira la vacuidad de Gödel I/II (nada prueba hoy esa hipótesis). Este fichero hace la **capa
aritmética**: la interpretación sobre `Nat` y los axiomas core que no tocan listas.

## ⭐ Lo que NO hubo que construir

`triN`, `consN`, `two_mul_consN` y **`consN_inj`** ya estaban en producción
(`Meta/CodeNumeralPrf.lean:46`, `Meta/CodeNatInjPrf.lean:85`) — el emparejamiento de Cantor sobre
`Nat` y su inyectividad, que es lo que hace existir `carc`/`cdrc` en el modelo.
🔑 Van **DOCE** de «antes de construir, buscar»: M3 (ADR‑085) los re‑derivó sin saberlo.

## ⛔ Lo que SÍ hubo que construir, y es lo único

**`Nat.sqrt` no existe en el core de Lean**, y `ax14_sqrt_le`/`ax15_lt_succ_sqrt` lo piden. Se
mira también en `Peano/PeanoNat/Sqrt.lean`, que tiene una implementación completa —`sqrtMod`,
`sqrtRem`, `sqrt_upper_bound`— pero sobre **`ℕ₀`**, el natural propio de Peano. ℕ₀ es isomorfo a
`Nat`, así que transportarla es posible; medido, **transportarla cuesta más que las 30 líneas de
abajo** para lo único que aquí hace falta: **dos desigualdades**.
🔑 *Un desarrollo ajeno se reutiliza por lo que hay que TRANSPORTAR, no por lo que contiene.*
⬜ Donde el transporte sí puede pagar es más adelante: `div`/`mod`, `pow`, y sobre todo la
**β de Gödel** (`Peano/PeanoNat/Foundation/GodelBeta.lean`), que la capa de listas necesitará.

## Cómo re‑ejecutarlo

    lake env lean sondeos/ModeloNat.lean      # desde la raíz de RPP
-/

namespace ModeloNat

/-! ## §1 · La raíz entera sobre `Nat`

Estilo `triN`: **recursión, sin división**, para que `omega` trate los productos como átomos. -/

def sqrtN : Nat → Nat
  | 0 => 0
  | n + 1 => if (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1 then sqrtN n + 1 else sqrtN n

/-- La única pieza no lineal.
    ⚠️ El sucesor va como `k+1+1` y **NO** como `k+2`: para `omega` el producto es un **ÁTOMO**,
    y `(k+2)*(k+2)` y `(k+1+1)*(k+1+1)` son átomos **distintos**. Con `k+2` no cierra. -/
theorem sq_lt_sq_succ (k : Nat) : (k + 1) * (k + 1) < (k + 1 + 1) * (k + 1 + 1) := by
  have h1 : (k + 1 + 1) * (k + 1 + 1) = (k + 1) * (k + 1) + 2 * (k + 1) + 1 := by
    rw [Nat.succ_mul, Nat.mul_succ]
    generalize (k + 1) * (k + 1) = A
    omega
  omega

/-- `ax14_sqrt_le` en el modelo: `sq (√x) ≤ x`. -/
theorem sqrtN_le : ∀ n : Nat, sqrtN n * sqrtN n ≤ n
  | 0 => by simp [sqrtN]
  | n + 1 => by
      have ih := sqrtN_le n
      simp only [sqrtN]
      by_cases h : (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1
      · rw [if_pos h]; exact h
      · rw [if_neg h]; omega

/-- `ax15_lt_succ_sqrt` en el modelo: `x < sq (σ (√x))`. -/
theorem lt_sq_succ_sqrtN : ∀ n : Nat, n < (sqrtN n + 1) * (sqrtN n + 1)
  | 0 => by simp [sqrtN]
  | n + 1 => by
      have ih := lt_sq_succ_sqrtN n
      have ih2 := sqrtN_le n
      simp only [sqrtN]
      by_cases h : (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1
      · rw [if_pos h]
        have hlt := sq_lt_sq_succ (sqrtN n)
        omega
      · rw [if_neg h]; exact Nat.lt_of_not_le h

end ModeloNat

/-! ## §2 · LA INTERPRETACIÓN

⚠️ `open` acotado: fuera de esta sección `≤` resuelve al símbolo OBJETO `le` (ADR‑085 §3). -/

section Interpretacion
open FOL
open FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms
open ModeloNat

/-- **El modelo estándar**, capa aritmética. Los símbolos de lista (`::`, `##`, `Π_p`) quedan
    a `0` **a propósito**: se interpretan en la capa siguiente, con `consN`. -/
def MN : Model Nat where
  func := fun s args =>
    match s, args with
    | "0",  []     => 0
    | "σ",  [a]    => a + 1
    | "+",  [a, b] => a + b
    | "*",  [a, b] => a * b
    | "−",  [a, b] => a - b            -- monus, como dice el comentario de `sub_sym`
    | "√",  [a]    => sqrtN a
    | "/₂", [a]    => a / 2
    | "%₂", [a]    => a % 2
    | "τ",  [a]    => a - 1            -- `pred`
    | _, _         => 0
  rel := fun s args =>
    match s, args with
    | "<", [a, b] => a < b
    | _, _        => False

/-! ### Los axiomas core de ARITMÉTICA, validados -/

theorem v_ax2  : ∀ v : Nat → Nat, evalFormula MN v ax2_peano_succ_neq_zero := by
  intro v d; simp [succ, zero, succ_sym, zero_sym, neg,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN]

theorem v_ax3  : ∀ v : Nat → Nat, evalFormula MN v ax3_peano_succ_inj := by
  intro v d d'; simp [succ, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN]

theorem v_ax4  : ∀ v : Nat → Nat, evalFormula MN v ax4_add_zero := by
  intro v d; simp [add, zero, add_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN]

theorem v_ax18 : ∀ v : Nat → Nat, evalFormula MN v ax18_lt_irrefl := by
  intro v d; simp [lt, lt_sym, neg,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN]

theorem v_ax25 : ∀ v : Nat → Nat, evalFormula MN v ax25_pred_zero := by
  -- ⚠️ `ax25_pred_zero` NO es un `forall_`: sin su nombre en el `simp` no hay nada que abrir.
  -- El linter lo marcó «no usado» en los OTROS siete (allí `forall_` lo abre) y aquí NO.
  -- 🔑 *Un aviso de «no usado» no es una medición de que sobre.* Segunda vez en esta sesión.
  intro v; simp [ax25_pred_zero, pred, zero, pred_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, MN]

theorem v_ax26 : ∀ v : Nat → Nat, evalFormula MN v ax26_pred_succ := by
  intro v d; simp [pred, succ, pred_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN]

/-- ⭐ Los dos que necesitaban la raíz. -/
theorem v_ax14 : ∀ v : Nat → Nat, evalFormula MN v ax14_sqrt_le := by
  intro v d
  simp only [ax14_sqrt_le, forall_, le, lt, sq, mul, sqrt, lt_sym, mul_sym, sqrt_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN]
  have := sqrtN_le d
  omega

theorem v_ax15 : ∀ v : Nat → Nat, evalFormula MN v ax15_lt_succ_sqrt := by
  intro v d
  simp only [ax15_lt_succ_sqrt, forall_, lt, sq, mul, succ, sqrt, lt_sym, mul_sym, succ_sym,
    sqrt_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN]
  exact lt_sq_succ_sqrtN d

end Interpretacion

#print axioms ModeloNat.sqrtN_le
#print axioms ModeloNat.lt_sq_succ_sqrtN
#print axioms v_ax2
#print axioms v_ax14
#print axioms v_ax15

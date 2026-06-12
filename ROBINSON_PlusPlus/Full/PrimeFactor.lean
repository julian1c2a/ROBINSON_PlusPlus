/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-!
## FULL — Teoría de números META (pura ℕ, sin Mathlib)

Capa meta-nivel autocontenida sobre `ℕ` (no usa FOL ni Mathlib): primalidad,
existencia de factor primo y factorización como **lista plana de primos con
repetición** (producto = n). Es el cómputo que luego se transfiere al object
vía el puente de numerales (`Factorization.lean`).

**Diseño**: para *existencia* basta una lista de primos con repetición
(`[2,2,3]` para 12), cuyo producto es `n`. Equivale a exponente 1 en cada
factor — y `prod_pairs [(p,1)…] = Π p`. La forma con exponentes (`P × ℕ₁`)
sólo se necesita para *unicidad* (forma canónica), no aquí.
-/

namespace ROBINSON_PlusPlus.Full

/-- Primalidad sobre `ℕ` (sin Mathlib): `2 ≤ p` y todo divisor es `1` o `p`.
    Coincide con las hipótesis de `isPrime_numeral`. -/
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ a : Nat, a ∣ p → a = 1 ∨ a = p

/-- Producto de una lista de naturales. -/
def natProd : List Nat → Nat
  | []      => 1
  | p :: ps => p * natProd ps

@[simp] theorem natProd_nil : natProd [] = 1 := rfl
@[simp] theorem natProd_cons (p : Nat) (ps : List Nat) :
    natProd (p :: ps) = p * natProd ps := rfl

/-- **Existencia de factor primo**: todo `n ≥ 2` tiene un divisor primo.
    Por inducción fuerte: si `n` no es primo, tiene un divisor propio `a`
    (`2 ≤ a < n`); por HI `a` tiene un factor primo, que también divide a `n`. -/
theorem exists_prime_factor : ∀ n : Nat, 2 ≤ n → ∃ p, IsPrimeNat p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn2
    by_cases hp : IsPrimeNat n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · -- n no primo (con 2 ≤ n) ⇒ ∃ a ∣ n, a ≠ 1, a ≠ n
      have key : ∃ a, a ∣ n ∧ a ≠ 1 ∧ a ≠ n := by
        apply Classical.byContradiction
        intro hcon
        apply hp
        refine ⟨hn2, ?_⟩
        intro a hda
        by_cases h1 : a = 1
        · exact Or.inl h1
        · by_cases hN : a = n
          · exact Or.inr hN
          · exact absurd ⟨a, hda, h1, hN⟩ hcon
      obtain ⟨a, hadvd, ha1, haN⟩ := key
      have ha0 : a ≠ 0 := by
        intro ha; subst ha
        exact absurd (Nat.eq_zero_of_zero_dvd hadvd) (by omega)
      have ha2 : 2 ≤ a := by omega
      have halt : a < n := by
        have hle := Nat.le_of_dvd (show 0 < n by omega) hadvd; omega
      obtain ⟨p, hp_prime, hp_dvd⟩ := ih a halt ha2
      exact ⟨p, hp_prime, Nat.dvd_trans hp_dvd hadvd⟩

/-- **Factorización (existencia)**: todo `n ≥ 1` es producto de una lista de
    primos. Por inducción fuerte: `n = 1` da la lista vacía; `n ≥ 2` toma un
    factor primo `p`, factoriza `n / p` (que es `< n` y `≥ 1`) y antepone `p`. -/
theorem primeFactorList : ∀ n : Nat, 1 ≤ n →
    ∃ ps : List Nat, (∀ p ∈ ps, IsPrimeNat p) ∧ natProd ps = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h1
    by_cases hn1 : n = 1
    · exact ⟨[], by simp, by simp [hn1]⟩
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨p, hp_prime, hp_dvd⟩ := exists_prime_factor n hn2
      have hp2 : 2 ≤ p := hp_prime.1
      have hnp_lt : n / p < n := Nat.div_lt_self (by omega) (by omega)
      have hnp_pos : 1 ≤ n / p :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) (by omega)
      obtain ⟨ps', hps'_prime, hps'_prod⟩ := ih (n / p) hnp_lt hnp_pos
      refine ⟨p :: ps', ?_, ?_⟩
      · intro q hq
        cases List.mem_cons.mp hq with
        | inl h => exact h ▸ hp_prime
        | inr h => exact hps'_prime q h
      · -- natProd (p :: ps') = p * (n/p) = n
        rw [natProd_cons, hps'_prod]
        exact Nat.mul_div_cancel' hp_dvd

end ROBINSON_PlusPlus.Full

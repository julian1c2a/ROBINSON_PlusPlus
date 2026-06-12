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

/-! ### Lema de Euclides y UNICIDAD de la factorización (ℕ) -/

/-- **Euclides**: `p` primo, `p ∣ a·b` ⇒ `p ∣ a ∨ p ∣ b`. Vía coprimalidad
    (core: `Nat.Coprime.dvd_of_dvd_mul_left`); si `p ∤ a` entonces `gcd p a = 1`
    (porque `gcd p a ∣ p` primo y `≠ p`). -/
theorem euclid {p a b : Nat} (hp : IsPrimeNat p) (hdvd : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · have hcop : Nat.Coprime p a := by
      have hg : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
      rcases hp.2 (Nat.gcd p a) hg with h1 | hpp
      · exact h1
      · exact absurd (hpp ▸ Nat.gcd_dvd_right p a) ha
    exact Or.inr (hcop.dvd_of_dvd_mul_left hdvd)

/-- Dos primos con `p ∣ q` son iguales. -/
theorem prime_dvd_prime_eq {p q : Nat} (hp : IsPrimeNat p) (hq : IsPrimeNat q)
    (hpq : p ∣ q) : p = q := by
  rcases hq.2 p hpq with h1 | h
  · exact absurd h1 (by have := hp.1; omega)
  · exact h

/-- **Euclides iterado**: un primo que divide al producto de una lista divide a
    algún elemento. -/
theorem euclid_list {p : Nat} (hp : IsPrimeNat p) :
    ∀ qs : List Nat, p ∣ natProd qs → ∃ q ∈ qs, p ∣ q := by
  intro qs
  induction qs with
  | nil =>
    intro h
    have h1 := Nat.eq_one_of_dvd_one h
    have := hp.1; omega
  | cons a as ih =>
    intro h
    rcases euclid hp h with ha | hrest
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨q, hq_mem, hpq⟩ := ih hrest
      exact ⟨q, List.mem_cons_of_mem a hq_mem, hpq⟩

/-- `q ∈ qs ⇒ natProd qs = q · natProd (qs.erase q)`. -/
theorem natProd_erase : ∀ (qs : List Nat) (q : Nat), q ∈ qs →
    natProd qs = q * natProd (qs.erase q) := by
  intro qs
  induction qs with
  | nil => intro q hq; cases hq
  | cons a as ih =>
    intro q hq
    by_cases haq : a = q
    · subst haq; simp [List.erase_cons_head]
    · have hq_as : q ∈ as := by
        rcases List.mem_cons.mp hq with h | h
        · exact absurd h.symm haq
        · exact h
      have herase : (a :: as).erase q = a :: as.erase q := by
        simp [haq]
      rw [herase, natProd_cons, natProd_cons, ih q hq_as]
      exact Nat.mul_left_comm a q _

/-- Producto `1` con factores `≥ 2` ⇒ lista vacía. -/
theorem natProd_eq_one_imp_nil : ∀ (qs : List Nat), (∀ q ∈ qs, 2 ≤ q) →
    natProd qs = 1 → qs = [] := by
  intro qs
  cases qs with
  | nil => intro _ _; rfl
  | cons a as =>
    intro hge h
    have ha1 : a = 1 := Nat.eq_one_of_dvd_one ⟨natProd as, h.symm⟩
    have := hge a List.mem_cons_self; omega

/-- **Unicidad (multiplicidades)**: dos factorizaciones primas del mismo `n`
    tienen cada primo con la misma multiplicidad. Por inducción en `ps`,
    cancelando un primo común (Euclides + `natProd_erase`). -/
theorem count_unique : ∀ (ps qs : List Nat),
    (∀ p ∈ ps, IsPrimeNat p) → (∀ q ∈ qs, IsPrimeNat q) →
    natProd ps = natProd qs → ∀ r, List.count r ps = List.count r qs := by
  intro ps
  induction ps with
  | nil =>
    intro qs _ hqs hprod r
    have hqs_nil : qs = [] :=
      natProd_eq_one_imp_nil qs (fun q hq => (hqs q hq).1) hprod.symm
    subst hqs_nil; rfl
  | cons p ps' ih =>
    intro qs hps hqs hprod r
    have hp_prime : IsPrimeNat p := hps p List.mem_cons_self
    have hp_pos : 0 < p := by have := hp_prime.1; omega
    have hp_dvd : p ∣ natProd qs := ⟨natProd ps', by rw [← hprod, natProd_cons]⟩
    obtain ⟨q, hq_mem, hpq⟩ := euclid_list hp_prime qs hp_dvd
    have hq_prime : IsPrimeNat q := hqs q hq_mem
    have hpq_eq : p = q := prime_dvd_prime_eq hp_prime hq_prime hpq
    subst hpq_eq
    have herase : natProd qs = p * natProd (qs.erase p) := natProd_erase qs p hq_mem
    have hcancel : natProd ps' = natProd (qs.erase p) := by
      apply Nat.eq_of_mul_eq_mul_left hp_pos
      calc p * natProd ps' = natProd (p :: ps') := (natProd_cons p ps').symm
        _ = natProd qs := hprod
        _ = p * natProd (qs.erase p) := herase
    have hps' : ∀ x ∈ ps', IsPrimeNat x := fun x hx => hps x (List.mem_cons_of_mem p hx)
    have hqs' : ∀ x ∈ qs.erase p, IsPrimeNat x := fun x hx => hqs x (List.mem_of_mem_erase hx)
    have ih_r := ih (qs.erase p) hps' hqs' hcancel r
    rw [List.count_cons, (List.perm_cons_erase hq_mem).count_eq r, List.count_cons, ih_r]

/-- **Unicidad (permutación)**: dos factorizaciones primas del mismo `n` son
    permutaciones una de la otra. Es el TFA-unicidad en `ℕ`. -/
theorem factorization_perm_unique (ps qs : List Nat)
    (hps : ∀ p ∈ ps, IsPrimeNat p) (hqs : ∀ q ∈ qs, IsPrimeNat q)
    (hprod : natProd ps = natProd qs) : ps.Perm qs :=
  List.perm_iff_count.mpr (count_unique ps qs hps hqs hprod)

end ROBINSON_PlusPlus.Full

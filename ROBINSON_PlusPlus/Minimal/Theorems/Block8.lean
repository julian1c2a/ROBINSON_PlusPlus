/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block2
open ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block8

/-!
## BLOQUE VIII — PRIMOS Y FACTORIZACIÓN

Implementa **Def 25** (`Dvd` y `IsPrime`), **Def 26** (`IsFactorization`) y
**Ax-P** (TFA, Teorema Fundamental de la Aritmética), siguiendo
`TuplasFuncionesYListas.md §BLOQUE VIII Fase 17`.

**Estado del bloque**:

* **Def 25 + lemas básicos**: completo (`Dvd`, `IsPrime`, refl/zero/one).
* **Def 26 `IsFactorization`** + **Ax-P (TFA)**: completos. Requirieron extender
  el lenguaje con `pow` y `prod_pairs` (ver `Axioms.lean`, +4 axiomas).
* **Fases 18-19 (Gödelización, autorreferencia)**: **fuera de scope** del
  sistema `Minimal`. Requieren meta-codificación (G : símbolos → ℕ, ⌜·⌝,
  IsFormula, Dem) y corresponderían a un módulo `Meta/` futuro.

**Estilo de formalización**: igual que `Block7`, los predicados `Dvd`,
`IsPrime` e `IsFactorization` se definen como meta-Props (`Term → Prop`)
parametrizados por cuantificación universal sobre `Term`. Esto evita el manejo
manual de `liftTerm`/`substTerm` que aparecería al usar `forall_`/`ex` en FOL
puro. `ax_p_tfa` es un meta-axioma en el estilo de `imp_intro`, `gen`, `raa`,
`or_elim`, `ex_elim`: incrementable de 5 a 6 meta-axiomas si se cuenta como tal.
-/

def Γ := axioms

/-!
### Fase 17: Divisibilidad y Primalidad
-/

/-- **Def 25.a** (divisibilidad): `Dvd a b ⟺ ∃q. a·q = b`. -/
def Dvd (a b : Term) : Prop :=
  ∃ q : Term, axioms ⊢ (mul a q =eq b)

/-- **Def 25** (primalidad): `IsPrime p ⟺ p ≥ 2 ∧ ∀d. Dvd d p → d=1 ∨ d=p`.

    Nota: `p ≥ 2` se expresa como `lt one p` (estrictamente mayor que 1).
    La disyunción de la conclusión usa la `∨` de FOL (`Formula.or`). -/
def IsPrime (p : Term) : Prop :=
  (axioms ⊢ lt one p) ∧
  ∀ d : Term, Dvd d p → axioms ⊢ ((d =eq one) ∨ (d =eq p))

/-!
### Lemas básicos de `Dvd`
-/

/-- `Dvd a a` con testigo `q := one`. -/
theorem dvd_refl (a : Term) : Dvd a a :=
  ⟨one, by
    have h := spec teo_2_5 a
    simp [substFormula, substTerm, substTerms, mul, one, zero, succ] at h
    exact h⟩

/-- `Dvd one a` con testigo `q := a`. -/
theorem dvd_one (a : Term) : Dvd one a :=
  ⟨a, by
    have h := spec teo_2_6 a
    simp [substFormula, substTerm, substTerms, mul, one, zero, succ] at h
    exact h⟩

/-- `Dvd a zero` con testigo `q := zero` (todo número divide a 0). -/
theorem dvd_zero (a : Term) : Dvd a zero :=
  ⟨zero, by
    have h := spec teo_2_3 a
    simp [substFormula, substTerm, substTerms, mul, zero] at h
    exact h⟩

/-!
### Álgebra de `Dvd` (sin inducción)

Propiedades algebraicas de la divisibilidad que se derivan del puro álgebra de
`mul`/`add` (`mul_assoc'`, `mul_comm'`, `mul_distrib'` de Block4_C5) más la
congruencia de la igualdad (`eq_congr_mul_*`, `eq_congr_add_*` de Axioms).
**Ninguna requiere inducción.**
-/

/-- **Transitividad** de `Dvd`: `a ∣ b → b ∣ c → a ∣ c`. Testigo `q₁·q₂`.

    `a·(q₁·q₂) = (a·q₁)·q₂ = b·q₂ = c` (asociatividad + congruencia + hipótesis). -/
theorem dvd_trans {a b c : Term} (hab : Dvd a b) (hbc : Dvd b c) : Dvd a c := by
  obtain ⟨q₁, hq₁⟩ := hab
  obtain ⟨q₂, hq₂⟩ := hbc
  refine ⟨mul q₁ q₂, ?_⟩
  have h₁ : axioms ⊢ (mul a (mul q₁ q₂) =eq mul (mul a q₁) q₂) :=
    eq_symm (mul_assoc' a q₁ q₂)
  have h₂ : axioms ⊢ (mul (mul a q₁) q₂ =eq mul b q₂) := eq_congr_mul_right hq₁
  exact FOL.derive_eq_trans (FOL.derive_eq_trans h₁ h₂) hq₂

/-- `a ∣ a·b`. Testigo `b` (reflexividad). -/
theorem dvd_mul_right (a b : Term) : Dvd a (mul a b) :=
  ⟨b, Derives.refl axioms (mul a b)⟩

/-- `b ∣ a·b`. Testigo `a` (vía conmutatividad `b·a = a·b`). -/
theorem dvd_mul_left (a b : Term) : Dvd b (mul a b) :=
  ⟨a, by exact mul_comm' b a⟩

/-- `a ∣ b → a ∣ b·c`. Testigo `q·c`.  `a·(q·c) = (a·q)·c = b·c`. -/
theorem dvd_mul_of_dvd_left {a b : Term} (h : Dvd a b) (c : Term) :
    Dvd a (mul b c) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨mul q c, ?_⟩
  have h₁ : axioms ⊢ (mul a (mul q c) =eq mul (mul a q) c) :=
    eq_symm (mul_assoc' a q c)
  have h₂ : axioms ⊢ (mul (mul a q) c =eq mul b c) := eq_congr_mul_right hq
  exact FOL.derive_eq_trans h₁ h₂

/-- `a ∣ c → a ∣ b·c`. Testigo `q·b`.  `a·(q·b) = (a·q)·b = c·b = b·c`. -/
theorem dvd_mul_of_dvd_right {a c : Term} (h : Dvd a c) (b : Term) :
    Dvd a (mul b c) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨mul q b, ?_⟩
  have h₁ : axioms ⊢ (mul a (mul q b) =eq mul (mul a q) b) :=
    eq_symm (mul_assoc' a q b)
  have h₂ : axioms ⊢ (mul (mul a q) b =eq mul c b) := eq_congr_mul_right hq
  have h₃ : axioms ⊢ (mul c b =eq mul b c) := mul_comm' c b
  exact FOL.derive_eq_trans (FOL.derive_eq_trans h₁ h₂) h₃

/-- `a ∣ b → a ∣ c → a ∣ b+c`. Testigo `q₁+q₂` (vía distributividad).

    `a·(q₁+q₂) = a·q₁ + a·q₂ = b + c`. -/
theorem dvd_add {a b c : Term} (hb : Dvd a b) (hc : Dvd a c) :
    Dvd a (add b c) := by
  obtain ⟨q₁, hq₁⟩ := hb
  obtain ⟨q₂, hq₂⟩ := hc
  refine ⟨add q₁ q₂, ?_⟩
  have h₁ : axioms ⊢ (mul a (add q₁ q₂) =eq add (mul a q₁) (mul a q₂)) :=
    mul_distrib' a q₁ q₂
  have h₂ : axioms ⊢ (add (mul a q₁) (mul a q₂) =eq add b (mul a q₂)) :=
    eq_congr_add_right hq₁
  have h₃ : axioms ⊢ (add b (mul a q₂) =eq add b c) := eq_congr_add_left hq₂
  exact FOL.derive_eq_trans (FOL.derive_eq_trans h₁ h₂) h₃

/-!
### Lemas básicos de `IsPrime`
-/

/-- `IsPrime zero` haría el sistema inconsistente: la primera condición
    (`lt one zero`) contradice `ax2` (sucesor ≠ 0) vía `ax13` + `ax5`.

    Nota sobre la forma del enunciado: NO podemos probar `¬IsPrime zero` en
    Lean directamente, porque eso requeriría conocer que `axioms` es
    consistente (algo que no demostramos). Lo que SÍ podemos probar es:
    "si tuvieras una prueba meta de `IsPrime zero`, derivaríamos `axioms ⊢ ⊥`",
    es decir, una **inconsistencia interna**. -/
theorem isPrime_zero_inconsistent (h_prime : IsPrime zero) : axioms ⊢ ⊥ := by
  have h_lt_one_zero : axioms ⊢ lt one zero := h_prime.1
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  -- spec ax13 en (one, zero): lt 1 0 ⇔ ∃k. 1 + σk = 0
  have h_iff := spec (spec h_ax13 one) zero
  simp [substFormula, substTerm, substTerms, lt, one, zero, succ, iff,
        liftTerm, liftTerms] at h_iff
  apply ex_elim (iff_mp h_iff h_lt_one_zero); intro k h_k
  simp [substFormula, substTerm, substTerms, add] at h_k
  -- h_k : add (succ zero) (succ k) =eq zero. ax5 ⇒ succ(1+k) = 0 ⇒ contradicción ax2.
  have h_ax5_inst : axioms ⊢ (add one (succ k) =eq succ (add one k)) := by
    have hh := spec (spec h_ax5 one) k
    simp [substFormula, substTerm, substTerms, add, one, zero, succ,
          liftTerm, liftTerms] at hh
    exact hh
  have h_succ_eq_zero : axioms ⊢ (succ (add one k) =eq zero) :=
    FOL.derive_eq_trans (eq_symm h_ax5_inst) h_k
  have h_ax2_inst : axioms ⊢ neg (succ (add one k) =eq zero) := by
    have hh := spec h_ax2 (add one k)
    simp [succ, zero] at hh
    exact hh
  exact mp h_ax2_inst h_succ_eq_zero

/-- `IsPrime one` haría el sistema inconsistente vía `ax18` (irreflexividad). -/
theorem isPrime_one_inconsistent (h_prime : IsPrime one) : axioms ⊢ ⊥ := by
  have h_lt_one_one : axioms ⊢ lt one one := h_prime.1
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_irr : axioms ⊢ neg (lt one one) := by
    have hh := spec h_ax18 one
    simp [lt] at hh
    exact hh
  exact mp h_irr h_lt_one_one

/-!
### Fase 17 extendida: Potencia y producto sobre listas de pares

Estos lemas son las instancias inmediatas de los nuevos axiomas
`ax_pow_zero`, `ax_pow_succ`, `ax_prodp_nil`, `ax_prodp_cons`.
Sirven como interfaz limpia para los demás bloques (evitan el `spec`+`simp`
verbose en cada uso).
-/

/-- `b^0 = 1` (instancia de ax_pow_zero). -/
theorem pow_zero (b : Term) : Γ ⊢ (pow b zero =eq one) := by
  have h_ax := ax (by simp [axioms] : ax_pow_zero ∈ axioms)
  have h := spec h_ax b
  simp [substFormula, substTerm, substTerms, pow, zero, one, succ] at h
  exact h

/-- `b^(σe) = b^e * b` (instancia de ax_pow_succ). -/
theorem pow_succ (b e : Term) : Γ ⊢ (pow b (succ e) =eq mul (pow b e) b) := by
  have h_ax := ax (by simp [axioms] : ax_pow_succ ∈ axioms)
  have h := spec (spec h_ax b) e
  simp [substFormula, substTerm, substTerms, pow, mul, succ,
        FOL.substTerm_liftTerm] at h
  exact h

/-- `prod_pairs [] = 1` (instancia de ax_prodp_nil). -/
theorem prod_pairs_nil : Γ ⊢ (prod_pairs nil =eq one) :=
  ax (by simp [axioms] : ax_prodp_nil ∈ axioms)

/-- `prod_pairs ((p,e) :: t) = p^e * prod_pairs t` (instancia de ax_prodp_cons). -/
theorem prod_pairs_cons (p e t : Term) :
    Γ ⊢ (prod_pairs (cons (pair p e) t) =eq mul (pow p e) (prod_pairs t)) := by
  have h_ax := ax (by simp [axioms] : ax_prodp_cons ∈ axioms)
  have h := spec (spec (spec h_ax p) e) t
  simp [substFormula, substTerm, substTerms, prod_pairs, cons, pair,
        cantor_func, cantor_poly, div2, mul, add, succ, two, one, zero, pow,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
  exact h

/-!
### Def 26: IsFactorization

`IsFactorization f n` significa: `f` es una lista de pares `(pᵢ, eᵢ)` tales que
cada `pᵢ` es primo, cada `eᵢ ≥ 1`, y `Π pᵢ^eᵢ = n`.

Se define como meta-Prop (estilo Block7/Block8): combina una derivación
object-level (`prod_pairs f =eq n`) con cuantificación meta-level sobre los
elementos de la lista (vía `In`).

**Nota sobre la formulación**: la condición "cada elemento de f es un par
(p,e) con p primo y e ≥ 1" se expresa como: `∀ p e, In (pair p e) f →
IsPrime p ∧ e > 0`. Esto es permisivo (no obliga a que los elementos sean
literalmente de la forma `pair p e`), pero la condición `prod_pairs f =eq n`
es la que restringe la forma de `f`, ya que `ax_prodp_cons` sólo se activa
en listas con cabeza `pair p e`. -/
def IsFactorization (f n : Term) : Prop :=
  (axioms ⊢ (prod_pairs f =eq n)) ∧
  ∀ p e : Term, (axioms ⊢ In (pair p e) f) → (IsPrime p ∧ axioms ⊢ lt zero e)

/-- **Lista vacía factoriza al 1**: `IsFactorization [] 1`.

    Esto es el caso base del TFA (`Ax-P` requiere `n ≥ 1`, y `1` es el caso
    límite — la factorización vacía da producto 1).

    La condición sobre los elementos es vacuamente cierta: si tuviéramos una
    derivación de `In (pair p e) nil`, junto con `ax_L1_in_nil` derivaríamos
    object-level `⊥` y por explosión cualquier otra cosa. -/
theorem isFactorization_nil_one : IsFactorization nil one := by
  refine ⟨prod_pairs_nil, ?_⟩
  intro p e h_in
  have h_axL1 := ax (by simp [axioms] : ax_L1_in_nil ∈ axioms)
  have h_not_in : axioms ⊢ neg (In (pair p e) nil) := by
    have hh := spec h_axL1 (pair p e)
    simp [In, nil, zero] at hh
    exact hh
  have h_bot : axioms ⊢ ⊥ := mp h_not_in h_in
  -- Explosión object-level: derivamos toda subcomponente desde ⊥.
  refine ⟨⟨false_elim h_bot, ?_⟩, false_elim h_bot⟩
  intro _d _h_dvd
  exact false_elim h_bot

/-!
### Ax-P (TFA): Teorema Fundamental de la Aritmética

Para todo `n ≥ 1`, existe una **única** factorización (módulo igualdad
provable) de `n` en primos.

**Justificación**: en sistemas con inducción débil este resultado es un
teorema (vía inducción fuerte sobre `n`); en el sistema `Minimal` (sin
inducción) se adopta como **axioma**. Esto sigue la línea del spec
§Bloque VIII Fase 17 y §Apéndice B.4.

**Estilo**: meta-axioma (como `imp_intro`, `gen`, `raa`, `or_elim`,
`ex_elim`). No es expresable directamente como `Formula` porque
`IsFactorization` es meta-Prop. -/
axiom ax_p_tfa : ∀ n : Term, axioms ⊢ lt zero n →
  ∃ f : Term, IsFactorization f n ∧
    ∀ f' : Term, IsFactorization f' n → axioms ⊢ (f =eq f')

/-!
### Corolarios del TFA (`ax_p_tfa`)

Consecuencias inmediatas del Teorema Fundamental de la Aritmética. **No
introducen axiomas nuevos**: sólo proyectan la existencia y la unicidad
contenidas en `ax_p_tfa`.

**Fuera de scope `Minimal/`** (requieren inducción / `Intermediate/` o `Full/`):
el **lema de Euclides** (`IsPrime p → p ∣ a·b → p ∣ a ∨ p ∣ b`) y la
**multiplicatividad** (`prod_pairs (concat f g) = prod_pairs f · prod_pairs g`)
necesitan `prod_pairs_concat`, que es una recursión sobre la lista no demostrable
sin inducción. Se difieren a sistemas con esquema de inducción. -/

/-- **Existencia de factorización** para `n ≥ 1`: proyección directa del TFA. -/
theorem factorization_exists (n : Term) (h : axioms ⊢ lt zero n) :
    ∃ f : Term, IsFactorization f n := by
  obtain ⟨f, hf, _⟩ := ax_p_tfa n h
  exact ⟨f, hf⟩

/-- **Unicidad de factorización** para `n ≥ 1`: dos factorizaciones cualesquiera
    de `n` son provablemente iguales. Se obtiene de la unicidad del TFA pasando
    por la factorización canónica `g`: `g =eq f` y `g =eq f'` dan `f =eq f'`
    (vía `eq_trans` no estándar). -/
theorem factorization_unique {n f f' : Term} (h : axioms ⊢ lt zero n)
    (hf : IsFactorization f n) (hf' : IsFactorization f' n) :
    axioms ⊢ (f =eq f') := by
  obtain ⟨g, _hg, huniq⟩ := ax_p_tfa n h
  exact eq_trans (huniq f hf) (huniq f' hf')

/-- `0 < 1`. Testigo `k := 0` en `ax13`: `0 + σ0 = 1` (es `teo_1_2`). -/
theorem lt_zero_one : axioms ⊢ lt zero one := by
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_iff := spec (spec h_ax13 zero) one
  simp [substFormula, substTerm, substTerms, lt, one, zero, succ, iff,
        liftTerm, liftTerms] at h_iff
  refine iff_mpr h_iff (ex_intro zero ?_)
  simp [substFormula, substTerm, substTerms, add, zero]
  exact teo_1_2

/-- **La factorización de `1` es la lista vacía**: `IsFactorization f 1 → f =eq []`.
    Une `isFactorization_nil_one` con la unicidad del TFA (`1 ≥ 1` vía
    `lt_zero_one`). -/
theorem factorization_one_eq_nil {f : Term} (hf : IsFactorization f one) :
    axioms ⊢ (f =eq nil) :=
  factorization_unique lt_zero_one hf isFactorization_nil_one

end ROBINSON_PlusPlus.Minimal.Theorems.Block8

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block8 (
  Dvd
  IsPrime
  IsFactorization
  dvd_refl
  dvd_one
  dvd_zero
  dvd_trans
  dvd_mul_right
  dvd_mul_left
  dvd_mul_of_dvd_left
  dvd_mul_of_dvd_right
  dvd_add
  isPrime_zero_inconsistent
  isPrime_one_inconsistent
  pow_zero
  pow_succ
  prod_pairs_nil
  prod_pairs_cons
  isFactorization_nil_one
  ax_p_tfa
  factorization_exists
  factorization_unique
  lt_zero_one
  factorization_one_eq_nil
)

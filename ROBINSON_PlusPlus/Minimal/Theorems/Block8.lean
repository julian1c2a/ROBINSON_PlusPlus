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

set_option linter.unusedSimpArgs true

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block8

/-!
## BLOQUE VIII — PRIMOS

Implementa **Def 25** (`Dvd` y `IsPrime`) y lemas básicos de divisibilidad y
primalidad, siguiendo `TuplasFuncionesYListas.md §BLOQUE VIII Fase 17`.

**Alcance de esta fase**: `Dvd`, `IsPrime`, y los teoremas que no requieren
extender el lenguaje. Quedan **pendientes** (necesitan extensión del lenguaje):

* **Def 26 `IsFactorization(f,n)`**: requiere función de potencia `pow` y
  producto sobre listas (`prod_list`) — ninguno está en el lenguaje base.
* **Ax-P (TFA, ∀n≥1, ∃¹f. IsFactorization(f,n))**: la spec lo postula como
  axioma incluso en sistemas con inducción fuerte; pendiente de decidir
  si añadirlo a `Minimal` o reservarlo para `Intermediate/Full`.
* **Fases 18-19 (Gödelización, autorreferencia)**: requieren meta-codificación
  (G : símbolos → ℕ, ⌜·⌝, IsFormula, Dem). Fuera de scope del sistema
  `Minimal`; corresponderían a un módulo `Meta/` futuro.

**Estilo de formalización**: igual que `Block7`, `Dvd` e `IsPrime` se definen
como meta-predicados Lean (`Term → Prop` y `Term → Term → Prop`) parametrizados
por cuantificación universal sobre `Term`. Esto evita el manejo manual de
`liftTerm`/`substTerm` que aparecería al usar `forall_`/`ex` en FOL puro.
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

end ROBINSON_PlusPlus.Minimal.Theorems.Block8

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block8 (
  Dvd
  IsPrime
  dvd_refl
  dvd_one
  dvd_zero
  isPrime_zero_inconsistent
  isPrime_one_inconsistent
)

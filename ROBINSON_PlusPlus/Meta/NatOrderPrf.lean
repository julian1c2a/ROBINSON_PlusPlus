/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.NatOrderPrf

/-!
## META — NIVEL D real: ORDEN (`≤`) y asociatividad de `+` en `Prf`

Entregable **i‑a** de la ruta (1a) (`NEXT-STEPS.md`): la aritmética de orden existe hoy sólo a
nivel `⊢` (`Minimal/Theorems/Block3‑5`) y **no puede importarse** desde allí — no hay puente
`⊢ → Prf` (`Derives` tiene la ω‑regla; sólo existe `prf_to_derives`). Se re‑prueba en `Prf`, como
en su día se hizo con `Meta/ArithPrf.lean`.

**Destino:** monotonía del emparejamiento de Cantor ⟹ `sub‑código < código` ⟹ inducción fuerte
⟹ `pcc_eval_substfc` ⟹ los 7 tags de `lineWF` que faltan.

**Recordatorios del terreno** (`Minimal/Axioms.lean`):
* `add` recurre **por la derecha**: `a + 0 = a`, `a + σb = σ(a + b)`.
* `lt a b :⇔ ∃k. a + σk = b` (`ax13_lt_def`).
* `le a b := lt a b ∨ a =eq b` — **no es primitivo**: cada lema de `≤` arrastra el manejo de la
  disyunción interna.
-/

/-! ### Congruencias de `+` (vía Leibniz)

No existían: `ArithPrf` sólo tenía `prf_eq_congr_succ`/`_pred`. Mismo patrón (contexto de un
hueco + `prf_leibniz_subst`). -/

/-- Congruencia de `+` en el **primer** argumento. -/
theorem prf_eq_congr_add1 {t₁ t₂ : Term} (c : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (add t₁ c =eq add t₂ c) := by
  let f : Formula := Formula.eq (add (liftTerm 0 t₁) (liftTerm 0 c)) (add (.var 0) (liftTerm 0 c))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add t₁ c) (add s c) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (add t₁ c))

/-- Congruencia de `+` en el **segundo** argumento. -/
theorem prf_eq_congr_add2 {t₁ t₂ : Term} (c : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (add c t₁ =eq add c t₂) := by
  let f : Formula := Formula.eq (add (liftTerm 0 c) (liftTerm 0 t₁)) (add (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add c t₁) (add c s) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (add c t₁))

/-- Congruencia de `+` en el segundo argumento, en contexto. -/
theorem PrfH_eq_congr_add2 {Γ : List Formula} {t₁ t₂ : Term} (c : Term)
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (add c t₁ =eq add c t₂) := by
  let f : Formula := Formula.eq (add (liftTerm 0 c) (liftTerm 0 t₁)) (add (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add c t₁) (add c s) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (add c t₁)) Γ)

/-! ### Asociatividad de `+`

Pieza base del resto: la transitividad de `<` la necesita para componer testigos
(`a + σk = b` y `b + σj = c` ⟹ `a + σ(k + σj) = c`). Inducción sobre el **tercer** argumento
—el que `add` consume—, con los otros dos como parámetros protegidos por `liftTerm 0` y
devueltos intactos por `norm11`. -/

/-- **Asociatividad de `+`** en `Prf`: `(a + b) + c = a + (b + c)`. -/
theorem prf_add_assoc (a b c : Term) :
    Prf (add (add a b) c =eq add a (add b c)) := by
  have key : Prf (Formula.forall (Formula.eq
      (add (add (liftTerm 0 a) (liftTerm 0 b)) (.var 0))
      (add (liftTerm 0 a) (add (liftTerm 0 b) (.var 0))))) := by
    refine prf_nat_induction _ ?base ?step
    · -- ⚠️ el `liftTerm 0 a` de un parámetro ABSTRACTO no reduce solo: hay que `simp` antes
      simp only [substFormula, substTerm, substTerms, add, zero, Nat.reduceEqDiff, reduceIte,
        if_true, FOL.substTerm_liftTerm]
      exact prf_eq_trans (prf_add_zero_t (add a b))
        (prf_eq_symm (prf_eq_congr_add2 a (prf_add_zero_t b)))
    · refine Prf.gen _ ?_
      simp only [substFormula, substTerm, substTerms, add, succ, liftFormula, liftTerm, liftTerms,
        norm11, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction ?_
      have ih := prfH_hyp_self (Formula.eq
        (add (add (liftTerm 0 a) (liftTerm 0 b)) (.var 0))
        (add (liftTerm 0 a) (add (liftTerm 0 b) (.var 0))))
      -- `(a+b)+σn = σ((a+b)+n) = σ(a+(b+n)) = a+σ(b+n) = a+(b+σn)`
      refine PrfH_eq_trans
        (prf_to_prfH (prf_add_succ_t (add (liftTerm 0 a) (liftTerm 0 b)) (.var 0)) _) ?_
      refine PrfH_eq_trans (PrfH_eq_congr_succ ih) ?_
      refine PrfH_eq_trans
        (prf_to_prfH (prf_eq_symm (prf_add_succ_t (liftTerm 0 a)
          (add (liftTerm 0 b) (.var 0)))) _) ?_
      exact PrfH_eq_congr_add2 (liftTerm 0 a)
        (prf_to_prfH (prf_eq_symm (prf_add_succ_t (liftTerm 0 b) (.var 0))) _)
  have hc := prf_spec key c
  simpa only [substFormula, substTerm, substTerms, add, Nat.reduceEqDiff, reduceIte, if_true,
    FOL.substTerm_liftTerm] using hc

/-! ### Introducción de `≤`

`le a b` **es** `lt a b ∨ a =eq b`, así que la introducción son las dos reglas de la disyunción
(`j1`/`j2`) y la reflexividad sale de la rama derecha. -/

/-- `a < b ⟹ a ≤ b`. -/
theorem prf_le_of_lt (a b : Term) : Prf (lt a b ⇒ le a b) :=
  Prf.incl (Prf₀.j1 (lt a b) (Formula.eq a b))

/-- `a = b ⟹ a ≤ b`. -/
theorem prf_le_of_eq (a b : Term) : Prf ((a =eq b) ⇒ le a b) :=
  Prf.incl (Prf₀.j2 (lt a b) (Formula.eq a b))

/-- **Reflexividad de `≤`**. -/
theorem prf_le_refl (a : Term) : Prf (le a a) :=
  prf_mp (prf_le_of_eq a a) (prf_refl a)

/-! ### `<` estricto contra `+`

`a < a + σk` es inmediato: el testigo de `∃k. a + σk = b` es el propio `k` y la ecuación es
reflexividad. Es la semilla de la monotonía de Cantor. -/

/-- **`a < a + σk`** — testigo directo. -/
theorem prf_lt_add_succ (a k : Term) : Prf (lt a (add a (succ k))) :=
  prf_lt_intro a (add a (succ k)) k (prf_refl _)

end ROBINSON_PlusPlus.Meta.NatOrderPrf

export ROBINSON_PlusPlus.Meta.NatOrderPrf (
  prf_eq_congr_add1 prf_eq_congr_add2 PrfH_eq_congr_add2
  prf_add_assoc
  prf_le_of_lt prf_le_of_eq prf_le_refl
  prf_lt_add_succ
)

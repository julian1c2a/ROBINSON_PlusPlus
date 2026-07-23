/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatOrderPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.NatMulPrf

/-!
## META — NIVEL D real: aritmética de `·` en `Prf` (entregable **i‑b** de la ruta 1a)

**Hallazgo que abarata este entregable** (2026‑07‑23): las leyes algebraicas del producto **son
AXIOMAS de la teoría objeto** — `ax8_mul_zero`, `ax9_mul_succ`, `ax10_mul_comm`, `ax11_mul_assoc`,
`ax12_mul_distrib` están todas en la lista `axioms`. Portarlas a `Prf` es por tanto
**instanciación directa** (`prf_spec` + `simp`), no inducción. Lo mismo valía para `ax6_add_comm`
y `ax7_add_assoc` — ver la corrección al principio de `Meta/NatOrderPrf.lean`.

Sólo hay que **probar** lo que no es axioma: la identidad izquierda (`0 · n = 0`, `add` y `mul`
recurren por la derecha) y la **monotonía** (`a ≤ a · σk`), que es lo que Cantor necesita.

**Destino:** `prf_cantor_mono` (i‑c) ⟹ `sub‑código < código` ⟹ inducción fuerte ⟹
`pcc_eval_substfc` ⟹ los 7 tags de `lineWF` que faltan.
-/

/-! ### Las leyes, por instanciación directa de los axiomas -/

/-- `n · 0 = 0` — `ax8_mul_zero`. -/
theorem prf_mul_zero (n : Term) : Prf (mul n zero =eq zero) := by
  have hh := prf_spec (prf_ax (show ax8_mul_zero ∈ axioms by simp [axioms])) n
  simp [ax8_mul_zero, substFormula, substTerm, substTerms, mul, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `n · σm = n · m + n` — `ax9_mul_succ`. -/
theorem prf_mul_succ (n m : Term) : Prf (mul n (succ m) =eq add (mul n m) n) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax9_mul_succ ∈ axioms by simp [axioms])) n) m
  simp [ax9_mul_succ, substFormula, substTerm, substTerms, mul, add, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- `n · m = m · n` — `ax10_mul_comm`. -/
theorem prf_mul_comm (n m : Term) : Prf (mul n m =eq mul m n) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax10_mul_comm ∈ axioms by simp [axioms])) n) m
  simp [ax10_mul_comm, substFormula, substTerm, substTerms, mul,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Congruencias de `·` (vía Leibniz)

No existían, como no existían las de `+`. Mismo patrón. -/

/-- Congruencia de `·` en el **primer** argumento. -/
theorem prf_eq_congr_mul1 {t₁ t₂ : Term} (c : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (mul t₁ c =eq mul t₂ c) := by
  let f : Formula := Formula.eq (mul (liftTerm 0 t₁) (liftTerm 0 c)) (mul (.var 0) (liftTerm 0 c))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mul t₁ c) (mul s c) := by
    intro s
    simp only [f, substFormula, mul, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (mul t₁ c))

/-- Congruencia de `·` en el **segundo** argumento. -/
theorem prf_eq_congr_mul2 {t₁ t₂ : Term} (c : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (mul c t₁ =eq mul c t₂) := by
  let f : Formula := Formula.eq (mul (liftTerm 0 c) (liftTerm 0 t₁)) (mul (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mul c t₁) (mul c s) := by
    intro s
    simp only [f, substFormula, mul, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (mul c t₁))

/-! ### Identidad izquierda del producto

`0 · n = 0` **no** es axioma (`ax8` da `n · 0 = 0`, y `mul` recurre por la derecha), pero sale
gratis de la conmutatividad — que **sí** lo es (`ax10`). Nótese el contraste con `+`: allí
`0 + n = n` necesitó inducción sólo porque se probó **antes** de disponer de `ax6_add_comm`. -/

/-- `0 · n = 0` — vía conmutatividad. -/
theorem prf_zero_mul (n : Term) : Prf (mul zero n =eq zero) :=
  prf_eq_trans (prf_mul_comm zero n) (prf_mul_zero n)

/-- `n · 1 = n`. -/
theorem prf_mul_one (n : Term) : Prf (mul n one =eq n) := by
  show Prf (mul n (succ zero) =eq n)
  exact prf_eq_trans (prf_mul_succ n zero)
    (prf_eq_trans (prf_eq_congr_add1 n (prf_mul_zero n)) (prf_add_zero_left n))

/-! ### MONOTONÍA — lo que Cantor necesita

`a ≤ a · σk`: el producto por un sucesor no decrece. Se prueba por inducción sobre `k`, usando
`a · σk = a·k + a` (`ax9`) y `a ≤ a·k ⟹ a ≤ a·k + a`… pero ese último paso es justamente
`prf_le_self_add` con los sumandos al revés. Se hace la versión directa: `a · σk = a·k + a`, y
`a ≤ x + a` para todo `x`. -/

/-- **`a ≤ x + a`** — el sumando derecho está por debajo de la suma. Por casos sobre `x`
    (`prf_zero_or_succ`): si `x = 0` vale la igualdad (`0 + a = a`); si `x = σm`, entonces
    `x + a = σm + a = σ(m + a) = a + σ(m+a)`… se usa la conmutatividad para reducirlo a
    `a < a + σ(m + a)`, que es `prf_lt_add_succ`. -/
theorem prf_le_add_self (x a : Term) : Prf (le a (add x a)) := by
  have hcase := prf_zero_or_succ x
  refine prf_mp (prf_mp (prf_mp (Prf.incl (Prf₀.j3 _ _ (le a (add x a)))) hcase) ?_) ?_
  · -- rama `x = 0`: `0 + a = a`
    refine prf_deduction ?_
    have hx : PrfH [Formula.eq x zero] (x =eq zero) := prfH_hyp_self _
    have heq : PrfH [Formula.eq x zero] (add x a =eq a) :=
      PrfH_eq_trans (PrfH_eq_congr_add1 a hx) (prf_to_prfH (prf_add_zero_left a) _)
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_eq a (add x a)) _) (PrfH_eq_symm heq)
  · -- rama `x = σm`: `σm + a = a + σm` (conmutatividad) y `a < a + σm`
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (liftTerm 0 x) (succ (.var 0))]
      (le (liftTerm 0 a) (add (liftTerm 0 x) (liftTerm 0 a)))
    have hx : PrfH [Formula.eq (liftTerm 0 x) (succ (.var 0))]
        (liftTerm 0 x =eq succ (.var 0)) := prfH_hyp_self _
    -- `↑x + ↑a = σ#0 + ↑a = ↑a + σ#0`
    have heq : PrfH [Formula.eq (liftTerm 0 x) (succ (.var 0))]
        (add (liftTerm 0 x) (liftTerm 0 a) =eq add (liftTerm 0 a) (succ (.var 0))) :=
      PrfH_eq_trans (PrfH_eq_congr_add1 (liftTerm 0 a) hx)
        (prf_to_prfH (prf_add_comm (succ (.var 0)) (liftTerm 0 a)) _)
    have hlt : PrfH [Formula.eq (liftTerm 0 x) (succ (.var 0))]
        (lt (liftTerm 0 a) (add (liftTerm 0 x) (liftTerm 0 a))) :=
      PrfH_lt_subst2 (PrfH_eq_symm heq)
        (prf_to_prfH (prf_lt_add_succ (liftTerm 0 a) (.var 0)) _)
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt (liftTerm 0 a) _) _) hlt

/-- **`a ≤ a + x`** — versión simétrica (la que faltaba de i‑a). -/
theorem prf_le_self_add (a x : Term) : Prf (le a (add a x)) := by
  have h := prf_le_add_self x a
  exact prf_mp (prf_deduction (PrfH_le_subst2 (prf_to_prfH (prf_add_comm x a) _)
    (prfH_hyp_self _))) h

/-- **`a ≤ a · σk`** — la monotonía del producto que consume Cantor. -/
theorem prf_le_mul_succ (a k : Term) : Prf (le a (mul a (succ k))) :=
  prf_mp (prf_deduction (PrfH_le_subst2
    (prf_to_prfH (prf_eq_symm (prf_mul_succ a k)) _) (prfH_hyp_self _)))
    (prf_le_add_self (mul a k) a)

end ROBINSON_PlusPlus.Meta.NatMulPrf

export ROBINSON_PlusPlus.Meta.NatMulPrf (
  prf_mul_zero prf_mul_succ prf_mul_comm
  prf_eq_congr_mul1 prf_eq_congr_mul2
  prf_zero_mul prf_mul_one
  prf_le_add_self prf_le_self_add prf_le_mul_succ
)

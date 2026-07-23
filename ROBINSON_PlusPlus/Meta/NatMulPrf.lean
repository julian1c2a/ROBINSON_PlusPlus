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

/-- Congruencia de `·` en el primer argumento, en contexto. -/
theorem PrfH_eq_congr_mul1 {Γ : List Formula} {t₁ t₂ : Term} (c : Term)
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (mul t₁ c =eq mul t₂ c) := by
  let f : Formula := Formula.eq (mul (liftTerm 0 t₁) (liftTerm 0 c)) (mul (.var 0) (liftTerm 0 c))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mul t₁ c) (mul s c) := by
    intro s
    simp only [f, substFormula, mul, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (mul t₁ c)) Γ)

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

/-! ### Puentes `div2`/`mod2` (instancias de axioma) — cimiento de i‑c

Los tres son instanciación directa: `ax17_div_mod_eq`, `ax21_mod2_range` y `ax24_mod2_of_even`
están en la lista `axioms`. Son el cimiento del cálculo con `pair = div2 ∘ cantor_poly`. -/

/-- `div2(n)·2 + mod2(n) = n` — `ax17_div_mod_eq`. -/
theorem prf_div_mod_eq (n : Term) :
    Prf (add (mul (div2 n) two) (mod2 n) =eq n) := by
  have hh := prf_spec (prf_ax (show ax17_div_mod_eq ∈ axioms by simp [axioms])) n
  simp [ax17_div_mod_eq, substFormula, substTerm, substTerms, add, mul, div2, mod2, two, one,
    succ, zero, FOL.substTerm_liftTerm] at hh
  exact hh

/-- `mod2 n = 0 ∨ mod2 n = 1` — `ax21_mod2_range`. -/
theorem prf_mod2_range (n : Term) :
    Prf (lor (mod2 n =eq zero) (mod2 n =eq one)) := by
  have hh := prf_spec (prf_ax (show ax21_mod2_range ∈ axioms by simp [axioms])) n
  simp [ax21_mod2_range, substFormula, substTerm, substTerms, mod2, one, succ, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-! ### Monotonía aditiva

`x ≤ y ⟹ x + u ≤ y + u`. Es la pieza reutilizable que pide la monotonía del producto (y con
ella, Cantor). Se hace por `or_elim` sobre `≤`: la rama `=` es congruencia, la rama `<`
transporta el testigo (`x + σk = y` ⟹ `(x+u) + σk = y+u`, usando conmutatividad y asociatividad). -/

/-- **`x ≤ y ⟹ x + u ≤ y + u`**. -/
theorem prf_add_le_mono_right (x y u : Term) : Prf (le x y ⇒ le (add x u) (add y u)) := by
  refine prf_deduction ?_
  have hle : PrfH [le x y] (lor (lt x y) (Formula.eq x y)) := prfH_hyp_self _
  refine PrfH_or_elim hle ?_ ?_
  · -- rama `x < y`: transporta el testigo
    have hlt : PrfH (lt x y :: [le x y]) (lt x y) := PrfH.hyp _ _ (List.Mem.head _)
    have hstep : PrfH (lt x y :: [le x y]) (lt (add x u) (add y u)) := by
      have himp : Prf (lt x y ⇒ lt (add x u) (add y u)) := by
        have hgen : Prf (Formula.ex (Formula.eq (add (liftTerm 0 x) (succ (.var 0)))
            (liftTerm 0 y)) ⇒ lt (add x u) (add y u)) := by
          refine prf_ex_elim_imp ?_
          show PrfH [Formula.eq (add (liftTerm 0 x) (succ (.var 0))) (liftTerm 0 y)]
            (lt (add (liftTerm 0 x) (liftTerm 0 u)) (add (liftTerm 0 y) (liftTerm 0 u)))
          refine PrfH_lt_intro _ _ (.var 0) ?_
          -- `(↑x+↑u) + σ#0 = (↑x + σ#0) + ↑u = ↑y + ↑u`
          refine PrfH_eq_trans (prf_to_prfH (prf_add_assoc (liftTerm 0 x) (liftTerm 0 u)
            (succ (.var 0))) _) ?_
          refine PrfH_eq_trans (prf_to_prfH (prf_eq_congr_add2 (liftTerm 0 x)
            (prf_add_comm (liftTerm 0 u) (succ (.var 0)))) _) ?_
          refine PrfH_eq_trans (prf_to_prfH (prf_eq_symm (prf_add_assoc (liftTerm 0 x)
            (succ (.var 0)) (liftTerm 0 u))) _) ?_
          exact PrfH_eq_congr_add1 (liftTerm 0 u)
            (prfH_hyp_self (Formula.eq (add (liftTerm 0 x) (succ (.var 0))) (liftTerm 0 y)))
        exact prf_deduction (PrfH.mp _ _ _ (prf_to_prfH hgen _)
          (PrfH_iff_mp (prf_lt_iff x y) (prfH_hyp_self _)))
      exact PrfH.mp _ _ _ (prf_to_prfH himp _) hlt
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt (add x u) (add y u)) _) hstep
  · -- rama `x = y`: congruencia
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_eq (add x u) (add y u)) _)
      (PrfH_eq_congr_add1 u (PrfH.hyp _ _ (List.Mem.head _)))

/-! ### Monotonía multiplicativa (i‑c)

`x ≤ y ⟹ x·c ≤ y·c`, por inducción sobre `c` usando `x·σc = x·c + x` (`ax9`) y la monotonía
aditiva en **ambos** argumentos. La hipótesis `x ≤ y` se mete **dentro** de la fórmula de
inducción (no se puede dejar fuera: `prf_nat_induction` pide base y paso como `Prf` cerrados). -/

/-- `u ≤ v ⟹ a + u ≤ a + v` — simétrico de `prf_add_le_mono_right`, vía conmutatividad. -/
theorem prf_add_le_mono_left (a u v : Term) : Prf (le u v ⇒ le (add a u) (add a v)) := by
  refine prf_deduction ?_
  have h : PrfH [le u v] (le (add u a) (add v a)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_add_le_mono_right u v a) _) (prfH_hyp_self _)
  exact PrfH_le_subst2 (prf_to_prfH (prf_add_comm v a) _)
    (PrfH_le_subst1 (prf_to_prfH (prf_add_comm u a) _) h)

/-- **Monotonía aditiva en ambos argumentos**: `x ≤ y ⟹ u ≤ v ⟹ x + u ≤ y + v`. -/
theorem prf_add_le_mono (x y u v : Term) :
    Prf (le x y ⇒ (le u v ⇒ le (add x u) (add y v))) := by
  refine prf_deduction (deduction_aux ?_ (le u v) [le x y] rfl)
  have h1 : PrfH [le u v, le x y] (le (add x u) (add y u)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_add_le_mono_right x y u) _)
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  have h2 : PrfH [le u v, le x y] (le (add y u) (add y v)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_add_le_mono_left y u v) _) (PrfH.hyp _ _ (List.Mem.head _))
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (prf_le_trans (add x u) (add y u) (add y v)) _) h1) h2

/-- **Monotonía multiplicativa**: `x ≤ y ⟹ x·c ≤ y·c`. -/
theorem prf_mul_le_mono_right (x y c : Term) : Prf (le x y ⇒ le (mul x c) (mul y c)) := by
  have key : Prf (Formula.forall (Formula.impl (le (liftTerm 0 x) (liftTerm 0 y))
      (le (mul (liftTerm 0 x) (.var 0)) (mul (liftTerm 0 y) (.var 0))))) := by
    refine prf_nat_induction _ ?base ?step
    · -- `x·0 = 0 = y·0`
      simp only [substFormula, substTerm, substTerms, le, lt, lor, mul, zero,
        Nat.reduceEqDiff, reduceIte, if_true, FOL.substTerm_liftTerm]
      refine prf_mp (Prf.incl (Prf₀.p1 _ (le x y))) ?_
      exact prf_le_subst2 (prf_eq_symm (prf_mul_zero y))
        (prf_le_subst1 (prf_eq_symm (prf_mul_zero x)) (prf_le_refl zero))
    · refine Prf.gen _ ?_
      simp only [substFormula, substTerm, substTerms, le, lt, lor, mul, succ, liftFormula,
        liftTerm, liftTerms, norm11, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      refine prf_deduction (deduction_aux ?_ (le (liftTerm 0 x) (liftTerm 0 y)) _ rfl)
      -- Γ = [x ≤ y, IH] — hay que escribirlo: los `_` no lo infieren
      let Δ : List Formula := [le (liftTerm 0 x) (liftTerm 0 y),
        Formula.impl (le (liftTerm 0 x) (liftTerm 0 y))
          (le (mul (liftTerm 0 x) (.var 0)) (mul (liftTerm 0 y) (.var 0)))]
      have hxy : PrfH Δ (le (liftTerm 0 x) (liftTerm 0 y)) := PrfH.hyp _ _ (List.Mem.head _)
      have hih : PrfH Δ (le (mul (liftTerm 0 x) (.var 0)) (mul (liftTerm 0 y) (.var 0))) :=
        PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) hxy
      -- `x·σn = x·n + x ≤ y·n + y = y·σn`
      have hsum : PrfH Δ (le (add (mul (liftTerm 0 x) (.var 0)) (liftTerm 0 x))
          (add (mul (liftTerm 0 y) (.var 0)) (liftTerm 0 y))) :=
        PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_add_le_mono
          (mul (liftTerm 0 x) (.var 0)) (mul (liftTerm 0 y) (.var 0))
          (liftTerm 0 x) (liftTerm 0 y)) _) hih) hxy
      exact PrfH_le_subst2 (prf_to_prfH (prf_eq_symm (prf_mul_succ (liftTerm 0 y) (.var 0))) _)
        (PrfH_le_subst1 (prf_to_prfH (prf_eq_symm (prf_mul_succ (liftTerm 0 x) (.var 0))) _) hsum)
  have hc := prf_spec key c
  simpa only [substFormula, substTerm, substTerms, le, lt, lor, mul, Nat.reduceEqDiff, reduceIte,
    if_true, FOL.substTerm_liftTerm] using hc

/-! ### Irreflexividad, tricotomía y CANCELACIÓN multiplicativa

`ax18_lt_irrefl` y `ax19_lt_trichotomy` son axiomas pero **no estaban portados** a `Prf`. Con
ellos, la cancelación (`x·c < y·c ⟹ x < y`) sale por tricotomía: los otros dos casos
(`x = y` y `y < x`) contradicen la hipótesis vía irreflexividad. Recuérdese `neg A = A ⇒ ⊥`. -/

/-- `¬ (a < a)` — `ax18_lt_irrefl`. -/
theorem prf_lt_irrefl (a : Term) : Prf (neg (lt a a)) := by
  have hh := prf_spec (prf_ax (show ax18_lt_irrefl ∈ axioms by simp [axioms])) a
  simp [ax18_lt_irrefl, substFormula, substTerm, substTerms, neg, lt,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- Tricotomía — `ax19_lt_trichotomy`. -/
theorem prf_lt_trichotomy (a b : Term) :
    Prf (lor (lt a b) (lor (a =eq b) (lt b a))) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax19_lt_trichotomy ∈ axioms by simp [axioms])) a) b
  simp [ax19_lt_trichotomy, substFormula, substTerm, substTerms, lor, lt,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- De una contradicción `a < a` sale cualquier cosa (irreflexividad + ex falso). -/
theorem PrfH_absurd_lt {Γ : List Formula} {C : Formula} (a : Term)
    (h : PrfH Γ (lt a a)) : PrfH Γ C :=
  PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq C))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_irrefl a) _) h)

/-- **CANCELACIÓN multiplicativa**: `x·c < y·c ⟹ x < y`. Recíproca de la monotonía; sale por
    tricotomía sobre `x`,`y`: si `x = y` la hipótesis da `x·c < x·c`; si `y < x`, la monotonía da
    `y·c ≤ x·c` y con la hipótesis sale otra vez `x·c < x·c`. -/
theorem prf_lt_of_mul_lt_mul_right (x y c : Term) :
    Prf (lt (mul x c) (mul y c) ⇒ lt x y) := by
  refine prf_deduction ?_
  have hyp : PrfH [lt (mul x c) (mul y c)] (lt (mul x c) (mul y c)) := prfH_hyp_self _
  refine PrfH_or_elim (prf_to_prfH (prf_lt_trichotomy x y) _) ?_ ?_
  · -- `x < y`: es la conclusión
    exact PrfH.hyp _ _ (List.Mem.head _)
  · refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
    · -- `x = y`: la hipótesis se vuelve `x·c < x·c`
      let Δ₁ : List Formula := [Formula.eq x y, lor (Formula.eq x y) (lt y x),
        lt (mul x c) (mul y c)]
      have heq : PrfH Δ₁ (mul y c =eq mul x c) :=
        PrfH_eq_symm (PrfH_eq_congr_mul1 c (PrfH.hyp _ _ (List.Mem.head _)))
      exact PrfH_absurd_lt (mul x c)
        (PrfH_lt_subst2 heq (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · -- `y < x`: monotonía da `y·c ≤ x·c`, y con la hipótesis `x·c < x·c`
      let Δ₂ : List Formula := [lt y x, lor (Formula.eq x y) (lt y x),
        lt (mul x c) (mul y c)]
      have hle : PrfH Δ₂ (le (mul y c) (mul x c)) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_mul_le_mono_right y x c) _)
          (PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt y x) _) (PrfH.hyp _ _ (List.Mem.head _)))
      have hlt : PrfH Δ₂ (lt (mul x c) (mul x c)) :=
        PrfH.mp _ _ _
          (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_le_trans (mul x c) (mul y c) (mul x c)) _)
            (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
          hle
      exact PrfH_absurd_lt (mul x c) hlt

end ROBINSON_PlusPlus.Meta.NatMulPrf

export ROBINSON_PlusPlus.Meta.NatMulPrf (
  prf_mul_zero prf_mul_succ prf_mul_comm
  prf_eq_congr_mul1 prf_eq_congr_mul2 PrfH_eq_congr_mul1
  prf_zero_mul prf_mul_one
  prf_le_add_self prf_le_self_add prf_le_mul_succ
  prf_div_mod_eq prf_mod2_range prf_add_le_mono_right
  prf_add_le_mono_left prf_add_le_mono prf_mul_le_mono_right
  prf_lt_irrefl prf_lt_trichotomy PrfH_absurd_lt prf_lt_of_mul_lt_mul_right
)

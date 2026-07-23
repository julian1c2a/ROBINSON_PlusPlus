/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatMulPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.CantorMonoPrf

/-!
## META — NIVEL D real: MONOTONÍA DE CANTOR (entregable **i‑c** de la ruta 1a)

**Objetivo:** `h < cons h t` y `t < cons h t` en `Prf`, es decir **sub‑código < código**. Con eso
la inducción fuerte sobre códigos (ii) es derivable de `ax_induction`, y con ella
`pcc_eval_substfc` (iii) y los 7 tags de `lineWF` que faltan.

⚠️ **`cons h t` NO es defeq a `pair h (σt)`** (verificado): `cons` es `.func "::"` opaco y la
conexión con la aritmética es el **axioma objeto** `ax_L0_cons_def`. Todo el cálculo de esta
sección va por tanto a nivel `Prf`, no por `rfl`.

Cadena de definiciones (`Minimal/Axioms.lean`):
* `cons h t = pair h (σt)`  — `ax_L0_cons_def`
* `pair x y = cantor_func x y = div2 (cantor_poly x y)` — definicional
* `cantor_poly x y = (x + y)·σ(x + y) + 2·y` — definicional
-/

/-! ### Paso 1 — el puente `cons ↔ pair` (el único que no es definicional) -/

/-- **`cons h t = pair h (σt)`** — instancia de `ax_L0_cons_def`. Es el puente entre el
    constructor de listas (opaco) y la aritmética de Cantor. -/
theorem prf_cons_def (h t : Term) : Prf (cons h t =eq pair h (succ t)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_L0_cons_def ∈ axioms by simp [axioms])) h) t
  simp [ax_L0_cons_def, substFormula, substTerm, substTerms, cons, pair, cantor_func,
    cantor_poly, div2, add, mul, succ, two, one, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Paso 2 — copias locales por ORDEN DE IMPORTS

⚠️ **Defecto detectado por verificación adversarial** (y confirmado con el compilador): dos lemas
que parecían disponibles **no están en scope aquí**.

* `prf_lt_succ_self` vive en `Meta/BdAllIntroPrf.lean:295`, y ese módulo importa `D3InDotPrf` +
  `PropCodePrf` — la **cima** de la pila D3. `CantorMonoPrf` está en la **base**
  (`NatMulPrf → NatOrderPrf → NatArithPrf`). Importarlo invertiría la capa y arriesga ciclo con
  los consumidores previstos de esta monotonía (los 7 tags de `lineWF`).
* `prf_lt_subst2` (nivel `Prf`) vive en `Meta/BoundedInPrf.lean`, también posterior.
  (`PrfH_lt_subst2` sí está, por la copia local de `NatOrderPrf`.)

Se hacen copias locales con sufijo `_cm`. **No se exportan con el nombre original**: `Meta.lean`
importa ambos módulos y coincidir crearía ambigüedad en la raíz — la misma trampa que ya costó
`substTerm_numeralM`. -/

/-- `n < σn` — copia local (el original está aguas abajo, ver nota de sección). -/
theorem prf_lt_succ_self_cm (n : Term) : Prf (lt n (succ n)) :=
  prf_lt_intro n (succ n) zero
    (prf_eq_trans (prf_add_succ_t n zero) (prf_eq_congr_succ (prf_add_zero_t n)))

/-- Sustitución en el 2º argumento de `<` a nivel `Prf` — copia local. -/
theorem prf_lt_subst2_cm {a b₁ b₂ : Term} (h : Prf (b₁ =eq b₂)) (hlt : Prf (lt a b₁)) :
    Prf (lt a b₂) := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b₂) ▸ prf_leibniz_subst (A := f) h ((hS b₁) ▸ hlt)

/-! ### Paso 3 — aritmética de `one` y `two`

`one = σ0` y `two = σone` son **defeq**, así que estos dos salen de `ax4`/`ax5`/`ax8`/`ax9` sin
inducción. `prf_mul_two` es el que convierte «el doble» en una suma, que es como se manipula la
ecuación de `ax17` (`div2(n)·two + mod2(n) = n`). -/

/-- `n + 1 = σn`. -/
theorem prf_add_one (n : Term) : Prf (add n one =eq succ n) :=
  prf_eq_trans (prf_add_succ_t n zero) (prf_eq_congr_succ (prf_add_zero_t n))

/-- `n · 2 = n + n`. -/
theorem prf_mul_two (n : Term) : Prf (mul n two =eq add n n) :=
  prf_eq_trans (prf_mul_succ n one) (prf_eq_congr_add1 n (prf_mul_one n))

/-! ### Paso 4 — `mod2 n ≤ 1`

La cota del resto. Es lo que permite pasar de la ecuación exacta de `ax17`
(`div2(n)·2 + mod2(n) = n`) a una **desigualdad** utilizable, y con ello **evitar
`cantor_poly_is_even`** (`ax24`), que era la pieza más incierta del plan original: no hace falta
saber que `cantor_poly` es par, basta acotar su resto. -/

/-- Eliminación de la disyunción con las dos ramas ya cerradas (azúcar sobre `j3`; hoy se escribe
    inline en varios sitios). -/
theorem prf_or_elim {A B C : Formula} (hor : Prf (lor A B))
    (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) : Prf C :=
  prf_mp (prf_mp (prf_mp (Prf.incl (Prf₀.j3 A B C)) hor) h1) h2

/-- `0 ≤ 1`. (`one = σ0` es defeq, así que `prf_zero_lt_succ zero` ya **es** `lt zero one`.) -/
theorem prf_le_zero_one : Prf (le zero one) :=
  prf_mp (prf_le_of_lt zero one) (prf_zero_lt_succ zero)

/-- **`mod2 n ≤ 1`** — de `ax21_mod2_range` por casos. -/
theorem prf_le_mod2_one (n : Term) : Prf (le (mod2 n) one) := by
  refine prf_or_elim (prf_mod2_range n) ?_ ?_
  · -- rama `mod2 n = 0`
    refine prf_deduction ?_
    exact PrfH_le_subst1 (PrfH_eq_symm (prfH_hyp_self (Formula.eq (mod2 n) zero)))
      (prf_to_prfH prf_le_zero_one _)
  · -- rama `mod2 n = 1`
    refine prf_deduction ?_
    exact PrfH_le_subst1 (PrfH_eq_symm (prfH_hyp_self (Formula.eq (mod2 n) one)))
      (prf_to_prfH (prf_le_refl one) _)

/-! ### Paso 5 — monotonía de `σ` sobre `≤`

`a ≤ b ⟹ σa ≤ σb`. Sus dos mitades ya existían (`prf_succ_lt_succ_of_lt` para `<`, la congruencia
para `=`) pero el lema combinado no. -/

/-- **`a ≤ b ⟹ σa ≤ σb`**. -/
theorem prf_le_succ_succ (a b : Term) : Prf (le a b ⇒ le (succ a) (succ b)) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prfH_hyp_self (le a b)) ?_ ?_
  · -- rama `a < b`
    have hlt : PrfH (lt a b :: [le a b]) (lt (succ a) (succ b)) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_succ_lt_succ_of_lt a b) _) (PrfH.hyp _ _ (List.Mem.head _))
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt (succ a) (succ b)) _) hlt
  · -- rama `a = b`
    have heq : PrfH (Formula.eq a b :: [le a b]) (succ a =eq succ b) :=
      PrfH_eq_congr_succ (PrfH.hyp _ _ (List.Mem.head _))
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_eq (succ a) (succ b)) _) heq

/-! ### Paso 6 — el núcleo contradictorio: `¬ (σw ≤ w)`

Es el lema que cierra el argumento por contradicción de las dos mitades: cuando la hipótesis
`cons h t ≤ h` se propaga por la ecuación de Cantor, desemboca exactamente en `σσz ≤ σz`, o sea
en una instancia de éste. Ambas ramas mueren en `w < w` (irreflexividad). -/

/-- **`σw ≤ w ⟹ ⊥`**. -/
theorem prf_not_le_succ_self (w : Term) : Prf (le (succ w) w ⇒ Formula.bottom) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prfH_hyp_self (le (succ w) w)) ?_ ?_
  · -- rama `σw < w`: con `w < σw` da `w < w`
    have hww : PrfH (lt (succ w) w :: [le (succ w) w]) (lt w w) :=
      PrfH.mp _ _ _
        (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans w (succ w) w) _)
          (prf_to_prfH (prf_lt_succ_self_cm w) _))
        (PrfH.hyp _ _ (List.Mem.head _))
    exact PrfH_absurd_lt w hww
  · -- rama `σw = w`: reescribe `w < σw` a `w < w`
    have hww : PrfH (Formula.eq (succ w) w :: [le (succ w) w]) (lt w w) :=
      PrfH_lt_subst2 (PrfH.hyp _ _ (List.Mem.head _))
        (prf_to_prfH (prf_lt_succ_self_cm w) _)
    exact PrfH_absurd_lt w hww

/-! ### Pasos 7–8 — el término CUADRÁTICO de Cantor domina al doble

La clave de la mitad izquierda: `cantor_poly h (σt)` contiene `s·σs` con `s = h + σt`, y hay que
ver que eso ya supera a `2h+2`. Se hace en dos escalones, evitando la **monotonía estricta del
producto** (que no existe en el catálogo y costaría construir).

⚠️ **La hipótesis `a = σk` es OBLIGATORIA** en esta forma, no un adorno: el catálogo sólo ofrece
`prf_le_mul_succ a k : le a (a·σk)`, es decir, la cota necesita que el multiplicador sea
**un sucesor**. Se suministra siempre desde `prf_add_succ_t h t` (que da `s = σ(h+t)`). -/

/-- **`a ≤ a·a`**, para `a` un sucesor. -/
theorem prf_le_self_mul_self {a k : Term} (h : Prf (a =eq succ k)) : Prf (le a (mul a a)) :=
  prf_le_subst2 (prf_eq_congr_mul2 a (prf_eq_symm h)) (prf_le_mul_succ a k)

/-- **`a + a ≤ a·σa`**, para `a` un sucesor. Es el escalón donde el término cuadrático de Cantor
    domina al doble; usa sólo monotonía aditiva, no monotonía estricta del producto. -/
theorem prf_le_double_self_mul_succ {a k : Term} (h : Prf (a =eq succ k)) :
    Prf (le (add a a) (mul a (succ a))) :=
  prf_le_subst2 (prf_eq_symm (prf_mul_succ a a))
    (prf_mp (prf_add_le_mono_right a (mul a a) a) (prf_le_self_mul_self h))

end ROBINSON_PlusPlus.Meta.CantorMonoPrf

export ROBINSON_PlusPlus.Meta.CantorMonoPrf (
  prf_cons_def prf_lt_succ_self_cm prf_lt_subst2_cm prf_add_one prf_mul_two
  prf_or_elim prf_le_zero_one prf_le_mod2_one
  prf_le_succ_succ prf_not_le_succ_self
  prf_le_self_mul_self prf_le_double_self_mul_succ
)

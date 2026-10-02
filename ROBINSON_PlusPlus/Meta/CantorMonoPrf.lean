/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatMulPrf

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`ax_induction`, `cantor_poly_is_even`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

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

⚠️ **`cons h t` NO es defeq a `σ (pair h t)`** (verificado): `cons` es `.func "::"` opaco y la
conexión con la aritmética es el **axioma objeto** `ax_L0_cons_def`. Todo el cálculo de esta
sección va por tanto a nivel `Prf`, no por `rfl`.

Cadena de definiciones (`Minimal/Axioms.lean`):
* `cons h t = σ (pair h t)`  — `ax_L0_cons_def` (ADR-113; antes `pair h (σt)`)
* `pair x y = cantor_func x y = div2 (cantor_poly x y)` — definicional
* `cantor_poly x y = (x + y)·σ(x + y) + 2·y` — definicional
-/

/-! ### Paso 1 — el puente `cons ↔ pair` (el único que no es definicional) -/

/-- **`cons h t = σ (pair h t)`** — instancia de `ax_L0_cons_def` (salida (5) de ADR-093). Es el
    puente entre el constructor de listas (opaco) y la aritmética de Cantor. -/
theorem prf_cons_def (h t : Term) : Prf (cons h t =eq succ (pair h t)) := by
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
  prf_mp (prf_mp (prf_mp (Prf.incl (Prfᵢ.j3 A B C)) hor) h1) h2

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
`σ(div2 c) ≤ a` se propaga por la ecuación de Cantor, desemboca exactamente en `σσz ≤ σz`, o sea
en una instancia de éste (paso 11c). Ambas ramas mueren en `w < w` (irreflexividad). -/

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

`cantor_poly h t` contiene `s·σs` con `s = h + t`, y hay que ver que eso ya supera a `s+s`. Se
hace en dos escalones, evitando la **monotonía estricta del producto** (que no existe en el
catálogo y costaría construir).

⚠️ En esta forma **la hipótesis `a = σk` es obligatoria**: el catálogo sólo ofrece
`prf_le_mul_succ a k : le a (a·σk)`. Con `cons = σ (pair h t)` (ADR-113) `s = h + t` puede ser `0`,
y por eso existen las variantes `_all` de abajo (inducción, el paso no usa la hipótesis). -/

/-- **`a ≤ a·a`**, para `a` un sucesor. -/
theorem prf_le_self_mul_self {a k : Term} (h : Prf (a =eq succ k)) : Prf (le a (mul a a)) :=
  prf_le_subst2 (prf_eq_congr_mul2 a (prf_eq_symm h)) (prf_le_mul_succ a k)

/-- **`a + a ≤ a·σa`**, para `a` un sucesor. Es el escalón donde el término cuadrático de Cantor
    domina al doble; usa sólo monotonía aditiva, no monotonía estricta del producto. -/
theorem prf_le_double_self_mul_succ {a k : Term} (h : Prf (a =eq succ k)) :
    Prf (le (add a a) (mul a (succ a))) :=
  prf_le_subst2 (prf_eq_symm (prf_mul_succ a a))
    (prf_mp (prf_add_le_mono_right a (mul a a) a) (prf_le_self_mul_self h))

/-- **`a ≤ a·a` para TODO `a`** — por inducción; el paso no usa la hipótesis (`σk ≤ σk·σk` es
    `prf_le_mul_succ`) y la base es `0·0 = 0`. Sustituye a la hipótesis `a = σk` de
    `prf_le_self_mul_self` donde `a` puede ser `0`. -/
theorem prf_le_self_mul_self_all (a : Term) : Prf (le a (mul a a)) := by
  have key : Prf (Formula.forall (le (.var 0) (mul (.var 0) (.var 0)))) := by
    refine prf_nat_induction _ ?base ?step
    · show Prf (le zero (mul zero zero))
      exact prf_mp (prf_le_of_eq zero (mul zero zero)) (prf_eq_symm (prf_mul_zero zero))
    · refine Prf.gen _ ?_
      simp only [le, lt, substFormula, substTerm, substTerms, zero, succ, mul, liftFormula, liftTerm,
        liftTerms, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub,
        reduceIte, if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      exact prf_deduction (prf_to_prfH (prf_le_mul_succ (succ (.var 0)) (.var 0)) _)
  have ha := prf_spec key a
  simpa only [le, lt, substFormula, substTerm, substTerms, mul, Nat.reduceEqDiff, reduceIte,
    if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] using ha

/-- **`a + a ≤ a·σa`** para TODO `a`. -/
theorem prf_le_double_self_mul_succ_all (a : Term) : Prf (le (add a a) (mul a (succ a))) :=
  prf_le_subst2 (prf_eq_symm (prf_mul_succ a a))
    (prf_mp (prf_add_le_mono_right a (mul a a) a) (prf_le_self_mul_self_all a))

/-! ### Pasos 9–10 — de `s+s` a `cantor_poly h t`

Con `s := h + t`, `cantor_poly h t = s·σs + 2·t`. El sumando `2·t` se trata como **OPACO**: sólo
hace falta que *esté* (`a ≤ a + x`). -/

/-- Abreviatura: el polinomio de Cantor de `⟨h,t⟩` (es `cantor_poly h t` desplegado). -/
abbrev cpOf (h t : Term) : Term :=
  add (mul (add h t) (succ (add h t))) (mul two t)

/-- **`s + s ≤ cantor_poly h t`** con `s = h + t`. -/
theorem prf_le_double_s_cantor (h t : Term) :
    Prf (le (add (add h t) (add h t)) (cpOf h t)) :=
  prf_mp
    (prf_mp (prf_le_trans (add (add h t) (add h t)) (mul (add h t) (succ (add h t))) (cpOf h t))
      (prf_le_double_self_mul_succ_all (add h t)))
    (prf_le_self_add (mul (add h t) (succ (add h t))) (mul two t))

/-- De `a ≤ s` a `a + a ≤ cantor_poly h t`. -/
theorem prf_le_double_cantor_of_le {a h t : Term} (ha : Prf (le a (add h t))) :
    Prf (le (add a a) (cpOf h t)) :=
  prf_mp
    (prf_mp (prf_le_trans (add a a) (add (add h t) (add h t)) (cpOf h t))
      (prf_mp (prf_mp (prf_add_le_mono a (add h t) a (add h t)) ha) ha))
    (prf_le_double_s_cantor h t)

/-! ### Paso 11a — las dos identidades que hacen encajar la contradicción

* `σa + σa = σσ(a+a)`
* `n·2 + 1 = σ(n+n)` -/

/-- `σa + σa = σσ(a+a)`. -/
theorem prf_succ_add_succ_eq (a : Term) :
    Prf (add (succ a) (succ a) =eq succ (succ (add a a))) :=
  prf_eq_trans (prf_add_succ_t (succ a) a) (prf_eq_congr_succ (prf_add_succ_left a a))

/-- `n·2 + 1 = σ(n+n)`. -/
theorem prf_mul_two_add_one (n : Term) :
    Prf (add (mul n two) one =eq succ (add n n)) :=
  prf_eq_trans (prf_eq_congr_add1 one (prf_mul_two n)) (prf_add_one (add n n))

/-! ### Paso 11b — la ecuación de `ax17` sobre `pair h t = div2 (cantor_poly h t)` -/

/-- **`cons h t = σ (div2 (cantor_poly h t))`** — `prf_cons_def` con `pair` desplegado. -/
theorem prf_cons_div2 (h t : Term) : Prf (cons h t =eq succ (div2 (cpOf h t))) :=
  prf_cons_def h t

/-- **La ecuación de `ax17` para `pair h t`**: `(div2 cp)·2 + mod2(cp) = cp`. -/
theorem prf_pair_div_mod (h t : Term) :
    Prf (add (mul (div2 (cpOf h t)) two) (mod2 (cpOf h t)) =eq cpOf h t) :=
  prf_div_mod_eq (cpOf h t)

/-! ### Paso 11c — el núcleo: `a + a ≤ c ⟹ a < σ(div2 c)`

Si `σP ≤ a` (con `P := div2 c`), entonces `(σP)·2 ≤ a + a ≤ c = P·2 + mod2 c ≤ P·2 + 1`, y por las
identidades de 11a eso es `σσ(P+P) ≤ σ(P+P)`: `prf_not_le_succ_self`. -/

/-- **`σ(div2 c) ≤ a ⟹ ⊥`**, si `a + a ≤ c`. -/
theorem prf_bot_of_le_succ_div2 {a c : Term} (hac : Prf (le (add a a) c)) :
    Prf (le (succ (div2 c)) a ⇒ Formula.bottom) := by
  refine prf_deduction ?_
  let P : Term := div2 c
  let Γ : List Formula := [le (succ P) a]
  -- (1) el doble, monótono, y `a·2 = a + a`
  have hC2 : PrfH Γ (le (mul (succ P) two) (add a a)) :=
    PrfH_le_subst2 (prf_to_prfH (prf_mul_two a) _)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_mul_le_mono_right (succ P) a two) _) (prfH_hyp_self _))
  -- (2) hasta `c`
  have hc : PrfH Γ (le (mul (succ P) two) c) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_le_trans _ _ _) _) hC2) (prf_to_prfH hac _)
  -- (3) `c = P·2 + mod2 c ≤ P·2 + 1`
  have hcb : Prf (le c (add (mul P two) one)) :=
    prf_le_subst1 (prf_div_mod_eq c)
      (prf_mp (prf_mp (prf_add_le_mono (mul P two) (mul P two) (mod2 c) one) (prf_le_refl _))
        (prf_le_mod2_one c))
  have htr : PrfH Γ (le (mul (succ P) two) (add (mul P two) one)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_le_trans _ _ _) _) hc) (prf_to_prfH hcb _)
  -- (4) reconocer `σw ≤ w` con `w = σ(P+P)`
  have hfin : PrfH Γ (le (succ (succ (add P P))) (succ (add P P))) :=
    PrfH_le_subst2 (prf_to_prfH (prf_mul_two_add_one P) _)
      (PrfH_le_subst1 (prf_to_prfH (prf_eq_trans (prf_mul_two (succ P)) (prf_succ_add_succ_eq P)) _)
        htr)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_le_succ_self (succ (add P P))) _) hfin

/-- **`a + a ≤ c ⟹ a < σ(div2 c)`**, por tricotomía. -/
theorem prf_lt_succ_div2 {a c : Term} (hac : Prf (le (add a a) c)) :
    Prf (lt a (succ (div2 c))) := by
  let C : Term := succ (div2 c)
  refine prf_or_elim (prf_lt_trichotomy a C) (prf_deduction (prfH_hyp_self _)) ?_
  refine prf_deduction ?_
  refine PrfH_or_elim (prfH_hyp_self (lor (Formula.eq a C) (lt C a))) ?_ ?_
  · have hle : PrfH (Formula.eq a C :: [lor (Formula.eq a C) (lt C a)]) (le C a) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_eq C a) _)
        (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_bot_of_le_succ_div2 hac) _) hle)
  · have hle : PrfH (lt C a :: [lor (Formula.eq a C) (lt C a)]) (le C a) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt C a) _) (PrfH.hyp _ _ (List.Mem.head _))
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_bot_of_le_succ_div2 hac) _) hle)

/-! ### Pasos 12–13 — las dos mitades

`h ≤ h + t` y `t ≤ h + t`; el núcleo da `· < σ(div2 cp)`, y `prf_cons_div2` lo reescribe a `cons`. -/

/-- **`h < cons h t`** — sub‑código (cabeza) estrictamente menor que el código. -/
theorem prf_cantor_mono_left (h t : Term) : Prf (lt h (cons h t)) :=
  prf_lt_subst2_cm (prf_eq_symm (prf_cons_div2 h t))
    (prf_lt_succ_div2 (prf_le_double_cantor_of_le (prf_le_self_add h t)))

/-- **`t < cons h t`** — sub‑código (cola) estrictamente menor que el código. -/
theorem prf_cantor_mono_right (h t : Term) : Prf (lt t (cons h t)) :=
  prf_lt_subst2_cm (prf_eq_symm (prf_cons_div2 h t))
    (prf_lt_succ_div2 (prf_le_double_cantor_of_le (prf_le_add_self h t)))

end ROBINSON_PlusPlus.Meta.CantorMonoPrf

export ROBINSON_PlusPlus.Meta.CantorMonoPrf (
  prf_cons_def prf_lt_succ_self_cm prf_lt_subst2_cm prf_add_one prf_mul_two
  prf_or_elim prf_le_zero_one prf_le_mod2_one
  prf_le_succ_succ prf_not_le_succ_self
  prf_le_self_mul_self prf_le_double_self_mul_succ
  prf_le_self_mul_self_all prf_le_double_self_mul_succ_all
  cpOf prf_le_double_s_cantor prf_le_double_cantor_of_le
  prf_succ_add_succ_eq prf_mul_two_add_one
  prf_cons_div2 prf_pair_div_mod prf_bot_of_le_succ_div2 prf_lt_succ_div2
  prf_cantor_mono_left prf_cantor_mono_right
)

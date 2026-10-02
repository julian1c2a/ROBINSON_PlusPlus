/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · L1‑1 — `Prf ⊥` con la codificación vieja de `cons`, y el control que la vigila (2026‑10‑02)

## Lo que se midió (registro: compilado en `master` `2510f70`, ANTES de ADR‑113)

Con `ax_L0_cons_def : cons a b = pair a (σ b)`, y sin ninguna hipótesis ni axioma del proyecto:

    theorem prf_bot : Prf Formula.bottom        -- footprint [propext, Classical.choice, Quot.sound]

1. `prf_nil_or_cons 1`, que sale de `Prf.listInd` (sin guarda), da `1 = nil ∨ 1 = cons (carc 1) (cdrc 1)`.
2. La rama `1 = nil` cae por `prf_succ_ne_zero`, porque `nil := zero`.
3. La rama `cons` cae porque `Prf` demuestra `¬ (cons h t = 1)` para términos ARBITRARIOS: las monotonías
   de Cantor dan `h, t < 1`, luego `h = t = 0`, y con la codificación vieja `prf_cons_eval 0 0` daba
   `cons 0 0 = 2`.

⇒ `¬ ConsistentH` y una instancia trivial de `AnclaEq`: en ese `master` TODO resultado sobre `Prf` era
trivial. ADR‑088 §3 y la cabecera de `ModeloBasura.lean` decían lo contrario («no significa que `Prf` sea
inconsistente»): ℕ no era modelo PORQUE la teoría era inconsistente. El texto exacto de la derivación está en
la §3, como registro; desde ADR‑113 ya no compila.

## El control (§2)

Con ADR‑113 (`cons a b = σ (pair a b)`, fusionado el 2026‑10‑02) el paso 3 es imposible: `cons 0 0 = 1`.
`cons_cero_cero_en_Prf` lo fija DENTRO de `Prf`, y `consN_cero_cero` a nivel meta. Si la codificación volviera
atrás, `consN 0 0` sería `2` y los dos dejarían de compilar.

⚠️ Lo que este sondeo NO dice: que `Prf` sea consistente tras ADR‑113. Sólo cierra ESTA ruta. La
consistencia es el frente del modelo de los 141.
-/

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace Sondeos.PrfBotCodificacionVieja

/-! ## §2 · CONTROL NEGATIVO: con la codificación vigente, `cons 0 0 = 1` -/

/-- A nivel meta: el espejo numérico de `cons` da `1` en `(0, 0)`. -/
theorem consN_cero_cero : consN 0 0 = 1 := by decide

/-- Dentro de `Prf`: `cons 0 0 = 1`. Con esto `Prf` refutaría el paso 3 de la derivación vieja. -/
theorem cons_cero_cero_en_Prf : Prf (cons zero zero =eq succ zero) := prf_cons_eval 0 0

end Sondeos.PrfBotCodificacionVieja

/-! ## §3 · La derivación de `2510f70`, como REGISTRO (no compila desde ADR‑113)

```lean
theorem PrfH_eq_zero_of_lt_one {Γ : List Formula} {x : Term}
    (h : PrfH Γ (lt x (succ zero))) : PrfH Γ (x =eq zero) :=
  PrfH_or_elim (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split x zero) _) h)
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero x) _) (PrfH.hyp _ _ (List.Mem.head _))))
    (PrfH.hyp _ _ (List.Mem.head _))

theorem prf_cons_ne_one (h t : Term) : Prf (neg (cons h t =eq succ zero)) := by
  refine prf_deduction ?_
  have E : PrfH [cons h t =eq succ zero] (cons h t =eq succ zero) := prfH_hyp_self _
  have hh := PrfH_eq_zero_of_lt_one (PrfH_lt_subst2 E (prf_to_prfH (prf_cantor_mono_left h t) _))
  have ht := PrfH_eq_zero_of_lt_one (PrfH_lt_subst2 E (prf_to_prfH (prf_cantor_mono_right h t) _))
  have h2 : PrfH [cons h t =eq succ zero] (cons h t =eq succ (succ zero)) :=
    PrfH_eq_trans (PrfH_eq_trans (PrfH_congr_cons_head hh) (PrfH_congr_cons_tail ht))
      (prf_to_prfH (prf_cons_eval 0 0) _)   -- consN 0 0 = triN 1 + 1 = 2  (codificación VIEJA)
  have h01 : PrfH [cons h t =eq succ zero] (zero =eq succ zero) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj zero (succ zero)) _) (PrfH_eq_trans (PrfH_eq_symm E) h2)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero zero) _) (PrfH_eq_symm h01)

theorem prf_bot : Prf Formula.bottom :=
  ROBINSON_PlusPlus.Meta.CantorMonoPrf.prf_or_elim (prf_nil_or_cons (succ zero))
    (prf_succ_ne_zero zero)                                     -- 1 = nil (= 0)
    (prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_cons_ne_one _ _) _)
      (PrfH_eq_symm (prfH_hyp_self _))))                        -- 1 = cons (carc 1) (cdrc 1)
```
-/

#print axioms Sondeos.PrfBotCodificacionVieja.cons_cero_cero_en_Prf

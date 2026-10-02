/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · L1‑4 — `OmegaConsistent` es refutable por su propia DEFINICIÓN (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1, L1‑4): ¿puede valer la hipótesis de la mitad `⊬¬G`?
`OmegaConsistent` (`Meta/OmegaReflect.lean:267`) cuantifica sobre TODA fórmula `A`, pero sólo con testigos
`objList l` de cadenas estándar (`StdChain`, la estrechada de ADR‑022).

## 🏁 Respuesta, COMPILADA: no

Con `A := (#0 = 1)`: `axioms ⊢ ∃A` sale por `intro_ex` + `refl`, y para toda cadena estándar
`objList l ≠ 1` (si `l = []` es `nil = 0`; si `l = x :: l'`, `x` es un `cons`, y las monotonías de Cantor
cierran sin evaluar nada). ⇒ `¬ OmegaConsistent`.

    theorem not_omega_of …                 -- la REDUCCIÓN, limpia: [propext, Classical.choice, Quot.sound]
    theorem not_omegaConsistent : ¬ OmegaConsistent

La instancia pasa hoy por `prf_to_derives`, que arrastra `imp_intro` y los dos esquemas de `⊢`; lo que vale
en cualquier teoría es la reducción, y sólo usa las dos monotonías: vale en las dos codificaciones de `cons`.
⇒ `reflects_of_omega` y `goedel_first_undecidable_omega` son vacuos por la DEFINICIÓN de su hipótesis, y lo
seguirían siendo tras reparar todo lo demás. ADR‑022 vio que la solidez no cubría la clase estrecha, pero no
que la hacía REFUTABLE. Arreglo propuesto por la auditoría: restringir al único `∃` que se usa
(`OmegaConsistentProv`, sólo `provBody`), o Rosser.

## Uso

Evidencia del estado del árbol el 2026‑10‑02; se retira con la capa `⊢`, sobre la que está definida
`OmegaConsistent` (decisión del propietario del 2026‑10‑02). La lección (la forma general de una hipótesis
puede ser falsa aunque la prueba sólo use una instancia razonable) va en ADR‑114.
-/

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.OmegaReflect

namespace Sondeos.OmegaConsistentRefutable

theorem PrfH_eq_zero_of_lt_one {Γ : List Formula} {x : Term}
    (h : PrfH Γ (lt x (succ zero))) : PrfH Γ (x =eq zero) :=
  PrfH_or_elim (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split x zero) _) h)
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero x) _) (PrfH.hyp _ _ (List.Mem.head _))))
    (PrfH.hyp _ _ (List.Mem.head _))

/-- `cons (cons F R) T ≠ 1`: `x := cons F R < cons x T = 1` ⇒ `x = 0` ⇒ `R < x = 0`. -/
theorem prf_cons2_ne_one (F R T : Term) : Prf (neg (cons (cons F R) T =eq succ zero)) := by
  refine prf_deduction ?_
  have E := prfH_hyp_self (cons (cons F R) T =eq succ zero)
  have hx := PrfH_eq_zero_of_lt_one
    (PrfH_lt_subst2 E (prf_to_prfH (prf_cantor_mono_left (cons F R) T) _))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero R) _)
    (PrfH_lt_subst2 hx (prf_to_prfH (prf_cantor_mono_right F R) _))

theorem prf_objList_ne_one : ∀ l : List Term, StdChain l → Prf (neg (objList l =eq succ zero))
  | [], _ => prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero zero) _)
      (PrfH_eq_symm (prfH_hyp_self _)))
  | x :: _, hl => by
      obtain ⟨f, k, as, hx, _⟩ := hl x (List.Mem.head _)
      subst hx; exact prf_cons2_ne_one _ _ _

/-- La reducción, LIMPIA: sólo `intro_ex` y `refl`. -/
theorem not_omega_of (h : ∀ l, StdChain l → axioms ⊢ neg (objList l =eq succ zero)) :
    Not OmegaConsistent := fun hω =>
  hω (Formula.eq (.var 0) (succ zero))
    (Derives.intro_ex _ _ (succ zero)
      (by simp only [substFormula, substTerm, substTerms, succ, zero, if_true]; exact Derives.refl _ _))
    (fun l hl => by simpa only [substFormula, substTerm, substTerms, succ, zero, if_true] using h l hl)

theorem not_omegaConsistent : Not OmegaConsistent :=
  not_omega_of (fun l hl => prf_to_derives (prf_objList_ne_one l hl))

end Sondeos.OmegaConsistentRefutable

#print axioms Sondeos.OmegaConsistentRefutable.not_omega_of
#print axioms Sondeos.OmegaConsistentRefutable.not_omegaConsistent

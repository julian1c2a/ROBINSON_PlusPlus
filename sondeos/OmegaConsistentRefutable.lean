/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · L1‑4 — `OmegaConsistent` es refutable por su propia DEFINICIÓN (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1, L1‑4): ¿puede valer la hipótesis de la mitad `⊬¬G`?
`OmegaConsistent` (`Meta/OmegaReflect.lean:267`, retirada con ADR‑115) cuantificaba sobre TODA fórmula `A`,
pero sólo con testigos `objList l` de cadenas estándar (`StdChain`, la estrechada de ADR‑022).

## 🏁 Respuesta, COMPILADA: no

Con `A := (#0 = 1)`: `∃A` sale por introducción del `∃` + reflexividad, y para toda cadena estándar
`objList l ≠ 1` (si `l = []` es `nil = 0`; si `l = x :: l'`, `x` es un `cons`, y las monotonías de Cantor
cierran sin evaluar nada). ⇒ la hipótesis es FALSA.

## Registro (compilado el 2026‑10‑02 contra RPP `1dac85a`, antes de la retirada)

Sobre la definición de entonces, en `⊢`:

```lean
theorem not_omega_of (h : ∀ l, StdChain l → axioms ⊢ neg (objList l =eq succ zero)) :
    Not OmegaConsistent                      -- [propext, Classical.choice, Quot.sound]
theorem not_omegaConsistent : Not OmegaConsistent :=
  not_omega_of (fun l hl => prf_to_derives (prf_objList_ne_one l hl))
  -- [propext, Classical.choice, Quot.sound, MetaRules.imp_intro,
  --  ROBINSON_PlusPlus.Full.ax_induction_prim, ROBINSON_PlusPlus.Full.ax_list_induction]
```

⇒ `reflects_of_omega` y `goedel_first_undecidable_omega` eran vacuos por la DEFINICIÓN de su hipótesis, y lo
habrían seguido siendo tras reparar todo lo demás. ADR‑022 vio que la solidez no cubría la clase estrecha,
pero no que la hacía REFUTABLE.

## Hoy (ADR‑115): la misma definición sobre `Prf` también es refutable

`OmegaConsistent`, `prf_to_derives` y toda la capa `⊢` se retiraron el 2026‑10‑02. Lo que se conserva es la
lección, trasladada al cálculo que queda: `OmegaConsistentPrf` es la definición retirada con `Prf` en lugar de
`axioms ⊢`, y `not_omegaConsistentPrf` la refuta con la MISMA prueba, ahora sin nada de `⊢`.

⚠️ Para la mitad `⊬¬G` sobre `Prf`: la ω‑consistencia NO puede enunciarse así. Arreglo propuesto por la
auditoría: restringir al único `∃` que se usa (`OmegaConsistentProv`, sólo `provBody`), o Rosser.
-/

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.OmegaReflect ROBINSON_PlusPlus.Meta.ArithPrf

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

/-- La definición retirada (`OmegaReflect.lean:267`), con `Prf` en lugar de `axioms ⊢`: los mismos
    testigos, sólo `objList l` de cadenas estándar. -/
def OmegaConsistentPrf : Prop :=
  ∀ A : Formula, Prf (Formula.ex A) →
    ¬ (∀ l : List Term, StdChain l → Prf (neg (substFormula 0 (objList l) A)))

/-- 🏁 Y es REFUTABLE, sobre `Prf` y sin nada de `⊢`. -/
theorem not_omegaConsistentPrf : Not OmegaConsistentPrf := fun hω =>
  hω (Formula.eq (.var 0) (succ zero))
    (prf_ex_intro (succ zero)
      (by simp only [substFormula, substTerm, substTerms, succ, zero, if_true]; exact prf_refl _))
    (fun l hl => by
      simpa only [substFormula, substTerm, substTerms, succ, zero, if_true] using prf_objList_ne_one l hl)

end Sondeos.OmegaConsistentRefutable

#print axioms Sondeos.OmegaConsistentRefutable.prf_objList_ne_one
#print axioms Sondeos.OmegaConsistentRefutable.not_omegaConsistentPrf

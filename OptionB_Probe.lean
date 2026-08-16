/-
SONDA DESECHABLE — NO AÑADIR AL BUILD.
Objetivo: comprobar en el COMPILADOR si la "OPCION B" (cons como ALGEBRA LIBRE
dentro del lenguaje mono-sorted) es viable.

Los tres axiomas de algebra libre se pasan como HIPOTESIS (no se tocan `axioms`):
  F1 : inyectividad de cons
  F2 : cons h t != nil
  F3 : DISYUNCION DE FORMAS  (cons h t no es un sucesor)   <-- el que mata

Se demuestra: F2 + F3 |- bottom, usando SOLO `prf_zero_or_succ`, que YA es
teorema del repo (Meta/NatArithPrf.lean:201, via `prf_nat_induction`).
-/
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.HilbertDeduction

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta

namespace OptionBProbe

/-- **F3 mata la Opcion B.** Si `cons` es un constructor libre DISJUNTO de los
    numeros (no es 0 — F2 — ni sucesor — F3), la teoria es inconsistente, porque
    `prf_zero_or_succ` (teorema YA existente, via el esquema de induccion
    `Prf.ind` sin relativizar) dice que TODO elemento es 0 o sucesor. -/
theorem free_algebra_kills
    (F2 : ∀ h t : Term, Prf (neg (cons h t =eq nil)))
    (F3 : ∀ h t y : Term, Prf (neg (cons h t =eq succ y))) :
    Prf Formula.bottom := by
  have hor := NatArithPrf.prf_zero_or_succ (cons zero zero)
  refine CantorMonoPrf.prf_or_elim hor ?_ ?_
  · -- rama 0: contradice F2  (nil := zero, defeq)
    exact F2 zero zero
  · -- rama sucesor: ∃-elim + F3
    refine HilbertDeduction.prf_ex_elim_imp (C := Formula.bottom) ?_
    show PrfH [Formula.eq (liftTerm 0 (cons zero zero)) (succ (.var 0))] Formula.bottom
    have hF3 := F3 zero zero (.var 0)
    simp only [liftTerm, liftTerms, cons, zero, neg] at hF3 ⊢
    exact ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.mp _ _ _
      (HilbertDeduction.prf_to_prfH hF3 _) (HilbertDeduction.prfH_hyp_self _)

end OptionBProbe

#print axioms OptionBProbe.free_algebra_kills

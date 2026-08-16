/-
SONDEO S4 — evaluación provable del emparejamiento de Cantor sobre numerales.

Cadena para `prf_cons_eval (a b) : Prf (cons ā b̄ =eq numeral (consN a b))`:
  (1) cons h t =eq div2 (cpOf h t)        -- prf_cons_div2      ✅ YA EXISTE
  (2) cpOf ā b̄ =eq numeral P              -- prf_numeral_add/mul ✅ YA EXISTEN
  (3) div2 (numeral P) =eq numeral (P/2)  -- ❌ NO EXISTE  <- lo que se sondea

Se ataca (3) en forma OBJETO (`x` abstracto): net-0 y sirve para todo `a,b` a la vez.
NO ES MÓDULO DE PRODUCCIÓN.
-/
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf

namespace S4

/-! ### Paso 1 — el sumando derecho de una suma nula es nulo -/

theorem prf_add_eq_zero_right (a b : Term) : Prf ((add a b =eq zero) ⇒ (b =eq zero)) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred b) _) ?zc ?sc
  · -- rama `b = 0`: es exactamente la conclusión
    exact PrfH.hyp _ _ (List.Mem.head _)
  · -- rama `b = σ(pred b)`: absurdo, porque `add a b` sería un sucesor igual a 0
    have hb : PrfH [Formula.eq b (succ (pred b)), add a b =eq zero]
        (b =eq succ (pred b)) := PrfH.hyp _ _ (List.Mem.head _)
    have hH : PrfH [Formula.eq b (succ (pred b)), add a b =eq zero]
        (add a b =eq zero) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have h1 : PrfH [Formula.eq b (succ (pred b)), add a b =eq zero]
        (add a b =eq add a (succ (pred b))) := PrfH_eq_congr_add2 a hb
    have h2 : PrfH [Formula.eq b (succ (pred b)), add a b =eq zero]
        (succ (add a (pred b)) =eq zero) :=
      PrfH_eq_trans
        (PrfH_eq_symm (PrfH_eq_trans h1 (prf_to_prfH (prf_add_succ_t a (pred b)) _))) hH
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (add a (pred b))) _) h2)

end S4

#print axioms S4.prf_add_eq_zero_right

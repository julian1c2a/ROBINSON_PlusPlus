/- ADR-019: ¿puede `PrfH_congr_predcT` VIVIR al final de `Meta/EvalPredPrf.lean`?
   Importa SOLO EvalPredPrf (NO el barrel, NO nada aguas abajo). -/
import ROBINSON_PlusPlus.Meta.EvalPredPrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.ChainPrf  -- ⚠️ NO lo abre EvalPredPrf hoy: hay que ANADIRLO

namespace ROBINSON_PlusPlus.Meta.EvalPredPrf

/-- Copia LITERAL del sondeo, dentro del namespace de EvalPredPrf, importando SOLO EvalPredPrf. -/
theorem ADVW_PrfH_congr_predcT {G : List Formula} {a b : Term} (h : PrfH G (a =eq b)) :
    PrfH G (predcT a =eq predcT b) := by
  let f : Formula := Formula.eq (predcT (liftTerm 0 a)) (predcT (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (predcT a) (predcT s) := by
    intro s
    simp only [f, predcT, funcc, cons, nil, zero, succ, substFormula, substTerm, substTerms,
      substTerm_strCode, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (predcT a)) G)

/-- Y el de produccion sale de ella (corolario, aquí mismo). -/
theorem ADVW_corolario {x y : Term} (h : Prf (x =eq y)) : Prf (predcT x =eq predcT y) :=
  prfH_nil_to_prf (ADVW_PrfH_congr_predcT (prf_to_prfH h [])) rfl

/-- Y el tipo del corolario es EXACTAMENTE el de produccion. -/
theorem ADVW_tipo : ∀ {x y : Term}, Prf (x =eq y) → Prf (predcT x =eq predcT y) :=
  @prf_congr_predcT

end ROBINSON_PlusPlus.Meta.EvalPredPrf

#print axioms ROBINSON_PlusPlus.Meta.EvalPredPrf.ADVW_PrfH_congr_predcT

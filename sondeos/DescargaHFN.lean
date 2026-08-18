/-
DESCARGA DE `hFN` — la comprobación decisiva.

`sondeos/PilotoDiagonal.lean` mostró que el punto fijo de Gödel sobrevive con códigos numerales,
pero ASUMIENDO `hFN` como axioma de Lean. Aquí `hFN` se **DEMUESTRA** (con `prf_formCode_numeral`
de `Meta/CodeNumeralPrf.lean`) y se rehace el piloto.

CRITERIO: `godelCN_fixedpoint` debe compilar SIN `codeN`, SIN `hFN` y —lo esencial— SIN `tc_cons`.
-/
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.Diagonal

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.Induction
open ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open FOL

namespace Descarga

/-! ### `hFN`, ya NO asumida -/

/-- Lo que el piloto postulaba, ahora **teorema**. -/
theorem hFN (φ : Formula) : axioms ⊢ (numeral (codeNat φ) =eq formCode φ) :=
  FOL.derive_eq_symm (prf_to_derives (prf_formCode_numeral φ))

/-! ### El piloto, reconstruido sobre la `hFN` demostrada -/

noncomputable def selfAppN (ψ : Formula) : Formula := substFormula 0 (numeral (codeNat ψ)) ψ

theorem diag_arith_num (ψ : Formula) :
    axioms ⊢ (substTerm 0 (numeral (codeNat ψ)) diagTerm =eq numeral (codeNat (selfAppN ψ))) := by
  have p1 : axioms ⊢ (substfc (numeral 0) (tcFn (numeral (codeNat ψ))) (numeral (codeNat ψ)) =eq
                      substfc (numeral 0) (termCode (numeral (codeNat ψ))) (numeral (codeNat ψ))) :=
    congr_substfc_arg2 (tc_numeral (codeNat ψ))
  have p2 : axioms ⊢ (substfc (numeral 0) (termCode (numeral (codeNat ψ))) (numeral (codeNat ψ)) =eq
                      substfc (numeral 0) (termCode (numeral (codeNat ψ))) (formCode ψ)) :=
    congr_substfc_arg3 (hFN ψ)
  have p3 : axioms ⊢ (substfc (numeral 0) (termCode (numeral (codeNat ψ))) (formCode ψ) =eq
                      formCode (substFormula 0 (numeral (codeNat ψ)) ψ)) :=
    substFormula_arith 0 (numeral (codeNat ψ)) ψ
  have p4 : axioms ⊢ (formCode (selfAppN ψ) =eq numeral (codeNat (selfAppN ψ))) :=
    FOL.derive_eq_symm (hFN (selfAppN ψ))
  exact FOL.derive_eq_trans p1 (FOL.derive_eq_trans p2 (FOL.derive_eq_trans p3 p4))

noncomputable def provCodeN (φ : Formula) : Formula :=
  substFormula 0 (numeral (codeNat φ)) provFormulaC

noncomputable def godelCN : Formula := selfAppN godelBeta

/-- **EL PUNTO FIJO CON CÓDIGOS NUMERALES, SIN NADA ASUMIDO.** -/
theorem godelCN_fixedpoint : axioms ⊢ (godelCN ⇔ neg (provCodeN godelCN)) := by
  have hiff := subst_eq_iff godelPred (diag_arith_num godelBeta)
  rw [← godel_comp (numeral (codeNat godelBeta))] at hiff
  simpa only [godelCN, selfAppN, godelPred, provCodeN, neg, substFormula] using hiff

/-- Transferencia con la representación en árbol: **un** paso de Leibniz. -/
theorem provCode_transfer (φ : Formula) : axioms ⊢ (provCodeN φ ⇔ provCodeC φ) :=
  subst_eq_iff provFormulaC (hFN φ)

end Descarga

/- CRITERIO: ni `codeN`, ni `hFN`, ni `tc_cons`. -/
#print axioms Descarga.hFN
#print axioms Descarga.diag_arith_num
#print axioms Descarga.godelCN_fixedpoint
#print axioms Descarga.provCode_transfer

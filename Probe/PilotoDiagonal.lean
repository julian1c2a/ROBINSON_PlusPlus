/-
PILOTO DEL LEMA DIAGONAL BAJO CÓDIGOS NUMERALES  (el riesgo nº1 de S2)

Pregunta: ¿sobrevive `diag_arith` si `⌜ψ⌝` se representa como NUMERAL en vez de como árbol `cons`?
Si no sobrevive, la vía numeral NO EXISTE y S4 (20 lemas) sería trabajo tirado.

MÉTODO: se ASUME el resultado de S4 como axioma de Lean —

    hFN (φ) : axioms ⊢ (numeral (codeN φ) =eq formCode φ)

— y se comprueba si la cadena cierra. `codeN` se deja ABSTRACTO (axioma), así el piloto no depende
de los detalles de `codeNat` y mide sólo lo que se quiere medir.

CRITERIO DE ÉXITO: que `diag_arith_num` compile **sin `tc_cons`** en su footprint. Si aparece
`tc_cons`, la vía numeral no compra nada.

NO ES MÓDULO DE PRODUCCIÓN.
-/
import ROBINSON_PlusPlus.Meta.Diagonal

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.Induction
open ROBINSON_PlusPlus.Meta.Diagonal
open FOL

namespace PilotoDiag

/-! ### Lo que se ASUME de S4 (y nada más) -/

/-- Código numérico de una fórmula. Abstracto: el piloto no depende de cómo se calcule. -/
axiom codeN : Formula → Nat

/-- **EL RESULTADO DE S4, ASUMIDO**: el numeral del código y el árbol de código denotan lo mismo.
    Es lo que produciría `prf_cons_eval` aplicado recursivamente sobre `formCode`. -/
axiom hFN (φ : Formula) : axioms ⊢ (numeral (codeN φ) =eq formCode φ)

/-! ### La auto-aplicación en versión NUMERAL -/

/-- `selfApp` con el código escrito como NUMERAL (en vez de como árbol `cons`). -/
noncomputable def selfAppN (ψ : Formula) : Formula := substFormula 0 (numeral (codeN ψ)) ψ

/-! ### EL PILOTO -/

/-- **`diag_arith` bajo códigos numerales.**

    Cadena:
    1. `tc_numeral N` — `tcFn (numeral N) =eq termCode (numeral N)`. **Sólo usa `ax_tc_zero`/
       `ax_tc_succ`**: es la lectura NUMERAL, la consistente.
    2. `congr_substfc_arg2` — la mete en el 2º argumento de `substfc`.
    3. `hFN ψ` + `congr_substfc_arg3` — cambia el 3er argumento de numeral a árbol,
       para poder aplicar `substFormula_arith`.
    4. `substFormula_arith 0 (numeral N) ψ` — **acepta un `s` ARBITRARIO**, luego traga el numeral.
    5. `hFN (selfAppN ψ)` al revés — devuelve el resultado a forma numeral. -/
theorem diag_arith_num (ψ : Formula) :
    axioms ⊢ (substTerm 0 (numeral (codeN ψ)) diagTerm =eq numeral (codeN (selfAppN ψ))) := by
  have p1 : axioms ⊢ (substfc (numeral 0) (tcFn (numeral (codeN ψ))) (numeral (codeN ψ)) =eq
                      substfc (numeral 0) (termCode (numeral (codeN ψ))) (numeral (codeN ψ))) :=
    congr_substfc_arg2 (tc_numeral (codeN ψ))
  have p2 : axioms ⊢ (substfc (numeral 0) (termCode (numeral (codeN ψ))) (numeral (codeN ψ)) =eq
                      substfc (numeral 0) (termCode (numeral (codeN ψ))) (formCode ψ)) :=
    congr_substfc_arg3 (hFN ψ)
  have p3 : axioms ⊢ (substfc (numeral 0) (termCode (numeral (codeN ψ))) (formCode ψ) =eq
                      formCode (substFormula 0 (numeral (codeN ψ)) ψ)) :=
    substFormula_arith 0 (numeral (codeN ψ)) ψ
  have p4 : axioms ⊢ (formCode (selfAppN ψ) =eq numeral (codeN (selfAppN ψ))) :=
    FOL.derive_eq_symm (hFN (selfAppN ψ))
  exact FOL.derive_eq_trans p1
    (FOL.derive_eq_trans p2 (FOL.derive_eq_trans p3 p4))

end PilotoDiag

/-! ### PASO 2 — el PUNTO FIJO mismo (el objetivo real; `diag_arith` es sólo el escalón previo)

`godelPred`, `godelBeta`, `diagTerm` y `godel_comp` NO cambian: ninguno menciona la representación
del código. Sólo cambia dónde se sustituye el código, y `godel_comp` vale para `s` ARBITRARIO. -/

namespace PilotoDiag

/-- `Prov(⌜φ⌝)` con el código escrito como NUMERAL. -/
noncomputable def provCodeN (φ : Formula) : Formula :=
  substFormula 0 (numeral (codeN φ)) provFormulaC

/-- Sentencia de Gödel con código numeral. `godelBeta` se REUTILIZA sin cambios. -/
noncomputable def godelCN : Formula := selfAppN godelBeta

/-- **EL PUNTO FIJO BAJO CÓDIGOS NUMERALES**: `⊢ Gₙ ⇔ ¬Prov(⌜Gₙ⌝ₙ)`.
    Misma estructura que `godelC_fixedpoint` (Diagonal.lean:186), con `diag_arith_num`
    en lugar de `diag_arith`. -/
theorem godelCN_fixedpoint : axioms ⊢ (godelCN ⇔ neg (provCodeN godelCN)) := by
  have hiff := subst_eq_iff godelPred (diag_arith_num godelBeta)
  rw [← godel_comp (numeral (codeN godelBeta))] at hiff
  simpa only [godelCN, selfAppN, godelPred, provCodeN, neg, substFormula] using hiff

/-- **TRANSFERENCIA**: las dos representaciones son intercambiables por UN paso de Leibniz.
    Si esto vale, D1 (`repr_pos'`) y toda la cadena existente se transfieren sin re-demostrarse:
    basta componer con este bicondicional. -/
theorem provCode_transfer (φ : Formula) : axioms ⊢ (provCodeN φ ⇔ provCodeC φ) :=
  subst_eq_iff provFormulaC (hFN φ)

end PilotoDiag

/- CRITERIO: no debe aparecer `tc_cons`. Si aparece, la via numeral no compra nada. -/
#print axioms PilotoDiag.diag_arith_num
#print axioms PilotoDiag.godelCN_fixedpoint
#print axioms PilotoDiag.provCode_transfer

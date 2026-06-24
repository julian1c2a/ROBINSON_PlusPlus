/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.Induction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.Hilbert

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ListInductionArith

/-!
## META — NIVEL D real: reconstrucción del código de la inducción de listas

`listInd_concl_code` reconstruye el **código** de `listInductionFormula A` (esquema
objeto de inducción de listas, `Meta/Hilbert.lean`) a partir de `⌜A⌝`, vía
`substFormula_arith`/`liftFormula_arith`. Es el análogo de `ind_concl_code`
(`Meta/Induction.lean`) para listas; más complejo porque el término sustituido
`cons #1 #0` lleva **variables libres** (`varc`), no códigos cerrados como en `ind`.
Núcleo de una **regla `listInd` sólida** del verificador (Prf.listInd / Rule.listInd).
-/

/-- Congruencia de `liftfc` en su 2º argumento (la fórmula codificada). -/
theorem congr_liftfc_arg2 {c a b : Term} (h : axioms ⊢ (a =eq b)) :
    axioms ⊢ (liftfc c a =eq liftfc c b) := by
  let f : Formula := Formula.eq (liftfc (liftTerm 0 c) (liftTerm 0 a)) (liftfc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftfc c a) (liftfc c s) := by
    intro s; simp only [f, liftfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst axioms a b f h ((hS a) ▸ Derives.refl axioms (liftfc c a))

/-- **Reconstrucción del código de la instancia de inducción de listas para `A`**: el
    código object reconstruido con `substfc`/`liftfc` (caso base `A[nil]`, paso
    `∀h∀t (A[t] ⇒ A[cons h t])` con `cons h t` codificado por `termCode (cons #1 #0)`,
    conclusión `∀L A[L]`) coincide con `formCode (listInductionFormula A)`. -/
theorem listInd_concl_code (A : Formula) :
    axioms ⊢ (
      implc (substfc (numeral 0) (termCode nil) (formCode A))
        (implc (forallc (forallc (implc (liftfc (numeral 1) (formCode A))
                  (substfc (numeral 0) (termCode (cons (.var 1) (.var 0)))
                    (liftfc (numeral 2) (liftfc (numeral 1) (formCode A)))))))
               (forallc (formCode A)))
      =eq formCode (listInductionFormula A)) := by
  have base_eq : axioms ⊢
      (substfc (numeral 0) (termCode nil) (formCode A) =eq formCode (substFormula 0 nil A)) :=
    substFormula_arith 0 nil A
  have ante_eq : axioms ⊢
      (liftfc (numeral 1) (formCode A) =eq formCode (liftFormula 1 A)) :=
    liftFormula_arith 1 A
  have lift2_eq : axioms ⊢
      (liftfc (numeral 2) (liftfc (numeral 1) (formCode A)) =eq formCode (liftFormula 2 (liftFormula 1 A))) :=
    FOL.derive_eq_trans (congr_liftfc_arg2 (liftFormula_arith 1 A)) (liftFormula_arith 2 (liftFormula 1 A))
  have conseq_eq : axioms ⊢
      (substfc (numeral 0) (termCode (cons (.var 1) (.var 0)))
          (liftfc (numeral 2) (liftfc (numeral 1) (formCode A)))
        =eq formCode (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))) :=
    FOL.derive_eq_trans (ROBINSON_PlusPlus.Meta.Induction.congr_substfc_arg3 lift2_eq)
      (substFormula_arith 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))
  exact FOL.derive_eq_trans (congr_bin1 base_eq)
    (congr_bin2 (congr_bin1 (congr_un (congr_un
      (FOL.derive_eq_trans (congr_bin1 ante_eq) (congr_bin2 conseq_eq))))))

end ROBINSON_PlusPlus.Meta.ListInductionArith

export ROBINSON_PlusPlus.Meta.ListInductionArith (congr_liftfc_arg2 listInd_concl_code)

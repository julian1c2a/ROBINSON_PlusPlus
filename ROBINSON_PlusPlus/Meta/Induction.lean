/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.StepArith
import ROBINSON_PlusPlus.Full.Induction

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Induction

/-!
## META — NIVEL D (real): esquema de inducción  (Fase 5) — cimientos

Para que el sistema aritmetizado sea **IΣ₁-fuerte** (necesario para D3 / Gödel II)
hay que añadir el **esquema de inducción**. A nivel de la teoría verificadora
`axioms ⊢` la inducción ya está disponible: `Full.ax_induction` postula
`axioms ⊢ inductionFormula φ` (axioma legítimo de la aritmética, sobre la misma
`Minimal.axioms`; `Meta` ya importa `Full`).

El núcleo aritmético para una **regla `ind` SÓLIDA** del verificador (que NO
rompa la fidelidad de `provCodeC`) es reconstruir el **código de la instancia de
inducción** a partir de `⌜φ⌝`, vía `substFormula_arith`/`liftFormula_arith`. Eso
es `ind_concl_code` (análogo a `q1_concl_code`/`leibniz_concl_code`, pero para la
fórmula de inducción completa, que lleva un `liftFormula 1`).
-/

/-- Congruencia de `substfc` en el 3er argumento (la fórmula sustituida). -/
theorem congr_substfc_arg3 {x t a b : Term} (h : axioms ⊢ (a =eq b)) :
    axioms ⊢ (substfc x t a =eq substfc x t b) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 x) (liftTerm 0 t) (liftTerm 0 a))
                                 (substfc (liftTerm 0 x) (liftTerm 0 t) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc x t a) (substfc x t s) := by
    intro s
    simp only [f, substfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ Derives.subst axioms a b f h ((hS a) ▸ Derives.refl axioms (substfc x t a))

/-- **Reconstrucción del código de la instancia de inducción** para `φ`: el código
    object reconstruido con `substfc`/`liftfc` coincide con `formCode` de
    `Full.inductionFormula φ`. Núcleo de una regla `ind` sólida del verificador.

    `inductionFormula φ = φ(0) ⇒ ((∀(φ ⇒ φ[σ#0/0 sobre ↑¹φ])) ⇒ ∀φ)`.
    El paso usa `liftFormula 1 φ`, de ahí la composición `liftfc`+`substfc`. -/
theorem ind_concl_code (φ : Formula) :
    axioms ⊢ (
      implc (substfc (numeral 0) (termCode zero) (formCode φ))
        (implc (forallc (implc (formCode φ)
                  (substfc (numeral 0) (termCode (succ (.var 0))) (liftfc (numeral 1) (formCode φ)))))
               (forallc (formCode φ)))
      =eq formCode (Full.inductionFormula φ)) := by
  -- código del caso base
  have base_eq : axioms ⊢
      (substfc (numeral 0) (termCode zero) (formCode φ) =eq formCode (substFormula 0 zero φ)) :=
    substFormula_arith 0 zero φ
  -- código del caso de paso: liftfc → ⌜lift⌝ luego substfc → ⌜subst⌝
  have step_eq : axioms ⊢
      (substfc (numeral 0) (termCode (succ (.var 0))) (liftfc (numeral 1) (formCode φ)) =eq
        formCode (substFormula 0 (succ (.var 0)) (liftFormula 1 φ))) :=
    FOL.derive_eq_trans (congr_substfc_arg3 (liftFormula_arith 1 φ))
      (substFormula_arith 0 (succ (.var 0)) (liftFormula 1 φ))
  exact FOL.derive_eq_trans (congr_bin1 base_eq)
    (congr_bin2 (congr_bin1 (congr_un (congr_bin2 step_eq))))

end ROBINSON_PlusPlus.Meta.Induction

export ROBINSON_PlusPlus.Meta.Induction (
  congr_substfc_arg3
  ind_concl_code
)

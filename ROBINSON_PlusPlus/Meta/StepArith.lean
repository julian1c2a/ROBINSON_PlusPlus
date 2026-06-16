/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SubstArith

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.StepArith

/-!
## META — NIVEL D (real): reconocimiento object de instancias de axioma  (Fase 2.3)

Para que el verificador object-level (`demFormula`, Fase 2.4) reconozca que una
línea es una instancia válida de un esquema de axioma, necesita reconstruir el
**código de la conclusión** a partir de los códigos de los parámetros.

* Esquemas **proposicionales/estructurales** (P1/P2, C, J, efq, P3): la
  conclusión se construye con `implc`/`andc`/`orc`/`botc` directamente sobre los
  códigos de los parámetros, y `formCode` es composicional ⟹ la igualdad es
  **definicional** (`eq_refl`). No requieren lema.
* Esquemas de **sustitución** (Q1, Q2, Leibniz): la conclusión contiene
  `substFormula 0 t A`, cuyo código se reconstruye con `substfc` vía el cómputo
  `substFormula_arith` (Fase 2.2f) + congruencias de constructor.

Aquí damos los lemas de los tres esquemas de sustitución (el núcleo de 2.3). MP y
Gen, que dependen de líneas anteriores (índices), se aritmetizan en la Fase 2.4
junto con la estructura de secuencia.
-/

/-- **Q1** `(∀A) ⇒ A[t]`: el código object reconstruido con `substfc` coincide con
    `formCode` de la conclusión real. -/
theorem q1_concl_code (A : Formula) (t : Term) :
    axioms ⊢ (implc (forallc (formCode A)) (substfc (numeral 0) (termCode t) (formCode A))
      =eq formCode (Formula.impl (Formula.forall A) (substFormula 0 t A))) :=
  congr_bin2 (substFormula_arith 0 t A)

/-- **Q2** `A[t] ⇒ ∃A`: idem en el primer argumento de la implicación. -/
theorem q2_concl_code (A : Formula) (t : Term) :
    axioms ⊢ (implc (substfc (numeral 0) (termCode t) (formCode A)) (exc (formCode A))
      =eq formCode (Formula.impl (substFormula 0 t A) (Formula.ex A))) :=
  congr_bin1 (substFormula_arith 0 t A)

/-- **Leibniz** `(t₁ ≐ t₂) ⇒ (A[t₁] ⇒ A[t₂])`: ambas sustituciones reconstruidas. -/
theorem leibniz_concl_code (A : Formula) (t₁ t₂ : Term) :
    axioms ⊢ (implc (eqc (termCode t₁) (termCode t₂))
        (implc (substfc (numeral 0) (termCode t₁) (formCode A))
               (substfc (numeral 0) (termCode t₂) (formCode A)))
      =eq formCode (Formula.impl (Formula.eq t₁ t₂)
            (Formula.impl (substFormula 0 t₁ A) (substFormula 0 t₂ A)))) :=
  congr_bin2 (FOL.derive_eq_trans
    (congr_bin1 (substFormula_arith 0 t₁ A))
    (congr_bin2 (substFormula_arith 0 t₂ A)))

end ROBINSON_PlusPlus.Meta.StepArith

export ROBINSON_PlusPlus.Meta.StepArith (
  q1_concl_code
  q2_concl_code
  leibniz_concl_code
)

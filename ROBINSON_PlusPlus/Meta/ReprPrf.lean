/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.Hilbert

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ReprPrf

/-!
## META — NIVEL D real: re-nivelación de la cadena a `Prf` (hacia Gödel II real)

Para Gödel II real (`ConsistentH → ¬ Prf Con'`) la cadena HBL debe vivir en el
cálculo **finitario `Prf`** (no en `axioms ⊢`), porque `provCodeC'` rastrea `Prf` y
`¬⊢Con'` es falso (el ω-sistema es sólido). El refactor `Prf.thy → axioms` lo
habilitó: `Prf` ya puede usar TODO axioma (incluida la maquinaria de coding) vía
`thy`.

**Infraestructura de porte.** Los lemas-ecuación del verificador se demostraron a
nivel `axioms ⊢` con `ax`(=`Derives.hyp`/thy) + `spec`(=`elim_forall`) + `simp`. Su
contraparte `Prf` usa `prf_ax`(=`Prf₀.thy`) + `prf_spec`(=`q1`+`mp`) + el MISMO
`simp` (que solo manipula la igualdad meta de fórmulas). Esta sonda valida el patrón.
-/

/-- **Axioma como teorema de `Prf`** (regla `thy`, ahora sobre todo `axioms`). -/
theorem prf_ax {f : Formula} (h : f ∈ axioms) : Prf f := Prf.incl (Prf₀.thy f h)

/-- **Especialización en `Prf`** (instancia del esquema `q1` + `mp`): de `Prf (∀A)`
    y un término `t` sale `Prf (A[t])`. Contraparte finitaria de `spec`. -/
theorem prf_spec {A : Formula} (h : Prf (Formula.forall A)) (t : Term) :
    Prf (substFormula 0 t A) :=
  Prf.mp _ _ (Prf.incl (Prf₀.q1 A t)) h

/-- **Modus ponens en `Prf`** (alias cómodo). -/
theorem prf_mp {A B : Formula} (hAB : Prf (A ⇒ B)) (hA : Prf A) : Prf B :=
  Prf.mp A B hAB hA

/-! ### Sonda: ecuaciones de `runFn`/`chainOk` portadas a `Prf` -/

/-- `Prf (runFn c nil =eq c)` (porte de `runFn_nil`). -/
theorem prf_runFn_nil (c : Term) : Prf (runFn c nil =eq c) := by
  have hh := prf_spec (prf_ax (show ax_runFn_nil ∈ axioms by simp [axioms])) c
  simp [ax_runFn_nil, substFormula, substTerm, substTerms, runFn, nil, zero,
    FOL.substTerm_liftTerm] at hh
  exact hh

/-- `Prf (runFn c (cons line rest) =eq runFn (concat c [carc line]) rest)`. -/
theorem prf_runFn_cons (c line rest : Term) :
    Prf (runFn c (cons line rest) =eq runFn (concat c (cons (carc line) nil)) rest) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax_runFn_cons ∈ axioms by simp [axioms])) c) line) rest
  simp [ax_runFn_cons, substFormula, substTerm, substTerms, runFn, concat, carc, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

end ROBINSON_PlusPlus.Meta.ReprPrf

export ROBINSON_PlusPlus.Meta.ReprPrf (
  prf_ax
  prf_spec
  prf_mp
  prf_runFn_nil
  prf_runFn_cons
)

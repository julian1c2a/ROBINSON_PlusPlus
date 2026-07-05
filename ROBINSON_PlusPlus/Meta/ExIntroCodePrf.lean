/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.ExIntroCodePrf

/-!
## META - NIVEL D real (Opcion A, A-F4): cimientos del ex-intro a nivel de codigo

Hacia `pcc_exIntro_code (Ac w) : Prf (provFromCode (substfc 0 w Ac) => provFromCode (exc Ac))`
- la reflexion de la regla Q2 (`A[t] => existe A`) al nivel de CODIGO, con testigo-codigo
arbitrario `w`. Este modulo entrega las clausuras De Bruijn (lift = identidad) que el ensamblaje
de cadena tipo `d2_prf` necesita; el ensamblaje final queda planificado abajo.
-/

/-- `liftTerm` es identidad sobre `exc Ac` a cualquier nivel si lo es sobre `Ac` (tag cerrado). -/
theorem liftTerm_exc (Ac : Term) (hAc : ∀ c, liftTerm c Ac = Ac) :
    ∀ c, liftTerm c (exc Ac) = exc Ac := by
  intro c
  simp only [exc, cons, nil, zero, succ, liftTerm, liftTerms, hAc c]

/-- Clausura de `provFromCode (exc Ac)` bajo `liftFormula 0` (para `Ac` cerrado a todo nivel,
    como `formCode psi` via `liftTerm_formCode`). -/
theorem liftFormula_provFromCode_exc (Ac : Term) (hAc : ∀ c, liftTerm c Ac = Ac) :
    liftFormula 0 (provFromCode (exc Ac)) = provFromCode (exc Ac) := by
  simp only [provFromCode, provFormulaC', substFormula, substTerm, substTerms, liftFormula, liftTerm,
    liftTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, liftTerm_exc Ac hAc]

/-- `liftTerm` es identidad sobre `substfc zero w Ac` a cualquier nivel (para `Ac`,`w` cerrados). -/
theorem liftTerm_substfc (Ac w : Term) (hAc : ∀ c, liftTerm c Ac = Ac) (hw : ∀ c, liftTerm c w = w) :
    ∀ c, liftTerm c (substfc zero w Ac) = substfc zero w Ac := by
  intro c
  simp only [substfc, zero, liftTerm, liftTerms, hAc c, hw c]

/-!
### Pendiente: `pcc_exIntro_code` (ensamblaje de cadena, proxima sesion)

`pcc_exIntro_code (Ac w) (hAc hw) : Prf (provFromCode (substfc 0 w Ac) => provFromCode (exc Ac))`.
Receta (patron `d2_prf`), con los cimientos ya verificados arriba:
1. `prf_ex_elim_imp` + `rw [liftFormula_provFromCode_exc Ac hAc]` + `simp [liftTerm_substfc ...]` ->
   contexto `[chainOk nil #0 AND In (substfc 0 w Ac) (runFn nil #0)]`, meta `provFromCode (exc Ac)`.
2. `PrfH_ex_intro (concat #0 (cons q2line (cons mpline nil)))` con
   `q2line = [implc Ain Bex, 10, Ac, w]` (linea Q2, `prf_lineOk_q2`) y
   `mpline = [Bex, 16, Ain]` (MP), `Ain = substfc 0 w Ac`, `Bex = exc Ac`.
3. `chainOk nil (concat #0 tl)` via `prf_chainOk_concat` + `prf_chainOk_cons` x2
   (`prf_lineOk_q2` para q2line; `prf_lineWF_mp`+`prf_premsOf_mp`+`allIn` para mpline;
   premisas `implc Ain Bex` = `carc q2line`, `Ain` de la hipotesis via `prf_In_mono`/`prf_runFn_weaken`).
4. `In Bex (runFn nil (concat #0 tl))` via `prf_runFn_concat` + `prf_runFn_cons` x2 + `prf_carc_cons`
   (`carc mpline = Bex`) + `prf_In_mono`.
El algebra de cadena es identica a la segunda mitad de `d2_prf` (`DerivCondPrf.lean`).
-/

end ROBINSON_PlusPlus.Meta.ExIntroCodePrf

export ROBINSON_PlusPlus.Meta.ExIntroCodePrf (
  liftTerm_exc liftFormula_provFromCode_exc liftTerm_substfc
)

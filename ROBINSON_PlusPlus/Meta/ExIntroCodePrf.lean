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
### `pcc_exIntro_code` (∃‑intro a nivel de CÓDIGO)

`pcc_exIntro_code (Ac w) (hAc hw) : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))`
— la regla Q2 (`A[t] ⇒ ∃A`) reflejada al nivel de código, con testigo‑código arbitrario `w`
(cerrado a todo nivel, junto con `Ac`). Ensamblaje tipo `d2_prf` pero con **un solo testigo**
`p = #0` (de la hipótesis) y **dos líneas apendizadas**: una línea‑axioma Q2 (`prf_lineOk_q2`)
que concluye `implc (substfc zero w Ac) (exc Ac)` = `⌜A[w] ⇒ ∃A⌝`, y una línea MP que de ella y
de la premisa `Ain` (que la hipótesis ya sitúa en `runFn nil p`) concluye `Bex = exc Ac`. El
álgebra de cadena (`prf_runFn_concat`/`prf_chainOk_concat`/`prf_chainOk_cons`/…) es la 2ª mitad
de `d2_prf`. -/

/-- **∃‑intro a nivel de código** (reflexión de la regla Q2): para `Ac`, `w` cerrados a todo
    nivel (`hAc`, `hw`), de la demostrabilidad del código sustituido `substfc zero w Ac` sale la
    demostrabilidad del código del existencial `exc Ac`. Es el ladrillo que la Opción A necesita
    para el ∃‑intro rastreado del testigo en `d3`. -/
theorem pcc_exIntro_code (Ac w : Term)
    (hAc : ∀ c, liftTerm c Ac = Ac) (hw : ∀ c, liftTerm c w = w) :
    Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac)) := by
  -- elimina el ∃ externo de `provFromCode (substfc zero w Ac)`; testigo `p = #0`
  refine prf_ex_elim_imp ?_
  rw [liftFormula_provFromCode_exc Ac hAc]
  -- colapsa `liftTerm 0 (substfc zero w Ac)` MIENTRAS `zero` es literal (patrón con `zero`)
  simp only [liftTerm_substfc Ac w hAc hw]
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- ctx: [chainOk nil #0 ∧ In Ain (runFn nil #0)] ; meta: provFromCode (exc Ac)
  -- testigo `r = p ++ [q2line, mpline]`
  refine PrfH_ex_intro
    (concat (.var 0)
      (cons (cons (implc (substfc zero w Ac) (exc Ac))
              (cons (numeralM 10) (cons Ac (cons w nil))))
        (cons (cons (exc Ac) (cons (numeralM 16) (cons (substfc zero w Ac) nil))) nil))) ?_
  -- el slot `liftTerm 0 (exc Ac)` se cancela con la subst externa `substTerm 0 r (·)` (`substTerm_liftTerm`)
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- abreviaturas
  let Ain : Term := substfc zero w Ac
  let Bex : Term := exc Ac
  let p_ : Term := (.var 0)
  let q2line : Term := cons (implc Ain Bex) (cons (numeralM 10) (cons Ac (cons w nil)))
  let mpline : Term := cons Bex (cons (numeralM 16) (cons Ain nil))
  let tl : Term := cons q2line (cons mpline nil)
  let Γ : List Formula := [land (chainOk nil p_) (In Ain (runFn nil p_))]
  let Cp : Term := runFn nil p_
  let Cp1 : Term := concat Cp (cons (carc q2line) nil)
  -- hipótesis del contexto
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hpIn : PrfH Γ (In Ain (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  -- Part B: In Bex (runFn nil r)
  have hmp : Prf (runFn Cp1 (cons mpline nil) =eq concat Cp1 (cons Bex nil)) :=
    prf_eq_trans (prf_runFn_cons Cp1 mpline nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_congr_concat_left (prf_congr_cons_head
          (prf_carc_cons Bex (cons (numeralM 16) (cons Ain nil))))))
  have hRunR : Prf (runFn nil (concat p_ tl) =eq concat Cp1 (cons Bex nil)) :=
    prf_eq_trans (prf_runFn_concat nil p_ tl)
      (prf_eq_trans (prf_runFn_cons Cp q2line (cons mpline nil)) hmp)
  have hInB : PrfH Γ (In Bex (runFn nil (concat p_ tl))) :=
    prf_to_prfH (prf_eq_subst_in (prf_eq_symm hRunR)
      (prf_In_mono Bex (cons Bex nil) Cp1 (prf_in_cons_head Bex nil))) Γ
  -- Part A: chainOk nil r
  have hChainR : PrfH Γ (chainOk nil (concat p_ tl)) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ tl) (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_cons Cp q2line (cons mpline nil)) (PrfH_and_intro ?_ ?_)
    · -- lineOk Cp q2line (línea‑axioma Q2)
      exact prf_to_prfH (prf_lineOk_q2 Cp Ac w) Γ
    · -- chainOk Cp1 [mpline]
      refine PrfH_iff_mpr (prf_chainOk_cons Cp1 mpline nil)
        (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
      -- lineOk Cp1 mpline
      refine PrfH_and_intro (prf_to_prfH (prf_lineWF_mp Bex Ain) Γ) ?_
      refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_mp Bex Ain)) Γ) ?_
      refine PrfH_iff_mpr (prf_allIn_cons Cp1 (implc Ain Bex) (cons Ain nil))
        (PrfH_and_intro ?_ ?_)
      · -- In (implc Ain Bex) Cp1  (= carc q2line, apendizada por la línea Q2)
        have hcarc : Prf (cons (implc Ain Bex) nil =eq cons (carc q2line) nil) :=
          prf_congr_cons_head (prf_eq_symm
            (prf_carc_cons (implc Ain Bex) (cons (numeralM 10) (cons Ac (cons w nil)))))
        exact prf_to_prfH
          (prf_In_mono (implc Ain Bex) (cons (carc q2line) nil) Cp
            (prf_eq_subst_in hcarc (prf_in_cons_head (implc Ain Bex) nil))) Γ
      · refine PrfH_iff_mpr (prf_allIn_cons Cp1 Ain nil)
          (PrfH_and_intro ?_ (prf_to_prfH (prf_allIn_nil _) Γ))
        -- In Ain Cp1  (Ain ∈ Cp por hipótesis, monotonía por la derecha)
        exact PrfH.mp Γ _ _
          (prf_to_prfH (prf_In_mono_right_imp Ain (cons (carc q2line) nil) Cp) Γ) hpIn
  exact PrfH_and_intro hChainR hInB

end ROBINSON_PlusPlus.Meta.ExIntroCodePrf

export ROBINSON_PlusPlus.Meta.ExIntroCodePrf (
  liftTerm_exc liftFormula_provFromCode_exc liftTerm_substfc
  pcc_exIntro_code
)

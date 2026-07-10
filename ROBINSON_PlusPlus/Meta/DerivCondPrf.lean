/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.Representability2Prf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.DerivCondPrf

/-!
## META — NIVEL D real: D2 finitaria sobre `provCodeC'` (a nivel `Prf`)

Porte de `Meta/DerivCond.lean` (D2 ω-level) al cálculo finitario `Prf`. Los testigos de
prueba `p`, `q` son ahora **variables De Bruijn** del contexto `PrfH` (eliminadas con
`PrfH_ex_elim`, introducidas con `PrfH_ex_intro`); el ensamblaje `r = p ++ q ++ [mp]` y
la validez de la cadena usan los lemas de cadena `Prf` (`prf_runFn_concat`, … paso 8).
-/

/-! ### Clausura de `formCode`/`provCodeC'` bajo `liftTerm`/`liftFormula` -/

theorem liftTerm_numeral (c : Nat) : ∀ n : Nat, liftTerm c (numeral n) = numeral n
  | 0 => rfl
  | n + 1 => by
      have ih := liftTerm_numeral c n
      simp only [numeral, succ, liftTerm, liftTerms, ih]

theorem liftTerm_charsCode (c : Nat) : ∀ l : List Char, liftTerm c (charsCode l) = charsCode l
  | [] => rfl
  | _ :: cs => by
      simp only [charsCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_charsCode c cs]

theorem liftTerm_strCode (c : Nat) (s : String) : liftTerm c (strCode s) = strCode s :=
  liftTerm_charsCode c s.toList

/-! Duales bajo `substTerm`: los códigos base son **cerrados**, luego la sustitución los atraviesa
    sin tocarlos. Los necesita la **inducción object** sobre fórmulas `provFromCode (…#0…)`, donde
    tras `substFormula_provFromCode_open` hay que computar el `substTerm` sobre el código. -/

theorem substTerm_numeral (v : Nat) (s : Term) : ∀ n : Nat, substTerm v s (numeral n) = numeral n
  | 0 => rfl
  | n + 1 => by
      have ih := substTerm_numeral v s n
      simp only [numeral, succ, substTerm, substTerms, ih]

theorem substTerm_charsCode (v : Nat) (s : Term) :
    ∀ l : List Char, substTerm v s (charsCode l) = charsCode l
  | [] => rfl
  | _ :: cs => by
      simp only [charsCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_charsCode v s cs]

theorem substTerm_strCode (v : Nat) (s : Term) (str : String) :
    substTerm v s (strCode str) = strCode str :=
  substTerm_charsCode v s str.toList

mutual
theorem liftTerm_termCode (c : Nat) : ∀ t : Term, liftTerm c (termCode t) = termCode t
  | .var _ => by simp only [termCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral]
  | .func s ts => by
      simp only [termCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode,
        liftTerm_termsCode c ts]
theorem liftTerm_termsCode (c : Nat) : ∀ ts : List Term, liftTerm c (termsCode ts) = termsCode ts
  | [] => rfl
  | t :: ts => by
      simp only [termsCode, cons, liftTerm, liftTerms, liftTerm_termCode c t, liftTerm_termsCode c ts]
end

theorem liftTerm_formCode (c : Nat) : ∀ φ : Formula, liftTerm c (formCode φ) = formCode φ
  | .bottom => by simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral]
  | .atom _ _ => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode,
        liftTerm_termsCode]
  | .eq _ _ => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_termCode]
  | .impl a b => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_formCode c a,
        liftTerm_formCode c b]
  | Formula.forall a => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_formCode c a]
  | .and a b => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_formCode c a,
        liftTerm_formCode c b]
  | .or a b => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_formCode c a,
        liftTerm_formCode c b]
  | .ex a => by
      simp only [formCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, liftTerm_formCode c a]

/-- `provCodeC' φ` es **cerrada**: invariante bajo `liftFormula`. -/
theorem liftFormula_provCodeC' (c : Nat) (φ : Formula) :
    liftFormula c (provCodeC' φ) = provCodeC' φ := by
  simp only [provCodeC', provFormulaC', substFormula, substTerm, substTerms, liftFormula, liftTerm,
    liftTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, liftTerm_formCode]

theorem d2_prf (A B : Formula) :
    Prf (provCodeC' (Formula.impl A B) ⇒ (provCodeC' A ⇒ provCodeC' B)) := by
  -- elimina el ∃ externo de `provCodeC'(A⇒B)`; testigo `p` = `#0`
  refine prf_ex_elim_imp ?_
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, liftTerm_formCode, liftFormula,
    liftFormula_provCodeC']
  -- ctx: [P_AB[p=#0]] ; goal: provCodeC' A ⇒ provCodeC' B
  refine deduction_aux ?_ (provCodeC' A)
    [land (chainOk nil (.var 0)) (In (formCode (Formula.impl A B)) (runFn nil (.var 0)))] rfl
  -- elimina el ∃ de `provCodeC'(A)` (testigo `q = #0`)
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil, liftFormula, liftTerm, liftTerms, liftFormula_provCodeC',
    substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ,
    if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, liftTerm_formCode]
  -- ctx: [A_A (q=#0), provCodeC' A, P_AB (p=#1)] ; goal: provCodeC' B
  -- testigo `r = p ++ q ++ [mpline]`,  mpline = ⌜B⌝ :: 16 :: ⌜A⌝ :: nil
  refine PrfH_ex_intro
    (concat (.var 1) (concat (.var 0)
      (cons (cons (formCode B) (cons (numeralM 16) (cons (formCode A) nil))) nil))) ?_
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- abreviaturas
  let Γ : List Formula := [land (chainOk nil (.var 0)) (In (formCode A) (runFn nil (.var 0))),
    provCodeC' A,
    land (chainOk nil (.var 1)) (In (formCode (Formula.impl A B)) (runFn nil (.var 1)))]
  let cA : Term := formCode A
  let cB : Term := formCode B
  let p_ : Term := (.var 1)
  let q_ : Term := (.var 0)
  let mpline : Term := cons cB (cons (numeralM 16) (cons cA nil))
  let Cpq : Term := runFn (runFn nil p_) q_
  -- hipótesis extraídas del contexto
  have hqChain : PrfH Γ (chainOk nil q_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hqIn : PrfH Γ (In cA (runFn nil q_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hpIn : PrfH Γ (In (implc cA cB) (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  -- hCpq_mp : runFn Cpq [mpline] =eq concat Cpq [cB]
  have hCpq_mp : Prf (runFn Cpq (cons mpline nil) =eq concat Cpq (cons cB nil)) :=
    prf_eq_trans (prf_runFn_cons Cpq mpline nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_congr_concat_left (prf_congr_cons_head
          (prf_carc_cons cB (cons (numeralM 16) (cons cA nil))))))
  -- hRunR : runFn nil r =eq concat Cpq [cB]
  have hRunR : Prf (runFn nil (concat p_ (concat q_ (cons mpline nil))) =eq concat Cpq (cons cB nil)) :=
    prf_eq_trans (prf_runFn_concat nil p_ (concat q_ (cons mpline nil)))
      (prf_eq_trans (prf_runFn_concat (runFn nil p_) q_ (cons mpline nil)) hCpq_mp)
  -- In ⌜B⌝ (runFn nil r)  (cerrado)
  have hInB : PrfH Γ (In cB (runFn nil (concat p_ (concat q_ (cons mpline nil))))) :=
    prf_to_prfH (prf_eq_subst_in (prf_eq_symm hRunR)
      (prf_In_mono cB (cons cB nil) Cpq (prf_in_cons_head cB nil))) Γ
  -- chainOk nil r
  have hChainR : PrfH Γ (chainOk nil (concat p_ (concat q_ (cons mpline nil)))) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ (concat q_ (cons mpline nil)))
      (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_concat (runFn nil p_) q_ (cons mpline nil))
      (PrfH_and_intro ?_ ?_)
    · -- chainOk (runFn nil p) q
      exact PrfH_chainOk_subst1 (prf_to_prfH (prf_concat_nil_right (runFn nil p_)) Γ)
        (PrfH.mp Γ _ _ (prf_to_prfH (prf_chainOk_mono_imp (runFn nil p_) nil q_) Γ) hqChain)
    · -- chainOk Cpq [mpline]
      refine PrfH_iff_mpr (prf_chainOk_cons Cpq mpline nil)
        (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
      -- lineOk Cpq mpline
      refine PrfH_and_intro (prf_to_prfH (prf_lineWF_mp cB cA) Γ) ?_
      refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_mp cB cA)) Γ) ?_
      refine PrfH_iff_mpr (prf_allIn_cons Cpq (implc cA cB) (cons cA nil))
        (PrfH_and_intro ?_ ?_)
      · -- In (implc cA cB) Cpq
        exact PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_runFn_weaken (runFn nil p_) q_)) Γ)
          (PrfH.mp Γ _ _ (prf_to_prfH (prf_In_mono_right_imp (implc cA cB) (runFn nil q_)
            (runFn nil p_)) Γ) hpIn)
      · refine PrfH_iff_mpr (prf_allIn_cons Cpq cA nil)
          (PrfH_and_intro ?_ (prf_to_prfH (prf_allIn_nil _) Γ))
        -- In ⌜A⌝ Cpq
        exact PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_runFn_weaken (runFn nil p_) q_)) Γ)
          (PrfH.mp Γ _ _ (prf_to_prfH (prf_In_mono_imp cA (runFn nil q_) (runFn nil p_)) Γ) hqIn)
  exact PrfH_and_intro hChainR hInB

end ROBINSON_PlusPlus.Meta.DerivCondPrf

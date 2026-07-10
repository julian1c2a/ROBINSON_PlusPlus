/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ForallElimCodePrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.MpCodePrf

/-!
## META — NIVEL D real (§19): **MP a nivel de CÓDIGO** (D2 generalizada)

`d2_prf` es la condición D2 para códigos de la forma `formCode φ`. Para la **evaluación provable**
(§18.3) hace falta razonar internamente con códigos **arbitrarios** (cerrados), no sólo con los que
provienen de una fórmula meta: los axiomas codificados se instancian con `pcc_forallElim_code'`, y el
resultado es un código `substfc zero w Ac` que ya no es un `formCode` de nada meta.

`pcc_mp_code` es el porte de `d2_prf` a códigos cerrados arbitrarios. Con él, más
`pcc_forallElim_code'` (∀‑elim) y `pcc_exIntro_code'` (∃‑intro), se tiene un **sistema de prueba
interno completo a nivel de código**, que es el andamiaje de la evaluación provable.
-/

/-- `liftTerm` es identidad sobre `implc Ac Bc` si lo es sobre `Ac` y `Bc` (tag cerrado). -/
theorem liftTerm_implc (Ac Bc : Term)
    (hAc : ∀ c, liftTerm c Ac = Ac) (hBc : ∀ c, liftTerm c Bc = Bc) :
    ∀ c, liftTerm c (implc Ac Bc) = implc Ac Bc := by
  intro c
  simp only [implc, cons, nil, zero, succ, liftTerm, liftTerms, hAc c, hBc c]

/-- **MP a nivel de código** (D2 para códigos cerrados arbitrarios):
    `Prov(⌜Ac ⇒ Bc⌝) ⇒ (Prov(⌜Ac⌝) ⇒ Prov(⌜Bc⌝))`.

    Ensamblaje `r = p ++ q ++ [mpline]`, espejo exacto de `d2_prf`, con `Ac`/`Bc` en lugar de
    `formCode A`/`formCode B` y las clausuras `hAc`/`hBc` en lugar de `liftTerm_formCode`. -/
theorem pcc_mp_code (Ac Bc : Term)
    (hAc : ∀ c, liftTerm c Ac = Ac) (hBc : ∀ c, liftTerm c Bc = Bc) :
    Prf (provFromCode (implc Ac Bc) ⇒ (provFromCode Ac ⇒ provFromCode Bc)) := by
  have hLA : ∀ k, liftFormula k (provFromCode Ac) = provFromCode Ac :=
    fun k => liftFormula_provFromCode k Ac hAc
  have hLB : ∀ k, liftFormula k (provFromCode Bc) = provFromCode Bc :=
    fun k => liftFormula_provFromCode k Bc hBc
  have hLI : ∀ c, liftTerm c (implc Ac Bc) = implc Ac Bc := liftTerm_implc Ac Bc hAc hBc
  -- elimina el ∃ externo de `provFromCode (implc Ac Bc)`; testigo `p = #0`
  refine prf_ex_elim_imp ?_
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, hLI, liftFormula, hLA, hLB]
  -- ctx: [P_AB[p=#0]] ; goal: provFromCode Ac ⇒ provFromCode Bc
  refine deduction_aux ?_ (provFromCode Ac)
    [land (chainOk nil (.var 0)) (In (implc Ac Bc) (runFn nil (.var 0)))] rfl
  -- elimina el ∃ de `provFromCode Ac` (testigo `q = #0`)
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil, liftFormula, liftTerm, liftTerms,
    substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ,
    if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, hLI, hLA, hLB, hAc, hBc]
  -- testigo `r = p ++ q ++ [mpline]`,  mpline = ⟨Bc, 16, Ac⟩
  refine PrfH_ex_intro
    (concat (.var 1) (concat (.var 0)
      (cons (cons Bc (cons (numeralM 16) (cons Ac nil))) nil))) ?_
  -- NO colapsar aquí `liftTerm 0 Bc`: se cancela con la subst externa `substTerm 0 r (·)`
  -- (`FOL.substTerm_liftTerm`). Incluir `hBc` lo destruiría (mismo escollo que `pcc_exIntro_code`).
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- abreviaturas
  let Γ : List Formula := [land (chainOk nil (.var 0)) (In Ac (runFn nil (.var 0))),
    provFromCode Ac,
    land (chainOk nil (.var 1)) (In (implc Ac Bc) (runFn nil (.var 1)))]
  let p_ : Term := (.var 1)
  let q_ : Term := (.var 0)
  let mpline : Term := cons Bc (cons (numeralM 16) (cons Ac nil))
  let Cpq : Term := runFn (runFn nil p_) q_
  have hqChain : PrfH Γ (chainOk nil q_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hqIn : PrfH Γ (In Ac (runFn nil q_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hpIn : PrfH Γ (In (implc Ac Bc) (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hCpq_mp : Prf (runFn Cpq (cons mpline nil) =eq concat Cpq (cons Bc nil)) :=
    prf_eq_trans (prf_runFn_cons Cpq mpline nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_congr_concat_left (prf_congr_cons_head
          (prf_carc_cons Bc (cons (numeralM 16) (cons Ac nil))))))
  have hRunR : Prf (runFn nil (concat p_ (concat q_ (cons mpline nil))) =eq
      concat Cpq (cons Bc nil)) :=
    prf_eq_trans (prf_runFn_concat nil p_ (concat q_ (cons mpline nil)))
      (prf_eq_trans (prf_runFn_concat (runFn nil p_) q_ (cons mpline nil)) hCpq_mp)
  have hInB : PrfH Γ (In Bc (runFn nil (concat p_ (concat q_ (cons mpline nil))))) :=
    prf_to_prfH (prf_eq_subst_in (prf_eq_symm hRunR)
      (prf_In_mono Bc (cons Bc nil) Cpq (prf_in_cons_head Bc nil))) Γ
  have hChainR : PrfH Γ (chainOk nil (concat p_ (concat q_ (cons mpline nil)))) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ (concat q_ (cons mpline nil)))
      (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_concat (runFn nil p_) q_ (cons mpline nil))
      (PrfH_and_intro ?_ ?_)
    · exact PrfH_chainOk_subst1 (prf_to_prfH (prf_concat_nil_right (runFn nil p_)) Γ)
        (PrfH.mp Γ _ _ (prf_to_prfH (prf_chainOk_mono_imp (runFn nil p_) nil q_) Γ) hqChain)
    · refine PrfH_iff_mpr (prf_chainOk_cons Cpq mpline nil)
        (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
      refine PrfH_and_intro (prf_to_prfH (prf_lineWF_mp Bc Ac) Γ) ?_
      refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_mp Bc Ac)) Γ) ?_
      refine PrfH_iff_mpr (prf_allIn_cons Cpq (implc Ac Bc) (cons Ac nil))
        (PrfH_and_intro ?_ ?_)
      · exact PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_runFn_weaken (runFn nil p_) q_)) Γ)
          (PrfH.mp Γ _ _ (prf_to_prfH (prf_In_mono_right_imp (implc Ac Bc) (runFn nil q_)
            (runFn nil p_)) Γ) hpIn)
      · refine PrfH_iff_mpr (prf_allIn_cons Cpq Ac nil)
          (PrfH_and_intro ?_ (prf_to_prfH (prf_allIn_nil _) Γ))
        exact PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_runFn_weaken (runFn nil p_) q_)) Γ)
          (PrfH.mp Γ _ _ (prf_to_prfH (prf_In_mono_imp Ac (runFn nil q_) (runFn nil p_)) Γ) hqIn)
  exact PrfH_and_intro hChainR hInB

/-- **MP interno como esquema, a nivel de código** (aplicación directa). -/
theorem pcc_mp_code_apply {Ac Bc : Term}
    (hAc : ∀ c, liftTerm c Ac = Ac) (hBc : ∀ c, liftTerm c Bc = Bc)
    (himp : Prf (provFromCode (implc Ac Bc))) (ha : Prf (provFromCode Ac)) :
    Prf (provFromCode Bc) :=
  prf_mp (prf_mp (pcc_mp_code Ac Bc hAc hBc) himp) ha

/-! ### Instanciación de axiomas CODIFICADOS de la teoría

Primer uso real del toolkit: un axioma `∀x. φ(x)` de `axioms` tiene su código demostrable
(`repr_pos'_prf` sobre `prf_ax`), y el ∀‑elim de código lo **instancia en cualquier código‑testigo
`w`, incluso abierto**. Es el paso que la **evaluación provable** repite sobre `ax4`/`ax5`. -/

/-- **Instanciación de un axioma universal codificado**: si `∀φ ∈ axioms`, entonces para todo
    código‑testigo `w` (abierto o cerrado) el código sustituido `substfc zero w ⌜φ⌝` es demostrable.

    `formCode (Formula.forall φ) = forallc (formCode φ)` (definicional). -/
theorem pcc_axiom_inst (φ : Formula) (hmem : Formula.forall φ ∈ axioms) (w : Term) :
    Prf (provFromCode (substfc zero w (formCode φ))) :=
  prf_mp
    (pcc_forallElim_code' (formCode φ) w (fun c => liftTerm_formCode c φ))
    (repr_pos'_prf (prf_ax hmem))

/-- Instancia codificada de **`ax4_add_zero`** (`∀n. n + 0 = n`): el caso base de la evaluación
    provable de `+`. Testigo‑código `w` arbitrario (puede ser `tcFn` de una variable ligada). -/
theorem pcc_ax4_inst (w : Term) :
    Prf (provFromCode (substfc zero w (formCode (add (.var 0) zero =eq (.var 0))))) :=
  pcc_axiom_inst _ (show ax4_add_zero ∈ axioms by simp [axioms]) w

end ROBINSON_PlusPlus.Meta.MpCodePrf

export ROBINSON_PlusPlus.Meta.MpCodePrf (
  liftTerm_implc pcc_mp_code pcc_mp_code_apply pcc_axiom_inst pcc_ax4_inst
)

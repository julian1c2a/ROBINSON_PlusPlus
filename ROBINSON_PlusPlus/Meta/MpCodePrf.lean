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
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ForallElimCodePrf

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

/-- **Versión lift‑aware (`Ac`, `Bc` ABIERTOS)**: el lift atraviesa `implc` (tag cerrado). -/
theorem liftTerm_implc_open (Ac Bc : Term) :
    ∀ c, liftTerm c (implc Ac Bc) = implc (liftTerm c Ac) (liftTerm c Bc) := by
  intro c
  simp only [implc, cons, nil, zero, succ, liftTerm, liftTerms]

/-- **MP a nivel de código, con códigos ABIERTOS** (§25.3):
    `Prov(⌜Ac ⇒ Bc⌝) ⇒ (Prov(⌜Ac⌝) ⇒ Prov(⌜Bc⌝))`, **sin** exigir `Ac`, `Bc` cerrados.

    Ensamblaje `r = p ++ q ++ [mpline]`, espejo de `d2_prf`. La clausura `hAc`/`hBc` era, como `hw`
    (§17) y `hAc` en el `∀`‑elim (§22), un **artefacto de colapsar los lifts**: aquí se **arrastran**
    (`liftFormula_provFromCode_open` los traslada al código, `liftTerm_implc_open` los mete bajo el
    `implc`). Tras los dos `∃`‑elim los códigos quedan **doblemente lifteados** (`↑↑Ac`, `↑↑Bc`), y el
    resto de la prueba pasa verbatim con ellos. -/
theorem pcc_mp_code_open (Ac Bc : Term) :
    Prf (provFromCode (implc Ac Bc) ⇒ (provFromCode Ac ⇒ provFromCode Bc)) := by
  -- elimina el ∃ externo de `provFromCode (implc Ac Bc)`; testigo `p = #0`
  refine prf_ex_elim_imp ?_
  -- CONSECUENTE: el lift se traslada a los códigos
  have hC : liftFormula 0 (provFromCode Ac ⇒ provFromCode Bc)
      = (provFromCode (liftTerm 0 Ac) ⇒ provFromCode (liftTerm 0 Bc)) := by
    simp only [liftFormula, liftFormula_provFromCode_open]
  rw [hC]
  -- ANTECEDENTE: el lift atraviesa el `implc`
  simp only [liftTerm_implc_open Ac Bc]
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- ctx: [P_AB[p=#0]] ; goal: provFromCode ↑Ac ⇒ provFromCode ↑Bc
  refine deduction_aux ?_ (provFromCode (liftTerm 0 Ac))
    [land (chainOk nil (.var 0))
      (In (implc (liftTerm 0 Ac) (liftTerm 0 Bc)) (runFn nil (.var 0)))] rfl
  -- elimina el ∃ de `provFromCode ↑Ac` (testigo `q = #0`); el contexto se liftea otra vez
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil, liftFormula, liftFormula_provFromCode_open,
    liftTerm_implc_open, liftTerm, liftTerms,
    substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ,
    if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- abreviaturas: los códigos van DOBLEMENTE lifteados
  let A2 : Term := liftTerm 0 (liftTerm 0 Ac)
  let B2 : Term := liftTerm 0 (liftTerm 0 Bc)
  -- testigo `r = p ++ q ++ [mpline]`,  mpline = ⟨B2, 16, A2⟩
  refine PrfH_ex_intro
    (concat (.var 1) (concat (.var 0)
      (cons (cons B2 (cons (numeralM 16) (cons A2 nil))) nil))) ?_
  -- NO colapsar aquí `liftTerm 0 B2`: se cancela con la subst externa `substTerm 0 r (·)`
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  let Γ : List Formula := [land (chainOk nil (.var 0)) (In A2 (runFn nil (.var 0))),
    provFromCode A2,
    land (chainOk nil (.var 1)) (In (implc A2 B2) (runFn nil (.var 1)))]
  let p_ : Term := (.var 1)
  let q_ : Term := (.var 0)
  let mpline : Term := cons B2 (cons (numeralM 16) (cons A2 nil))
  let Cpq : Term := runFn (runFn nil p_) q_
  have hqChain : PrfH Γ (chainOk nil q_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hqIn : PrfH Γ (In A2 (runFn nil q_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hpIn : PrfH Γ (In (implc A2 B2) (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hCpq_mp : Prf (runFn Cpq (cons mpline nil) =eq concat Cpq (cons B2 nil)) :=
    prf_eq_trans (prf_runFn_cons Cpq mpline nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_congr_concat_left (prf_congr_cons_head
          (prf_carc_cons B2 (cons (numeralM 16) (cons A2 nil))))))
  have hRunR : Prf (runFn nil (concat p_ (concat q_ (cons mpline nil))) =eq
      concat Cpq (cons B2 nil)) :=
    prf_eq_trans (prf_runFn_concat nil p_ (concat q_ (cons mpline nil)))
      (prf_eq_trans (prf_runFn_concat (runFn nil p_) q_ (cons mpline nil)) hCpq_mp)
  have hInB : PrfH Γ (In B2 (runFn nil (concat p_ (concat q_ (cons mpline nil))))) :=
    prf_to_prfH (prf_eq_subst_in (prf_eq_symm hRunR)
      (prf_In_mono B2 (cons B2 nil) Cpq (prf_in_cons_head B2 nil))) Γ
  have hChainR : PrfH Γ (chainOk nil (concat p_ (concat q_ (cons mpline nil)))) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ (concat q_ (cons mpline nil)))
      (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_concat (runFn nil p_) q_ (cons mpline nil))
      (PrfH_and_intro ?_ ?_)
    · exact PrfH_chainOk_subst1 (prf_to_prfH (prf_concat_nil_right (runFn nil p_)) Γ)
        (PrfH.mp Γ _ _ (prf_to_prfH (prf_chainOk_mono_imp (runFn nil p_) nil q_) Γ) hqChain)
    · refine PrfH_iff_mpr (prf_chainOk_cons Cpq mpline nil)
        (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
      refine PrfH_and_intro (prf_to_prfH (prf_lineWF_mp B2 A2) Γ) ?_
      refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_mp B2 A2)) Γ) ?_
      refine PrfH_iff_mpr (prf_allIn_cons Cpq (implc A2 B2) (cons A2 nil))
        (PrfH_and_intro ?_ ?_)
      · exact PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_runFn_weaken (runFn nil p_) q_)) Γ)
          (PrfH.mp Γ _ _ (prf_to_prfH (prf_In_mono_right_imp (implc A2 B2) (runFn nil q_)
            (runFn nil p_)) Γ) hpIn)
      · refine PrfH_iff_mpr (prf_allIn_cons Cpq A2 nil)
          (PrfH_and_intro ?_ (prf_to_prfH (prf_allIn_nil _) Γ))
        exact PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_runFn_weaken (runFn nil p_) q_)) Γ)
          (PrfH.mp Γ _ _ (prf_to_prfH (prf_In_mono_imp A2 (runFn nil q_) (runFn nil p_)) Γ) hqIn)
  exact PrfH_and_intro hChainR hInB

/-- **Corolario (compatibilidad)**: la versión con `Ac`, `Bc` cerrados. Las hipótesis `hAc`/`hBc` ya
    **no se usan** (cuarto artefacto de clausura; ver `hw` §17, `hAc` §22). -/
theorem pcc_mp_code (Ac Bc : Term)
    (_hAc : ∀ c, liftTerm c Ac = Ac) (_hBc : ∀ c, liftTerm c Bc = Bc) :
    Prf (provFromCode (implc Ac Bc) ⇒ (provFromCode Ac ⇒ provFromCode Bc)) :=
  pcc_mp_code_open Ac Bc

/-- **MP interno como esquema, a nivel de código** (aplicación directa, códigos ABIERTOS). -/
theorem pcc_mp_code_apply {Ac Bc : Term}
    (himp : Prf (provFromCode (implc Ac Bc))) (ha : Prf (provFromCode Ac)) :
    Prf (provFromCode Bc) :=
  prf_mp (prf_mp (pcc_mp_code_open Ac Bc) himp) ha

/-! ### Instanciación de axiomas CODIFICADOS de la teoría

Primer uso real del toolkit: un axioma `∀x. φ(x)` de `axioms` tiene su código demostrable
(`repr_pos'_prf` sobre `prf_ax`), y el ∀‑elim de código lo **instancia en cualquier código‑testigo
`w`, incluso abierto**. Es el paso que la **evaluación provable** repite sobre `ax4`/`ax5`. -/

/-- **Instanciación de un TEOREMA universal codificado**: de `Prf (∀φ)` sale que, para todo
    código‑testigo `w` (abierto o cerrado), el código sustituido `substfc zero w ⌜φ⌝` es demostrable.

    `formCode (Formula.forall φ) = forallc (formCode φ)` (definicional). Es la forma general:
    `pcc_axiom_inst` es el caso `h = prf_ax hmem`. Sirve para internalizar **cualquier** teorema
    universal de la teoría objeto (p. ej. la transitividad de `=`), no sólo los axiomas. -/
theorem pcc_thm_inst (φ : Formula) (h : Prf (Formula.forall φ)) (w : Term) :
    Prf (provFromCode (substfc zero w (formCode φ))) :=
  prf_mp (pcc_forallElim_code_open (formCode φ) w) (repr_pos'_prf h)

/-- **Instanciación de un TEOREMA `∀∀φ` codificado** (dos testigos, ambos pueden ser abiertos). -/
theorem pcc_thm_inst2 (φ : Formula) (h : Prf (forall_2 φ)) (w₁ w₂ : Term) :
    Prf (provFromCode (substfc zero w₂ (substfc (succ zero) (liftc zero w₁) (formCode φ)))) := by
  have h0 : Prf (provFromCode (formCode (forall_2 φ))) := repr_pos'_prf h
  have h1 : Prf (provFromCode (substfc zero w₁ (forallc (formCode φ)))) :=
    prf_mp (pcc_forallElim_code_open (forallc (formCode φ)) w₁) h0
  have h2 : Prf (provFromCode (forallc (substfc (succ zero) (liftc zero w₁) (formCode φ)))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₁ (formCode φ))) h1
  exact prf_mp (pcc_forallElim_code_open _ w₂) h2

/-- **Instanciación de un axioma universal codificado** (caso `h = prf_ax hmem` de `pcc_thm_inst`). -/
theorem pcc_axiom_inst (φ : Formula) (hmem : Formula.forall φ ∈ axioms) (w : Term) :
    Prf (provFromCode (substfc zero w (formCode φ))) :=
  pcc_thm_inst φ (prf_ax hmem) w

/-- Instancia codificada de **`ax4_add_zero`** (`∀n. n + 0 = n`): el caso base de la evaluación
    provable de `+`. Testigo‑código `w` arbitrario (puede ser `tcFn` de una variable ligada). -/
theorem pcc_ax4_inst (w : Term) :
    Prf (provFromCode (substfc zero w (formCode (add (.var 0) zero =eq (.var 0))))) :=
  pcc_axiom_inst _ (show ax4_add_zero ∈ axioms by simp [axioms]) w

/-- **Instanciación de un axioma `∀∀φ` codificado** (dos testigos).

    `formCode (forall_2 φ) = forallc (forallc (formCode φ))` (definicional). Se elimina el `∀` externo
    con `w₁`, se empuja el `substfc` bajo el binder (`prf_substfc_forall`, que **levanta el testigo**:
    `liftc zero w₁`), y se elimina el `∀` interno con `w₂`.

    **Nota:** el cuerpo de la segunda eliminación, `substfc (σ0) (liftc 0 w₁) ⌜φ⌝`, contiene `w₁` y
    por tanto **no es cerrado** cuando `w₁` es abierto. Por eso hace falta `pcc_forallElim_code_open`
    (sin `hAc`), no `pcc_forallElim_code'`. -/
theorem pcc_axiom_inst2 (φ : Formula) (hmem : forall_2 φ ∈ axioms) (w₁ w₂ : Term) :
    Prf (provFromCode (substfc zero w₂ (substfc (succ zero) (liftc zero w₁) (formCode φ)))) :=
  pcc_thm_inst2 φ (prf_ax hmem) w₁ w₂

/-- Instancia codificada de **`ax5_add_succ`** (`∀n∀m. n + σm = σ(n+m)`): el paso inductivo de la
    evaluación provable de `+`. Ambos testigos‑código arbitrarios (pueden ser abiertos). -/
theorem pcc_ax5_inst (w₁ w₂ : Term) :
    Prf (provFromCode (substfc zero w₂ (substfc (succ zero) (liftc zero w₁)
      (formCode (add (.var 1) (succ (.var 0)) =eq succ (add (.var 1) (.var 0))))))) :=
  pcc_axiom_inst2 _ (show ax5_add_succ ∈ axioms by simp [axioms]) w₁ w₂

/-- **Instanciación de un TEOREMA `∀∀∀φ` codificado** (tres testigos, todos pueden ser abiertos).
    Extiende `pcc_thm_inst2` con un binder más: elimina el `∀` externo con `w₁`, empuja el `substfc`
    bajo cada binder (`prf_substfc_forall`, que levanta el testigo con `liftc zero`), y elimina los
    dos `∀` internos con `w₂`, `w₃`. -/
theorem pcc_thm_inst3 (φ : Formula) (h : Prf (forall_3 φ)) (w₁ w₂ w₃ : Term) :
    Prf (provFromCode (substfc zero w₃ (substfc (succ zero) (liftc zero w₂)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₁)) (formCode φ))))) := by
  have h0 : Prf (provFromCode (formCode (forall_3 φ))) := repr_pos'_prf h
  have h1 : Prf (provFromCode (substfc zero w₁ (formCode (forall_2 φ)))) :=
    prf_mp (pcc_forallElim_code_open (formCode (forall_2 φ)) w₁) h0
  have h2 : Prf (provFromCode (forallc (substfc (succ zero) (liftc zero w₁)
      (forallc (formCode φ))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₁ (forallc (formCode φ)))) h1
  have h3 : Prf (provFromCode (substfc zero w₂ (substfc (succ zero) (liftc zero w₁)
      (forallc (formCode φ))))) :=
    prf_mp (pcc_forallElim_code_open _ w₂) h2
  have h4 : Prf (provFromCode (substfc zero w₂ (forallc (substfc (succ (succ zero))
      (liftc zero (liftc zero w₁)) (formCode φ))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (succ zero) (liftc zero w₁) (formCode φ)))) h3
  have h5 : Prf (provFromCode (forallc (substfc (succ zero) (liftc zero w₂)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₁)) (formCode φ))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₂
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₁)) (formCode φ)))) h4
  exact prf_mp (pcc_forallElim_code_open _ w₃) h5

/-- **Instanciación de un axioma `∀∀∀φ` codificado** (tres testigos). -/
theorem pcc_axiom_inst3 (φ : Formula) (hmem : forall_3 φ ∈ axioms) (w₁ w₂ w₃ : Term) :
    Prf (provFromCode (substfc zero w₃ (substfc (succ zero) (liftc zero w₂)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₁)) (formCode φ))))) :=
  pcc_thm_inst3 φ (prf_ax hmem) w₁ w₂ w₃

/-! ### §N+1 · Cuatro testigos (promovido de `sondeos/SubstfcPlanos.lean`, 2026‑08‑31)

La familia se paraba en **tres**, pero los axiomas binarios de `substfc` son `forall_4`:
`ax_substfc_impl`/`_and`/`_or` (`Minimal/Axioms.lean:506,512,515`), y también `ax_substfc_atom`
(`:500`) y `ax_substfc_eq` (`:503`). **Cinco consumidores** en el frente `substfc`, y dos agentes
independientes escribieron esta misma pieza por separado antes de que se promoviera.

Extensión **mecánica** de `pcc_thm_inst3` con un binder más: el mismo baile de
`pcc_forallElim_code_open` + `prf_substfc_forall` + `prf_congr_substfc_arg3`, una vuelta más. -/

/-- **Instanciación de un TEOREMA `∀∀∀∀φ` codificado** (cuatro testigos, todos pueden ser abiertos). -/
theorem pcc_thm_inst4 (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) := by
  have h0 : Prf (provFromCode (formCode (forall_4 φ))) := repr_pos'_prf h
  have h1 : Prf (provFromCode (substfc zero w₁ (formCode (forall_3 φ)))) :=
    prf_mp (pcc_forallElim_code_open (formCode (forall_3 φ)) w₁) h0
  have h2 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₁)
      (formCode (forall_2 φ))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₁ (formCode (forall_2 φ)))) h1
  have h3 : Prf (provFromCode (substfc zero w₂ (substfc (numeral 1) (liftc zero w₁)
      (formCode (forall_2 φ))))) :=
    prf_mp (pcc_forallElim_code_open _ w₂) h2
  have h4 : Prf (provFromCode (substfc zero w₂ (forallc (substfc (numeral 2)
      (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 1) (liftc zero w₁) (forallc (formCode φ))))) h3
  have h5 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₂)
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₂
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ))))) h4
  have h6 : Prf (provFromCode (substfc zero w₃ (substfc (numeral 1) (liftc zero w₂)
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (pcc_forallElim_code_open _ w₃) h5
  have h7 : Prf (provFromCode (substfc zero w₃ (substfc (numeral 1) (liftc zero w₂)
      (forallc (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁)))
        (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 2) (liftc zero (liftc zero w₁)) (formCode φ))))) h6
  have h8 : Prf (provFromCode (substfc zero w₃ (forallc (substfc (numeral 2)
      (liftc zero (liftc zero w₂))
      (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 1) (liftc zero w₂)
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) h7
  have h9 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₃
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) h8
  exact prf_mp (pcc_forallElim_code_open _ w₄) h9

/-- **Instanciación de un axioma `∀∀∀∀φ` codificado** (cuatro testigos). -/
theorem pcc_axiom_inst4 (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_thm_inst4 φ (prf_ax hmem) w₁ w₂ w₃ w₄

end ROBINSON_PlusPlus.Meta.MpCodePrf

export ROBINSON_PlusPlus.Meta.MpCodePrf (
  liftTerm_implc liftTerm_implc_open pcc_mp_code_open pcc_mp_code pcc_mp_code_apply
  pcc_thm_inst pcc_thm_inst2 pcc_thm_inst3 pcc_thm_inst4
  pcc_axiom_inst pcc_axiom_inst2 pcc_axiom_inst3 pcc_axiom_inst4
  pcc_ax4_inst pcc_ax5_inst
)

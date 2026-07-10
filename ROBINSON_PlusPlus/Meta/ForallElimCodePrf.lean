/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ExIntroCodePrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf

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
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.ExIntroCodePrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.ForallElimCodePrf

/-!
## META — NIVEL D real (§18.4/§19): `∀`‑elim a nivel de CÓDIGO

Dual de `pcc_exIntro_code'` (`Meta/ExIntroCodePrf.lean`): reflexión de la **regla Q1**
(`∀A ⇒ A[t]`) al nivel de código, con **testigo‑código abierto** `w`.

**La asimetría con Q2.** En `pcc_exIntro_code'` el código abierto (`substfc zero w Ac`) cae en el
**antecedente**, y se arrastra su lift. Aquí cae en el **consecuente**, así que la clausura que
`prf_ex_elim_imp` exige no puede ser «código cerrado» — hay que usar la versión para códigos
abiertos, `liftFormula_provFromCode_open` (`Meta/TrackedCorePrf.lean`).

`prf_lineWF_q1 (concl A t) : lineWF ⟨concl, 9, A, t⟩ ⇔ (concl =eq implc (forallc A) (substfc zero t A))`
es **estructural** (no aparece `termCode`), igual que la línea Q2 — por eso admite `A`,`t` arbitrarios.

**Para qué:** instanciar **axiomas codificados** (`ax4`, `ax5`, …) dentro de una prueba interna. Es
el ladrillo que la **evaluación provable** (§18.3, núcleo de la fase 3) necesita.
-/

/-- `liftTerm` es identidad sobre `forallc Ac` si lo es sobre `Ac` (tag cerrado). -/
theorem liftTerm_forallc (Ac : Term) (hAc : ∀ c, liftTerm c Ac = Ac) :
    ∀ c, liftTerm c (forallc Ac) = forallc Ac := by
  intro c
  simp only [forallc, cons, nil, zero, succ, liftTerm, liftTerms, hAc c]

/-- **Validez de una línea Q1** en cualquier contexto `c`:
    `q1line = ⟨implc (forallc Ac) (substfc zero w Ac), 9, Ac, w⟩`. `lineWF` por reflexividad de la
    conclusión (`prf_lineWF_q1`), sin premisas (`prf_premsOf_q1` → `allIn c nil`). -/
theorem prf_lineOk_q1 (c Ac w : Term) :
    Prf (lineOk c (cons (implc (forallc Ac) (substfc zero w Ac))
      (cons (numeralM 9) (cons Ac (cons w nil))))) :=
  prf_and_intro
    (prf_iff_mpr (prf_lineWF_q1 _ Ac w) (prf_refl _))
    (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_q1 _ Ac w)) (prf_allIn_nil c))

/-- **`∀`‑elim a nivel de código** (reflexión de la regla Q1), con testigo‑código **abierto**:
    de la demostrabilidad del código universal `forallc Ac` sale la del código sustituido
    `substfc zero w Ac`. Sólo pide `Ac` cerrado (`hAc`).

    Ensamblaje `r = p ++ [q1line, mpline]`, espejo de `pcc_exIntro_code'`. -/
theorem pcc_forallElim_code' (Ac w : Term)
    (hAc : ∀ c, liftTerm c Ac = Ac) :
    Prf (provFromCode (forallc Ac) ⇒ provFromCode (substfc zero w Ac)) := by
  -- elimina el ∃ externo de `provFromCode (forallc Ac)`; testigo `p = #0`
  refine prf_ex_elim_imp ?_
  -- el CONSECUENTE tiene código abierto: su lift se traslada al código (no se colapsa)
  rw [liftFormula_provFromCode_open 0 (substfc zero w Ac),
    liftTerm_substfc_open Ac hAc w 0]
  -- el ANTECEDENTE tiene código cerrado (`forallc Ac`)
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, liftTerm_forallc Ac hAc]
  -- ctx: [chainOk nil #0 ∧ In (forallc Ac) (runFn nil #0)] ; meta: provFromCode (substfc zero ↑w Ac)
  refine PrfH_ex_intro
    (concat (.var 0)
      (cons (cons (implc (forallc Ac) (substfc zero (liftTerm 0 w) Ac))
              (cons (numeralM 9) (cons Ac (cons (liftTerm 0 w) nil))))
        (cons (cons (substfc zero (liftTerm 0 w) Ac)
          (cons (numeralM 16) (cons (forallc Ac) nil))) nil))) ?_
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- abreviaturas (`w'` = testigo LIFTEADO)
  let w' : Term := liftTerm 0 w
  let Aall : Term := forallc Ac
  let Bsub : Term := substfc zero w' Ac
  let p_ : Term := (.var 0)
  let q1line : Term := cons (implc Aall Bsub) (cons (numeralM 9) (cons Ac (cons w' nil)))
  let mpline : Term := cons Bsub (cons (numeralM 16) (cons Aall nil))
  let tl : Term := cons q1line (cons mpline nil)
  let Γ : List Formula := [land (chainOk nil p_) (In Aall (runFn nil p_))]
  let Cp : Term := runFn nil p_
  let Cp1 : Term := concat Cp (cons (carc q1line) nil)
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hpIn : PrfH Γ (In Aall (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  -- Part B: In Bsub (runFn nil r)
  have hmp : Prf (runFn Cp1 (cons mpline nil) =eq concat Cp1 (cons Bsub nil)) :=
    prf_eq_trans (prf_runFn_cons Cp1 mpline nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_congr_concat_left (prf_congr_cons_head
          (prf_carc_cons Bsub (cons (numeralM 16) (cons Aall nil))))))
  have hRunR : Prf (runFn nil (concat p_ tl) =eq concat Cp1 (cons Bsub nil)) :=
    prf_eq_trans (prf_runFn_concat nil p_ tl)
      (prf_eq_trans (prf_runFn_cons Cp q1line (cons mpline nil)) hmp)
  have hInB : PrfH Γ (In Bsub (runFn nil (concat p_ tl))) :=
    prf_to_prfH (prf_eq_subst_in (prf_eq_symm hRunR)
      (prf_In_mono Bsub (cons Bsub nil) Cp1 (prf_in_cons_head Bsub nil))) Γ
  -- Part A: chainOk nil r
  have hChainR : PrfH Γ (chainOk nil (concat p_ tl)) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ tl) (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_cons Cp q1line (cons mpline nil)) (PrfH_and_intro ?_ ?_)
    · -- lineOk Cp q1line (línea‑axioma Q1)
      exact prf_to_prfH (prf_lineOk_q1 Cp Ac w') Γ
    · -- chainOk Cp1 [mpline]
      refine PrfH_iff_mpr (prf_chainOk_cons Cp1 mpline nil)
        (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
      -- lineOk Cp1 mpline
      refine PrfH_and_intro (prf_to_prfH (prf_lineWF_mp Bsub Aall) Γ) ?_
      refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_mp Bsub Aall)) Γ) ?_
      refine PrfH_iff_mpr (prf_allIn_cons Cp1 (implc Aall Bsub) (cons Aall nil))
        (PrfH_and_intro ?_ ?_)
      · -- In (implc Aall Bsub) Cp1  (= carc q1line, apendizada por la línea Q1)
        have hcarc : Prf (cons (implc Aall Bsub) nil =eq cons (carc q1line) nil) :=
          prf_congr_cons_head (prf_eq_symm
            (prf_carc_cons (implc Aall Bsub) (cons (numeralM 9) (cons Ac (cons w' nil)))))
        exact prf_to_prfH
          (prf_In_mono (implc Aall Bsub) (cons (carc q1line) nil) Cp
            (prf_eq_subst_in hcarc (prf_in_cons_head (implc Aall Bsub) nil))) Γ
      · refine PrfH_iff_mpr (prf_allIn_cons Cp1 Aall nil)
          (PrfH_and_intro ?_ (prf_to_prfH (prf_allIn_nil _) Γ))
        -- In Aall Cp1  (Aall ∈ Cp por hipótesis, monotonía por la derecha)
        exact PrfH.mp Γ _ _
          (prf_to_prfH (prf_In_mono_right_imp Aall (cons (carc q1line) nil) Cp) Γ) hpIn
  exact PrfH_and_intro hChainR hInB

end ROBINSON_PlusPlus.Meta.ForallElimCodePrf

export ROBINSON_PlusPlus.Meta.ForallElimCodePrf (
  liftTerm_forallc prf_lineOk_q1 pcc_forallElim_code'
)

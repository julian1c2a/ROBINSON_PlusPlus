/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalBoundedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.ExIntroCodePrf
open ROBINSON_PlusPlus.Meta.ForallElimCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace ROBINSON_PlusPlus.Meta.Delta0ReflectPrf

/-!
## META — NIVEL D real (§31): completitud‑Δ₀ provable — reflexión del átomo `<` ABIERTO

Arranque de la **completitud‑Δ₀ provable** (la dirección elegida para cerrar D3). El átomo `<` sobre
términos **abstractos** se reflejaba, en apariencia, contra el muro: `tcFn` no distribuye sobre `+`.
La clave que lo desbloquea es que **`pcc_eval_add` (probado por inducción interna) SÍ demuestra**

```text
⊢ Prov( ⌜ ȧ + ḃ = (a+b)˙ ⌝ )    para a, b ARBITRARIOS
```

— es decir, el término simbólico `addcT (tcFn a) (tcFn b)` y el numeral del valor `tcFn (add a b)`
son **provablemente iguales como códigos**. Con eso, `s < t` (vía `ax13`: `∃k. s+σk=t`) se refleja:

* `∃`‑elim de la hipótesis da un testigo `k` con `s + σk = t`;
* `pcc_eval_add s (σk)` da `Prov(⌜ ṡ + (σk)˙ = (s+σk)˙ ⌝)`, y transportando `(s+σk)˙ = ṫ` y
  `(σk)˙ = σ(k̇)` se obtiene `Prov(⌜ ṡ + σ(k̇) = ṫ ⌝)`, la premisa que pide `pcc_lt_intro`;
* pero `pcc_lt_intro` exige `s`, `t` **cerrados** (para el `∃`‑intro). El único artefacto es la
  clausura `hAc` del `∃`‑intro, que se elimina **arrastrando el lift** (patrón §26): este módulo abre
  con `pcc_exIntro_code_open` (Q2 sin `hAc`).
-/

/-- `liftTerm` atraviesa `exc Ac` (tag cerrado), **sin** exigir `Ac` cerrado. -/
theorem liftTerm_exc_open (Ac : Term) : ∀ c, liftTerm c (exc Ac) = exc (liftTerm c Ac) := by
  intro c
  simp only [exc, cons, nil, zero, succ, liftTerm, liftTerms]

/-- **∃‑intro a nivel de código, con `Ac` ABIERTO** (reflexión de Q2 sin clausura): para `Ac`, `w`
    **arbitrarios**, `Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))`.

    Espejo de `pcc_exIntro_code'` **arrastrando el lift** (§26): tras `prf_ex_elim_imp`, el
    consecuente `provFromCode (exc Ac)` bajo `liftFormula 0` se traslada al código
    (`liftFormula_provFromCode_open`) y cae sobre `exc (liftTerm 0 Ac)` (`liftTerm_exc_open`); el
    antecedente `substfc zero w Ac` bajo el lift se abre con `liftTerm_substfc_open2`. El ensamblaje
    `p ++ [q2line, mpline]` pasa verbatim con `Ac ↦ liftTerm 0 Ac`. -/
theorem pcc_exIntro_code_open (Ac w : Term) :
    Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_provFromCode_open 0 (exc Ac), liftTerm_exc_open Ac 0]
  simp only [liftTerm_substfc_open2 Ac w]
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  -- ctx: [chainOk nil #0 ∧ In Ain (runFn nil #0)] con `Ain = substfc zero (↑w) (↑Ac)`
  refine PrfH_ex_intro
    (concat (.var 0)
      (cons (cons (implc (substfc zero (liftTerm 0 w) (liftTerm 0 Ac)) (exc (liftTerm 0 Ac)))
              (cons (numeralM 10) (cons (liftTerm 0 Ac) (cons (liftTerm 0 w) nil))))
        (cons (cons (exc (liftTerm 0 Ac))
          (cons (numeralM 16) (cons (substfc zero (liftTerm 0 w) (liftTerm 0 Ac)) nil))) nil))) ?_
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  let A' : Term := liftTerm 0 Ac
  let w' : Term := liftTerm 0 w
  let Ain : Term := substfc zero w' A'
  let Bex : Term := exc A'
  let p_ : Term := (.var 0)
  let q2line : Term := cons (implc Ain Bex) (cons (numeralM 10) (cons A' (cons w' nil)))
  let mpline : Term := cons Bex (cons (numeralM 16) (cons Ain nil))
  let tl : Term := cons q2line (cons mpline nil)
  let Γ : List Formula := [land (chainOk nil p_) (In Ain (runFn nil p_))]
  let Cp : Term := runFn nil p_
  let Cp1 : Term := concat Cp (cons (carc q2line) nil)
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hpIn : PrfH Γ (In Ain (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
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
  have hChainR : PrfH Γ (chainOk nil (concat p_ tl)) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ tl) (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_cons Cp q2line (cons mpline nil)) (PrfH_and_intro ?_ ?_)
    · exact prf_to_prfH (prf_lineOk_q2 Cp A' w') Γ
    · refine PrfH_iff_mpr (prf_chainOk_cons Cp1 mpline nil)
        (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
      refine PrfH_and_intro (prf_to_prfH (prf_lineWF_mp Bex Ain) Γ) ?_
      refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_mp Bex Ain)) Γ) ?_
      refine PrfH_iff_mpr (prf_allIn_cons Cp1 (implc Ain Bex) (cons Ain nil))
        (PrfH_and_intro ?_ ?_)
      · have hcarc : Prf (cons (implc Ain Bex) nil =eq cons (carc q2line) nil) :=
          prf_congr_cons_head (prf_eq_symm
            (prf_carc_cons (implc Ain Bex) (cons (numeralM 10) (cons A' (cons w' nil)))))
        exact prf_to_prfH
          (prf_In_mono (implc Ain Bex) (cons (carc q2line) nil) Cp
            (prf_eq_subst_in hcarc (prf_in_cons_head (implc Ain Bex) nil))) Γ
      · refine PrfH_iff_mpr (prf_allIn_cons Cp1 Ain nil)
          (PrfH_and_intro ?_ (prf_to_prfH (prf_allIn_nil _) Γ))
        exact PrfH.mp Γ _ _
          (prf_to_prfH (prf_In_mono_right_imp Ain (cons (carc q2line) nil) Cp) Γ) hpIn
  exact PrfH_and_intro hChainR hInB

/-! ### `<` desde el testigo, código rastreado (`pcc_lt_intro` sin clausura) -/

/-- **Reflexión de `<` con `a`, `b` ABIERTOS, en forma implicación**: de `Prov(⌜ ȧ + σK = ḃ ⌝)` sale
    `Prov(⌜ ȧ < ḃ ⌝)`, sin exigir `a`, `b` cerrados. Es `pcc_lt_intro` con el `∃`‑intro ABIERTO. -/
theorem pcc_lt_intro_open_imp (a b K : Term) :
    Prf (provFromCode (eqCodeFn (addcT (tcFn a) (succcT K)) (tcFn b))
      ⇒ provFromCode (ltCodeFn (tcFn a) (tcFn b))) := by
  refine prf_deduction ?_
  have hsub : PrfH [provFromCode (eqCodeFn (addcT (tcFn a) (succcT K)) (tcFn b))]
      (provFromCode (substfc zero K (exBodyc (tcFn a) (tcFn b)))) :=
    PrfH.mp _ _ _
      (prf_to_prfH (prf_provCode_congr (prf_eq_symm
        (prf_substfc_exBodyc (tcFn a) (tcFn b) K (substtc_inv_tcFn a) (substtc_inv_tcFn b)))) _)
      (prfH_hyp_self _)
  have hex : PrfH [provFromCode (eqCodeFn (addcT (tcFn a) (succcT K)) (tcFn b))]
      (provFromCode (exc (exBodyc (tcFn a) (tcFn b)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_exIntro_code_open (exBodyc (tcFn a) (tcFn b)) K) _) hsub
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_mp (pcc_mp_code_open (exc (exBodyc (tcFn a) (tcFn b)))
      (ltCodeFn (tcFn a) (tcFn b))) (pcc_ltBwd_computed a b)) _) hex

/-- **Reflexión de `<` con `a`, `b` ABIERTOS** (aplicación directa). -/
theorem pcc_lt_intro_open (a b K : Term)
    (h : Prf (provFromCode (eqCodeFn (addcT (tcFn a) (succcT K)) (tcFn b)))) :
    Prf (provFromCode (ltCodeFn (tcFn a) (tcFn b))) :=
  prf_mp (pcc_lt_intro_open_imp a b K) h

end ROBINSON_PlusPlus.Meta.Delta0ReflectPrf

export ROBINSON_PlusPlus.Meta.Delta0ReflectPrf (
  liftTerm_exc_open pcc_exIntro_code_open pcc_lt_intro_open_imp pcc_lt_intro_open
)

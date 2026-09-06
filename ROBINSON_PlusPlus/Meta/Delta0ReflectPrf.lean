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
-- ADR-020: la guarda de `pcc_exIntro_code_open` va sobre el codigo LIFTEADO, y comprobar
-- que `liftTerm 0 (exBodyc ...)` es el nodo `eqc` esperado agota la pila por defecto.
set_option maxRecDepth 8000

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
theorem pcc_exIntro_code_open (Ac w : Term)
    (hwA : Prf (hasWitF (liftTerm 0 Ac))) (hwW : Prf (hasWit (liftTerm 0 w))) :
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
    · exact prf_to_prfH (prf_lineOk_q2 Cp A' w' hwA hwW) Γ
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

/-- **GEN a nivel de código** (reflexión de la regla GEN, ahora que la línea 17 es sólida): para
    `body` **arbitrario** (abierto), `Prf (provFromCode body ⇒ provFromCode (forallc body))`.

    La cadena de `provFromCode body` ya tiene `body` en `checked`; se le apendiza **una línea GEN**
    `⟨forallc ↑body, 17, ↑body⟩`, cuya premisa `↑body` está en `checked` y cuya `lineWF` vale por
    reflexividad (`concl =eq forallc ↑body`, tras el fix de solidez). Arrastra el lift como
    `pcc_exIntro_code_open`. -/
theorem pcc_gen_code (body : Term) :
    Prf (provFromCode body ⇒ provFromCode (forallc body)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula_provFromCode_open 0 (forallc body), liftTerm_forallc_open body 0]
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  refine PrfH_ex_intro
    (concat (.var 0)
      (cons (cons (forallc (liftTerm 0 body))
              (cons (numeralM 17) (cons (liftTerm 0 body) nil))) nil)) ?_
  simp only [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  let B' : Term := liftTerm 0 body
  let genline : Term := cons (forallc B') (cons (numeralM 17) (cons B' nil))
  let p_ : Term := (.var 0)
  let Γ : List Formula := [land (chainOk nil p_) (In B' (runFn nil p_))]
  let Cp : Term := runFn nil p_
  let tl : Term := cons genline nil
  have hpChain : PrfH Γ (chainOk nil p_) :=
    PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _))
  have hpIn : PrfH Γ (In B' (runFn nil p_)) :=
    PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))
  have hmp : Prf (runFn Cp tl =eq concat Cp (cons (forallc B') nil)) :=
    prf_eq_trans (prf_runFn_cons Cp genline nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_congr_concat_left (prf_congr_cons_head
          (prf_carc_cons (forallc B') (cons (numeralM 17) (cons B' nil))))))
  have hRunR : Prf (runFn nil (concat p_ tl) =eq concat Cp (cons (forallc B') nil)) :=
    prf_eq_trans (prf_runFn_concat nil p_ tl) hmp
  have hInB : PrfH Γ (In (forallc B') (runFn nil (concat p_ tl))) :=
    prf_to_prfH (prf_eq_subst_in (prf_eq_symm hRunR)
      (prf_In_mono (forallc B') (cons (forallc B') nil) Cp
        (prf_in_cons_head (forallc B') nil))) Γ
  have hChainR : PrfH Γ (chainOk nil (concat p_ tl)) := by
    refine PrfH_iff_mpr (prf_chainOk_concat nil p_ tl) (PrfH_and_intro hpChain ?_)
    refine PrfH_iff_mpr (prf_chainOk_cons Cp genline nil)
      (PrfH_and_intro ?_ (prf_to_prfH (prf_chainOk_nil _) Γ))
    refine PrfH_and_intro
      (prf_to_prfH (prf_iff_mpr (prf_lineWF_gen (forallc B') B') (prf_refl _)) Γ) ?_
    refine PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_premsOf_gen (forallc B') B')) Γ) ?_
    refine PrfH_iff_mpr (prf_allIn_cons Cp B' nil)
      (PrfH_and_intro hpIn (prf_to_prfH (prf_allIn_nil _) Γ))
  exact PrfH_and_intro hChainR hInB

/-! ### `<` desde el testigo, código rastreado (`pcc_lt_intro` sin clausura) -/

/-- **Reflexión de `<` con `a`, `b` ABIERTOS, en forma implicación**: de `Prov(⌜ ȧ + σK = ḃ ⌝)` sale
    `Prov(⌜ ȧ < ḃ ⌝)`, sin exigir `a`, `b` cerrados. Es `pcc_lt_intro` con el `∃`‑intro ABIERTO. -/
theorem pcc_lt_intro_open_imp (a b K : Term) (hwK : Prf (hasWit (liftTerm 0 K))) :
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
    PrfH.mp _ _ _ (prf_to_prfH (pcc_exIntro_code_open (exBodyc (tcFn a) (tcFn b)) K
      (prf_hasWitF_eq2 (addcT (tcFn (liftTerm 0 a)) (succcT (varc (numeral 0))))
        (tcFn (liftTerm 0 b))
        (prf_hasWit_addcT (prf_hasWit_tcFn (liftTerm 0 a))
          (prf_hasWit_succcT (prf_hasWit_varc (numeral 0))))
        (prf_hasWit_tcFn (liftTerm 0 b)))
      hwK) _) hsub
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_mp (pcc_mp_code_open (exc (exBodyc (tcFn a) (tcFn b)))
      (ltCodeFn (tcFn a) (tcFn b))) (pcc_ltBwd_computed a b)) _) hex

/-- **Reflexión de `<` con `a`, `b` ABIERTOS** (aplicación directa). -/
theorem pcc_lt_intro_open (a b K : Term)
    (h : Prf (provFromCode (eqCodeFn (addcT (tcFn a) (succcT K)) (tcFn b))))
    (hwK : Prf (hasWit (liftTerm 0 K))) :
    Prf (provFromCode (ltCodeFn (tcFn a) (tcFn b))) :=
  prf_mp (pcc_lt_intro_open_imp a b K hwK) h

/-- `liftTerm` atraviesa `ltCodeFn` con argumentos `tcFn`. -/
theorem liftTerm_ltCodeFn_tcFn (s t : Term) (c : Nat) :
    liftTerm c (ltCodeFn (tcFn s) (tcFn t))
      = ltCodeFn (tcFn (liftTerm c s)) (tcFn (liftTerm c t)) := by
  simp only [ltCodeFn, atom2CodeFn, tcFn, cons, nil, zero, liftTerm, liftTerms,
    liftTerm_numeral, liftTerm_strCode]

/-! ### REFLEXIÓN DEL ÁTOMO `<` DESDE HIPÓTESIS -/

/-- **REFLEXIÓN DEL ÁTOMO `<` desde su hipótesis** (completitud‑Δ₀ provable del átomo `<`):
    `⊢ (s < t) ⇒ provFromCode (ltCodeFn (tcFn s) (tcFn t))`, para `s`, `t` **arbitrarios**.

    `ax13` da un testigo `k` con `s + σk = t` (`∃`‑elim de la hipótesis); `pcc_eval_add` evalúa el
    sumatorio simbólico `ṡ + σ(k̇)` al numeral del valor `(s+σk)˙`, que la hipótesis identifica con
    `ṫ` (`prf_congr_tcFn`); `pcc_lt_intro_open` cierra. **Ésta es la base atómica de la
    completitud‑Δ₀ provable para el orden.** -/
theorem pcc_lt_tracked (s t : Term) :
    Prf ((lt s t) ⇒ provFromCode (ltCodeFn (tcFn s) (tcFn t))) := by
  refine prf_deduction ?_
  have hiff : PrfH [lt s t]
      (Formula.ex (Formula.eq (add (liftTerm 0 s) (succ (.var 0))) (liftTerm 0 t))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_lt_iff s t)) _) (prfH_hyp_self _)
  refine PrfH_ex_elim hiff ?_
  rw [liftFormula_provFromCode_open, liftTerm_ltCodeFn_tcFn]
  -- ctx: [add ↑s (σ#0) = ↑t, ↑(lt s t)] ; objetivo: provFromCode (ltCodeFn ⌜↑s⌝ ⌜↑t⌝)
  let s' : Term := liftTerm 0 s
  let t' : Term := liftTerm 0 t
  let Γ : List Formula :=
    [Formula.eq (add s' (succ (.var 0))) t', liftFormula 0 (lt s t)]
  -- `pcc_eval_add s' (σ#0)` transportado por `(σ#0)˙ = σ(#0˙)`
  have heval : Prf (provFromCode (eqCodeFn (addcT (tcFn s') (succcT (tcFn (.var 0))))
      (tcFn (add s' (succ (.var 0)))))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_addcT (prf_refl _) (prf_tc_succ' (.var 0))) (prf_refl _)))
      (pcc_eval_add s' (succ (.var 0)))
  -- bajo Γ: `(s'+σ#0)˙ = ṫ'`
  have hcong : PrfH Γ (tcFn (add s' (succ (.var 0))) =eq tcFn t') :=
    PrfH_congr_tcFn (PrfH.hyp _ _ (List.Mem.head _))
  have hcodeq : PrfH Γ
      (eqCodeFn (addcT (tcFn s') (succcT (tcFn (.var 0)))) (tcFn (add s' (succ (.var 0))))
        =eq eqCodeFn (addcT (tcFn s') (succcT (tcFn (.var 0)))) (tcFn t')) :=
    PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) hcong
  -- transporta `heval` a `Prov(⌜ ṡ' + σ(#0˙) = ṫ' ⌝)` (Leibniz sobre `provFormulaC'`)
  have h2 : PrfH Γ (provFromCode (eqCodeFn (addcT (tcFn s') (succcT (tcFn (.var 0)))) (tcFn t'))) :=
    PrfH.mp _ _ _
      (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.leibniz provFormulaC' _ _)) hcodeq)
      (prf_to_prfH heval _)
  exact PrfH.mp _ _ _
    (prf_to_prfH (pcc_lt_intro_open_imp s' t' (tcFn (.var 0))
      (prf_hasWit_tcFn (liftTerm 0 (.var 0)))) _) h2

/-! ### Casos COMPOSICIONALES `∧` / `∨`

La reflexión de una fórmula Δ₀ se compone de las reflexiones de sus partes. Con `Ac`/`Bc` los códigos
(rastreados) de `φ`/`ψ`, y `hφ : φ ⇒ provFromCode Ac`, `hψ : ψ ⇒ provFromCode Bc`:

* `∧`: `∧`‑elim object de la hipótesis + `pcc_and_intro_code` (§30);
* `∨`: `∨`‑elim object (`PrfH_or_elim`) + `pcc_or_introL_code`/`pcc_or_introR_code` (§30).

Ambos combinadores son **agnósticos del código** (`Ac`, `Bc` arbitrarios) y sólo suben las
reflexiones de las partes. -/

open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.ChainPrf

/-- **Reflexión composicional de `∧`**: de las reflexiones de `φ` y `ψ` (a códigos `Ac`, `Bc`) sale
    la de `φ ∧ ψ` (al código `andc Ac Bc`). -/
theorem pcc_reflect_and (φ ψ : Formula) (Ac Bc : Term)
    (hφ : Prf (φ ⇒ provFromCode Ac)) (hψ : Prf (ψ ⇒ provFromCode Bc)) :
    Prf ((φ ∧ ψ) ⇒ provFromCode (andc Ac Bc)) := by
  refine prf_deduction ?_
  have ha : PrfH [φ ∧ ψ] (provFromCode Ac) :=
    PrfH.mp _ _ _ (prf_to_prfH hφ _) (PrfH_and_elim_left (prfH_hyp_self _))
  have hb : PrfH [φ ∧ ψ] (provFromCode Bc) :=
    PrfH.mp _ _ _ (prf_to_prfH hψ _) (PrfH_and_elim_right (prfH_hyp_self _))
  -- de `pcc_c1_code` (⌜Ac ⇒ Bc ⇒ Ac∧Bc⌝), dos pasos de MP interno
  have step1 : Prf (provFromCode Ac ⇒ provFromCode (implc Bc (andc Ac Bc))) :=
    prf_mp (pcc_mp_code_open Ac (implc Bc (andc Ac Bc))) (pcc_c1_code Ac Bc)
  have hImplBc : PrfH [φ ∧ ψ] (provFromCode (implc Bc (andc Ac Bc))) :=
    PrfH.mp _ _ _ (prf_to_prfH step1 _) ha
  have hBcToAnd : PrfH [φ ∧ ψ] (provFromCode Bc ⇒ provFromCode (andc Ac Bc)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_mp_code_open Bc (andc Ac Bc)) _) hImplBc
  exact PrfH.mp _ _ _ hBcToAnd hb

/-- **Reflexión composicional de `∨`**: de las reflexiones de `φ` y `ψ` sale la de `φ ∨ ψ` (al código
    `orc Ac Bc`), por `∨`‑elim object. -/
theorem pcc_reflect_or (φ ψ : Formula) (Ac Bc : Term)
    (hφ : Prf (φ ⇒ provFromCode Ac)) (hψ : Prf (ψ ⇒ provFromCode Bc)) :
    Prf ((lor φ ψ) ⇒ provFromCode (orc Ac Bc)) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prfH_hyp_self (lor φ ψ)) ?_ ?_
  · -- caso φ:  Prov Ac  →  Prov(orc Ac Bc)   [J1]
    have ha : PrfH [φ, lor φ ψ] (provFromCode Ac) :=
      PrfH.mp _ _ _ (prf_to_prfH hφ _) (PrfH.hyp _ _ (List.Mem.head _))
    exact PrfH.mp _ _ _
      (prf_to_prfH (prf_mp (pcc_mp_code_open Ac (orc Ac Bc)) (pcc_j1_code Ac Bc)) _) ha
  · -- caso ψ:  Prov Bc  →  Prov(orc Ac Bc)   [J2]
    have hb : PrfH [ψ, lor φ ψ] (provFromCode Bc) :=
      PrfH.mp _ _ _ (prf_to_prfH hψ _) (PrfH.hyp _ _ (List.Mem.head _))
    exact PrfH.mp _ _ _
      (prf_to_prfH (prf_mp (pcc_mp_code_open Bc (orc Ac Bc)) (pcc_j2_code Ac Bc)) _) hb

end ROBINSON_PlusPlus.Meta.Delta0ReflectPrf

export ROBINSON_PlusPlus.Meta.Delta0ReflectPrf (
  liftTerm_exc_open pcc_exIntro_code_open pcc_gen_code pcc_lt_intro_open_imp pcc_lt_intro_open
  liftTerm_ltCodeFn_tcFn pcc_lt_tracked
  pcc_reflect_and pcc_reflect_or
)

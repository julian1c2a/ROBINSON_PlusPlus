/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.LineWFDerives

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.ProofChain

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.DerivCond

/-!
## META — NIVEL D real: condiciones de derivabilidad sobre `provCodeC'` (D2, …)

Con el verificador estructural `runFn`/`chainOk` (`Meta/ProofChain.lean`) ya se puede
razonar sobre **testigos de prueba arbitrarios**, lo que permite demostrar las
condiciones de Hilbert-Bernays-Löb **internamente** (`axioms ⊢ …`), no postuladas.

* **D2** (este archivo): `⊢ Prov'(⌜A⇒B⌝) ⇒ (Prov'(⌜A⌝) ⇒ Prov'(⌜B⌝))`. Construcción:
  de testigos `p` (de `A⇒B`) y `q` (de `A`) se ensambla `r = p ++ q ++ [mp]`, una
  cadena válida (`chainOk`) cuya última conclusión es `⌜B⌝`. Usa toda el álgebra de
  cadenas: `runFn_concat`/`runFn_weaken`, `chainOk_concat`/`chainOk_mono`,
  `In_mono`/`In_mono_right`, y la validez de la línea `mp` (`lineWF_mp`/`premsOf_mp`).
-/

/-- **D2 (distribución de la demostrabilidad)**: `⊢ Prov'(⌜A⇒B⌝) ⇒ (Prov'(⌜A⌝) ⇒ Prov'(⌜B⌝))`.
    Internalizada (no postulada): de pruebas de `A⇒B` y `A` se concatena una prueba de `B`
    mediante una línea `mp`. -/
theorem d2 (A B : Formula) :
    axioms ⊢ (provCodeC' (Formula.impl A B) ⇒ (provCodeC' A ⇒ provCodeC' B)) := by
  apply Minimal.Axioms.imp_intro; intro hAB
  apply Minimal.Axioms.imp_intro; intro hA
  -- código de A⇒B = implc ⌜A⌝ ⌜B⌝ (formCode composicional)
  have hcAB : formCode (Formula.impl A B) = implc (formCode A) (formCode B) := rfl
  refine provCodeC'_elim hAB (fun p hpChain hpInRaw => ?_)
  refine provCodeC'_elim hA (fun q hqChain hqIn => ?_)
  -- hpIn : In (implc ⌜A⌝ ⌜B⌝) (runFn nil p)
  have hpIn : axioms ⊢ In (implc (formCode A) (formCode B)) (runFn nil p) := by
    rwa [hcAB] at hpInRaw
  -- abreviaturas
  let cA := formCode A
  let cB := formCode B
  -- línea mp y cadena combinada
  -- mpline = cons ⌜B⌝ (cons 16 (cons ⌜A⌝ nil));  r = p ++ (q ++ [mpline])
  -- conclusión: In ⌜B⌝ (runFn nil r) y chainOk nil r
  have hCpq_mp : axioms ⊢
      (runFn (runFn (runFn nil p) q) (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil)
        =eq concat (runFn (runFn nil p) q) (cons cB nil)) := by
    refine FOL.derive_eq_trans
      (runFn_cons (runFn (runFn nil p) q) (cons cB (cons (numeralM 16) (cons cA nil))) nil) ?_
    refine FOL.derive_eq_trans
      (runFn_nil (concat (runFn (runFn nil p) q)
        (cons (carc (cons cB (cons (numeralM 16) (cons cA nil)))) nil))) ?_
    exact Full.eq_congr_concat_left
      (congr_cons_head (carc_cons cB (cons (numeralM 16) (cons cA nil))))
  -- runFn nil r =eq concat Cpq (cons cB nil)
  have hRunR : axioms ⊢
      (runFn nil (concat p (concat q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil)))
        =eq concat (runFn (runFn nil p) q) (cons cB nil)) := by
    refine FOL.derive_eq_trans
      (runFn_concat nil p (concat q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil))) ?_
    refine FOL.derive_eq_trans
      (runFn_concat (runFn nil p) q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil)) ?_
    exact hCpq_mp
  -- In ⌜B⌝ (runFn nil r)
  have hInB : axioms ⊢
      In cB (runFn nil (concat p (concat q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil)))) :=
    Full.eq_subst_in (FOL.derive_eq_symm hRunR)
      (In_mono cB (cons cB nil) (runFn (runFn nil p) q) (in_cons_head cB nil))
  -- chainOk nil r
  have hChainR : axioms ⊢
      chainOk nil (concat p (concat q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil))) := by
    refine iff_mpr (chainOk_concat nil p
      (concat q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil))) ?_
    refine Minimal.Axioms.and_intro hpChain ?_
    refine iff_mpr (chainOk_concat (runFn nil p) q
      (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil)) ?_
    refine Minimal.Axioms.and_intro ?_ ?_
    · -- chainOk (runFn nil p) q  desde  chainOk nil q
      exact chainOk_subst1 (concat_nil_right (runFn nil p)) (chainOk_mono (runFn nil p) nil q hqChain)
    · -- chainOk (runFn (runFn nil p) q) [mpline]
      refine iff_mpr (chainOk_cons (runFn (runFn nil p) q)
        (cons cB (cons (numeralM 16) (cons cA nil))) nil) ?_
      refine Minimal.Axioms.and_intro ?_ (chainOk_nil _)
      -- lineOk Cpq mpline = lineWF mpline ∧ allIn Cpq (premsOf mpline)
      refine Minimal.Axioms.and_intro (lineWF_mp cB cA) ?_
      refine allIn_subst2 (FOL.derive_eq_symm (premsOf_mp cB cA)) ?_
      -- allIn Cpq [implc ⌜A⌝ ⌜B⌝, ⌜A⌝]
      refine iff_mpr (allIn_cons (runFn (runFn nil p) q) (implc cA cB) (cons cA nil)) ?_
      refine Minimal.Axioms.and_intro ?_ ?_
      · -- In (implc ⌜A⌝ ⌜B⌝) Cpq
        exact Full.eq_subst_in (FOL.derive_eq_symm (runFn_weaken (runFn nil p) q))
          (In_mono_right (implc cA cB) (runFn nil q) (runFn nil p) hpIn)
      · refine iff_mpr (allIn_cons (runFn (runFn nil p) q) cA nil) ?_
        refine Minimal.Axioms.and_intro ?_ (allIn_nil _)
        -- In ⌜A⌝ Cpq
        exact Full.eq_subst_in (FOL.derive_eq_symm (runFn_weaken (runFn nil p) q))
          (In_mono cA (runFn nil q) (runFn nil p) hqIn)
  -- ensamblaje: r es testigo de Prov'(⌜B⌝)
  exact provCodeC'_intro B
    (concat p (concat q (cons (cons cB (cons (numeralM 16) (cons cA nil))) nil)))
    hChainR hInB

end ROBINSON_PlusPlus.Meta.DerivCond

export ROBINSON_PlusPlus.Meta.DerivCond (d2)

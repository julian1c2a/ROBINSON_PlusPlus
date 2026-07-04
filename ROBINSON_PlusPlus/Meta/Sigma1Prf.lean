/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReflectionPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.ReflectionPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.Sigma1Prf

/-!
## META — NIVEL D real: Σ₁-completitud provable del verificador (núcleo duro de D3)

Hacia `hI`/`hC` (las hipótesis de `d3_prf_of_sigma1`). Σ₁-completitud provable:
`Prf (In x L ⇒ provCodeC'(In x L))` y `Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))`.

**Combinador clave `pcc_imp`**: cualquier **implicación object cerrada** `Prf (A ⇒ B)`
se eleva a una **implicación de demostrabilidad** `Prf (provCodeC' A ⇒ provCodeC' B)`,
vía **D2** (`d2_prf`) + **D1** (`repr_pos'_prf`). Es el "modus ponens interno" como
esquema, y la pieza de ensamblaje de toda la reflexión.

Con `pcc_imp` + las leyes object del verificador (`ax_L1`/`ax_L2`/`ax_chainOk_*`/…) se
construyen los **combinadores de reflexión** (`pcc_in_*`, `pcc_chainOk_*`). El cierre
inductivo final (`hI`/`hC` para testigo abstracto) necesita aún la inducción object
sobre el código con seguimiento aritmético (`substfc`/`tcFn`) — "la bestia" (Fase 5).
-/

/-! ### Demostrabilidad parametrizada por el código + transporte por igualdad de códigos

`provFromCode c` = "el código `c` (de una fórmula) es demostrable". Se relaciona con
`provCodeC'` por `provCodeC' φ = provFromCode (formCode φ)` (definicional). A diferencia
de `provCodeC'(In x #0)` (donde el código **absorbe** la variable object), aquí `c` es
un **slot-término genuino** del predicado, así que la demostrabilidad **respeta la
igualdad de códigos** vía Leibniz object (`prf_provCode_congr`). Este es el transporte
que parte la reflexión de igualdad. -/

/-- Demostrabilidad de un **código de fórmula** `c` (no de una fórmula meta). -/
def provFromCode (c : Term) : Formula := substFormula 0 c provFormulaC'

/-- `provCodeC' φ` es `provFromCode` del código de `φ` (definicional). -/
theorem provCodeC'_eq_provFromCode (φ : Formula) :
    provCodeC' φ = provFromCode (formCode φ) := rfl

/-- **Transporte de la demostrabilidad por igualdad de códigos** (Leibniz object):
    de `Prf (c₁ =eq c₂)` sale `Prf (provFromCode c₁ ⇒ provFromCode c₂)`. El código `c`
    aparece como término honesto, no absorbido — por eso Leibniz funciona aquí. -/
theorem prf_provCode_congr {c₁ c₂ : Term} (h : Prf (c₁ =eq c₂)) :
    Prf (provFromCode c₁ ⇒ provFromCode c₂) :=
  prf_mp (Prf.incl (Prf₀.leibniz provFormulaC' c₁ c₂)) h

/-- **Reflexión de igualdad REDUCIDA** al puente de doble-codificación: dada la implicación
    object `(x=eq y) ⇒ (formCode(x=eq x) =eq formCode(x=eq y))` (igualdad de los *códigos*
    de las fórmulas, que se reduce a `termCode x =eq termCode y` — el puente `termCode`/`tcFn`,
    la pieza irreducible), vale la **reflexión de igualdad** `(x=eq y) ⇒ provCodeC'(x=eq y)`.
    Transporte (`prf_provCode_congr`) de la demostrabilidad de la reflexividad `provCodeC'(x=eq x)`. -/
theorem pcc_eq_of_codeEq (x y : Term)
    (hcode : Prf ((x =eq y) ⇒ (formCode (Formula.eq x x) =eq formCode (Formula.eq x y)))) :
    Prf ((x =eq y) ⇒ provCodeC' (x =eq y)) := by
  refine prf_deduction ?_
  -- de la hipótesis `x=eq y`: igualdad de los códigos
  have hcodeEq : PrfH [x =eq y] (formCode (Formula.eq x x) =eq formCode (Formula.eq x y)) :=
    PrfH.mp _ _ _ (prf_to_prfH hcode _) (prfH_hyp_self _)
  -- `provCodeC'(x=eq x)` demostrable (reflexividad)
  have hrefl : PrfH [x =eq y] (provFromCode (formCode (Formula.eq x x))) :=
    prf_to_prfH (repr_pos'_prf (prf_refl x)) _
  -- transporta por el código vía Leibniz object (`provFromCode`)
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.leibniz provFormulaC' _ _)) hcodeEq) hrefl

/-! ### Combinador clave: elevar implicaciones object a implicaciones de demostrabilidad -/

/-- **MP interno como esquema** (`pcc_imp`): de una implicación object cerrada
    `Prf (A ⇒ B)` sale `Prf (provCodeC' A ⇒ provCodeC' B)`. Vía D2 + D1. -/
theorem pcc_imp {A B : Formula} (h : Prf (A ⇒ B)) :
    Prf (provCodeC' A ⇒ provCodeC' B) :=
  prf_mp (d2_prf A B) (repr_pos'_prf h)

/-- Versión bi-premisa: de `Prf (A ⇒ B ⇒ C)` sale `provCodeC' A ⇒ provCodeC' B ⇒ provCodeC' C`. -/
theorem pcc_imp2 {A B C : Formula} (h : Prf (A ⇒ (B ⇒ C))) :
    Prf (provCodeC' A ⇒ (provCodeC' B ⇒ provCodeC' C)) := by
  have h1 : Prf (provCodeC' A ⇒ provCodeC' (B ⇒ C)) := pcc_imp h
  exact prf_deduction (PrfH.mp _ _ _
    (prf_to_prfH (d2_prf B C) _)
    (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _)))

/-! ### Combinadores de reflexión de `In` (vía las leyes object `ax_L1`/`ax_L2`) -/

/-- Implicación object `In x t ⇒ In x (cons hd t)` (cola). -/
theorem prf_in_cons_tail_imp (hd x t : Term) : Prf (In x t ⇒ In x (cons hd t)) :=
  prf_deduction (PrfH_in_cons_tail hd (prfH_hyp_self (In x t)))

/-- Implicación object `(x =eq hd) ⇒ In x (cons hd t)` (cabeza). -/
theorem prf_in_cons_head_imp (hd x t : Term) : Prf ((x =eq hd) ⇒ In x (cons hd t)) := by
  refine prf_deduction ?_
  -- de `x =eq hd`: `cons x t =eq cons hd t`; sustituye en `In x (cons x t)` (cabeza)
  exact PrfH_eq_subst_in
    (PrfH_congr_cons_head (t := t) (prfH_hyp_self (x =eq hd)))
    (prf_to_prfH (prf_in_cons_head x t) _)

/-- **Reflexión de `In` — cabeza directa**: `provCodeC'(In x (cons x t))` (es instancia
    de axioma `ax_L2`, demostrable; `repr_pos'_prf`). -/
theorem pcc_in_head (x t : Term) : Prf (provCodeC' (In x (cons x t))) :=
  repr_pos'_prf (prf_in_cons_head x t)

/-- **Reflexión de `In` — cola** (combinador): `provCodeC'(In x t) ⇒ provCodeC'(In x (cons hd t))`. -/
theorem pcc_in_tail (hd x t : Term) :
    Prf (provCodeC' (In x t) ⇒ provCodeC' (In x (cons hd t))) :=
  pcc_imp (prf_in_cons_tail_imp hd x t)

/-- **Reflexión de `In` — cabeza por igualdad** (combinador):
    `provCodeC'(x =eq hd) ⇒ provCodeC'(In x (cons hd t))`. -/
theorem pcc_in_head_eq (hd x t : Term) :
    Prf (provCodeC' (x =eq hd) ⇒ provCodeC' (In x (cons hd t))) :=
  pcc_imp (prf_in_cons_head_imp hd x t)

/-- **Reflexión de `In` — base `nil`**: `In x nil ⇒ provCodeC'(In x nil)` (vacío: `In x nil`
    es falso, por explosión). -/
theorem pcc_in_nil (x : Term) : Prf (In x nil ⇒ provCodeC' (In x nil)) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq (provCodeC' (In x nil))))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil x) _) (prfH_hyp_self _))

/-! ### Combinadores de reflexión de `chainOk` / `allIn` (vía `ax_chainOk_*` / `ax_allIn_*`) -/

/-- **Reflexión de `chainOk` — base `nil`**: `provCodeC'(chainOk c nil)` (demostrable). -/
theorem pcc_chainOk_nil (c : Term) : Prf (provCodeC' (chainOk c nil)) :=
  repr_pos'_prf (prf_chainOk_nil c)

/-- Implicación object: `lineOk c line ⇒ chainOk (c ++ [carc line]) rest ⇒ chainOk c (cons line rest)`. -/
theorem prf_chainOk_cons_imp (c line rest : Term) :
    Prf (lineOk c line ⇒ (chainOk (concat c (cons (carc line) nil)) rest ⇒
      chainOk c (cons line rest))) := by
  refine prf_deduction (deduction_aux ?_
    (chainOk (concat c (cons (carc line) nil)) rest) [lineOk c line] rfl)
  exact PrfH_iff_mpr (prf_chainOk_cons c line rest)
    (PrfH_and_intro (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (PrfH.hyp _ _ (List.Mem.head _)))

/-- **Reflexión de `chainOk` — cons** (combinador): de la demostrabilidad de la cabeza
    (`lineOk`) y de la cola (`chainOk`) sale la del todo. -/
theorem pcc_chainOk_cons (c line rest : Term) :
    Prf (provCodeC' (lineOk c line) ⇒ (provCodeC' (chainOk (concat c (cons (carc line) nil)) rest) ⇒
      provCodeC' (chainOk c (cons line rest)))) :=
  pcc_imp2 (prf_chainOk_cons_imp c line rest)

/-- **Reflexión de `allIn` — base `nil`**: `provCodeC'(allIn c nil)` (demostrable). -/
theorem pcc_allIn_nil (c : Term) : Prf (provCodeC' (allIn c nil)) :=
  repr_pos'_prf (prf_allIn_nil c)

/-- Implicación object: `In x c ⇒ allIn c t ⇒ allIn c (cons x t)`. -/
theorem prf_allIn_cons_imp (c x t : Term) :
    Prf (In x c ⇒ (allIn c t ⇒ allIn c (cons x t))) := by
  refine prf_deduction (deduction_aux ?_ (allIn c t) [In x c] rfl)
  exact PrfH_iff_mpr (prf_allIn_cons c x t)
    (PrfH_and_intro (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (PrfH.hyp _ _ (List.Mem.head _)))

/-- **Reflexión de `allIn` — cons** (combinador). -/
theorem pcc_allIn_cons (c x t : Term) :
    Prf (provCodeC' (In x c) ⇒ (provCodeC' (allIn c t) ⇒ provCodeC' (allIn c (cons x t)))) :=
  pcc_imp2 (prf_allIn_cons_imp c x t)

end ROBINSON_PlusPlus.Meta.Sigma1Prf

export ROBINSON_PlusPlus.Meta.Sigma1Prf (
  provFromCode provCodeC'_eq_provFromCode prf_provCode_congr pcc_eq_of_codeEq
  pcc_imp pcc_imp2 prf_in_cons_tail_imp prf_in_cons_head_imp
  pcc_in_head pcc_in_tail pcc_in_head_eq pcc_in_nil
  pcc_chainOk_nil prf_chainOk_cons_imp pcc_chainOk_cons
  pcc_allIn_nil prf_allIn_cons_imp pcc_allIn_cons
)

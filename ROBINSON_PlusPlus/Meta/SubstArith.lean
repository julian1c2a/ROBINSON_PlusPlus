/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.CodeArith

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Deduction

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`: los lemas de cómputo (`substTerm_arith`, `substFormula_arith`,
> `liftTerm_arith`, `liftFormula_arith`), sus ecuaciones recursivas sobre `⊢` (`substtc_var_eq`,
> `substfc_forall`, `liftfc_ex`…), las congruencias (`congr_cons_head`, `congr_bin1`,
> `congr_substfc_arg2`…) y `pred_numeral` **ya no existen**, como tampoco `ax` ni `spec`; lo que se lea
> sobre ellos es REGISTRO, no estado. Lo que queda en el módulo —las cancelaciones de lift triple y
> cuádruple, Lean puro— no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.SubstArith

/-!
## META — NIVEL D (real): aritmetización de la sustitución  (Fase 2, sub-paso 2.2)

Quedan sólo las **cancelaciones de lift triple y cuádruple** (`substTerm_liftLiftLift`,
`substTerm_liftLiftLiftLift` y sus versiones de lista), Lean puro: los portes a `Prf` las usan
para instanciar los axiomas `forall_4`/`forall_5` (`Meta/ArithPrf.lean`, `Meta/ReprPrf.lean`…).

🗑️ **2026‑10‑02 (ADR‑115) — registro.** El módulo internalizaba la sustitución De Bruijn
`substTerm`/`substFormula` como **funciones object** sobre los códigos y demostraba sobre `⊢`,
por **inducción meta**, el **lema de cómputo** `⊢ substtc(⌜v⌝,⌜s⌝,⌜t⌝) = ⌜substTerm v s t⌝`, a
nivel término y a nivel fórmula, con `liftTerm`/`liftFormula` aritmetizados, las ecuaciones
recursivas instanciadas desde `Minimal.axioms` (vía `ax` + `spec`) y las congruencias de `cons`.
Todo eso quedó retirado con la capa `⊢`. Su versión `Prf` está en `Meta/ArithPrf.lean`: los lemas
de cómputo `prf_substTerm_arith`/`prf_substFormula_arith` y `prf_liftTerm_arith`/
`prf_liftFormula_arith`, y las ecuaciones `prf_substtc_var_eq` … `prf_liftfc_ex`; las congruencias
de `cons` son `prf_congr_cons_head`/`_tail` (`Meta/ReprPrf.lean`). Las ecuaciones object
(`ax_substtc_var_eq` … `ax_liftfc_ex`) siguen en `Minimal/Axioms.lean`.
-/

/-! ### Cancelaciones de lift triple y cuádruple (Lean puro) -/

/- Cancelación de **triple lift** (espejo de `FOL.substTerm_liftLift`, un nivel
   más): sustituir en `c+2` un término triplemente desplazado en `c` devuelve el
   doblemente desplazado. Necesaria para instanciar axiomas `forall_4` (la
   primera variable atraviesa 3 binders ⟹ triple lift). -/
mutual
theorem substTerm_liftLiftLift (t : Term) (c : Nat) (s : Term) :
    substTerm (c + 2) s (liftTerm c (liftTerm c (liftTerm c t))) = liftTerm c (liftTerm c t) := by
  cases t with
  | var n =>
      by_cases h1 : n < c
      · simp [liftTerm, substTerm, h1, show ¬ n = c + 2 from by omega, show ¬ n > c + 2 from by omega]
      · have h2 : ¬ n + 1 < c := by omega
        have h3 : ¬ n + 1 + 1 < c := by omega
        have hgt : n + 1 + 1 + 1 > c + 2 := by omega
        simp [liftTerm, substTerm, h1, h2, h3, hgt]
        omega
  | func f ts =>
      simp only [liftTerm, substTerm]; congr 1; exact substTerms_liftLiftLift ts c s
theorem substTerms_liftLiftLift (ts : List Term) (c : Nat) (s : Term) :
    substTerms (c + 2) s (liftTerms c (liftTerms c (liftTerms c ts))) = liftTerms c (liftTerms c ts) := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨substTerm_liftLiftLift t c s, substTerms_liftLiftLift ts' c s⟩
end

/- Cancelación de **cuádruple lift** (para instanciar axiomas `forall_5`: la
   primera variable atraviesa 4 binders). -/
mutual
theorem substTerm_liftLiftLiftLift (t : Term) (c : Nat) (s : Term) :
    substTerm (c + 3) s (liftTerm c (liftTerm c (liftTerm c (liftTerm c t))))
      = liftTerm c (liftTerm c (liftTerm c t)) := by
  cases t with
  | var n =>
      by_cases h1 : n < c
      · simp [liftTerm, substTerm, h1, show ¬ n = c + 3 from by omega, show ¬ n > c + 3 from by omega]
      · have h2 : ¬ n + 1 < c := by omega
        have h3 : ¬ n + 1 + 1 < c := by omega
        have h4 : ¬ n + 1 + 1 + 1 < c := by omega
        have hgt : n + 1 + 1 + 1 + 1 > c + 3 := by omega
        simp [liftTerm, substTerm, h1, h2, h3, h4, hgt]
        omega
  | func f ts =>
      simp only [liftTerm, substTerm]; congr 1; exact substTerms_liftLiftLiftLift ts c s
theorem substTerms_liftLiftLiftLift (ts : List Term) (c : Nat) (s : Term) :
    substTerms (c + 3) s (liftTerms c (liftTerms c (liftTerms c (liftTerms c ts))))
      = liftTerms c (liftTerms c (liftTerms c ts)) := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨substTerm_liftLiftLiftLift t c s, substTerms_liftLiftLiftLift ts' c s⟩
end

-- (Aquí vivían, sobre `⊢`, las ecuaciones recursivas, los lemas de cómputo de `substTerm`,
-- `liftTerm`, `substFormula` y `liftFormula`, y las congruencias; retirados con ADR‑115.)

end ROBINSON_PlusPlus.Meta.SubstArith



/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`ax_induction`, `prim_to_axioms`, `ax_mod2_alternation`, `ax_list_induction`…) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — INDUCCIÓN GENERAL (object-level, lift-aware)

🗑️ **2026‑10‑02 (ADR‑115) — registro.** `Full` añadía sobre `Minimal` el **esquema de inducción
general** como axioma sobre `⊢` (`ax_induction`), y derivaba los axiomas algebraicos de `Minimal` por
derivación sobre `⊢` —`spec`, `mp`, `gen`, `imp_intro`—. Todo eso quedó retirado con la capa `⊢`.
Hoy la inducción de la cadena de Gödel es el constructor `Prf.ind`, que usa la `inductionFormula` de
abajo; de este módulo quedan esa fórmula, `primAxioms`, las longitudes del censo y los lemas de
sustitución.

**Codificación lift-aware**: `φ(σn)` se codifica como
`substFormula 0 (σ#0) (liftFormula 1 φ)`, que preserva las variables-parámetro
de `φ` (la versión ingenua `substFormula 0 (σ#0) φ` las decrementaba, rompiendo
la inducción multivariable). El lema de composición `substTerm_subst_succ_lift`
+ `step_eq_reduce` reducen el paso a la forma `φ(n) ⇒ φ(σn)` con sustituciones
únicas, manejables como en `Minimal`.
-/

/-! ### §0bis · ⭐ `primAxioms` — LOS 23 PRIMITIVOS ([ADR‑023](../../DECISIONS.md), 2026‑09‑10h)

🗑️ **2026‑10‑02 (ADR‑115):** lo que sigue describe un certificado sobre `⊢` que quedó retirado —los
`*_thm_prim`, `mod2_of_even`, `concat_assoc`/`in_concat`—. Hoy **no hay** certificado de que los 10
derivables se deriven de los primitivos: `primAxioms` queda como dato, sin consumidor.

El censo de `coreAxioms` (`doc/REFERENCE-Full.md` §3.14.1) lo partía en **23 primitivos** y
**11 derivables**, y los 11 estaban demostrados en `Full`. Pero se enunciaban **`axioms ⊢ axN`** con
`axN ∈ axioms` ⇒ **trivialmente ciertos por `ax`**: el tipo **no certifica** la redundancia.

`primAxioms` es la lista que sí la certifica. ⚠️ **No cambia la teoría**: `axioms` queda intacta y
`primAxioms ⊆ axioms`, así que la frontera de `axiomsCodeT`/`provCodeC'` —y con ella la sentencia
`G`— **no se mueve** (ADR‑015). Lo único que cambia es **qué se afirma** de cada derivación.

⭐ **El debilitamiento es GRATIS**: `Derives.weakening` es un **constructor** de `Derives` en
`FOL/FOL.lean`, no un lema por probar. ⇒ de `primAxioms ⊢ f` se recupera `axioms ⊢ f` en una línea
(`prim_to_axioms`), y **ninguna firma aguas abajo cambia**. -/

/-- Los **24** axiomas **PRIMITIVOS / DEFINITORIOS** de `coreAxioms`: los que **fijan el
    significado de un símbolo** (Peano, las ecuaciones de `+`, `·`, `<`, `√`, `mod2`/`div2`,
    `pred`, listas, `^`, `prod_pairs` y la resta truncada). Ningún esquema de inducción los deriva
    — sin ellos el símbolo no significa nada.

    Los **10 restantes** de `coreAxioms` (ax6, ax7, ax10, ax11, ax12, ax18, ax19, ax24, ax_C3,
    ax_L3) **deben** ser teoremas en `Full`, y lo eran sobre `⊢` hasta el 2026‑10‑02: esos teoremas
    quedaron retirados con esa capa (ADR‑115) y hoy no hay certificado. -/
def primAxioms : List Formula :=
  [ ax2_peano_succ_neq_zero, ax3_peano_succ_inj,
    ax4_add_zero, ax5_add_succ, ax8_mul_zero, ax9_mul_succ,
    ax13_lt_def, ax14_sqrt_le, ax15_lt_succ_sqrt,
    ax16_mod2_succ, ax17_div_mod_eq, ax21_mod2_range, ax25_pred_zero, ax26_pred_succ,
    ax_L0_cons_def, ax_L1_in_nil, ax_L2_in_cons,
    ax_C1_concat_nil, ax_C2_concat_cons, ax29_sub_witness,
    ax_pow_zero, ax_pow_succ, ax_prodp_nil, ax_prodp_cons ]

/-! #### Las cifras del banner, **comprobadas por el kernel** (auditoría 2026‑09‑11, F‑6)

⚠️ «**141 axiomas objeto** = 34 core + 107 coding» aparece en **siete banners** y **ningún control
lo comprobaba**: `check-doc-sync` `[A]` mira jobs, módulos, `axiom` de Lean y `sorry`, no esto. Era
cierto **por suerte**, no por control. Aquí deja de serlo: si alguna lista cambia, **el build rompe**.
✏️ Desde ADR‑117 son **142** = 141 de la base (`axiomsBase` = 34 + 107) y el ancla diagonal. -/

set_option maxRecDepth 8000 in
theorem axioms_len : axioms.length = 142 := rfl
set_option maxRecDepth 8000 in
theorem axiomsBase_len : axiomsBase.length = 141 := rfl
set_option maxRecDepth 4000 in
theorem coreAxioms_len : coreAxioms.length = 34 := rfl
set_option maxRecDepth 8000 in
theorem codingAxioms_len : codingAxioms.length = 107 := rfl

/-- El censo, comprobado por el kernel: **24 + 10 = 34 = `coreAxioms`**.

    ⚠️ **Eran 23 + 11 hasta el 2026‑09‑10h**, y la corrección la forzó una medición: `ax21` (el rango
    de `mod2`) **no es derivable de los primitivos**. Su «derivación» en `Full/Mod2.lean` usaba
    `ax_mod2_alternation`, y **ése** se deriva de `ax21` ⇒ era **circular en contenido**. `ax21`
    **caracteriza `mod2`** junto a `ax16`/`ax17` (sin él, `ax16 + ax17` admiten `mod2 2̄ = 2̄`), luego
    es **primitivo**; el teorema es la alternancia. Ver [ADR‑023](../../DECISIONS.md). -/
theorem primAxioms_len : primAxioms.length = 24 := rfl

/-- Y son **de verdad** axiomas de la teoría. -/
theorem primAxioms_subset : ∀ f ∈ primAxioms, f ∈ axioms := by
  intro f hf
  simp only [primAxioms, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> simp [axioms]


/-! ### Lema de composición de sustitución (De Bruijn, offset 0) -/

mutual
theorem substTerm_subst_succ_lift (m t : Term) :
    substTerm 0 m (substTerm 0 (succ (.var 0)) (liftTerm 1 t)) = substTerm 0 (succ m) t := by
  cases t with
  | var j =>
    by_cases hj : j = 0
    · subst hj; simp [liftTerm, substTerm, substTerms, succ]
    · have h1 : ¬ j < 1 := by omega
      have h2 : ¬ (j + 1 = 0) := by omega
      have h3 : j + 1 > 0 := by omega
      have h4 : j > 0 := by omega
      simp [liftTerm, substTerm, substTerms, succ, hj, h1, h2, h3, h4]
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_subst_succ_lift m ts
theorem substTerms_subst_succ_lift (m : Term) (ts : List Term) :
    substTerms 0 m (substTerms 0 (succ (.var 0)) (liftTerms 1 ts)) = substTerms 0 (succ m) ts := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms]
    rw [substTerm_subst_succ_lift m t, substTerms_subst_succ_lift m ts']
end

/-! ### Composición generalizada (offset arbitrario) — para fórmulas con `∀`/`∃` -/

mutual
theorem substTerm_subst_succ_lift_gen (c : Nat) (m t : Term) :
    substTerm c m (substTerm c (succ (.var c)) (liftTerm (c + 1) t)) = substTerm c (succ m) t := by
  cases t with
  | var j =>
    rcases Nat.lt_trichotomy j c with hlt | heq | hgt
    · have e1 : j < c + 1 := by omega
      simp [liftTerm, substTerm, substTerms, succ, e1,
            show ¬ j = c from by omega, show ¬ j > c from by omega, hlt]
    · subst heq
      simp [liftTerm, substTerm, substTerms, succ, show j < j + 1 from by omega]
    · have e1 : ¬ j < c + 1 := by omega
      simp [liftTerm, substTerm, substTerms, succ, e1,
            show ¬ (j + 1 = c) from by omega, show j + 1 > c from by omega,
            show ¬ (j = c) from by omega, hgt]
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_subst_succ_lift_gen c m ts
theorem substTerms_subst_succ_lift_gen (c : Nat) (m : Term) (ts : List Term) :
    substTerms c m (substTerms c (succ (.var c)) (liftTerms (c + 1) ts)) = substTerms c (succ m) ts := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms]
    rw [substTerm_subst_succ_lift_gen c m t, substTerms_subst_succ_lift_gen c m ts']
end

/-- Composición generalizada para **toda** fórmula (cualquier offset). -/
theorem substFormula_succ_lift_gen (c : Nat) (m : Term) (φ : Formula) :
    substFormula c m (substFormula c (succ (.var c)) (liftFormula (c + 1) φ))
      = substFormula c (succ m) φ := by
  induction φ generalizing c m with
  | bottom => rfl
  | atom p ts =>
      simp only [liftFormula, substFormula]
      rw [substTerms_subst_succ_lift_gen]
  | eq t u =>
      simp only [liftFormula, substFormula]
      rw [substTerm_subst_succ_lift_gen, substTerm_subst_succ_lift_gen]
  | impl a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c m, ihb c m]
  | «forall» a iha =>
      exact congrArg Formula.forall (iha (c + 1) (liftTerm 0 m))
  | and a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c m, ihb c m]
  | or a b iha ihb =>
      simp only [liftFormula, substFormula]
      rw [iha c m, ihb c m]
  | ex a iha =>
      exact congrArg Formula.ex (iha (c + 1) (liftTerm 0 m))

/-- Composición a offset 0 (la usada por el paso de inducción). -/
theorem substFormula_succ_lift (n : Term) (φ : Formula) :
    substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)) = substFormula 0 (succ n) φ :=
  substFormula_succ_lift_gen 0 n φ

/-- Reduce el cuerpo del paso de inducción para **cualquier** `φ` a `φ(n) ⇒ φ(σn)`. -/
theorem step_reduce (n : Term) (φ : Formula) :
    substFormula 0 n (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))
      = Formula.impl (substFormula 0 n φ) (substFormula 0 (succ n) φ) := by
  show Formula.impl (substFormula 0 n φ)
        (substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))
     = Formula.impl (substFormula 0 n φ) (substFormula 0 (succ n) φ)
  rw [substFormula_succ_lift]

/-- Composición para fórmulas de igualdad (suficiente: las fórmulas de inducción
    algebraica son ecuaciones, sin cuantificadores internos). -/
theorem substFormula_eq_succ_lift (n t u : Term) :
    substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u)))
      = substFormula 0 (succ n) (Formula.eq t u) := by
  show Formula.eq (substTerm 0 n (substTerm 0 (succ (.var 0)) (liftTerm 1 t)))
                  (substTerm 0 n (substTerm 0 (succ (.var 0)) (liftTerm 1 u)))
     = Formula.eq (substTerm 0 (succ n) t) (substTerm 0 (succ n) u)
  rw [substTerm_subst_succ_lift, substTerm_subst_succ_lift]

/-- Reduce el cuerpo del paso de inducción (para `φ` ecuación) a `φ(n) ⇒ φ(σn)`. -/
theorem step_eq_reduce (n t u : Term) :
    substFormula 0 n (Formula.impl (Formula.eq t u)
        (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u))))
      = Formula.impl (substFormula 0 n (Formula.eq t u)) (substFormula 0 (succ n) (Formula.eq t u)) := by
  show Formula.impl (substFormula 0 n (Formula.eq t u))
        (substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u))))
     = Formula.impl (substFormula 0 n (Formula.eq t u)) (substFormula 0 (succ n) (Formula.eq t u))
  rw [substFormula_eq_succ_lift]

/-! ### Esquema de inducción general (axioma object-level) -/

/-- Fórmula de inducción para `φ` (variable libre `0`), lift-aware:
    `φ(0) ⇒ ((∀n. φ(n) ⇒ φ(σn)) ⇒ ∀n. φ(n))` con `φ(σn) = substFormula 0 (σ#0) (liftFormula 1 φ)`. -/
def inductionFormula (φ : Formula) : Formula :=
  Formula.impl (substFormula 0 zero φ)
    (Formula.impl
      (Formula.forall (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ))))
      (Formula.forall φ))

/-! #### 🗑️ REGISTRO — lo que había aquí hasta el 2026‑10‑02 (ADR‑115)

El `axiom` `ax_induction_prim` (`primAxioms ⊢ inductionFormula φ`, ADR‑023), `ax_induction` como
teorema por debilitamiento, y las derivaciones sobre `⊢` de los axiomas algebraicos y de orden
—`zero_add_prim`, `succ_add_prim`, `add_comm`/`add_assoc` (ax6/ax7), `zero_mul_prim`, `succ_mul_prim`,
`mul_comm` (ax10), `mul_distrib` (ax12), `mul_assoc` (ax11), `lt_irrefl` (ax18), `lt_trichotomy`
(ax19)— con sus versiones sobre `axioms`. Todo quedó retirado con la capa `⊢`.

✏️ **Una frase de aquí era FALSA** (L1‑2): defendía la forma genérica en `Γ` de `ax_list_induction`
(«puede ser genérico porque es una REGLA»). Esa genericidad, con `φ` función de Lean, es justo lo que
daba `[] ⊢ ⊥` (`sondeos/ListInductionAxiomRefutable.lean`). La lección de la nota sobre el `sorry`
en el `simp set` —que no mide: **fabrica** el verde— sigue valiendo (AI‑GUIDE §27.1). -/

end ROBINSON_PlusPlus.Full

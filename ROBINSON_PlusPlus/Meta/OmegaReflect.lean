/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DiagonalTwo
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.DiagonalNumeral

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.DiagonalNumeral
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.DiagonalTwo

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.OmegaReflect

/-!
## META — NIVEL D real (§41): descargar la REFLEXIÓN desde la ω‑CONSISTENCIA

`goedel_first_undecidable_real'` (`Meta/DiagonalTwo.lean`) demuestra `⊬G ∧ ⊬¬G` **sin ningún postulado
gödeliano**, pero con la reflexión (`Reflects φ := (axioms ⊢ provCodeC' φ) → Prf φ`) como **hipótesis
META explícita**. Aquí se **reduce** esa hipótesis a dos piezas honestas y separadas.

### Por qué la reflexión NO puede venir de dentro de la teoría (cerrado por Gödel)

Se necesitaría `axioms ⊢ ¬ provCodeC' φ` para `φ` indemostrable. Con **`φ = ⊥`** eso es **literalmente
`Con(T)`** — indemostrable por **Gödel II**. (Con `φ = G` tampoco: por el punto fijo,
`⊢ ¬provCodeC' G ⟺ ⊢ G`, y `⊬G`.) Y la ω‑regla `gen` cuantifica sobre **todo `Term`**, no sólo sobre
numerales, así que tampoco se aplica desde hechos sobre testigos concretos: para una variable libre
`x`, `⊢ ¬A(x)` **es** la universal — circular. Ésta es la razón por la que el postulado legacy
`provFormula_repr` era **falso en general** (lo enunciaba bajo consistencia simple).

### La descomposición honesta

1. **`OmegaConsistent`** — la **ω‑consistencia clásica**, como hipótesis META explícita. NO es
   `ConsistentOmega` (que es sólo `¬(axioms ⊢ ⊥)`): es estrictamente más fuerte, y es **exactamente**
   lo que Gödel necesita para `⊬¬G`. Es **creíble**: toda teoría **sólida** (correcta en ℕ) la cumple.
2. **`NegVerifier`** — la **Δ₀‑completitud NEGATIVA del verificador**: si `φ` no es demostrable, la
   teoría **refuta** que cualquier testigo **estándar** sea una prueba suya. Es el **espejo de
   `repr_pos'`** (D1) y **sí es alcanzable**: para un testigo CONCRETO el chequeo es finito y
   estructural, a diferencia de la Π₁ universal (que Gödel bloquea).

`reflects_of_omega` compone ambas. Con esto, la reflexión deja de ser un enunciado bloqueado por Gödel
y pasa a ser un enunciado **Δ₀ concreto** (`NegVerifier`) más una hipótesis clásica y visible.
-/

/-! ### El `∃` de `provCodeC'`, explícito -/

/-- Cuerpo del `∃` de `provFromCode c` (testigo `p = #0`; el código va lifteado bajo el binder). -/
def provBody (c : Term) : Formula :=
  land (chainOk nil (.var 0)) (In (liftTerm 0 c) (runFn nil (.var 0)))

/-- `provFromCode c` **es** un `∃` de `provBody c` (por `rfl`). -/
theorem provFromCode_eq_ex (c : Term) : provFromCode c = Formula.ex (provBody c) := rfl

/-- `provCodeC' φ` **es** un `∃` (por `rfl`). -/
theorem provCodeC'_eq_ex (φ : Formula) :
    provCodeC' φ = Formula.ex (provBody (formCode φ)) := rfl

/-- «El testigo `t` verifica `φ`»: el cuerpo del `∃` instanciado en `t`. -/
def Verifies (φ : Formula) (t : Term) : Formula :=
  land (chainOk nil t) (In (formCode φ) (runFn nil t))

/-- Instanciar el cuerpo en `t` da exactamente `Verifies φ t` (el lift del código se cancela). -/
theorem subst_provBody (φ : Formula) (t : Term) :
    substFormula 0 t (provBody (formCode φ)) = Verifies φ t := by
  simp only [provBody, Verifies, substFormula, substTerm, substTerms, land, chainOk, In, runFn,
    nil, zero, FOL.substTerm_liftTerm, reduceIte, if_true]

/-! ### 1 · ω‑CONSISTENCIA (hipótesis META, explícita) — testigos «con forma de código» -/

/-- **Términos CON FORMA DE CÓDIGO**: los generados por los constructores del lenguaje de códigos
    (`numeralM` para tags/numerales, `strCodeM` para símbolos, `nil`, `cons`). Es la imagen sintáctica
    de `formCodeM`/`termCodeM`/`listFormCodeM`/`lineCode'`/`proofCode'` — precisamente los testigos que
    el `∃` de `provCodeC'` usa (cadenas de prueba codificadas).

    ⚠️ **Por qué NO «cerrado» ni «canónico genérico».** La def anterior `IsClosed x := ∀k, liftTerm k
    x = x` era **inservible**: la igualdad de términos cerrados **no es refutable** (`add zero zero =eq
    zero` es demostrable). Y «canónico» tampoco: `cons h t =eq pair h (succ t)` (`ax_L0_cons_def`) hace
    que un `cons` **sea un número**, luego `cons a b` puede igualar un `numeralM` (p.ej.
    `cons 0̇ [] =eq 2̇`). La refutabilidad **NO** es genérica sobre `IsCodeShaped`.

    **Cómo se refuta entonces** (clave del módulo D de `NegVerifier`, `PLAN-NEGVERIFIER.md`): las
    comparaciones de `NegVerifier` son **PARALELAS POR TIPO** — `formCode φ` contra `formCode ψ`
    (cabeza‑tag contra cabeza‑tag), nunca `cons` contra `numeral` en la misma ranura. Sobre esa
    disciplina de tipos, `formCode_ne`/`termCode_ne`/`cons_ne_head`/`cons_ne_tail`/`strCode_ne`
    (`Meta/CodeDistinct.lean`) **sí** deciden la desigualdad. El lema de distinción de líneas
    (`lineCode_ne`, análogo de `formCode_ne`) es parte del módulo D. -/
inductive IsCodeShaped : Term → Prop
  | numeral (n : Nat) : IsCodeShaped (numeralM n)
  | strCode (s : String) : IsCodeShaped (strCodeM s)
  | nil : IsCodeShaped nil
  | cons {h t : Term} : IsCodeShaped h → IsCodeShaped t → IsCodeShaped (cons h t)

/-- Con forma de código ⟹ **cerrado** (invariante bajo todo lift): los códigos no tienen variables
    libres. Recupera lo único que `IsClosed` aportaba de cierto. -/
theorem IsCodeShaped.isClosed {x : Term} (hx : IsCodeShaped x) : ∀ k, liftTerm k x = x := by
  intro k
  induction hx with
  | numeral n => exact liftTerm_numeralM k n
  | strCode s => exact liftTerm_strCodeM k s
  | nil => rfl
  | @cons h t _ _ ih_h ih_t =>
      show Term.func cons_sym [liftTerm k h, liftTerm k t] = Term.func cons_sym [h, t]
      rw [ih_h, ih_t]

/-- **Testigos ESTÁNDAR** del `∃` de `provCodeC'`: los términos‑lista `objList l` con **todos sus
    elementos CON FORMA DE CÓDIGO**. Es el papel que en la ω‑consistencia clásica juegan los
    **numerales** — aquí, las **codificaciones de pruebas** (imagen de `proofCode'`). -/
def StdChain (l : List Term) : Prop := ∀ x ∈ l, IsCodeShaped x

/-- **ω‑CONSISTENCIA** (hipótesis META, la clásica): la teoría **no demuestra un `∃` mientras refuta
    TODOS sus testigos estándar**.

    ⚠️ **NO es `ConsistentOmega`** (que es sólo `¬(axioms ⊢ ⊥)`, consistencia a secas). Es
    estrictamente **más fuerte**, y es **exactamente** la hipótesis que Gödel necesita para `⊬¬G` —
    por eso existe **Rosser**, que consigue ambas mitades desde consistencia simple, pero **cambiando
    de sentencia**.

    Es **creíble**: toda teoría **SÓLIDA** (correcta en ℕ) es ω‑consistente. -/
def OmegaConsistent : Prop :=
  ∀ A : Formula, (axioms ⊢ Formula.ex A) →
    ¬ (∀ l : List Term, StdChain l → axioms ⊢ neg (substFormula 0 (objList l) A))

/-! ### 2 · Δ₀‑COMPLETITUD NEGATIVA del verificador (lo que queda por construir) -/

/-- **Δ₀‑COMPLETITUD NEGATIVA DEL VERIFICADOR**: si `φ` **no** es demostrable, la teoría **REFUTA**
    que cualquier testigo **estándar** sea una prueba suya.

    Es el **espejo de `repr_pos'`** (D1) en la dirección negativa, y **es alcanzable**: para un testigo
    CONCRETO (cerrado) el chequeo es **finito y estructural**. Contrasta con la versión Π₁ universal
    `⊢ ¬provCodeC' φ`, que está **CERRADA POR GÖDEL II** (para `φ = ⊥` sería `Con(T)`).

    **Descomposición para construirlo** (ver `NEXT-STEPS.md`):
    * evaluar `runFn nil ⟦l⟧` en un testigo concreto (los axiomas de `runFn` computan);
    * si `⌜φ⌝` **no** está entre las conclusiones ⇒ refutar el `In` (base: `formCode_ne`,
      `Meta/CodeDistinct.lean`);
    * si **sí** está ⇒ la cadena no puede ser válida (si lo fuera, `φ` sería demostrable, contra la
      hipótesis) ⇒ refutar `chainOk` (vía `ax_lineWF_inv` + distinción de códigos). Esto último exige
      la **solidez estructural del verificador** respecto de `Prf` — el punto delicado. -/
def NegVerifier : Prop :=
  ∀ (φ : Formula), ¬ Prf φ →
    ∀ l : List Term, StdChain l → axioms ⊢ neg (Verifies φ (objList l))

/-! ### 3 · La REDUCCIÓN -/

/-- **ω‑consistencia + Δ₀‑completitud negativa ⟹ REFLEXIÓN.** Descarga la hipótesis `Reflects` de
    `goedel_first_undecidable_real'`. La prueba es inmediata una vez las definiciones encajan: si
    `φ` no fuera demostrable, `NegVerifier` refutaría **todos** los testigos estándar del `∃` que la
    teoría demuestra — violando la ω‑consistencia. -/
theorem reflects_of_omega (hω : OmegaConsistent) (hneg : NegVerifier) (φ : Formula) :
    Reflects φ := by
  intro hprov
  refine Classical.byContradiction (fun hnp => ?_)
  refine hω (provBody (formCode φ)) hprov ?_
  intro l hl
  rw [subst_provBody]
  exact hneg φ hnp l hl

/-- **PRIMER TEOREMA DE GÖDEL — `G` INDECIDIBLE desde la ω‑CONSISTENCIA** (la hipótesis honesta y
    clásica), sin ningún postulado gödeliano. Sólo queda por construir `NegVerifier` (Δ₀, alcanzable). -/
theorem goedel_first_undecidable_omega
    (hcon : ConsistentOmega) (hω : OmegaConsistent) (hneg : NegVerifier) :
    (¬ Prf godelCN) ∧ (¬ Prf (neg godelCN)) :=
  goedel_first_undecidable_numeral hcon (reflects_of_omega hω hneg godelCN)

end ROBINSON_PlusPlus.Meta.OmegaReflect

export ROBINSON_PlusPlus.Meta.OmegaReflect (
  provBody provFromCode_eq_ex provCodeC'_eq_ex Verifies subst_provBody
  IsCodeShaped StdChain OmegaConsistent NegVerifier
  reflects_of_omega goedel_first_undecidable_omega
)

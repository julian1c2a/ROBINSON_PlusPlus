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
open ROBINSON_PlusPlus.Meta.HilbertSeq

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

    ⛔⛔ **CORRECCIÓN 2026‑09‑10h (ADR‑022) — este docstring afirmaba algo FALSO.** Decía: *«las
    comparaciones de `NegVerifier` son PARALELAS POR TIPO — `formCode φ` contra `formCode ψ`, nunca
    `cons` contra `numeral` en la misma ranura»*. **No es cierto sobre esta clase**, y el
    contraejemplo está compilado (`sondeos/MedirF_Censo.lean` §4): `⟨formCode (⊥⇒⊥), 8̄, 3̄⟩` es
    `IsCodeShaped`, y refutarla obliga a comparar `formCode ⊥` (un `cons`) contra `numeralM 3` (un
    numeral) **en la misma ranura**. La única vía es por **VALOR** (`numTree_ne`), y el valor de un
    código **no es calculable** (`codeNat (⊥⇒⊥) = 583 734`; para una sentencia real, astronómico).

    ⇒ **Por eso `StdChain` YA NO se define sobre esta clase** sino sobre `StdLine` (§1bis): ahí la
    disciplina de tipos es **verdadera por construcción**, y entonces sí mandan
    `formCode_ne`/`termCode_ne`/`cons_ne_head`/`cons_ne_tail`/`strCode_ne`
    (`Meta/CodeDistinct.lean`). `IsCodeShaped` se conserva porque `isClosed` (abajo) sigue siendo
    útil y porque los sondeos la citan. -/
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

/-! ### 1bis · ⭐ LA CLASE DE TESTIGOS, **ESTRECHADA** ([ADR‑022](../../DECISIONS.md), 2026‑09‑10h)

⛔ **Por qué `IsCodeShaped` no servía, medido y no argumentado.** Su propio docstring (arriba)
afirmaba que las comparaciones de `NegVerifier` son *«PARALELAS POR TIPO — nunca `cons` contra
`numeral` en la misma ranura»*. **Es falso sobre la clase que él mismo define**, y hay contraejemplo
compilado en `sondeos/MedirF_Censo.lean` §4:

    IsCodeShaped ⟨formCode (⊥⇒⊥), 8̄, 3̄⟩        -- ✅ testigo `StdChain` legítimo del diseño viejo

y refutarla exige comparar `formCode ⊥` (un **`cons`**) contra `numeralM 3` (un **numeral**) en la
misma ranura. `formCode_ne`/`cons_ne_head` **no pueden**; sólo se puede por **VALOR** (`numTree_ne`,
mismo sondeo), y el valor de un código **no es calculable** (`codeNat (⊥⇒⊥)` ya son **583 734**, y
para una sentencia real es astronómico). ⇒ la obligación existía pero **no era descargable**.

⭐ **La clase estrechada la elimina de raíz**: la cabeza de una línea es **sintácticamente** un
`formCode`, la casilla del tag un `numeralM`, y los argumentos `formCode`/`termCode`. Todas las
comparaciones quedan **paralelas por tipo de verdad**, y las decide `formCode_ne`/`termCode_ne`
(`Meta/CodeDistinct.lean`) **sin evaluar Cantor**.

⚠️ **El precio, escrito y no escondido**: `OmegaConsistent` (abajo) cuantifica sobre **menos**
testigos ⇒ es una hipótesis **estrictamente más fuerte** que con la clase ancha. Ver la discusión
completa —incluido por qué el argumento «toda teoría sólida es ω‑consistente» ya **no** la cubre en
general, y por qué sí la cubre en el único `∃` al que se aplica— en **ADR‑022**. La garantía que lo
hace admisible es `stdChain_proofCode'` (§1ter): **la clase contiene los códigos de prueba REALES**. -/

/-- Los **ARGUMENTOS** de una justificación estándar: la lista‑código formada por códigos de
    fórmula (`formCode`) y de término (`termCode`), que es exactamente lo que produce `lineJustif`. -/
inductive StdArgs : Term → Prop
  | nil : StdArgs nil
  | form {t : Term} (A : Formula) : StdArgs t → StdArgs (cons (formCode A) t)
  | term {t : Term} (u : Term) : StdArgs t → StdArgs (cons (termCode u) t)

/-- Una **LÍNEA ESTÁNDAR**: `⟨⌜f⌝, k̄, args…⟩` — la forma exacta de `lineCode'`. -/
def StdLine (x : Term) : Prop :=
  ∃ (f : Formula) (k : Nat) (as : Term),
    And (x = cons (formCode f) (cons (numeralM k) as)) (StdArgs as)

/-- **Testigos ESTÁNDAR** del `∃` de `provCodeC'`: los términos‑lista `objList l` con **todas sus
    líneas ESTÁNDAR**. Es el papel que en la ω‑consistencia clásica juegan los **numerales** —
    aquí, las **codificaciones de pruebas** (imagen de `proofCode'`). -/
def StdChain (l : List Term) : Prop := ∀ x ∈ l, StdLine x

/-! ### 1ter · 🏁 LA GARANTÍA: la clase contiene los códigos de prueba REALES

Sin esto el estrechamiento sería una trampa: se podría hacer `NegVerifier` trivial vaciando la
clase, y `OmegaConsistent` se volvería **falsa**. Lo que sigue lo impide. -/

/-- Toda línea producida por `lineCode'` es estándar — los **21 tags**. -/
theorem stdLine_lineCode' (acc : List Formula) (f : Formula) (r : Rule) :
    StdLine (lineCode' acc f r) := by
  cases r with
  | p1 A B => exact ⟨f, 0, _, rfl, .form A (.form B .nil)⟩
  | p2 A B C => exact ⟨f, 1, _, rfl, .form A (.form B (.form C .nil))⟩
  | c1 A B => exact ⟨f, 2, _, rfl, .form A (.form B .nil)⟩
  | c2 A B => exact ⟨f, 3, _, rfl, .form A (.form B .nil)⟩
  | c3 A B => exact ⟨f, 4, _, rfl, .form A (.form B .nil)⟩
  | j1 A B => exact ⟨f, 5, _, rfl, .form A (.form B .nil)⟩
  | j2 A B => exact ⟨f, 6, _, rfl, .form A (.form B .nil)⟩
  | j3 A B C => exact ⟨f, 7, _, rfl, .form A (.form B (.form C .nil))⟩
  | efq A => exact ⟨f, 8, _, rfl, .form A .nil⟩
  | q1 A t => exact ⟨f, 9, _, rfl, .form A (.term t .nil)⟩
  | q2 A t => exact ⟨f, 10, _, rfl, .form A (.term t .nil)⟩
  | q3 A B => exact ⟨f, 11, _, rfl, .form A (.form B .nil)⟩
  | eqrefl t => exact ⟨f, 12, _, rfl, .term t .nil⟩
  | leibniz A t₁ t₂ => exact ⟨f, 13, _, rfl, .form A (.term t₁ (.term t₂ .nil))⟩
  | p3 A => exact ⟨f, 14, _, rfl, .form A .nil⟩
  | thy _ => exact ⟨f, 15, _, rfl, .nil⟩
  | mp _ _ => exact ⟨f, 16, _, rfl, .form _ .nil⟩
  | gen _ => exact ⟨f, 17, _, rfl, .form _ .nil⟩
  | ind A => exact ⟨f, 18, _, rfl, .form A .nil⟩
  | qconf P C => exact ⟨f, 19, _, rfl, .form P (.form C .nil)⟩
  | listInd A => exact ⟨f, 20, _, rfl, .form A .nil⟩

/-- 🏁 **LA GARANTÍA DE ADR‑022**: el código de **cualquier** demostración‑secuencia es un testigo
    estándar. ⇒ estrechar la clase **no deja fuera ningún testigo real**, que es lo único que
    hace admisible la `OmegaConsistent` reforzada. -/
theorem stdChain_proofCode' : ∀ (rs : List Rule) (acc : List Formula),
    ∃ l : List Term, And (StdChain l) (objList l = proofCode' rs acc) := by
  intro rs
  induction rs with
  | nil => intro acc; exact ⟨[], (by intro x hx; cases hx), rfl⟩
  | cons r rs ih =>
      intro acc
      cases hs : stepConcl acc r with
      | none => exact ⟨[], (by intro x hx; cases hx), (by simp [proofCode', hs]; rfl)⟩
      | some g =>
          obtain ⟨l, hl, hobj⟩ := ih (acc ++ [g])
          refine ⟨lineCode' acc g r :: l, ?_, ?_⟩
          · intro x hx
            cases hx with
            | head => exact stdLine_lineCode' acc g r
            | tail _ h => exact hl _ h
          · show cons (lineCode' acc g r) (objList l) = _
            simp [proofCode', hs, hobj]

/-! ### 1quater · Y EL PAYOFF: la basura que la clase ancha aceptaba queda FUERA -/

theorem formCode_is_cons (A : Formula) : ∃ h t, formCode A = cons h t := by
  cases A <;> exact ⟨_, _, rfl⟩

theorem termCode_is_cons (t : Term) : ∃ h u, termCode t = cons h u := by
  cases t <;> exact ⟨_, _, rfl⟩

theorem cons_ne_numeralM (h t : Term) (n : Nat) : cons h t ≠ numeralM n := by
  cases n <;> simp [cons, numeralM, succ, zero]

theorem stdArgs_head {x : Term} (hx : StdArgs x) :
    Or (x = nil) (∃ hd tl, And (x = cons hd tl)
      (Or (∃ A, hd = formCode A) (∃ u, hd = termCode u))) := by
  cases hx with
  | nil => exact .inl rfl
  | form A _ => exact .inr ⟨_, _, rfl, .inl ⟨A, rfl⟩⟩
  | term u _ => exact .inr ⟨_, _, rfl, .inr ⟨u, rfl⟩⟩

/-- ⛔ **Un NUMERAL PELADO no es un argumento estándar** — y ahí está toda la diferencia con
    `IsCodeShaped`, que sí lo aceptaba. -/
theorem not_stdArgs_numeralM (n : Nat) (as : Term) : ¬ StdArgs (cons (numeralM n) as) := by
  intro h
  rcases stdArgs_head h with hnil | ⟨hd, tl, heq, hcase⟩
  · exact absurd hnil (by simp [cons, nil, zero])
  · have hhd : hd = numeralM n := by
      have h2 := heq; simp [cons] at h2; exact h2.1.symm
    rcases hcase with ⟨A, hA⟩ | ⟨u, hu⟩
    · obtain ⟨a, b, hab⟩ := formCode_is_cons A
      exact cons_ne_numeralM a b n (by rw [← hab, ← hA, hhd])
    · obtain ⟨a, b, hab⟩ := termCode_is_cons u
      exact cons_ne_numeralM a b n (by rw [← hab, ← hu, hhd])

/-- 🏁 **La línea basura de `sondeos/MedirF_Censo.lean` §4 queda FUERA de la clase.** Era el
    testigo `StdChain` legítimo cuya refutación exigía evaluar Cantor. -/
theorem junk_line_not_stdLine :
    ¬ StdLine (cons (formCode (Formula.impl Formula.bottom Formula.bottom))
        (cons (numeralM 8) (cons (numeralM 3) nil))) := by
  rintro ⟨f, k, as, heq, has⟩
  have hs : as = cons (numeralM 3) nil := by simp [cons] at heq; exact heq.2.2.symm
  exact not_stdArgs_numeralM 3 nil (hs ▸ has)

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
  IsCodeShaped StdArgs StdLine StdChain OmegaConsistent NegVerifier
  stdLine_lineCode' stdChain_proofCode' not_stdArgs_numeralM junk_line_not_stdLine
  reflects_of_omega goedel_first_undecidable_omega
)

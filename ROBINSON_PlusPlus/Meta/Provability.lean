/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Meta.Godel

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Provability

/-!
## META — NIVEL C: DEMOSTRABILIDAD (provisional, en construcción)

Stage 1: codificación estructural de Gödel de los términos y fórmulas del
lenguaje (FOL `Term`/`Formula`). Construye sobre `numeral`/`cons`/`nil` de
`Meta/Godel.lean`. Cada nodo se codifica como `cons (numeral tag) payload`,
con `tag` distinto por constructor. Las cadenas (símbolos de función/predicado)
se codifican carácter a carácter.
-/

/-- Código de una cadena de caracteres (lista). -/
def charsCode : List Char → Term
  | []      => nil
  | c :: cs => cons (numeral c.toNat) (charsCode cs)

/-- Código de un símbolo (String) — carácter a carácter. -/
def strCode (s : String) : Term := charsCode s.toList

/- Código de Gödel de términos del lenguaje (mutuo con `termsCode` por el
   anidamiento `func : String → List Term → Term`).
   `var n ↦ ⟨0, n⟩`, `func s ts ↦ ⟨1, strCode s, termsCode ts⟩`. -/
mutual
def termCode : Term → Term
  | .var n     => cons (numeral 0) (cons (numeral n) nil)
  | .func s ts => cons (numeral 1) (cons (strCode s) (cons (termsCode ts) nil))
def termsCode : List Term → Term
  | []      => nil
  | t :: ts => cons (termCode t) (termsCode ts)
end

/-- **Def 27/29 (coding)** — código de Gödel de fórmulas del lenguaje.
    Tag por constructor: ⊥=2, atom=3, eq=4, impl=5, ∀=6, ∧=7, ∨=8, ∃=9. -/
def formCode : Formula → Term
  | .bottom          => cons (numeral 2) nil
  | .atom p ts       => cons (numeral 3) (cons (strCode p) (cons (termsCode ts) nil))
  | .eq t u          => cons (numeral 4) (cons (termCode t) (cons (termCode u) nil))
  | .impl a b        => cons (numeral 5) (cons (formCode a) (cons (formCode b) nil))
  | Formula.forall a => cons (numeral 6) (cons (formCode a) nil)
  | .and a b         => cons (numeral 7) (cons (formCode a) (cons (formCode b) nil))
  | .or a b          => cons (numeral 8) (cons (formCode a) (cons (formCode b) nil))
  | .ex a            => cons (numeral 9) (cons (formCode a) nil)

/-! ### Inyectividad de la codificación (consistency-free, vía `injection`) -/

/-- `nil` y `cons` nunca coinciden como `Term` (símbolos "0" vs "::"). -/
private theorem nil_ne_cons (a b : Term) : nil ≠ cons a b := by
  intro h
  simp only [nil, zero, cons] at h
  injection h with hs _
  exact absurd hs (by decide)

/-- `Char.toNat` es inyectiva. -/
private theorem char_toNat_inj {a b : Char} (h : a.toNat = b.toNat) : a = b := by
  first
    | exact Char.toNat_inj.mp h
    | exact Char.toNat.inj h
    | (rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b, h])
    | (apply Char.eq_of_val_eq; exact UInt32.toNat.inj h)

theorem charsCode_injective : ∀ {l l' : List Char}, charsCode l = charsCode l' → l = l'
  | [],      [],       _ => rfl
  | [],      _ :: _,   h => by simp only [charsCode] at h; exact absurd h (nil_ne_cons _ _)
  | _ :: _,  [],       h => by simp only [charsCode] at h; exact absurd h.symm (nil_ne_cons _ _)
  | c :: cs, c' :: cs', h => by
      simp only [charsCode, cons] at h
      injection h with _ hl; injection hl with hc hl2; injection hl2 with hrest _
      have hcn : c.toNat = c'.toNat := numeral_injective _ _ hc
      rw [char_toNat_inj hcn, charsCode_injective hrest]

theorem strCode_injective {s t : String} (h : strCode s = strCode t) : s = t := by
  have h' : charsCode s.toList = charsCode t.toList := h
  have hd : s.toList = t.toList := charsCode_injective h'
  first
    | exact String.toList_inj.mp hd
    | exact String.toList_injective hd
    | exact String.ext hd
    | (rw [← String.asString_toList s, ← String.asString_toList t, hd])

-- Peeling de `cons` a nivel Lean (constructor `func`).
private theorem cons_inj_lean {a b c d : Term}
    (h : cons a b = cons c d) : (a = c) ∧ (b = d) := by
  simp only [cons] at h
  injection h with _ hl
  injection hl with ha hl2
  injection hl2 with hb _
  exact ⟨ha, hb⟩

mutual
theorem termCode_injective : ∀ {t t' : Term}, termCode t = termCode t' → t = t'
  | .var n, .var n', h => by
      simp only [termCode] at h
      obtain ⟨_, h2⟩ := cons_inj_lean h
      obtain ⟨hn, _⟩ := cons_inj_lean h2
      rw [numeral_injective _ _ hn]
  | .var _, .func _ _, h => by
      simp only [termCode] at h
      obtain ⟨ht, _⟩ := cons_inj_lean h
      exact absurd (numeral_injective _ _ ht) (by decide)
  | .func _ _, .var _, h => by
      simp only [termCode] at h
      obtain ⟨ht, _⟩ := cons_inj_lean h
      exact absurd (numeral_injective _ _ ht) (by decide)
  | .func s ts, .func s' ts', h => by
      simp only [termCode] at h
      obtain ⟨_, h2⟩ := cons_inj_lean h
      obtain ⟨hs, h3⟩ := cons_inj_lean h2
      obtain ⟨hts, _⟩ := cons_inj_lean h3
      rw [strCode_injective hs, termsCode_injective hts]
theorem termsCode_injective : ∀ {ts ts' : List Term}, termsCode ts = termsCode ts' → ts = ts'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [termsCode] at h; exact absurd h (nil_ne_cons _ _)
  | _ :: _, [], h => by simp only [termsCode] at h; exact absurd h.symm (nil_ne_cons _ _)
  | t :: ts, t' :: ts', h => by
      simp only [termsCode] at h
      obtain ⟨ht, hts⟩ := cons_inj_lean h
      rw [termCode_injective ht, termsCode_injective hts]
end

/-- **Inyectividad de `formCode`** (Teo G1 a nivel de fórmulas): codes idénticos
    ⟹ fórmulas idénticas. Inducción estructural; cada arma cierra los casos de
    constructor distinto por contradicción de la etiqueta y el caso diagonal por
    recursión. Consistency-free. -/
theorem formCode_injective : ∀ {φ φ' : Formula}, formCode φ = formCode φ' → φ = φ' := by
  intro φ
  induction φ with
  | bottom =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | rfl
  | atom p ts =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨hp, h3⟩ := cons_inj_lean h2;
             obtain ⟨hts, _⟩ := cons_inj_lean h3; rw [strCode_injective hp, termsCode_injective hts])
  | eq t u =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨htt, h3⟩ := cons_inj_lean h2;
             obtain ⟨huu, _⟩ := cons_inj_lean h3; rw [termCode_injective htt, termCode_injective huu])
  | impl a b iha ihb =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨ha, h3⟩ := cons_inj_lean h2;
             obtain ⟨hb, _⟩ := cons_inj_lean h3; rw [iha ha, ihb hb])
  | «forall» a iha =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨ha, _⟩ := cons_inj_lean h2; rw [iha ha])
  | and a b iha ihb =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨ha, h3⟩ := cons_inj_lean h2;
             obtain ⟨hb, _⟩ := cons_inj_lean h3; rw [iha ha, ihb hb])
  | or a b iha ihb =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨ha, h3⟩ := cons_inj_lean h2;
             obtain ⟨hb, _⟩ := cons_inj_lean h3; rw [iha ha, ihb hb])
  | ex a iha =>
      intro φ' h; cases φ' <;> simp only [formCode] at h <;>
        first
          | (obtain ⟨ht, _⟩ := cons_inj_lean h; exact absurd (numeral_injective _ _ ht) (by decide))
          | (obtain ⟨_, h2⟩ := cons_inj_lean h; obtain ⟨ha, _⟩ := cons_inj_lean h2; rw [iha ha])

/-!
### Def 29 — `IsFormula`, y la demostrabilidad `Provable`

`IsFormula x` (Def 29): `x` es el código de una fórmula bien formada (i.e. está
en la imagen de `formCode`; toda fórmula de FOL `Formula` es wff por
construcción). `Provable x`: `x` codifica un teorema de `Minimal`.
-/

/-- **Def 29** — `x` codifica una fórmula bien formada del lenguaje. -/
def IsFormula (x : Term) : Prop := ∃ φ : Formula, x = formCode φ

theorem isFormula_formCode (φ : Formula) : IsFormula (formCode φ) := ⟨φ, rfl⟩

/-- `x` codifica un teorema de `Minimal` (`axioms ⊢ φ` con `x = ⌜φ⌝`). -/
def Provable (x : Term) : Prop := ∃ φ : Formula, (x = formCode φ) ∧ (axioms ⊢ φ)

/-- **`Provable` rastrea fielmente la derivabilidad** (teorema real, no postulado):
    `Provable ⌜φ⌝ ↔ axioms ⊢ φ`. Usa `formCode_injective`. -/
theorem provable_formCode_iff (φ : Formula) : Provable (formCode φ) ↔ (axioms ⊢ φ) := by
  constructor
  · rintro ⟨ψ, hcode, hψ⟩
    rw [formCode_injective hcode]; exact hψ
  · intro hφ; exact ⟨φ, rfl, hφ⟩

/-!
### Def 30 — `Dem`, y la Teo Meta (postulados)

Lo siguiente requiere la **aritmetización de las demostraciones** y/o el
**lema de diagonalización**, no demostrables en `Minimal` sin inducción. Se
postulan como **meta-axiomas** (estilo `ax_p_tfa`, `imp_intro`, …). Pasarán a
teoremas en el Nivel D (sobre `Intermediate/`/`Full/`). Ver `GODEL-STATUS.md`.
-/

/-- **Def 30** — `Dem d x`: `d` codifica una demostración cuya última línea es la
    fórmula de código `x`. Relación postulada (su construcción codifica árboles
    de derivación: aritmetización + inducción, Nivel D). -/
axiom Dem : Term → Term → Prop

/-- **Teo Meta** (spec Fase 19): el sistema expresa su propia derivabilidad —
    `axioms ⊢ φ ↔ ∃ d, Dem d ⌜φ⌝`. Meta-axioma. -/
axiom dem_iff_provable (φ : Formula) :
    (axioms ⊢ φ) ↔ ∃ d : Term, Dem d (formCode φ)

/-- Fórmula object-level `Prov(x)` con variable libre `0`, que expresa "el código
    `x` es demostrable". Postulada (su construcción aritmetiza `Dem`). -/
axiom provFormula : Formula

/-- **Representabilidad de la demostrabilidad**: `⊢ Prov(⌜φ⌝) ↔ ⊢ φ`.
    Meta-axioma (condición de demostrabilidad D1; requiere Nivel D). -/
axiom provFormula_repr (φ : Formula) :
    (axioms ⊢ substFormula 0 (formCode φ) provFormula) ↔ (axioms ⊢ φ)

/-- **Lema del punto fijo (diagonalización)**: para toda fórmula `φ` con variable
    libre `0` existe una sentencia `ψ` tal que `⊢ ψ ⇔ φ[⌜ψ⌝]`. Meta-axioma
    (la construcción diagonal requiere representabilidad de la sustitución). -/
axiom diagonal_lemma (φ : Formula) :
    ∃ ψ : Formula, axioms ⊢ (ψ ⇔ substFormula 0 (formCode ψ) φ)

/-- **Sentencia de Gödel** `G_Min`: punto fijo de `¬Prov(x)`, i.e. una sentencia
    que afirma su propia indemostrabilidad. Obtenida del lema de diagonalización
    aplicado a `¬provFormula`. -/
noncomputable def goedelSentence : Formula :=
  (diagonal_lemma (neg provFormula)).choose

/-- Propiedad de punto fijo de la sentencia de Gödel:
    `⊢ G_Min ⇔ (¬Prov(x))[⌜G_Min⌝]`, es decir `⊢ G_Min ⇔ ¬Prov(⌜G_Min⌝)`. -/
theorem goedelSentence_fixedpoint :
    axioms ⊢ (goedelSentence ⇔ substFormula 0 (formCode goedelSentence) (neg provFormula)) :=
  (diagonal_lemma (neg provFormula)).choose_spec

end ROBINSON_PlusPlus.Meta.Provability

-- Exports: API pública del Nivel C de demostrabilidad
export ROBINSON_PlusPlus.Meta.Provability (
  charsCode
  strCode
  termCode
  termsCode
  formCode
  charsCode_injective
  strCode_injective
  termCode_injective
  termsCode_injective
  formCode_injective
  IsFormula
  isFormula_formCode
  Provable
  provable_formCode_iff
  Dem
  dem_iff_provable
  provFormula
  provFormula_repr
  diagonal_lemma
  goedelSentence
  goedelSentence_fixedpoint
)

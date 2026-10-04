/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CheckArith
-- ⚠️ Añadido en el dedup del 2026‑09‑09d: este módulo tenía copias LITERALES de
--    `concat_nil_eq`, `concat_cons_eq`, `in_cons_head` e `in_cons_tail`, que declaraba y
--    **exportaba** `Meta/ProofChain.lean`. Los dos módulos eran independientes, así que la
--    salida barata fue este `import` (sin ciclo: `ProofChain` no depende de este módulo).
--    🗑️ Las cuatro eran de `⊢` y quedaron retiradas también de `ProofChain` (ADR‑115). Sus
--    versiones `Prf` son `prf_concat_nil_eq`, `prf_concat_cons_eq`, `prf_in_cons_head` y
--    `prf_in_cons_tail` (`Meta/ReprPrf.lean`).
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.HilbertSeq

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Minimal.Axioms

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`concat_nil_eq`, `concat_cons_eq`, `in_cons_head`, `in_cons_tail`…) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Representability

/-!
## META — NIVEL D (real): representabilidad positiva  (Fase 2.5)

Cerraba (sobre `⊢`; ver el registro de abajo) la dirección **positiva** del puente de
demostrabilidad object:

> `repr_pos : Prf φ → axioms ⊢ provCodeC φ`

es decir, de una demostración finitaria de Hilbert `Prf φ` se construye, **dentro
de la teoría**, una prueba de la fórmula Σ₁ `provCodeC φ = ∃p, In ⌜φ⌝
(validProofFn nil p)`. Es lo único que **D1 (necesitación, Fase 3)** necesita.

**Encoder object propio.** El verificador `validProofFn` espera que las líneas
`mp`/`gen` transporten los **códigos de las fórmulas** premisa/conclusión (las
comprueba por pertenencia con `In`), no índices de línea. El `ruleCode` de la
Fase 1c (para `Dem`) transporta índices, por lo que aquí se define un encoder
**a medida** `proofCode`/`lineCode` alineado con `validProofFn`: recorre la
secuencia acumulando conclusiones y emite cada línea con los códigos resueltos.
Como `provFormulaC` cuantifica sobre **cualquier** código de prueba, basta
exhibir éste.

La **inducción de seguimiento** `vpf_run` demostraba que `validProofFn` calcula,
sobre `proofCode rs acc`, el código object de la lista de conclusiones de
`checkAux rs acc`; cada paso usaba el step-lemma `vpf_*` correspondiente (los
esquemas de sustitución Q1/Q2/Q3/Leibniz, vía los `*_concl_code` de StepArith).

🗑️ **2026‑10‑02 (ADR‑115) — registro.** `repr_pos`, `vpf_run`, los `vpf_*` y sus auxiliares de
este módulo (`congr_vpf_checked`, `congr_concat2`, `concat_listFormCode`, `In_listFormCode`) eran de
`⊢` y quedaron retirados con esa capa (`StepArith` también). Aquí quedan `listFormCode`, el puente
`formCodeM = formCode` y el encoder `lineCode`/`proofCode`. En `Prf`, D1 es `repr_pos'_prf`, que
usa el ancla `prf_ancla`, y los auxiliares son `prf_concat_listFormCode` (ambos en
`Meta/Representability2Prf.lean`) y `prf_In_listFormCode` (`Meta/ReprPrf.lean`).
-/

/-! ### Código object de una lista de fórmulas -/

/-- Código object de una lista de fórmulas (lista `cons` de sus `formCode`). -/
def listFormCode : List Formula → Term
  | [] => nil
  | f :: fs => cons (formCode f) (listFormCode fs)

/-! ### Puente `formCodeM = formCode`

La codificación local de `Minimal` (`formCodeM`, con `numeralM`) coincide con la
de `Meta/Provability` (`formCode`, con `Godel.numeral`); vía `numeralM_eq`. Permite
relacionar `axiomsCodeT` (anclado por `prf_ancla` a `listFormCodeM axioms`) con la pertenencia
sobre `formCode`: era `In_listFormCode`, sobre `⊢`, retirado (ADR‑115); en `Prf` es
`prf_In_listFormCode`. -/

theorem charsCodeM_eq : ∀ cs : List Char, charsCodeM cs = charsCode cs
  | []      => rfl
  | _ :: cs => by simp only [charsCodeM, charsCode, numeralM_eq, charsCodeM_eq cs]

theorem strCodeM_eq (s : String) : strCodeM s = strCode s := charsCodeM_eq s.toList

mutual
theorem termCodeM_eq : ∀ t : Term, termCodeM t = termCode t
  | .var _    => by simp only [termCodeM, termCode, numeralM_eq]
  | .func s ts => by simp only [termCodeM, termCode, numeralM_eq, strCodeM_eq, termsCodeM_eq ts]
theorem termsCodeM_eq : ∀ ts : List Term, termsCodeM ts = termsCode ts
  | []      => rfl
  | t :: ts => by simp only [termsCodeM, termsCode, termCodeM_eq t, termsCodeM_eq ts]
end

theorem formCodeM_eq : ∀ φ : Formula, formCodeM φ = formCode φ
  | .bottom    => by simp only [formCodeM, formCode, numeralM_eq]
  | .atom _ _  => by simp only [formCodeM, formCode, numeralM_eq, strCodeM_eq, termsCodeM_eq]
  | .eq _ _    => by simp only [formCodeM, formCode, numeralM_eq, termCodeM_eq]
  | .impl a b  => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a, formCodeM_eq b]
  | .forall a  => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a]
  | .and a b   => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a, formCodeM_eq b]
  | .or a b    => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a, formCodeM_eq b]
  | .ex a      => by simp only [formCodeM, formCode, numeralM_eq, formCodeM_eq a]

theorem listFormCodeM_eq : ∀ L : List Formula, listFormCodeM L = listFormCode L
  | []      => rfl
  | f :: fs => by simp only [listFormCodeM, listFormCode, formCodeM_eq f, listFormCodeM_eq fs]

/-! ### Encoder object de demostraciones (a medida de `validProofFn`) -/

/-- Código object de una línea, dada la conclusión `f` ya computada y el
    acumulador `acc`. Las reglas-esquema usan sus parámetros; `mp`/`gen`
    transportan los códigos de las fórmulas (no índices); `thy` el código del
    axioma (= `f`). -/
def lineCode (acc : List Formula) (f : Formula) : Rule → Term
  | .p1 A B => cons (numeral 0) (cons (formCode A) (cons (formCode B) nil))
  | .p2 A B C => cons (numeral 1) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .c1 A B => cons (numeral 2) (cons (formCode A) (cons (formCode B) nil))
  | .c2 A B => cons (numeral 3) (cons (formCode A) (cons (formCode B) nil))
  | .c3 A B => cons (numeral 4) (cons (formCode A) (cons (formCode B) nil))
  | .j1 A B => cons (numeral 5) (cons (formCode A) (cons (formCode B) nil))
  | .j2 A B => cons (numeral 6) (cons (formCode A) (cons (formCode B) nil))
  | .j3 A B C => cons (numeral 7) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .efq A => cons (numeral 8) (cons (formCode A) nil)
  | .q1 A t => cons (numeral 9) (cons (formCode A) (cons (termCode t) nil))
  | .q2 A t => cons (numeral 10) (cons (formCode A) (cons (termCode t) nil))
  | .q3 A B => cons (numeral 11) (cons (formCode A) (cons (formCode B) nil))
  | .eqrefl t => cons (numeral 12) (cons (termCode t) nil)
  | .leibniz A t₁ t₂ =>
      cons (numeral 13) (cons (formCode A) (cons (termCode t₁) (cons (termCode t₂) nil)))
  | .p3 A => cons (numeral 14) (cons (formCode A) nil)
  | .ind A => cons (numeral 18) (cons (formCode A) nil)
  | .qconf P C => cons (numeral 19) (cons (formCode P) (cons (formCode C) nil))
  | .listInd A => cons (numeral 20) (cons (formCode A) nil)
  | .thy _ => cons (numeral 15) (cons (formCode f) nil)
  | .mp _ j => cons (numeral 16) (cons (formCode f) (cons (formCode ((acc[j]?).getD Formula.bottom)) nil))
  | .gen i => cons (numeral 17) (cons (formCode ((acc[i]?).getD Formula.bottom)) nil)

/-- Código object de una demostración-secuencia, alineado con `validProofFn`. -/
def proofCode : List Rule → List Formula → Term
  | [], _ => nil
  | r :: rs, acc =>
      match stepConcl acc r with
      | some f => cons (lineCode acc f r) (proofCode rs (acc ++ [f]))
      | none => nil

end ROBINSON_PlusPlus.Meta.Representability

export ROBINSON_PlusPlus.Meta.Representability (
  listFormCode
  proofCode
)

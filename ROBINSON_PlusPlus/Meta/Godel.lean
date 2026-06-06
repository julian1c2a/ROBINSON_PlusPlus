/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block6

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block6

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Godel

/-!
## META — NIVEL B: GÖDELIZACIÓN (codificación)

Implementa **Def 27** (asignación de Gödel `G : Λ → ℕ`), **Def 28** (corner
brackets `⌜·⌝`) y **Teo G1** (inyectividad) de `TuplasFuncionesYListas.md
§BLOQUE VIII Fase 18`.

**Nivel del módulo**: B (meta-codificación pura). No introduce axiomas
matemáticos sobre `Minimal/`; sólo construcciones Lean y un teorema
meta-inductivo. Ver `GODEL-STATUS.md` §2.2.

### Nota sobre la formulación de Teo G1

El enunciado del spec, `⌜S⌝ = ⌜S'⌝ ⟹ S = S'`, mezcla un antecedente sobre
códigos (`Term`) con una conclusión meta (igualdad de cadenas de símbolos
`S = S' : List Sym`). Hay dos lecturas, ambas presentes aquí:

* **Meta-inyectividad (consistency-free)** — `encode_injective`: si los `Term`
  `⌜S⌝` y `⌜S'⌝` son *idénticos como objetos Lean*, entonces `S = S'`. Se
  demuestra por inducción meta (estructural sobre la lista) usando la
  inyectividad de los constructores `cons`/`func` y de `G`. **No requiere
  consistencia** de `axioms`: es la inyectividad real de la codificación.

* **Versión objeto** — `encode_cons_inj` / `encode_cons_neq_nil`: los bloques
  de la prueba del spec ("por Teo L2 repetidamente"), es decir las instancias
  object-level de `cons_inj` (Block6) y `cons_neq_nil`. Pasar de éstas a la
  conclusión meta `S = S'` *sí* requeriría suponer `Con(axioms)` (un `axioms`
  inconsistente prueba cualquier igualdad de códigos). Por eso la inyectividad
  plena se establece a nivel meta; la conexión interna completa pertenece al
  Nivel C/D (junto a `Dem`).
-/

/-- **Def 27** — alfabeto `Λ` del lenguaje de `Minimal` (símbolos relevantes
    para la codificación; tabla de ejemplo del spec §Fase 18). -/
inductive Sym where
  | allS | exS | eqS | ltS | addS | mulS | zeroS | succS
  | varX | varY | varN | varM
  deriving DecidableEq, Repr

/-- **Def 27** — asignación de Gödel `G : Λ → ℕ` (tabla del spec). -/
def gNat : Sym → Nat
  | .allS  => 2   | .exS   => 3
  | .eqS   => 10  | .ltS   => 11
  | .addS  => 20  | .mulS  => 21
  | .zeroS => 30  | .succS => 31
  | .varX  => 100 | .varY  => 101
  | .varN  => 110 | .varM  => 111

/-- `gNat` es inyectiva (la tabla asigna valores distintos a símbolos distintos). -/
theorem gNat_injective {a b : Sym} (h : gNat a = gNat b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Numeral object-level `σⁿ(0)` correspondiente a `n : ℕ` (a nivel meta). -/
def numeral : Nat → Term
  | 0     => zero
  | n + 1 => succ (numeral n)

/-- `numeral` es inyectiva a nivel Lean: `σᵐ0 = σᵏ0 ⟹ m = k`. Inducción meta. -/
theorem numeral_injective : ∀ (m k : Nat), numeral m = numeral k → m = k
  | 0,     0,     _ => rfl
  | 0,     _ + 1, h => by
      simp only [numeral, zero, succ] at h
      injection h with hsym _
      exact absurd hsym (by decide)
  | _ + 1, 0,     h => by
      simp only [numeral, zero, succ] at h
      injection h with hsym _
      exact absurd hsym (by decide)
  | m + 1, k + 1, h => by
      simp only [numeral, succ] at h
      injection h with _ hargs
      injection hargs with hnum _
      exact congrArg Nat.succ (numeral_injective m k hnum)

/-- **Def 27** — `G : Λ → Term`, código de Gödel como numeral object-level. -/
def G (s : Sym) : Term := numeral (gNat s)

/-- `G` es inyectiva (composición de `numeral_injective` y `gNat_injective`). -/
theorem G_injective {a b : Sym} (h : G a = G b) : a = b := by
  apply gNat_injective
  apply numeral_injective
  exact h

/-- **Def 28** — corner brackets `⌜s₁…sₖ⌝ := cons(G s₁, cons(…, cons(G sₖ, nil)))`. -/
def encode : List Sym → Term
  | []          => nil
  | s :: rest   => cons (G s) (encode rest)

@[inherit_doc encode] scoped notation:max "⌜" S "⌝" => encode S

theorem encode_nil : ⌜([] : List Sym)⌝ = nil := rfl

theorem encode_cons (s : Sym) (S : List Sym) :
    ⌜s :: S⌝ = cons (G s) ⌜S⌝ := rfl

/-- Lean-level: `nil` y `cons` se construyen con símbolos de función distintos
    (`"0"` vs `"::"`), luego nunca son el mismo `Term`. -/
private theorem nil_ne_cons (a b : Term) : nil ≠ cons a b := by
  intro h
  simp only [nil, zero, cons] at h
  injection h with hsym _
  exact absurd hsym (by decide)

/-!
### Teo G1 — Inyectividad de la codificación (meta)
-/

/-- **Teo G1** (meta-inyectividad, consistency-free): si los códigos `⌜S⌝` y
    `⌜S'⌝` son el mismo `Term`, entonces `S = S'`. Inducción estructural sobre
    la lista, usando inyectividad de `cons`/`G` (cf. spec: "Teo L2 repetidamente"). -/
theorem encode_injective : ∀ (S S' : List Sym), ⌜S⌝ = ⌜S'⌝ → S = S'
  | [],      [],       _ => rfl
  | [],      _ :: _,   h => by
      rw [encode_nil, encode_cons] at h
      exact absurd h (nil_ne_cons _ _)
  | _ :: _,  [],       h => by
      rw [encode_nil, encode_cons] at h
      exact absurd h.symm (nil_ne_cons _ _)
  | s :: S,  s' :: S', h => by
      rw [encode_cons, encode_cons] at h
      simp only [cons] at h
      injection h with _ hargs
      injection hargs with hHead hargs2
      injection hargs2 with hTail _
      rw [G_injective hHead, encode_injective S S' hTail]

/-!
### Versión object-level (bloques de la prueba del spec, vía Block6)
-/

/-- Bloque object-level de Teo G1 (vía `cons_inj`, Block6): de la igualdad de
    códigos `⌜s::S⌝ =eq ⌜s'::S'⌝` el sistema deriva la igualdad de cabezas y de
    colas. Faithful al "Teo L2 aplicado repetidamente" del spec. -/
theorem encode_cons_inj (s s' : Sym) (S S' : List Sym) :
    axioms ⊢ (⌜s :: S⌝ =eq ⌜s' :: S'⌝)
      ⇒ land (G s =eq G s') (⌜S⌝ =eq ⌜S'⌝) := by
  show axioms ⊢ (cons (G s) ⌜S⌝ =eq cons (G s') ⌜S'⌝)
    ⇒ land (G s =eq G s') (⌜S⌝ =eq ⌜S'⌝)
  exact cons_inj

/-- Object-level: el sistema deriva que el código de una lista no vacía es
    distinto del código de la lista vacía (`⌜[]⌝ = nil`), vía `cons_neq_nil`. -/
theorem encode_cons_neq_nil (s : Sym) (S : List Sym) :
    axioms ⊢ neg (⌜s :: S⌝ =eq ⌜([] : List Sym)⌝) := by
  show axioms ⊢ neg (cons (G s) ⌜S⌝ =eq nil)
  exact cons_neq_nil (G s) ⌜S⌝

end ROBINSON_PlusPlus.Meta.Godel

-- Exports: API pública del Nivel B de Gödelización
export ROBINSON_PlusPlus.Meta.Godel (
  Sym
  gNat
  gNat_injective
  numeral
  numeral_injective
  G
  G_injective
  encode
  encode_nil
  encode_cons
  encode_injective
  encode_cons_inj
  encode_cons_neq_nil
)

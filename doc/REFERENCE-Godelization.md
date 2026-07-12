# REFERENCE — Gödelización Nivel B/C · `Meta/Godel`, `Meta/Provability` · ROBINSON_PlusPlus

> **Nodo temático** del sistema REFERENCE (árbol; ver `AI-GUIDE.md` §0.5).
> Índice raíz: [REFERENCE.md](../REFERENCE.md).
> **Nodos relacionados:** [Núcleo](REFERENCE-Kernel.md) (axiomas), [Aritmética](REFERENCE-Arithmetic.md)
> (`Block6` listas, base de la codificación), [Incompletitud](REFERENCE-Incompleteness.md) (Nivel D se
> construye sobre `formCode`/`provCodeC'`).
> **Ficheros `.lean`:** [Meta/Godel.lean](../ROBINSON_PlusPlus/Meta/Godel.lean),
> [Meta/Provability.lean](../ROBINSON_PlusPlus/Meta/Provability.lean).

**Contenido:** Nivel B (codificación `⌜·⌝`, sentencia `G`, Teorema G1) y Nivel C (`formCode`,
`IsFormula`, `Provable` — núcleo real de codificación; la capa legacy postulada se retiró en F7a).
**Last updated:** 2026-07-12 · Lean v4.31.0.

---

## Descripción de módulos

### 3.12 `Meta/Godel.lean` — Gödelización Nivel B (Fase 18)

**Namespace**: `ROBINSON_PlusPlus.Meta.Godel`
**Status**: ✅ Complete (Nivel B: codificación + Teo G1)
**@importance**: `high`
**@axiom_system**: `none` (meta-codificación pura sobre `Minimal/`; **no añade axiomas**)
**Last updated**: 2026-06-06 (creado)
**Dependencias**: `Axioms`, `Block6` (usa `cons`, `nil`, `cons_inj`, `cons_neq_nil`).

#### Defs

```lean
inductive Sym                            -- Def 27: alfabeto Λ (12 símbolos):
  | allS | exS | eqS | ltS | addS | mulS | zeroS | succS
  | varX | varY | varN | varM            --   deriving DecidableEq, Repr
def gNat : Sym → Nat                      -- Def 27: tabla de Gödel (∀↦2, ∃↦3, =↦10, …, m↦111)
def numeral : Nat → Term                  -- σⁿ(0): numeral 0 = zero, numeral (n+1) = succ (numeral n)
def G (s : Sym) : Term := numeral (gNat s)-- Def 27: código de Gödel como numeral object-level
def encode : List Sym → Term              -- Def 28: ⌜[]⌝ = nil; ⌜s::S⌝ = cons (G s) ⌜S⌝
scoped notation:max "⌜" S "⌝" => encode S -- corner brackets
```

#### Exports

```lean
theorem gNat_injective    {a b : Sym} : gNat a = gNat b → a = b
theorem numeral_injective (m k : Nat)  : numeral m = numeral k → m = k
theorem G_injective       {a b : Sym} : G a = G b → a = b
theorem encode_nil  : ⌜([] : List Sym)⌝ = nil
theorem encode_cons (s S) : ⌜s :: S⌝ = cons (G s) ⌜S⌝
-- Teo G1 (meta-inyectividad, consistency-free):
theorem encode_injective (S S' : List Sym) : ⌜S⌝ = ⌜S'⌝ → S = S'
-- Versión object-level (vía Block6, faithful al "Teo L2 repetidamente" del spec):
theorem encode_cons_inj (s s' S S') :
  axioms ⊢ (⌜s::S⌝ =eq ⌜s'::S'⌝) ⇒ land (G s =eq G s') (⌜S⌝ =eq ⌜S'⌝)
theorem encode_cons_neq_nil (s S) : axioms ⊢ neg (⌜s::S⌝ =eq ⌜[]⌝)
```

**Sobre Teo G1**: el enunciado del spec `⌜S⌝ = ⌜S'⌝ ⟹ S = S'` mezcla antecedente
sobre códigos (`Term`) con conclusión meta (`S = S' : List Sym`). La inyectividad
**plena** (`encode_injective`) se establece a nivel meta (Lean), por inducción
estructural sobre la lista vía inyectividad de `cons`/`func`/`G` (`injection` +
`decide` sobre los símbolos `String` distintos). **No requiere `Con(axioms)`**.
Pasar de la versión object-level (`encode_cons_inj`) a la conclusión meta sí
requeriría consistencia, por lo que esa conexión interna queda para el Nivel C/D.
Ver `GODEL-STATUS.md` §2.

---

### 3.13 `Meta/Provability.lean` — Demostrabilidad Nivel C (Fase 19)

**Namespace**: `ROBINSON_PlusPlus.Meta.Provability`
**Status**: ✅ Complete (Nivel C: codificación de la sintaxis + Def 29/30 + diagonalización)
**@importance**: `high`
**@axiom_system**: `none` (meta-codificación; añade **5 meta-axiomas** de Gödel)
**Last updated**: 2026-06-06 (creado)
**Dependencias**: `Axioms`, `Meta.Godel`, `FOL.FOL`/`FOL.Theorems.*`.

#### Defs (codificación estructural de Gödel)

```lean
def charsCode : List Char → Term          -- cadena de caracteres
def strCode   : String → Term             -- símbolo (vía s.toList)
mutual
  def termCode  : Term → Term             -- var n ↦ ⟨0,n⟩ ; func s ts ↦ ⟨1, strCode s, termsCode ts⟩
  def termsCode : List Term → Term
end
def formCode : Formula → Term             -- tags: ⊥2 atom3 eq4 impl5 ∀6 ∧7 ∨8 ∃9
def IsFormula (x : Term) : Prop := ∃ φ : Formula, x = formCode φ                 -- Def 29
def Provable  (x : Term) : Prop := ∃ φ : Formula, (x = formCode φ) ∧ (axioms ⊢ φ)
noncomputable def goedelSentence : Formula                                        -- punto fijo de ¬Prov
```

#### Exports — demostrado (consistency-free)

```lean
theorem charsCode_injective {l l'} : charsCode l = charsCode l' → l = l'
theorem strCode_injective   {s t}  : strCode s = strCode t → s = t
theorem termCode_injective  {t t'} : termCode t = termCode t' → t = t'      -- (mutuo)
theorem termsCode_injective {ts ts'} : termsCode ts = termsCode ts' → ts = ts'
theorem formCode_injective  {φ φ'} : formCode φ = formCode φ' → φ = φ'      -- Teo G1 (fórmulas)
theorem isFormula_formCode  (φ) : IsFormula (formCode φ)
theorem provable_formCode_iff (φ) : Provable (formCode φ) ↔ (axioms ⊢ φ)
theorem goedelSentence_fixedpoint :
  axioms ⊢ (goedelSentence ⇔ substFormula 0 (formCode goedelSentence) (neg provFormula))
```

#### Meta-axiomas (postulados, estilo `ax_p_tfa`; pasan a teoremas en Nivel D)

```lean
axiom Dem : Term → Term → Prop                                              -- Def 30
axiom dem_iff_provable (φ) : (axioms ⊢ φ) ↔ ∃ d, Dem d (formCode φ)         -- Teo Meta
axiom provFormula : Formula                                                 -- Prov(x) object-level
axiom provFormula_repr (φ) : (axioms ⊢ substFormula 0 (formCode φ) provFormula) ↔ (axioms ⊢ φ)
axiom diagonal_lemma (φ) : ∃ ψ, axioms ⊢ (ψ ⇔ substFormula 0 (formCode ψ) φ) -- punto fijo
```

**Sobre el alcance**: toda la **codificación + inyectividad** y `provable_formCode_iff` se
demuestran sin postular nada. La **aritmetización de `Dem`**, la **representabilidad** y el
**lema de diagonalización** requieren inducción y se adoptan como meta-axiomas (Nivel C según
`GODEL-STATUS.md` §2.2). El **Nivel D** (Gödel I/II: `Minimal ⊬ G_Min`, `⊬ Con`) requiere
`Intermediate/`/`Full/` y queda pendiente.

---


---

← Índice raíz: [REFERENCE.md](../REFERENCE.md) · Siguiente rama: [Incompletitud](REFERENCE-Incompleteness.md)

# REFERENCE — Gödelización Nivel B/C · `Meta/Godel`, `Meta/Provability` · ROBINSON_PlusPlus

> **Nodo temático** del sistema REFERENCE (árbol; ver `AI-GUIDE.md` §0.5).
> Índice raíz: [REFERENCE.md](../REFERENCE.md).
> **Nodos relacionados:** [Núcleo](REFERENCE-Kernel.md) (axiomas), [Incompletitud](REFERENCE-Incompleteness.md)
> (Nivel D se construye sobre `formCode`/`provCodeC'`). ([Aritmética](REFERENCE-Arithmetic.md), con `Block6`,
> se retiró con la capa `⊢`: ADR‑115.)
> **Ficheros `.lean`:** [Meta/Godel.lean](../ROBINSON_PlusPlus/Meta/Godel.lean),
> [Meta/Provability.lean](../ROBINSON_PlusPlus/Meta/Provability.lean).

**Contenido:** Nivel B (codificación `⌜·⌝`, `G`, Teorema G1 como **meta‑inyectividad**) y Nivel C
(`formCode`, `IsFormula` — núcleo real de codificación). La capa legacy postulada se retiró en F7a; lo
que había sobre `⊢` (`Provable`, la versión objeto de G1), con [ADR‑115](../DECISIONS.md).
**Last updated:** 2026-10-04 · Lean v4.31.0 — Gödel I/II, ya no vacuos por F1 y condicionales a
`ConsistentH` (ADR‑117). Antes, 2026-10-02 — revisado entero tras retirar la capa `⊢` (ADR‑115):
fuera `Block6`, `encode_cons_inj`/`encode_cons_neq_nil`, `Provable`/`provable_formCode_iff`, y los
meta‑axiomas de F7a marcados como lo que son, un registro.

---

## Descripción de módulos

### 3.12 `Meta/Godel.lean` — Gödelización Nivel B (Fase 18)

**Namespace**: `ROBINSON_PlusPlus.Meta.Godel`
**Status**: ✅ Complete (Nivel B: codificación + Teo G1)
**@importance**: `high`
**@axiom_system**: `none` (meta-codificación pura sobre `Minimal/`; **no añade axiomas**)
**Last updated**: 2026-06-06 (creado)
**Dependencias**: `Axioms` (usa `cons`, `nil`); `FOL.Theorems.Eq`. (Hasta ADR‑115 importaba `Block6`.)

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
```

🗑️ La versión object‑level (`encode_cons_inj`, `encode_cons_neq_nil`: `axioms ⊢ …`, vía `Block6`) se
retiró con la capa `⊢` (ADR‑115).

**Sobre Teo G1**: el enunciado del spec `⌜S⌝ = ⌜S'⌝ ⟹ S = S'` mezcla antecedente
sobre códigos (`Term`) con conclusión meta (`S = S' : List Sym`). La inyectividad
**plena** (`encode_injective`) se establece a nivel meta (Lean), por inducción
estructural sobre la lista vía inyectividad de `cons`/`func`/`G` (`injection` +
`decide` sobre los símbolos `String` distintos). **No requiere `Con(axioms)`**.
Pasar de la versión object-level (retirada, ver arriba) a la conclusión meta sí
requeriría consistencia, por lo que esa conexión interna quedaba para el Nivel C/D.
Ver `GODEL-STATUS.md` §2.

---

### 3.13 `Meta/Provability.lean` — Demostrabilidad Nivel C (Fase 19)

**Namespace**: `ROBINSON_PlusPlus.Meta.Provability`
**Status**: ✅ Complete (Nivel C: codificación de la sintaxis + Def 29/30 + diagonalización)
**@importance**: `high`
**@axiom_system**: `none` (meta-codificación; **no añade axiomas** desde F7a)
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
```

🗑️ `Provable` (`∃ φ, x = formCode φ ∧ axioms ⊢ φ`) se retiró con la capa `⊢` (ADR‑115);
`goedelSentence` (punto fijo de `¬Prov`) se retiró en F7a.

#### Exports — demostrado (consistency-free)

```lean
theorem charsCode_injective {l l'} : charsCode l = charsCode l' → l = l'
theorem strCode_injective   {s t}  : strCode s = strCode t → s = t
theorem termCode_injective  {t t'} : termCode t = termCode t' → t = t'      -- (mutuo)
theorem termsCode_injective {ts ts'} : termsCode ts = termsCode ts' → ts = ts'
theorem formCode_injective  {φ φ'} : formCode φ = formCode φ' → φ = φ'      -- Teo G1 (fórmulas)
theorem isFormula_formCode  (φ) : IsFormula (formCode φ)
```

🗑️ `provable_formCode_iff` (ADR‑115) y `goedelSentence_fixedpoint` (F7a), retirados.

#### 🗑️ REGISTRO — los meta‑axiomas que hubo aquí (postulados, estilo `ax_p_tfa`), retirados en F7a

```lean
axiom Dem : Term → Term → Prop                                              -- Def 30
axiom dem_iff_provable (φ) : (axioms ⊢ φ) ↔ ∃ d, Dem d (formCode φ)         -- Teo Meta
axiom provFormula : Formula                                                 -- Prov(x) object-level
axiom provFormula_repr (φ) : (axioms ⊢ substFormula 0 (formCode φ) provFormula) ↔ (axioms ⊢ φ)
axiom diagonal_lemma (φ) : ∃ ψ, axioms ⊢ (ψ ⇔ substFormula 0 (formCode ψ) φ) -- punto fijo
```

**Sobre el alcance**: toda la **codificación + inyectividad** se demuestra sin postular nada.
Los meta‑axiomas de arriba se retiraron en F7a: la aritmetización (`Dem`, `Meta/HilbertSeq.lean`), la
representabilidad y el punto fijo viven hoy como teoremas sobre `Prf` en el Nivel D
([Incompletitud](REFERENCE-Incompleteness.md)), donde Gödel I/II son `goedel_first_prf`/
`goedel_second_prf` — ⛔ vacuos por `[AnclaEq]` (F1, ADR‑114) hasta ADR‑117 (2026‑10‑04); hoy su única
hipótesis es `ConsistentH` (el ancla es el teorema `prf_ancla`); ✏️ desde ADR‑120 (2026‑10‑05) la descarga `consistencia`, un modelo de los 142, y `goedel_I`/`goedel_II` van sin hipótesis.

---


---

← Índice raíz: [REFERENCE.md](../REFERENCE.md) · Siguiente rama: [Incompletitud](REFERENCE-Incompleteness.md)

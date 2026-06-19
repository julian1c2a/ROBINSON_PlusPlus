# Technical Reference — ROBINSON_PlusPlus

**Last updated:** 2026-06-19 — **Gödel Nivel D REAL — Primer Teorema de Gödel REAL sin postulados**. Cadena completa sobre el cálculo de Hilbert finitario `Prf`: `Hilbert`/`HilbertSeq` (cálculo + verificador decidible + `dem_tracks`), `CodeArith`/`SubstArith`/`StepArith` (aritmética de códigos + sustitución/lift De Bruijn), `CheckArith` (verificador object `validProofFn` 18 reglas + `provFormulaC` Σ₁), **`Representability`** (`repr_pos : Prf φ → axioms ⊢ provCodeC φ`), **`Necessitation`** (D1 + Gödel I modular), **`Diagonal`** (`tc_arith` código-del-código + `diag_arith` + **`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`** + **`goedel_first_real`**), **`CodeDistinct`** (aritmética negativa `formCode_ne`). Soundness de `thy` vía `coreAxioms`/`formCodeM` (`provCodeC` fiel). Todo extensión definicional de `Minimal.axioms`; `#print axioms` de los resultados Gödel = solo ω-reglas ambiente, **ningún postulado de derivabilidad**. **35 módulos** (Minimal 11 + Meta 13 + Full 11), 0 sorrys, **49 jobs**. Pendiente: `⊢¬provCodeC` (Π₁, necesita inducción Fase 5) + D2/D3 → Gödel II. Plan: [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).
**Author**: Julián Calderón Almendros
**Lean version**: v4.29.1

---

## 0 · Naming Conventions Guide for the Reader

This project adopts [Mathlib](https://leanprover-community.github.io/contribute/naming.html)-style naming conventions. See `NAMING-CONVENTIONS.md` for the full reference and 12 formation rules.

### 0.1 Capitalization

- **Theorems/lemmas** (Prop): `snake_case` — `teo_2_7`, `mul_two_lt_mono`, `cantor_uniqueness`
- **Prop definitions** (predicates): `UpperCamelCase` — `IsFunction` (planned in Block7)
- **Functions/values**: `lowerCamelCase` — `pair`, `cantor_func`, `w_candidate`
- **Axioms**: `axNN_descriptor` or `ax_TagDescriptor` — `ax13_lt_def`, `ax_L0_cons_def`

### 0.2 Symbol-to-Word Dictionary

| Symbol | Name | | Symbol | Name | | Symbol | Name |
|--------|------|---|--------|------|---|--------|------|
| ∈ | `mem` / `In` | | + | `add` | | σ | `succ` |
| = | `eq` | | * | `mul` | | τ | `pred` |
| ≠ | `ne` | | − | `sub` | | √ | `sqrt` |
| ≤ | `le` | | / | `div` | | 0 | `zero` |
| < | `lt` | | ^ | `pow` | | 1 | `one` |
| ¬ | `not` / `neg` | | ∣ | `dvd` | | 2 | `two` |
| ⇔ | `iff` | | ↔ | `iff` | | ∅ | `empty` |
| ⇒ | `imp` (impl) | | ∨ | `lor` (or) | | ∧ | `land` (and) |

---

## 1 · Module Overview

### 1.1 Module Table

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Minimal/Axioms.lean` | `…Minimal.Axioms` | `FOL.FOL`, `FOL.Theorems.Eq` | ✅ Complete |
| `Minimal/Theorems/Block1.lean` | `…Block1` | `Axioms`, `FOL.Tactics` | ✅ Complete |
| `Minimal/Theorems/Block2.lean` | `…Block2` | `Axioms`, `Block1` | ✅ Complete |
| `Minimal/Theorems/Block3.lean` | `…Block3` | `Axioms`, `Block1`, `Block2` | ✅ Complete |
| `Minimal/Theorems/Block4.lean` | `…Block4` | `Axioms`, `Block1`, `Block3` | ✅ Complete |
| `Minimal/Theorems/Block4_C5.lean` | `…Block4_C5` | `Axioms`, `Block1`, `Block2`, `Block3` | ✅ Complete |
| `Minimal/Theorems/Block4_C6_C7.lean` | `…Block4_C6_C7` | `Axioms`, `Block1`–`Block4_C5` | ✅ Complete |
| `Minimal/Theorems/Block5.lean` | `…Block5` | `Axioms`, `Block1`, `Block3`, `Block4`, `Block4_C5`, `Block4_C6_C7` | ✅ Complete |
| `Minimal/Theorems/Block6.lean` | `…Block6` | `Axioms`, `Block1`, `Block4`, `Block5` | ✅ Complete |
| `Minimal/Theorems/Block7.lean` | `…Block7` | `Axioms`, `Block1`, `Block4`, `Block4_C6_C7`, `Block5` | ✅ Complete |
| `Minimal/Theorems/Block8.lean` | `…Block8` | `Axioms`, `Block1`, `Block2`, `Block4_C5` | ✅ Complete (Fase 17 + Ax-P TFA; +10 teoremas: álgebra de `Dvd` y corolarios TFA) |
| `Meta/Godel.lean` | `…Meta.Godel` | `Axioms`, `Block6` | ✅ Complete (Nivel B: `G`, `⌜·⌝`, Teo G1) |
| `Meta/Provability.lean` | `…Meta.Provability` | `Axioms`, `Meta.Godel`, `FOL.*` | ✅ Complete (Nivel C: `formCode`, `IsFormula`, `Dem`, `diagonal_lemma`, `goedelSentence`) |
| `Meta/Incompleteness.lean` | `…Meta.Incompleteness` | `Axioms`, `Meta.Godel`, `Meta.Provability`, `FOL.*` | ✅ Complete (Nivel D: Gödel I + Gödel II vía D2/D3 postulados) |
| `Meta/Hilbert.lean` | `…Meta.Hilbert` | `Axioms`, `FOL.*` | ✅ Nivel D real F0: `Prf₀`/`Prf` + puentes (`dne` aislado) |
| `Meta/HilbertSeq.lean` | `…Meta.HilbertSeq` | `Meta.Hilbert`, `Meta.Godel`, `Meta.Provability` | ✅ Nivel D real F1: `checkProof`, `prf_iff_derivation`, `Dem` concreto, `dem_tracks` |
| `Meta/CodeArith.lean` | `…Meta.CodeArith` | `Meta.Godel`, `Full.Numerals` | ✅ Nivel D real F2.1: `numeral_bridge`, `gnum_*` |
| `Meta/SubstArith.lean` | `…Meta.SubstArith` | `Meta.Provability`, `Meta.CodeArith` | ✅ Nivel D real F2.2: `substTerm_arith`/`substFormula_arith`/`liftTerm_arith`/`liftFormula_arith` (ecuaciones en `Minimal.axioms`) |
| `Meta/StepArith.lean` | `…Meta.StepArith` | `Meta.SubstArith` | ✅ Nivel D real F2.3: `q1/q2/leibniz_concl_code` (reconocimiento de instancias de axioma) |
| `Meta/CheckArith.lean` | `…Meta.CheckArith` | `Meta.StepArith` | ✅ Nivel D real F2.4: `validProofFn` (17 step lemmas) + `provFormulaC` Σ₁ |
| `Full/Induction.lean` | `…Full` | `Axioms`, `FOL.*` | ✅ ax6/7/10/11/12/18/19 derivados |
| `Full/Mod2.lean` | `…Full` | `Axioms`, `Block1`, `Full.Induction` | ✅ ax21/ax24 (Opción C.2) |
| `Full/Lists.lean` | `…Full` | `Axioms`, `Full.Induction` | ✅ ax_C3/ax_L3 (`ax_list_induction`) |
| `Full/StrongInduction.lean` | `…Full` | `Axioms`, `Full.Induction` | ✅ inducción fuerte DERIVADA |
| `Full/Numerals.lean` | `…Full` | `Axioms`, `Block1`, `Full.Induction` | ✅ puente `numeral` + homomorfismo |
| `Full/Bounded.lean` | `…Full` | `Axioms`, `Full.{Induction,StrongInduction,Numerals}` | ✅ `le_numeral_split` |
| `Full/Divisibility.lean` | `…Full` | `Axioms`, `Block1`, `Block8`, `Full.*` | ✅ `numeral_dvd`, `divisor_le` |
| `Full/Division.lean` | `…Full` | `Axioms`, `Full.Numerals` | ✅ `division_numeral` |
| `Full/PrimeFactor.lean` | `…Full` | (ℕ pura, sin imports) | ✅ factor primo + factorización + **Euclides + unicidad** |
| `Full/Primality.lean` | `…Full` | `Axioms`, `Block1`, `Block8`, `Full.*` | ✅ `isPrime_numeral` |
| `Full/Factorization.lean` | `…Full` | `Axioms`, `Block8`, `Full.{Numerals,PrimeFactor}` | ✅ **`tfa_numeral`** (TFA completo) |

*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending

**Total**: 25 módulos fuente (Minimal 11 + Meta 3 + Full 11), build verde **39 jobs**, **0 sorrys, 0 warnings**. Las meta-reglas ω de deducción (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) viven en `FOL/MetaRules.lean` (refactor 2026-06-12, re-export desde `Minimal.Axioms`); son `axiom`, no `:= sorry` (ADR-008). Meta-axiomas adicionales: `ax_p_tfa` (Block8), `ax_induction`/`ax_mod2_alternation`/`ax_list_induction` (Full), `Dem`/`diagonal_lemma`/`provFormula`/`provFormula_repr`/`dem_iff_provable` (Provability), `D2`/`D3` (Incompleteness).

---

## 2 · Dependency Graph

```mermaid
graph TD
    subgraph FOL ["Project: FOL"]
        direction LR
        FOL_FOL["FOL.FOL"]
        FOL_Eq["FOL.Theorems.Eq"]
        FOL_Tactics["FOL.Tactics"]
    end

    subgraph RPP ["Project: ROBINSON_PlusPlus"]
        direction TB
        Axioms["Minimal/Axioms"]
        Block1["Block1"]
        Block2["Block2"]
        Block3["Block3"]
        Block4["Block4"]
        Block4_C5["Block4_C5"]
        Block4_C6_C7["Block4_C6_C7"]
        Block5["Block5"]
        Block6["Block6"]
    end

    FOL_FOL --> Axioms
    FOL_Eq --> Axioms
    Axioms --> Block1
    FOL_Tactics --> Block1
    Block1 --> Block2
    Block1 --> Block3
    Block2 --> Block3
    Block1 --> Block4
    Block3 --> Block4
    Block1 --> Block4_C5
    Block2 --> Block4_C5
    Block3 --> Block4_C5
    Block4_C5 --> Block4_C6_C7
    Block1 --> Block4_C6_C7
    Block4 --> Block4_C6_C7
    Block4 --> Block5
    Block4_C5 --> Block5
    Block4_C6_C7 --> Block5
    Block3 --> Block5
    Block5 --> Block6
    Block4 --> Block6
```

---

## 3 · Module Descriptions

### 3.1 `Minimal/Axioms.lean`

**Namespace**: `ROBINSON_PlusPlus.Minimal.Axioms`
**Status**: ✅ Complete — **34 axiomas matemáticos** (25 aritm + 7 listas + 2 factorización) + 5 meta-reglas FOL.
**@axiom_system**: `Minimal`
**@importance**: `foundational`
**Last updated**: 2026-06-06 (Bloque VIII ext.: +pow, +prod_pairs, +4 axiomas)

#### 3.1.1 Language symbols

```lean
def succ_sym  : String := "σ"
def add_sym   : String := "+"
def mul_sym   : String := "*"
def sub_sym   : String := "−"     -- monus
def sqrt_sym  : String := "√"
def div2_sym  : String := "/₂"
def mod2_sym  : String := "%₂"
def proj1_sym : String := "π₁"
def proj2_sym : String := "π₂"
def pred_sym  : String := "τ"
def nil_sym   : String := "[]"
def cons_sym  : String := "::"
def concat_sym: String := "##"
def pow_sym   : String := "^"     -- 2026-06-06, Bloque VIII ext.
def prodp_sym : String := "Π_p"   -- 2026-06-06, Bloque VIII ext.
def lt_sym    : String := "<"
def le_sym    : String := "≤"
def in_sym    : String := "∈"
def zero_sym  : String := "0"
```

> **Nota 2026-06-02**: `proj1_sym`/`proj2_sym` ya **no son símbolos opacos** del lenguaje. `proj1`/`proj2` son ahora defs concretas en `Block4_C6_C7.lean` (`proj1 := x_of_c`, `proj2 := y_of_c`).

#### 3.1.2 Term constructors (computable, no termination proof needed)

```lean
def zero  : Term                               -- 0
def succ  (t : Term) : Term                    -- σt
def add   (t₁ t₂ : Term) : Term                -- t₁ + t₂
def mul   (t₁ t₂ : Term) : Term                -- t₁ · t₂
def sub   (t₁ t₂ : Term) : Term                -- t₁ − t₂
def sqrt  (t : Term) : Term                    -- √t
def div2  (t : Term) : Term                    -- ⌊t/2⌋
def mod2  (t : Term) : Term                    -- t mod 2
def proj1 (t : Term) : Term                    -- π₁(t)
def proj2 (t : Term) : Term                    -- π₂(t)
def pred  (t : Term) : Term                    -- τ(t)
def cons  (h t : Term) : Term                  -- h :: t
def concat (l₁ l₂ : Term) : Term               -- l₁ ## l₂
def pow   (b e : Term) : Term                  -- b^e   (Bloque VIII ext.)
def prod_pairs (l : Term) : Term               -- Π_p l (Bloque VIII ext.)
def sq    (t : Term) : Term := mul t t         -- t²
def one   : Term := succ zero
def two   : Term := succ one
def eight : Term := mul two (mul two two)      -- 8 = 2·(2·2)
def cantor_poly (x y : Term) : Term :=
  add (mul (add x y) (succ (add x y))) (mul two y)
                                               -- (x+y)·(x+y+1) + 2y
def cantor_func (x y : Term) : Term := div2 (cantor_poly x y)
def is_cantor (x y c : Term) : Formula := mul two c =eq cantor_poly x y
def pair (x y : Term) : Term := cantor_func x y
def nil : Term := zero
```

#### 3.1.3 Formula constructors

```lean
def lt (t₁ t₂ : Term) : Formula                -- t₁ < t₂
def le (t₁ t₂ : Term) : Formula := lt t₁ t₂ ∨ t₁ =eq t₂   -- ≤
def In (x l : Term) : Formula                  -- x ∈ l
def land (A B : Formula) : Formula             -- A ∧ B
def lor  (A B : Formula) : Formula             -- A ∨ B
def forall_  (f : Formula) : Formula           -- ∀
def forall_2 (f : Formula) : Formula           -- ∀∀
def forall_3 (f : Formula) : Formula           -- ∀∀∀
```

#### 3.1.4 Notation

```lean
scoped notation:50 t₁ " =eq " t₂ => Formula.eq t₁ t₂
scoped notation:50 t₁ " ≤ " t₂  => le t₁ t₂
scoped notation:50 x  " ∈ " l   => In x l
abbrev ex := @Formula.ex
```

#### 3.1.5 Axiomas matemáticos (30 axiomas en la lista `axioms`: 23 aritméticos + 7 listas)

| # | Nombre | Enunciado matemático |
|---|---|---|
| Ax 2 | `ax2_peano_succ_neq_zero` | ∀ n, σ(n) ≠ 0 |
| Ax 3 | `ax3_peano_succ_inj` | ∀ n, m, σ(n) = σ(m) ⇒ n = m |
| Ax 4 | `ax4_add_zero` | ∀ n, n + 0 = n |
| Ax 5 | `ax5_add_succ` | ∀ n, m, n + σ(m) = σ(n + m) |
| Ax 6 | `ax6_add_comm` | ∀ n, m, n + m = m + n |
| Ax 7 | `ax7_add_assoc` | ∀ n, m, k, (n+m)+k = n+(m+k) |
| Ax 8 | `ax8_mul_zero` | ∀ n, n · 0 = 0 |
| Ax 9 | `ax9_mul_succ` | ∀ n, m, n · σ(m) = (n·m) + n |
| Ax 10 | `ax10_mul_comm` | ∀ n, m, n · m = m · n |
| Ax 11 | `ax11_mul_assoc` | ∀ n, m, k, (n·m)·k = n·(m·k) |
| Ax 12 | `ax12_mul_distrib` | ∀ n, m, k, n·(m+k) = n·m + n·k |
| Ax 13 | `ax13_lt_def` | ∀ n, m, n < m ⇔ ∃ k, n + σ(k) = m |
| Ax 14 | `ax14_sqrt_le` | ∀ n, (√n)² ≤ n |
| Ax 15 | `ax15_lt_succ_sqrt` | ∀ n, n < (σ(√n))² |
| Ax 16 | `ax16_mod2_succ` | ∀ n, mod2(n)=0 ⇔ mod2(σ(n))=1 |
| Ax 17 | `ax17_div_mod_eq` | ∀ n, (div2(n)·2) + mod2(n) = n |
| Ax 18 | `ax18_lt_irrefl` | ∀ n, ¬(n < n) |
| Ax 19 | `ax19_lt_trichotomy` | ∀ a, b, a<b ∨ a=b ∨ b<a |
| Ax 21 | `ax21_mod2_range` | ∀ n, mod2(n)=0 ∨ mod2(n)=1 |
| Ax 24 | `ax24_mod2_of_even` | ∀ n, k, n = 2k ⇒ mod2(n) = 0 |
| Ax 25 | `ax25_pred_zero` | τ(0) = 0 |
| Ax 26 | `ax26_pred_succ` | ∀ n, τ(σ(n)) = n |
| Ax_L0 | `ax_L0_cons_def` | ∀ h, t, cons(h,t) = ⟨h, σ(t)⟩ (vía pair) |
| Ax_L1 | `ax_L1_in_nil` | ∀ x, ¬ In(x, nil) |
| Ax_L2 | `ax_L2_in_cons` | ∀ x, h, t, In(x, cons(h,t)) ⇔ x=h ∨ In(x,t) |
| Ax_L3 | `ax_L3_in_concat` | ∀ x, L, M, In(x, L##M) ⇔ In(x,L) ∨ In(x,M) (requiere inducción) |
| Ax_C1 | `ax_C1_concat_nil` | ∀ L, nil ## L = L |
| Ax_C2 | `ax_C2_concat_cons` | ∀ h, t, L, cons(h,t) ## L = cons(h, t##L) |
| Ax_C3 | `ax_C3_concat_assoc` | ∀ L, M, N, (L##M)##N = L##(M##N) (requiere inducción) |
| Ax 29 | `ax29_sub_witness` | ∀ a, b, b ≤ a ⇒ b + (a−b) = a |
| Ax-Pow-0 | `ax_pow_zero` | ∀ b, b^0 = 1 (Bloque VIII ext.) |
| Ax-Pow-σ | `ax_pow_succ` | ∀ b, e, b^(σe) = b^e · b (Bloque VIII ext.) |
| Ax-ProdP-nil | `ax_prodp_nil` | prod_pairs [] = 1 (Bloque VIII ext.) |
| Ax-ProdP-cons | `ax_prodp_cons` | ∀ p, e, t, prod_pairs ((p,e)::t) = p^e · prod_pairs t (Bloque VIII ext.) |

**Ax 20** (`ax20_eq_decidable`): definido pero NO en la lista — convertido en teorema `eq_decidable` (Block1).
**Ax 27** (`ax27_add_left_cancel`): **ELIMINADO 2026-06-03** — derivable en PA⁻ vía tricotomía (ax19) + monotonía (`lt_add_const_of_le_left`) + irreflexividad (ax18). Ver `add_left_cancel` en `Block4_C6_C7`.
**Ax 22** (`ax22_cantor_proj_exists`): **ELIMINADO 2026-06-02** — `proj1`/`proj2` ya no son símbolos opacos sino defs concretas en `Block4_C6_C7` (`proj1 := x_of_c`, `proj2 := y_of_c`). El contenido de ax22 se demuestra como teorema `proj_is_cantor` allí mismo.
**Ax 23** (`ax23_cantor_proj_uniq`): **ELIMINADO 2026-06-02** — `cantor_uniqueness` (Block4_C6_C7) probado constructivamente; ax23 nunca se usó en código.
**Ax 28** (`ax28_mul_two_cancel`): **ELIMINADO 2026-06-02** — derivable sin inducción, ver `teo_2_11` (Block1). El `def` permanece comentado en `Axioms.lean` como nota histórica.

#### 3.1.6 Meta-reglas FOL (5 `axiom`, ADR-008)

```lean
axiom imp_intro {Γ A B} (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)
axiom gen      {Γ A}   (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) : Γ ⊢ Formula.forall A
axiom raa      {Γ A}   (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A
axiom or_elim  {Γ A B C} (h : Γ ⊢ (A ∨ B)) (h1 : Γ ⊢ A → Γ ⊢ C) (h2 : Γ ⊢ B → Γ ⊢ C) : Γ ⊢ C
axiom ex_elim  {Γ A C}   (h : Γ ⊢ Formula.ex A)
                          (cont : ∀ t, Γ ⊢ substFormula 0 t A → Γ ⊢ C) : Γ ⊢ C
```

#### 3.1.7 Helper theorems

```lean
theorem ax {f : Formula} (h : f ∈ axioms) : axioms ⊢ f
theorem eq_refl  (t : Term)        : Γ ⊢ (t ≐ t)
theorem eq_symm  (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (t₂≐t₁)
theorem eq_trans (h1 : Γ⊢(t₁≐t₂))(h2 : Γ⊢(t₁≐t₃)) : Γ ⊢ (t₂≐t₃)  -- non-standard: shared LHS
theorem eq_congr_succ {t₁ t₂} (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (succ t₁ ≐ succ t₂)
theorem eq_congr_pred {t₁ t₂} (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (pred t₁ ≐ pred t₂)
theorem eq_congr_add_left  {u t₁ t₂} (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (add u t₁ ≐ add u t₂)
theorem eq_congr_add_right {u t₁ t₂} (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (add t₁ u ≐ add t₂ u)
theorem eq_congr_mul_left  {u t₁ t₂} (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (mul u t₁ ≐ mul u t₂)
theorem eq_congr_mul_right {u t₁ t₂} (h : Γ ⊢ (t₁≐t₂)) : Γ ⊢ (mul t₁ u ≐ mul t₂ u)
theorem spec     (h : Γ ⊢ Formula.forall A)(t : Term) : Γ ⊢ substFormula 0 t A
def     mp       (h1 : Γ ⊢ (A⇒B))(h2 : Γ ⊢ A) : Γ ⊢ B
def     and_intro / and_elim_left / and_elim_right
def     or_intro_left / or_intro_right
def     ex_intro (t : Term)(h : Γ ⊢ substFormula 0 t A) : Γ ⊢ Formula.ex A
def     iff_mp / iff_mpr
def     false_elim (h : Γ ⊢ ⊥) : Γ ⊢ φ
theorem eq_subst (h_eq : Γ⊢(t₁≐t₂))(h_phi : Γ ⊢ substFormula 0 t₁ A) : Γ ⊢ substFormula 0 t₂ A
```

---

### 3.2 `Block1.lean` — Aritmética Básica

**Namespace**: `ROBINSON_PlusPlus.Minimal.Theorems.Block1`
**Status**: ✅ Complete
**@axiom_system**: `Minimal`
**@importance**: `high`
**Last updated**: 2026-06-02 (añadidos `mul_two_succ_ne_zero`, `mul_two_lt_mono`; reprobado `teo_2_11` directamente)

**Constantes**: `three`, `four` (`def`).

#### Teoremas (orden de declaración)

| Nombre | Enunciado | Notas |
|---|---|---|
| `teo_1_1` … `teo_1_7` | 1+0=1, 0+1=1, 1+1=2, 2+1=3, 1+2=3, 3+1=4, 2+2=4 | evaluación constantes |
| `teo_1_8`, `teo_1_9`, `teo_1_10` | 1·1=1, 2·1=2, 2·2=4 | |
| `teo_1_11`, `teo_1_12`, `teo_1_13_*` | desigualdades entre 0, 1, 2, 3 | |
| `teo_2_1`, `teo_2_2` | ∀n, n+0=n y 0+n=n | |
| `teo_2_3`, `teo_2_4` | ∀n, n·0=0 y 0·n=0 | |
| `teo_2_5`, `teo_2_6` | ∀n, n·1=n y 1·n=n | |
| `teo_2_7` | ∀n, 2·n = n+n | clave para muchos lemas |
| **`mul_two_succ_ne_zero` (k)** | ¬(2·σ(k) = 0) | NUEVO 2026-06-02; helper para teo_2_11 |
| **`mul_two_lt_mono` ({a,b}, h:a<b)** | 2a < 2b | NUEVO 2026-06-02; monotonía estricta |
| `teo_2_8` | ∀n, σ(n) = n+1 | |
| `teo_2_9` | a+b=0 ⇒ a=0 ∧ b=0 | |
| `teo_2_10` | a·b=0 ⇒ a=0 ∨ b=0 | |
| **`teo_2_11`** | ∀a, b, 2a=2b ⇒ a=b | REPROBADO 2026-06-02 sin inducción; ax28 eliminado |
| `teo_3_11` | ∀n, n≠0 ⇒ ∃m, σ(m)=n (ex-Ax 4) | predecesor totalizado vía tricotomía |
| `eq_decidable` | ∀n, m, n=m ∨ n≠m (= ax20) | demostrado vía tricotomía + sustitución |

---

### 3.3 `Block2.lean` — Raíz cuadrada y orden

**Namespace**: `…Block2`
**Status**: ✅ Complete
**@importance**: `high`

#### Exports

```lean
theorem sqrt_sq_le (n : Term) : Γ ⊢ (sq (sqrt n) ≤ n)
theorem lt_succ_sqrt_sq (n : Term) : Γ ⊢ lt n (sq (succ (sqrt n)))
theorem sq_eq_zero_imp_zero (n : Term) : Γ ⊢ ((sq n =eq zero) ⇒ (n =eq zero))
theorem sqrt_zero : Γ ⊢ (sqrt zero =eq zero)
theorem sqrt_one  : Γ ⊢ (sqrt one  =eq one)
theorem sqrt_unique_of_bounds {k n} :
  Γ ⊢ ((sq k ≤ n) ∧ lt n (sq (succ k))) ⇒ (k =eq sqrt n)
theorem succ_le_of_lt {a b} (h : Γ ⊢ lt a b) : Γ ⊢ ((succ a) ≤ b)
theorem lt_le_trans {a b c} (h_lt : Γ⊢lt a b)(h_le : Γ⊢(b≤c)) : Γ ⊢ lt a c
theorem le_lt_trans {a b c} (h_le : Γ⊢(a≤b))(h_lt : Γ⊢lt b c) : Γ ⊢ lt a c
theorem le_trans    {a b c} (h_ab : Γ⊢(a≤b))(h_bc : Γ⊢(b≤c)) : Γ ⊢ (a≤c)
theorem zero_le (n : Term) : Γ ⊢ (zero ≤ n)
theorem mul_le_mono_right {a b c}(h_le : Γ⊢(a≤b))(h_c_pos : Γ⊢lt zero c) : Γ ⊢ (mul a c ≤ mul b c)
theorem sq_le_mono {a b}(h : Γ⊢(a≤b)) : Γ ⊢ (sq a ≤ sq b)
```

---

### 3.4 `Block3.lean` — div2 / mod2

**Namespace**: `…Block3`
**Status**: ✅ Complete
**@importance**: `medium`

**Nota de tamaño** (~1900 líneas): documentado en el header del archivo. Sin inducción, los `div2_n`/`mod2_n` se enumeran por numeral. En `Intermediate/` se reduce a ~5 teoremas.

#### Teoremas públicos

```lean
theorem mod2_zero  : Γ ⊢ (mod2 zero  =eq zero)
theorem mod2_one   : Γ ⊢ (mod2 one   =eq one)
theorem mod2_two   : Γ ⊢ (mod2 two   =eq zero)
theorem mod2_three : Γ ⊢ (mod2 three =eq one)
theorem mod2_four  : Γ ⊢ (mod2 four  =eq zero)
theorem div2_zero  : Γ ⊢ (div2 zero  =eq zero)
theorem div2_one   : Γ ⊢ (div2 one   =eq zero)
theorem div2_two   : Γ ⊢ (div2 two   =eq one)
theorem div2_three : Γ ⊢ (div2 three =eq one)
theorem div2_four  : Γ ⊢ (div2 four  =eq two)
theorem mod2_range (n : Term) : Γ ⊢ ((mod2 n =eq zero) ∨ (mod2 n =eq one))
                                                                -- delega a ax21
```

---

### 3.5 `Block4.lean` — Función de Cantor (Bloque IV: paridad, totalidad, inyectividad)

**Namespace**: `…Block4`
**Status**: ✅ Complete
**@importance**: `high`
**Last updated**: 2026-06-02 (cantor_injective_c ahora usa `teo_2_11` real)

#### Defs

```lean
def w_w_plus_1 (w : Term) : Term := mul w (succ w)        -- w·(w+1)
```

#### Exports

```lean
theorem w_mul_w_plus_one_eq_sq_w_add_w (w) : Γ ⊢ (mul w (succ w) =eq add (sq w) w)
                                                          -- Teo 6.1: w(w+1)=w²+w
theorem parity_lemma_case_even (w) : …                   -- mod2(w)=0 ⇒ ∃k, w(w+1)=2k
theorem parity_lemma_case_odd  (w) : …                   -- mod2(w)=1 ⇒ ∃k, w(w+1)=2k
theorem parity_lemma (w) : Γ ⊢ ex (mul (liftTerm 0 w)(succ (liftTerm 0 w)) =eq mul two #0)
                                                          -- Lema P1: ∀w, ∃k, w(w+1)=2k
theorem cantor_poly_term1_eq_sq_add (x y) : Γ ⊢ (w_w_plus_1 (add x y) =eq add (sq (add x y)) (add x y))
                                                          -- Teo C1
theorem cantor_poly_is_even (x y) : Γ ⊢ ex (liftTerm 0 (cantor_poly x y) =eq mul two #0)
                                                          -- Teo 7.2: cantor_poly par
theorem cantor_totality (x y) : Γ ⊢ ex (mul two #0 =eq liftTerm 0 (cantor_poly x y))
                                                          -- Teo C2: ∃c, Cantor(x,y,c)
theorem cantor_injective_c (x y c c') : Γ ⊢ land (is_cantor x y c)(is_cantor x y c') ⇒ (c =eq c')
                                                          -- Teo C4
```

---

### 3.6 `Block4_C5.lean` — Lema C5 (Bloque IV Fase 9) + ~25 helpers exportados

**Namespace**: `…Block4_C5`
**Status**: ✅ Complete
**@importance**: `high`

#### Defs

```lean
def w_candidate (c : Term) : Term := div2 (pred (sqrt (add (mul eight c) one)))
                                                          -- w = ⌊(√(8c+1)-1)/2⌋
```

#### Exports — Teoremas principales

```lean
theorem lemma_C5 (c) : Γ ⊢ ex (land
    (le (mul #0 (succ #0)) (mul two (liftTerm 0 c)))
    (lt (mul two (liftTerm 0 c)) (mul (succ #0) (succ (succ #0)))))
                                                          -- ∀c, ∃w, w(w+1) ≤ 2c < (w+1)(w+2)
theorem lemma_C5_unique {c w w'} (h_w : …)(h_w' : …) : Γ ⊢ (w =eq w')
                                                          -- Teo 10.1: unicidad de w
theorem cantor_bounds {x y c} (h : Γ⊢(mul two c =eq …)) : Γ ⊢ land (…) (…)
                                                          -- C5 bounds para w := x+y
```

#### Exports — Helpers reutilizables de orden / aritmética / álgebra

```lean
-- Reescritura por igualdad
theorem le_rewrite / lt_rewrite (h: …)(ha)(hb) : …
-- Manipulación add
theorem le_self_add (a b) : Γ ⊢ le a (add a b)
theorem le_add_one_cancel (h : add x one ≤ add y one) : Γ ⊢ (x ≤ y)
theorem le_add_const_of_le (h : a≤b) : Γ ⊢ (add a c ≤ add b c)
theorem le_add_const_of_le_left (h : a≤b) : Γ ⊢ (add c a ≤ add c b)
theorem lt_add_const_of_le_left (h : lt a b) : Γ ⊢ lt (add c a) (add c b)
-- σ y τ
theorem lt_zero_succ (a) : Γ ⊢ lt zero (succ a)
theorem le_of_succ_le_succ / succ_le_succ_of_le
theorem succ_pred_of_pos (h : 0 < s) : Γ ⊢ (succ (pred s) =eq s)
-- mul orden
theorem mul_lt_mono_right (h_lt)(h_c_pos) : Γ ⊢ lt (mul a c)(mul b c)
theorem le_mul_right / le_mul_left
theorem le_of_mul_le_mul_right / le_of_mul_le_mul_left
theorem sq_lt_mono (h : lt a b) : Γ ⊢ lt (sq a)(sq b)
-- ring algebra (variantes ' para usar como teoremas, no spec'd axiomas)
theorem add_comm' / add_assoc' / mul_comm' / mul_assoc' / mul_distrib' / mul_distrib_right'
```

---

### 3.7 `Block4_C6_C7.lean` — Sobreyectividad y Unicidad Cantor

**Namespace**: `…Block4_C6_C7`
**Status**: ✅ Complete
**@importance**: `high`
**Last updated**: 2026-06-03 (proj1/proj2 defs concretas; `proj_is_cantor` reemplaza ax22; `mod2_of_even` movido aquí desde Block5)

#### Defs

```lean
def w_of_c (c) : Term := w_candidate c
def y_of_c (c) : Term := sub c (div2 (mul (w_candidate c) (succ (w_candidate c))))
def x_of_c (c) : Term := sub (w_candidate c) (y_of_c c)
def proj1 (c) : Term := x_of_c c    -- ELIMINA ax22; antes era símbolo opaco en Axioms.lean
def proj2 (c) : Term := y_of_c c    -- idem
```

#### Exports

```lean
theorem add_left_cancel {a b c} (h : Γ⊢(add a c =eq add b c)) : Γ ⊢ (a =eq b)
                                                          -- PA⁻ style: tricotomía + monotonía + ax18 (REEMPLAZA ax27, eliminado 2026-06-03)
theorem mod2_of_even {n k} (h : Γ⊢(n =eq mul two k)) : Γ ⊢ (mod2 n =eq zero)
                                                          -- delega a ax24 (movido aquí desde Block5 el 2026-06-03)
theorem proj_is_cantor (c) : Γ ⊢ (mul two c =eq cantor_poly (proj1 c) (proj2 c))
                                                          -- REEMPLAZA ax22 constructivamente
theorem cantor_surjectivity (c) : Γ ⊢ ex (ex (is_cantor #1 #0 (liftTerm 0 (liftTerm 0 c))))
                                                          -- Teo C6: ∀c, ∃x y, Cantor(x,y,c) (wrapper de proj_is_cantor)
theorem cantor_uniqueness (x y x' y' c) :
    Γ ⊢ land (is_cantor x y c)(is_cantor x' y' c) ⇒ land (x=eq x')(y=eq y')
                                                          -- Teo C7
```

---

### 3.8 `Block5.lean` — Pares y proyecciones (Bloque V)

**Namespace**: `…Block5`
**Status**: ✅ Complete
**@importance**: `medium`

#### Exports

```lean
-- mod2_of_even FUE MOVIDO a Block4_C6_C7 (2026-06-03) para eliminar dependencia
-- circular: lo necesita `proj_is_cantor` allí y Block5 importa C6_C7.
theorem is_cantor_pair (x y) : Γ ⊢ (mul two (pair x y) =eq cantor_poly x y)
                                                          -- LEMA CLAVE: ∀x,y, is_cantor(x,y, pair x y)
theorem proj1_pair_eq_x (x y) : Γ ⊢ (proj1 (pair x y) =eq x)        -- Teo C8 (usa proj_is_cantor, ya no ax22)
theorem proj2_pair_eq_y (x y) : Γ ⊢ (proj2 (pair x y) =eq y)        -- Teo C9 (usa proj_is_cantor)
theorem pair_proj_eq_c (c)    : Γ ⊢ (pair (proj1 c)(proj2 c) =eq c) -- Teo C10 (usa proj_is_cantor)
theorem pair_inj {x y x' y'} : Γ ⊢ (pair x y =eq pair x' y') ⇒ land (x=eq x')(y=eq y')
                                                          -- Teo C11
```

---

### 3.9 `Block6.lean` — Listas (Bloque VI)

**Namespace**: `…Block6`
**Status**: ✅ Complete
**@importance**: `medium`

#### Exports

```lean
theorem cons_neq_nil (h t) : Γ ⊢ neg (cons h t =eq nil)             -- Teo L1
theorem cons_inj {h t h' t'} : Γ ⊢ (cons h t =eq cons h' t') ⇒ land (h=eq h')(t=eq t')
                                                          -- Teo L2 (vía ax_L0 + pair_inj + ax3)
theorem in_cons_self_nil (x)    : Γ ⊢ In x (cons x nil)             -- Teo L4
theorem in_cons_nil_imp_eq {x h}: Γ ⊢ In x (cons h nil) ⇒ (x =eq h) -- Teo L5
theorem concat_singletons (x y) : Γ ⊢ (concat (cons x nil)(cons y nil) =eq cons x (cons y nil))
                                                          -- Teo L6
theorem concat_assoc (L M N)    : Γ ⊢ (concat (concat L M) N =eq concat L (concat M N))
                                                          -- Teo L7 (delega a ax_C3, inducción)
theorem in_concat_iff (x L M)   : Γ ⊢ In x (concat L M) ⇔ lor (In x L)(In x M)
                                                          -- Teo L8 (delega a ax_L3, inducción)
```

---

### 3.10 `Block7.lean` — Funciones discretas (Bloque VII)

**Namespace**: `…Block7`
**Status**: ✅ Complete
**@importance**: `high`
**Last updated**: 2026-06-03 (creado: cierra el alcance Cantor + Pares + Listas + Funciones de `TuplasFuncionesYListas.md`)

#### Defs

```lean
def IsFunction (F : Term) : Prop :=
  ∀ p1 p2 : Term, (axioms ⊢ In p1 F) → (axioms ⊢ In p2 F) →
                  (axioms ⊢ (proj1 p1 =eq proj1 p2)) →
                  (axioms ⊢ (p1 =eq p2))                              -- Def 21
def Functional (F : Term) : Prop :=
  ∀ x y y' : Term, (axioms ⊢ In (pair x y) F) → (axioms ⊢ In (pair x y') F) →
                   (axioms ⊢ (y =eq y'))                              -- Def 24 (Map inlineado)
```

#### Exports

```lean
theorem teo_F1 : IsFunction nil                                       -- Teo F1 (vacuo vía ax_L1)
theorem teo_F2 {F x y y'} (h_isF : IsFunction F)
    (h_xy : Γ ⊢ In (pair x y) F) (h_xy' : Γ ⊢ In (pair x y') F) :
    Γ ⊢ (y =eq y')                                                    -- Teo F2 (eval única)
theorem teo_F3 (F : Term) : IsFunction F ↔ Functional F               -- Teo F3 (isomorfismo)
```

**Nota de estilo**: `IsFunction`/`Functional` son meta-predicados Lean (`Term → Prop`), no `Formula` con `forall_2/3`. Esto evita el manejo manual de De Bruijn (`liftTerm`/`substTerm`) en los cuantificadores externos; el contenido FOL queda en los cuerpos derivables (`axioms ⊢ ...`).

---

### 3.11 `Block8.lean` — Primos y factorización (Bloque VIII, Fase 17 completa)

**Namespace**: `…Block8`
**Status**: ✅ Complete (Fase 17 completa con `IsFactorization` + `Ax-P` TFA)
**@importance**: `high`
**Last updated**: 2026-06-06 (extensión con Bloque VIII extendido)

#### Defs

```lean
def Dvd (a b : Term) : Prop := ∃ q : Term, axioms ⊢ (mul a q =eq b)   -- Def 25.a
def IsPrime (p : Term) : Prop :=
  (axioms ⊢ lt one p) ∧                                                 -- p ≥ 2
  ∀ d : Term, Dvd d p → axioms ⊢ ((d =eq one) ∨ (d =eq p))             -- Def 25

def IsFactorization (f n : Term) : Prop :=
  (axioms ⊢ (prod_pairs f =eq n)) ∧                                     -- Def 26
  ∀ p e : Term, (axioms ⊢ In (pair p e) f) →
    (IsPrime p ∧ axioms ⊢ lt zero e)
```

#### Exports — Divisibilidad y primalidad (Def 25)

```lean
theorem dvd_refl (a) : Dvd a a                                          -- testigo q := one
theorem dvd_one  (a) : Dvd one a                                        -- testigo q := a
theorem dvd_zero (a) : Dvd a zero                                       -- testigo q := zero
theorem isPrime_zero_inconsistent : IsPrime zero → axioms ⊢ ⊥           -- lt one zero ⇒ ⊥
theorem isPrime_one_inconsistent  : IsPrime one  → axioms ⊢ ⊥           -- lt one one ⇒ ax18
```

#### Exports — Potencia y producto sobre listas de pares (Bloque VIII ext.)

```lean
-- Instancias inmediatas de los axiomas (Axioms.lean):
theorem pow_zero (b)         : Γ ⊢ (pow b zero =eq one)                 -- ax_pow_zero
theorem pow_succ (b e)       : Γ ⊢ (pow b (succ e) =eq mul (pow b e) b) -- ax_pow_succ
theorem prod_pairs_nil       : Γ ⊢ (prod_pairs nil =eq one)             -- ax_prodp_nil
theorem prod_pairs_cons (p e t) :
  Γ ⊢ (prod_pairs (cons (pair p e) t) =eq mul (pow p e) (prod_pairs t)) -- ax_prodp_cons
```

#### Exports — Factorización (Def 26 + Ax-P)

```lean
theorem isFactorization_nil_one : IsFactorization nil one
  -- Caso base: [] factoriza al 1. Cuantificación sobre elementos vacuamente
  -- satisfecha por explosión object-level vía ax_L1_in_nil.

-- Meta-axioma (estilo imp_intro/gen/raa/or_elim/ex_elim):
axiom ax_p_tfa : ∀ n : Term, axioms ⊢ lt zero n →
  ∃ f : Term, IsFactorization f n ∧
    ∀ f' : Term, IsFactorization f' n → axioms ⊢ (f =eq f')
```

#### Exports — Álgebra de `Dvd` (sin inducción, 2026-06-06)

```lean
theorem dvd_trans {a b c}    : Dvd a b → Dvd b c → Dvd a c          -- testigo q₁·q₂
theorem dvd_mul_right (a b)  : Dvd a (mul a b)                       -- testigo b (refl)
theorem dvd_mul_left  (a b)  : Dvd b (mul a b)                       -- testigo a (comm)
theorem dvd_mul_of_dvd_left  {a b} : Dvd a b → ∀ c, Dvd a (mul b c) -- testigo q·c
theorem dvd_mul_of_dvd_right {a c} : Dvd a c → ∀ b, Dvd a (mul b c) -- testigo q·b (comm)
theorem dvd_add {a b c}      : Dvd a b → Dvd a c → Dvd a (add b c)  -- testigo q₁+q₂ (distrib)
```

#### Exports — Corolarios del TFA (`ax_p_tfa`, 2026-06-06)

```lean
theorem factorization_exists (n) : axioms ⊢ lt zero n → ∃ f, IsFactorization f n
theorem factorization_unique {n f f'} :
  axioms ⊢ lt zero n → IsFactorization f n → IsFactorization f' n → axioms ⊢ (f =eq f')
theorem lt_zero_one : axioms ⊢ lt zero one                          -- testigo k=0 en ax13
theorem factorization_one_eq_nil {f} : IsFactorization f one → axioms ⊢ (f =eq nil)
```

**Fuera de scope `Minimal/`**: el **lema de Euclides** (`IsPrime p → p ∣ a·b → p ∣ a ∨ p ∣ b`)
y la **multiplicatividad** (`prod_pairs (concat f g) = prod_pairs f · prod_pairs g`) requieren
`prod_pairs_concat` (recursión sobre la lista), no demostrable sin inducción. Se difieren a
`Intermediate/`/`Full/`.

**Forma de los teoremas de no-primalidad**: NO podemos probar `¬IsPrime zero` directamente en Lean (requeriría meta-consistencia, que no demostramos). En su lugar, probamos "`IsPrime zero` derivaría `axioms ⊢ ⊥`" — el contenido genuino del enunciado.

**Sobre la formulación de `IsFactorization`**: meta-Prop combinando derivación object-level (`prod_pairs f =eq n`) con cuantificación meta-level sobre los pares `(p,e)` que aparecen como elementos de `f`. La permisividad sobre la forma de los elementos (no obliga a que sean literalmente `pair p e`) queda compensada por `ax_prodp_cons`, que sólo se activa en cabezas `pair p e`.

**Sobre `Ax-P` (TFA)**: justificado en spec §Apéndice B.4 como axioma porque requiere inducción fuerte para ser derivable. En `Minimal/` se adopta meta-axiomáticamente (estilo `imp_intro`, etc.); en `Intermediate/` será un teorema mediante inducción fuerte sobre `n`.

**Fases 18-19 (Gödelización, autorreferencia)**: requieren meta-codificación (G : símbolos → ℕ, ⌜·⌝, IsFormula, Dem). El **Nivel B** (G, ⌜·⌝, Teo G1) ya está implementado en `Meta/Godel.lean` (ver §3.12). Los Niveles C-D (IsFormula, Dem, incompletitud) siguen pendientes.

---

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

### 3.14 `Full/` — Inducción general, representabilidad y TFA (Eje 4)

**Namespace**: `ROBINSON_PlusPlus.Full`
**Status**: ✅ Fragmento aritmético + listas de Minimal derivado; **TFA completo**
**@importance**: `high`
**@axiom_system**: `Full` (inducción general como axioma object-level + meta-axiomas)
**Last updated**: 2026-06-12
**Módulos** (11): `Induction`, `Mod2`, `Lists`, `StrongInduction`, `Numerals`, `Bounded`, `Divisibility`, `Division`, `PrimeFactor`, `Primality`, `Factorization`.

> **Nota histórica**: `Intermediate/Induction.lean` (prototipo de inducción meta, Eje 3) fue **eliminado 2026-06-11**: el sistema con Φ finito es el caso particular de Full con inducción general, sin valor técnico añadido. Toda la inducción vive en `Full/`.

#### `Full/Induction.lean` — inducción general object-level

```lean
def inductionFormula (φ : Formula) : Formula                 -- φ(0) ⇒ ((∀n φ(n)⇒φ(σn)) ⇒ ∀n φ(n))
axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ
theorem induction_object {φ} (base step) : axioms ⊢ Formula.forall φ
-- Composición De Bruijn lift-aware (caso multivariable):
theorem substFormula_succ_lift_gen / step_reduce …
-- Axiomas de Minimal derivados como TEOREMAS:
theorem add_comm_thm : axioms ⊢ ax6_add_comm        -- ax6 ;  add_assoc_ax (ax7)
theorem mul_comm_thm : axioms ⊢ ax10_mul_comm       -- ax10 ; mul_assoc_ax (ax11), mul_distrib_ax (ax12)
theorem lt_irrefl_thm : axioms ⊢ ax18_lt_irrefl     -- ax18 ; lt_trichotomy_thm (ax19)
-- + lemas de orden: lt_succ_self, not_lt_zero, lt_succ_of_lt, zero_lt_succ, zero_or_succ_ax, lt_succ_cases
```

#### `Full/Mod2.lean` — ax21, ax24 (Opción C.2)

```lean
axiom ax_mod2_alternation : axioms ⊢ ∀. (add (mod2 (σ #0)) (mod2 #0) =eq one)  -- caracteriza mod2
theorem mod2_range_thm   : axioms ⊢ ax21_mod2_range      -- ax21 (inducción + alternancia)
theorem mod2_of_even_thm : axioms ⊢ ax24_mod2_of_even    -- ax24
```

Hallazgo: `ax16`+`ax17` dejan `mod2` subdeterminado (modelos con `mod2(σn)≥2`); `ax_mod2_alternation` lo cierra. Conservativo respecto a Minimal.

#### `Full/Lists.lean` — ax_C3, ax_L3 (inducción estructural sobre listas)

```lean
axiom ax_list_induction (φ : Term → Formula) (base : Γ ⊢ φ nil)
    (step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)) : ∀ L, Γ ⊢ φ L     -- meta-axioma
theorem concat_assoc_thm : axioms ⊢ ax_C3_concat_assoc   -- ax_C3
theorem in_concat_thm    : axioms ⊢ ax_L3_in_concat      -- ax_L3
```

#### Capa de representabilidad (camino Gödel-aware a TFA)

Reencuadre 2026-06-11: en vez del slog object-level De Bruijn, se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con cómputo meta en ℕ + transferencia por homomorfismo. Disuelve los "Muros" (FOL= no da testigos meta ni case-split meta).

```lean
-- Full/StrongInduction.lean — inducción fuerte DERIVADA de ax_induction (sin axioma nuevo)
theorem substFormula_liftFormula (φ c s) : substFormula c s (liftFormula c φ) = φ
theorem lt_succ_split (m n) : axioms ⊢ lt m (σ n) → axioms ⊢ lor (lt m n) (m =eq n)
theorem strong_induction (φ : Formula) (step) : ∀ n, axioms ⊢ substFormula 0 n φ
-- Full/Numerals.lean — puente meta↔object
def numeral : Nat → Term                                       -- n ↦ σⁿ(0)
theorem numeral_add / numeral_mul / numeral_pow                -- homomorfismo +, ·, ^
theorem numeral_lt {a b} (h : a < b) : axioms ⊢ lt (numeral a) (numeral b)
theorem numeral_ne {a b} (h : a ≠ b) : axioms ⊢ neg (numeral a =eq numeral b)
-- Full/Bounded.lean — cuantificación acotada → casos finitos
theorem le_numeral_split (d C) : ∀ n, axioms ⊢ le d (numeral n) →
    (∀ i, Nat.le i n → axioms ⊢ (d =eq numeral i) → axioms ⊢ C) → axioms ⊢ C
-- Full/Divisibility.lean
theorem numeral_dvd {a b} (h : a ∣ b) : Dvd (numeral a) (numeral b)
theorem divisor_le (d q n) : axioms ⊢ (mul d q =eq n) → axioms ⊢ lt zero n → axioms ⊢ le d n
-- Full/Division.lean
theorem division_numeral (n d) (hd : 0 < d) :
    (axioms ⊢ numeral n =eq add (mul (numeral (n/d)) (numeral d)) (numeral (n%d)))
    ∧ (axioms ⊢ lt (numeral (n%d)) (numeral d))
-- Full/Primality.lean
theorem isPrime_numeral (p) (hp2 : 2 ≤ p) (hpd : ∀ a, a∣p → a=1∨a=p) : IsPrime (numeral p)
```

#### `Full/PrimeFactor.lean` — teoría de números META (ℕ pura, sin Mathlib) + TFA

```lean
def IsPrimeNat (p) : Prop := 2 ≤ p ∧ ∀ a, a∣p → a=1 ∨ a=p
def natProd : List Nat → Nat
theorem exists_prime_factor (n) (hn : 2 ≤ n) : ∃ p, IsPrimeNat p ∧ p ∣ n      -- inducción fuerte
theorem primeFactorList (n) (hn : 1 ≤ n) : ∃ ps, (∀ p∈ps, IsPrimeNat p) ∧ natProd ps = n
-- Euclides + UNICIDAD (vía Nat.Coprime.dvd_of_dvd_mul, List.perm_cons_erase):
theorem euclid (hp : IsPrimeNat p) : p ∣ a*b → p∣a ∨ p∣b
theorem count_unique / factorization_perm_unique : dos factorizaciones del mismo n son permutaciones
```

#### `Full/Factorization.lean` — TFA transferido al object

```lean
def toTerm : List Nat → Term                                   -- lista de pares (numeral p, one)
theorem prod_pairs_toTerm (ps) : axioms ⊢ (prod_pairs (toTerm ps) =eq numeral (natProd ps))
theorem tfa_numeral (n) (hn : 1 ≤ n) : ∃ ps, (∀ p∈ps, IsPrimeNat p)
    ∧ (axioms ⊢ prod_pairs (toTerm ps) =eq numeral n)                   -- EXISTENCIA (object)
    ∧ (∀ qs, (∀ q∈qs, IsPrimeNat q) → natProd qs = n → ps.Perm qs)      -- UNICIDAD (ℕ)
```

**TFA completo** (existencia object ∧ unicidad ℕ), autocontenido sin Mathlib/Peano. El `ax_p_tfa` de Block8 queda como forma *idealizada* (membership object + testigo object, no discharge constructivo por el "Muro 1"); `tfa_numeral` es la realización equivalente para todos los usos reales.

**Axiomas extra de Full**: `ax_induction`, `ax_mod2_alternation`, `ax_list_induction`. **Estado del fragmento de Minimal en Full**: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅ + TFA ✅.

---

### 3.15 `Meta/Incompleteness.lean` — Incompletitud Nivel D (Fase 19)

**Namespace**: `ROBINSON_PlusPlus.Meta.Incompleteness`
**Status**: ✅ Gödel I (mitad esencial) + Gödel II (postulando D2/D3)
**@importance**: `high`
**Last updated**: 2026-06-12
**Dependencias**: `Axioms`, `Meta/Godel`, `Meta/Provability`, `FOL.*`.

Deriva los teoremas de incompletitud a partir de las condiciones de demostrabilidad del Nivel C (D1 vía `provFormula_repr`; diagonalización vía `goedelSentence_fixedpoint`) + D2/D3 postuladas.

```lean
noncomputable def provCode (φ) : Formula := substFormula 0 (formCode φ) provFormula   -- Prov(⌜φ⌝)
def Consistent : Prop := ¬ (axioms ⊢ Formula.bottom)
-- Primer Teorema (mitad esencial):
theorem goedel_first_unprovable (hcon : Consistent) : ¬ (axioms ⊢ goedelSentence)
theorem goedel_first_true (hcon) : ¬ Provable (formCode goedelSentence)   -- G verdadera-pero-indemostrable
theorem incompleteness (hcon) : ∃ φ, ¬ (axioms ⊢ φ)
-- Segundo Teorema (postulando D2, D3):
axiom D2 (A B) : axioms ⊢ (provCode (A ⇒ B) ⇒ (provCode A ⇒ provCode B))
axiom D3 (A)   : axioms ⊢ (provCode A ⇒ provCode (provCode A))
noncomputable def consistencyFormula : Formula := neg (provCode Formula.bottom)   -- Con := ¬Prov(⌜⊥⌝)
theorem con_imp_goedelSentence : axioms ⊢ (consistencyFormula ⇒ goedelSentence)   -- Gödel I formalizado
theorem goedel_second (hcon : Consistent) : ¬ (axioms ⊢ consistencyFormula)       -- ⊬ Con
```

**Clave**: toda la cadena HBL de Gödel II (incl. la contrapositiva) se construye con `imp_intro`/`mp`, **sin DNE object-level**. La otra mitad de Gödel I (`⊬ ¬G`) se cerró 2026-06-13 vía `dne` clásica (`goedel_first_unrefutable`/`goedel_first_undecidable`).

---

### 3.16 Nivel D REAL — aritmetización de D1–D3 (Fases 0–2.2t)

Conversión de D1/D2/D3 de **postulados** a **teoremas** sobre un cálculo de Hilbert finitario nuevo. Plan: [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md). El `axioms ⊢` del proyecto usa la ω-regla (no r.e.), así que Gödel se aplica a `Prf` (finitario, paralelo); el ω-sistema queda intacto.

**`Meta/Hilbert.lean`** (Fase 0) — namespace `…Meta.Hilbert`:
```lean
theorem subst_lift_same (f) (c) (s) : substFormula c s (liftFormula c f) = f
inductive Prf₀ : Formula → Prop   -- Hilbert intuicionista (P1/P2, C, J, efq, Q1-3, refl, leibniz, thy, mp, gen)
inductive Prf  : Formula → Prop   -- clásico: incl (Prf₀) + p3 (DNE) + mp + gen
theorem prf0_to_derives : Prf₀ φ → axioms ⊢ φ   -- SOLO constructores de Derives (sin dne)
theorem prf_to_derives  : Prf φ → axioms ⊢ φ    -- + dne en un único punto (esquema p3)
theorem consistentH_of_omega : ¬(axioms ⊢ ⊥) → ¬ Prf ⊥
-- #print axioms: prf0 sin dne; prf con FOL.MetaRules.dne (diferencia exacta = {dne})
```

**`Meta/HilbertSeq.lean`** (Fase 1) — namespace `…Meta.HilbertSeq`:
```lean
inductive Rule   -- líneas anotadas (evita invertir la sustitución)
def checkProof : List Rule → Option (List Formula)   -- verificador decidible (DecidableEq Term/Formula)
def Derivation (rs) (φ) : Prop := ∃ L, checkProof rs = some L ∧ φ ∈ L
theorem derivation_to_prf : Derivation rs φ → Prf φ            -- solidez
theorem prf_to_derivation : Prf φ → ∃ rs, Derivation rs φ       -- completitud (checkAux_append/_shift)
theorem prf_iff_derivation : Prf φ ↔ ∃ rs, Derivation rs φ
def ruleCode : Rule → Term ;  def rulesCode : List Rule → Term  -- coding de Gödel
def Dem (d x : Term) : Prop  -- "d codifica derivación válida con la fórmula de código x" (concreto)
def ProvableH (x : Term) : Prop := ∃ d, Dem d x
theorem dem_tracks (φ) : ProvableH (formCode φ) ↔ Prf φ         -- reemplaza dem_iff_provable
```

**`Meta/CodeArith.lean`** (Fase 2.1) — namespace `…Meta.CodeArith`:
```lean
theorem numeral_bridge (n) : Meta.Godel.numeral n = Full.numeral n
theorem gnum_ne {a b} (h : a ≠ b) : axioms ⊢ neg (numeral a =eq numeral b)   -- separación
theorem gnum_lt {a b} (h : a < b) : axioms ⊢ lt (numeral a) (numeral b)
theorem gnum_add (a b) : axioms ⊢ (add (numeral a) (numeral b) =eq numeral (a+b))   -- + gnum_mul, gnum_refl
```

**`Minimal/Axioms.lean`** (extensión definicional para coding): `varc`/`funcc` (códigos de `Term.var`/`Term.func`), `substtc`/`substtsc` (sustitución aritmetizada), `forall_4`, y 6 ecuaciones recursivas `ax_substtc_*`/`ax_substtsc_*` añadidas a `axioms`.

**`Meta/SubstArith.lean`** (Fase 2.2 nivel término) — namespace `…Meta.SubstArith`:
```lean
theorem congr_cons_head / congr_cons_tail   -- congruencia de cons (patrón eq_congr)
theorem pred_numeral (m) : axioms ⊢ (pred (numeral (m+1)) =eq numeral m)
theorem substTerm_liftLiftLift   -- cancelación de triple lift (para instanciar forall_4)
-- ecuaciones recursivas re-derivadas como TEOREMAS (de Minimal.axioms, vía ax+spec):
theorem substtc_var_eq / _var_gt / _var_lt / _func ;  theorem substtsc_nil / _cons
theorem substTerm_arith (v) (s) (t) : axioms ⊢ (substtc (numeral v) (termCode s) (termCode t) =eq termCode (substTerm v s t))
theorem substTerms_arith ...   -- mutuo; cómputo object de la sustitución (nivel término)
theorem liftTerm_arith / liftFormula_arith ; theorem substFormula_arith   -- nivel fórmula (con binders)
-- lemas de lift: substTerm_liftLiftLift (3-lift), substTerm_liftLiftLiftLift (4-lift)
-- #print axioms substFormula_arith = solo axiomas estándar de Lean (0 postulados nuevos)
```

**`Meta/StepArith.lean`** (Fase 2.3) — `…Meta.StepArith`:
```lean
theorem q1_concl_code / q2_concl_code / leibniz_concl_code   -- el código de la conclusión de
  -- los esquemas de sustitución, reconstruido con substfc, coincide con formCode (vía substFormula_arith)
```

**`Meta/CheckArith.lean`** (Fase 2.4) — `…Meta.CheckArith`:
```lean
theorem numeralM_eq (n) : numeralM n = Godel.numeral n
theorem carc_cons / cdrc_cons   -- cómputo de los extractores cabeza/cola
-- 17 step lemmas del verificador (re-derivadas de Minimal.axioms):
theorem vpf_nil/p1/p2/c1/c2/c3/j1/j2/j3/efq/q1/q2/q3/eqrefl/leibniz/p3   -- incondicionales
theorem vpf_mp (… h1 h2) / vpf_gen (… h1)   -- condicionales por pertenencia In
def provFormulaC : Formula := Formula.ex (In (var 1) (validProofFn nil (var 0)))   -- demostrabilidad Σ₁
noncomputable def provCodeC (φ) := substFormula 0 (formCode φ) provFormulaC
```

---

## 4 · Patterns notables y deuda técnica

- **Patrón `spec + simp`**: cada axioma instanciado vía `spec h_axN t` requiere un `simp` con simp-set propio según los binders del axioma. Para axiomas `forall_2` se necesita `liftTerm`/`FOL.substTerm_liftTerm`; para `forall_3`, además `FOL.substTerm_liftLift`. Ver `THOUGHTS.md` y `feedback_build_cache` en memoria de Claude.
- **`Γ` por módulo**: cada módulo define `def Γ := axioms`. La unificación entre `Block2.Γ` y `Block4_C5.Γ` falla con `apply` pero pasa con `exact` (defeq).
- **`=eq` no-estándar `eq_trans`**: `eq_trans (h1:a=b)(h2:a=c):b=c`. Para `a=b, b=c → a=c` usar `FOL.derive_eq_trans`.
- **Linter `unusedSimpArgs` desactivado** en todos los módulos (2026-06-06): `set_option linter.unusedSimpArgs false` global. Previamente se hizo un barrido a `true` (411 → 0 warnings), que confirmó qué args de `simp` eran innecesarios; tras ello se decidió dejar el linter en `false` (puede dar falsos positivos bajo binders existenciales y se prefiere libertad para conservar args de `simp` por robustez). El build permanece con 0 warnings.

---

## 5 · Próximos pasos

Ver `NEXT-STEPS.md` y `GODEL-STATUS.md`. Resumen (estado 2026-06-12):

1. **`Minimal/` ✅ cerrado**: Bloques I–VIII + extensión TFA. ax22/ax23/ax27/ax28 eliminados.
2. **`Full/` ✅**: inducción general object-level + capa de representabilidad. Fragmento de Minimal derivado como teoremas: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3. **TFA completo** (`tfa_numeral`: existencia object ∧ unicidad ℕ), autocontenido sin Mathlib/Peano. `Intermediate/` eliminado (caso particular de Full).
3. **`Meta/` ✅ (Niveles A–D)**: Gödelización completa. B (codificación + Teo G1), C (demostrabilidad + diagonalización), **D** (`Meta/Incompleteness.lean`): **Gödel I** mitad esencial (`goedel_first_unprovable`, `goedel_first_true`) + **Gödel II** (`goedel_second`, postulando D2/D3).
4. **Refactor**: 5 meta-reglas ω de deducción movidas a `FOL/MetaRules.lean` (re-export desde `Minimal.Axioms`, cero churn).
5. **Pendiente**: otra mitad de Gödel I (`⊬ ¬G`, vía ω-consistencia/Rosser); proyecto hermano `FOL_CompStructs` (listas/tuplas como base de Peano/AczelSetTheory); CZF / análisis constructivo (muy largo plazo).

---

**Author**: Julián Calderón Almendros

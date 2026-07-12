# REFERENCE — Núcleo · Teoría objeto `Minimal/Axioms` · ROBINSON_PlusPlus

> **Nodo temático** del sistema REFERENCE (árbol; ver `AI-GUIDE.md` §0.5).
> Índice raíz: [REFERENCE.md](../REFERENCE.md).
> **Nodos relacionados:** [Aritmética](REFERENCE-Arithmetic.md) (se construye sobre estos axiomas),
> [Gödelización](REFERENCE-Godelization.md) e [Incompletitud](REFERENCE-Incompleteness.md) (usan los
> esquemas del verificador `lineWF`/`premsOf` y los axiomas de codificación `lenc`/`nthc`).
> **Ficheros `.lean`:** [Minimal/Axioms.lean](../ROBINSON_PlusPlus/Minimal/Axioms.lean).

**Contenido:** la teoría objeto FOL⁼ (Q++) — axiomas de Robinson extendidos, esquemas del verificador
estructural (`lineWF`, `premsOf`, tags), y los axiomas de la capa Δ₀ (`lenc`/`nthc`/`ax_lineWF_inv`/
`ax_lineWF_cons`). **Last updated:** 2026-07-12 · Lean v4.31.0.

---

## Descripción de módulos

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


---

← Índice raíz: [REFERENCE.md](../REFERENCE.md) · Siguiente rama: [Aritmética](REFERENCE-Arithmetic.md)

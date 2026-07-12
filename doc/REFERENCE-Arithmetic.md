# REFERENCE — Aritmética desarrollada · `Minimal/Theorems/Block1–8` · ROBINSON_PlusPlus

> **Nodo temático** del sistema REFERENCE (árbol; ver `AI-GUIDE.md` §0.5).
> Índice raíz: [REFERENCE.md](../REFERENCE.md).
> **Nodos relacionados:** [Núcleo](REFERENCE-Kernel.md) (axiomas base), [Full](REFERENCE-Full.md)
> (inducción general que estos bloques no tienen), [Gödelización](REFERENCE-Godelization.md)
> (`Block6` listas → codificación).
> **Ficheros `.lean`:** `ROBINSON_PlusPlus/Minimal/Theorems/Block1.lean` … `Block8.lean`
> (ver [directorio](../ROBINSON_PlusPlus/Minimal/Theorems/)).

**Contenido:** la aritmética desarrollada sobre Q++ sin inducción general — aritmética básica, raíz
cuadrada y orden, `div2`/`mod2`, función de emparejamiento de Cantor (paridad/totalidad/inyectividad/
sobreyectividad/unicidad), pares y proyecciones, listas, funciones discretas, primos y factorización
(TFA a nivel objeto). **Last updated:** 2026-07-12 · Lean v4.31.0.

---

## Descripción de módulos

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


---

← Índice raíz: [REFERENCE.md](../REFERENCE.md) · Ramas: [Núcleo](REFERENCE-Kernel.md) · [Full](REFERENCE-Full.md)

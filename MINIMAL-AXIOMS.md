# Análisis de Minimalidad del Sistema Axiomático `Minimal`

**Last updated:** 2026-06-06
**Author:** Julián Calderón Almendros
**Estado:** 34 axiomas matemáticos (25 aritméticos + 7 listas + 2 factorización) + 5 meta-reglas FOL + 1 meta-axioma Ax-P (TFA), 0 sorrys reales.

Este documento recoge la información obtenida por **web research** y por **razonamiento sobre el sistema actual** para evaluar si el conjunto de 34 axiomas que sustenta `Minimal/` es minimal — o cerca de serlo — relativo a su objetivo de diseño: **construir aritmética de Cantor + tuplas + listas + factorización prima sin esquema de inducción**.

> **Bloque VIII extendido (2026-06-06)**: añadidos `pow` y `prod_pairs` al lenguaje, 4 axiomas definitorios (`ax_pow_zero`, `ax_pow_succ`, `ax_prodp_nil`, `ax_prodp_cons`) y el meta-axioma `ax_p_tfa` (Teorema Fundamental de la Aritmética: existencia y unicidad de factorización para `n ≥ 1`). Spec §BLOQUE VIII Fase 17 cubierta por completo. Las Fases 18–19 (Gödelización) permanecen fuera del scope `Minimal/`.

---

## 1 · Sistemas de referencia

### 1.1 Robinson Q (1950) — 7 axiomas

Fragmento finitamente axiomatizado de PA, deliberadamente sin esquema de inducción ([Wikipedia](https://en.wikipedia.org/wiki/Robinson_arithmetic)).

| # | Axioma | Comentario |
|---|---|---|
| Q1 | `σx ≠ 0` | 0 no es sucesor |
| Q2 | `σx = σy → x = y` | inyectividad del sucesor |
| Q3 | `y = 0 ∨ ∃x. σx = y` | todo no-cero es sucesor (predecesor por casos) |
| Q4 | `x + 0 = x` | identidad por la derecha |
| Q5 | `x + σy = σ(x + y)` | recursión de la suma |
| Q6 | `x · 0 = 0` | absorción cero por la derecha |
| Q7 | `x · σy = (x · y) + x` | recursión del producto |

**Limitación clave**: Q **NO demuestra** comm/assoc/distrib de `+` ni de `·`. Solo demuestra **instancias concretas** (`5+7 = 7+5` sí; `∀x,y. x+y = y+x` no). Tampoco demuestra propiedades como `∀x. x + 0 = 0 + x` o `∀x. 0 < x ∨ 0 = x` sin ayuda.

### 1.2 PA⁻ — 16 axiomas

Teoría del **semianillo discretamente ordenado** sin inducción ([Diagonal Argument](https://diagonalargument.com/2020/10/21/topics-in-nonstandard-arithmetic-6-the-axioms/)). Forma natural de obtener "Q + comm/assoc/distrib" como axiomas:

| # | Axioma | Notas |
|---|---|---|
| 1 | `(x+y)+z = x+(y+z)` | assoc + |
| 2 | `x+y = y+x` | comm + |
| 3 | `(x·y)·z = x·(y·z)` | assoc · |
| 4 | `x·y = y·x` | comm · |
| 5 | `x·(y+z) = x·y + x·z` | distrib |
| 6 | `x+0 = x` | identidad + |
| 7 | `x·0 = 0` | absorción · |
| 8 | `x·1 = x` | identidad · |
| 9 | `x<y ∧ y<z → x<z` | transitividad < |
| 10 | `¬(x<x)` | irreflexividad < |
| 11 | `x<y ∨ x=y ∨ y<x` | tricotomía |
| 12 | `x<y → x+z < y+z` | monotonía +,< |
| 13 | `z≠0 ∧ x<y → x·z < y·z` | monotonía ·,< |
| 14 | `x<y → ∃w. x+w = y` | "gap-free" |
| 15 | `0<1 ∧ (x>0 → x≥1)` | discreteness |
| 16 | `x ≥ 0` | no-negatividad |

PA⁻ **sí demuestra** sin inducción: `add_left_cancel`, propiedades básicas del orden, etc.

---

## 2 · Comparación con `Minimal` (30 axiomas)

### 2.1 Axiomas que están en Q **y** en `Minimal`

| `Minimal` | Q correspondiente | Comentario |
|---|---|---|
| `ax2_peano_succ_neq_zero` | Q1 | `∀n. σn ≠ 0` |
| `ax3_peano_succ_inj` | Q2 | `∀n,m. σn = σm → n=m` |
| `ax4_add_zero` | Q4 | `∀n. n+0 = n` |
| `ax5_add_succ` | Q5 | `∀n,m. n+σm = σ(n+m)` |
| `ax8_mul_zero` | Q6 | `∀n. n·0 = 0` |
| `ax9_mul_succ` | Q7 | `∀n,m. n·σm = n·m + n` |

**6 axiomas comunes**. `Minimal` omite Q3 (predecesor por casos) — usamos `pred` total como función con axiomas `ax25, ax26`.

### 2.2 Axiomas que están en PA⁻ **y** en `Minimal` (más allá de Q)

| `Minimal` | PA⁻ | Comentario |
|---|---|---|
| `ax6_add_comm` | 2 | `n+m = m+n` |
| `ax7_add_assoc` | 1 | `(n+m)+k = n+(m+k)` |
| `ax10_mul_comm` | 4 | `n·m = m·n` |
| `ax11_mul_assoc` | 3 | `(n·m)·k = n·(m·k)` |
| `ax12_mul_distrib` | 5 | `n·(m+k) = n·m + n·k` |
| `ax13_lt_def` | 14 (gap-free) | `n<m ⇔ ∃k. n + σk = m` (junto con la dirección "<") |
| `ax18_lt_irrefl` | 10 | `¬(n<n)` |
| `ax19_lt_trichotomy` | 11 | `n<m ∨ n=m ∨ m<n` |

**8 axiomas adicionales** que `Minimal` toma directamente de PA⁻. Total acumulado: **14 axiomas que tienen contrapartida directa en Q ∪ PA⁻**.

### 2.3 Axiomas estructurales/funcionales propios de `Minimal`

`Minimal` extiende el vocabulario con funciones adicionales (√, div2, mod2, pred, sub) y tipos de datos (listas). Cada función requiere axiomas que la caracterizan; algunos son **derivables en PA + inducción**, otros son testigos genuinos.

#### Aritméticos extendidos (9 axiomas)

| Axioma | Caracteriza | ¿Derivable sin inducción? |
|---|---|---|
| `ax14_sqrt_le` | `(√n)² ≤ n` | No — define √ por cotas |
| `ax15_lt_succ_sqrt` | `n < (σ√n)²` | No — define √ por cotas |
| `ax16_mod2_succ` | `mod2(n)=0 ⇔ mod2(σn)=1` | No — caracteriza mod2 |
| `ax17_div_mod_eq` | `div2(n)·2 + mod2(n) = n` | No — caracteriza div/mod |
| `ax21_mod2_range` | `mod2(n) ∈ {0,1}` | **NO** (requiere inducción) — ver §3 |
| `ax24_mod2_of_even` | `n = 2k → mod2(n) = 0` | **NO** (requiere inducción) — ver §3 |
| `ax25_pred_zero` | `pred(0) = 0` | Caracteriza pred (en Q se usa Q3) |
| `ax26_pred_succ` | `pred(σn) = n` | Caracteriza pred |
| `ax29_sub_witness` | `b≤a → b+(a−b) = a` | No — caracteriza sub (monus) |

#### Listas/concat (7 axiomas)

| Axioma | Caracteriza | ¿Derivable? |
|---|---|---|
| `ax_L0_cons_def` | `cons(h,t) = ⟨h, σt⟩` | No — codifica listas vía pair |
| `ax_L1_in_nil` | `¬In(x, nil)` | No — define ∈ |
| `ax_L2_in_cons` | `In(x, cons(h,t)) ⇔ x=h ∨ In(x,t)` | No — define ∈ |
| `ax_L3_in_concat` | `In(x, L##M) ⇔ In(x,L) ∨ In(x,M)` | **NO** (requiere inducción sobre L) |
| `ax_C1_concat_nil` | `nil ## L = L` | No — define concat (caso base) |
| `ax_C2_concat_cons` | `cons(h,t) ## L = cons(h, t##L)` | No — define concat (caso recursivo) |
| `ax_C3_concat_assoc` | `(L##M)##N = L##(M##N)` | **NO** (requiere inducción sobre L) |

### 2.4 Axiomas eliminados (historia)

| Axioma | Estado original | Por qué se eliminó | Cuándo |
|---|---|---|---|
| `ax20_eq_decidable` | `∀n,m. n=m ∨ ¬(n=m)` | derivable de ax18, ax19, sustitución; ahora teorema `eq_decidable` (Block1) | 2026-05-? |
| `ax22_cantor_proj_exists` | `∀c. is_cantor(π₁c, π₂c, c)` | `proj1/proj2` pasan a defs concretas `x_of_c/y_of_c` (Block4_C6_C7); contenido demostrado como `proj_is_cantor` | 2026-06-02 (`537fd68`) |
| `ax23_cantor_proj_uniq` | `Cantor(x,y,c) ∧ Cantor(x',y',c) → x=x' ∧ y=y'` | nunca usado en código; el teorema `cantor_uniqueness` ya cubre esto | 2026-06-02 (`537fd68`) |
| `ax27_add_left_cancel` | `a+c = b+c → a=b` | **derivable en PA⁻** vía tricotomía (ax19) + monotonía (`lt_add_const_of_le_left`) + irreflexividad (ax18) | **2026-06-03** |
| `ax28_mul_two_cancel` | `2a = 2b → a=b` | derivable sin inducción vía tricotomía + `mul_two_lt_mono` + ax18; ahora teorema `teo_2_11` (Block1) | 2026-06-02 |

---

## 3 · ¿Por qué los axiomas restantes son irreducibles?

Los 4 candidatos a "axiomas testigos inductivos" que aún están en la lista (`ax21`, `ax24`, `ax_C3`, `ax_L3`) **no son eliminables sin inducción**. El obstáculo común es:

> **Lema fantasma**: `∀n, m. n + m ≥ n` no se prueba sin inducción sobre `m`.

Sin esta propiedad uniforme, los casos del razonamiento "por tamaño" se atascan. Veamos cómo afecta cada axioma:

### 3.1 `ax24_mod2_of_even` (auditado 2026-06-03)

Enunciado: `∀n, k. n = 2k → mod2(n) = 0`.

Intento (siguiendo PA⁻):

- Por `ax21`, `mod2(n) ∈ {0, 1}`. Caso `0`: hecho. Caso `1`: por `ax17`, `div2(n)·2 + 1 = n = 2k`, así `succ(2d) = 2k` con `d := div2(n)`.
- Tricotomía (`ax19`) sobre `d` vs `k`:
  - `d = k`: `succ(2k) = 2k` → contradicción por `ax18 + ax13`. ✓
  - `d < k`: `∃j. d + σj = k` (`ax13`), luego `2k = succ(succ(2(d+j)))`, por `ax3` `2d = succ(2(d+j))`.
    - Para contradicción: `2(d+j) ≥ 2d` y por tanto `succ(2(d+j)) > 2d`.
    - **Obstáculo**: `d+j ≥ d` requiere `n + m ≥ n` para `m` arbitrario → inducción.

Conclusión: ax24 **es equivalente a una instancia del esquema de inducción** y por tanto irreducible.

### 3.2 `ax21_mod2_range` (sin auditar formalmente, pero por simetría)

`∀n. mod2(n) = 0 ∨ mod2(n) = 1`. Sin inducción no podemos extender el caso base (`mod2(0)`, `mod2(1)`) a todo `n`. Es esencialmente el rango de `mod2`, que es global y requiere inducción.

### 3.3 `ax_C3_concat_assoc` y `ax_L3_in_concat`

Ambos son propiedades **uniformes** sobre listas (`(L##M)##N = L##(M##N)`, `In(x, L##M) ⇔ In(x,L) ∨ In(x,M)`). En PA + inducción se demuestran inductando sobre la estructura de `L` (o sobre su longitud vía Cantor). Sin inducción quedan como axiomas testigos.

---

## 4 · ¿Cuánto se puede reducir más?

Resumen final del recuento:

| Categoría | Cantidad | ¿Reducible? |
|---|---|---|
| Núcleo Q | 6 (`ax2-5, ax8, ax9`) | NO — base de la aritmética |
| Estructura PA⁻ | 8 (`ax6, ax7, ax10-13, ax18, ax19`) | NO — sin inducción son necesarios |
| Caracterización √ | 2 (`ax14, ax15`) | NO — definen √ por cotas |
| Caracterización div/mod | 2 (`ax16, ax17`) | NO — definen las funciones |
| Caracterización pred | 2 (`ax25, ax26`) | NO — definen pred |
| Caracterización sub | 1 (`ax29`) | NO — define monus por testigo |
| Testigos inductivos aritméticos | 2 (`ax21, ax24`) | NO sin inducción (analizado §3) |
| Axiomas de listas | 7 (`ax_L0-3, ax_C1-3`) | NO sin inducción (estructurales) |
| **TOTAL** | **30** | — |

**Conclusión**: el sistema con **30 axiomas matemáticos** está en un mínimo local defendible. Para reducir más haría falta:

1. **Restringir la teoría** (eliminar √, mod2, sub, listas — perdiendo capacidad expresiva). El núcleo PA⁻ puro tiene 16 axiomas pero no expresa Cantor con sub/sqrt/mod2.
2. **Añadir inducción** restringida o general — pero eso violaría el objetivo de diseño de `Minimal/`. En cuanto se añade inducción, `ax21`, `ax24`, `ax_C3`, `ax_L3` se vuelven teoremas (sería un `Intermediate/` o `Full/` según [PLANNING.md](PLANNING.md)).
3. **Cambiar de codificación**: por ejemplo, eliminar `pred` como función primitiva y usar Q3 (predecesor existencial) — ahorra 1 axioma (`ax25`+`ax26` por `Q3`) pero complica todas las pruebas que usan `pred`.

---

## 5 · Posición de `Minimal` en el panorama

```text
Q (7 ax)  ⊂  Minimal-núcleo-Q (6 ax compartidos)
   ↓                            ↓ (añade comm/assoc/distrib + orden)
   ↓                       PA⁻ (16 ax)  ⊂  Minimal-PA⁻ (14 ax compartidos)
   ↓                                       ↓ (añade √, div2, mod2, pred, sub, listas)
   ↓                                  Minimal (30 ax)
   ↓                                       ↓ (añade esquema de inducción)
   ↓                                  Intermediate/Full → PA (∞ ax)
```

Más precisamente:

- `Minimal` es un **fortalecimiento conservativo de Q** que añade los axiomas necesarios para que las funciones extras (√, div, mod, pred, sub, cons, concat, In) tengan semántica determinada.
- Como teoría, `Minimal` es **estrictamente más débil que PA** (no tiene inducción) pero **estrictamente más fuerte que Q** y que el fragmento universal de PA⁻ (porque tiene más vocabulario).
- En la jerarquía habitual (`Q ⊊ PA⁻ ⊊ EA ⊊ I∆₀ ⊊ IΣ₁ ⊊ PA`), `Minimal` no encaja directamente — es un sistema construido **para un propósito** (Cantor + tuplas + listas constructivos), no para encajar en la jerarquía clásica.

---

## 6 · Próximos pasos relacionados

- **Block7** (`IsFunction`, Teo F3): es el siguiente módulo, no se espera que añada axiomas nuevos.
- **`Intermediate/`** y **`Full/`** (PLANNING §6, §7): se diseñan precisamente para *eliminar* `ax21, ax24, ax27 [ya], ax_C3, ax_L3` introduciendo inducción restringida primero y general después.

---

## 7 · Referencias

- [Robinson arithmetic — Wikipedia](https://en.wikipedia.org/wiki/Robinson_arithmetic)
- [Topics in Nonstandard Arithmetic 6: The Axioms — Diagonal Argument](https://diagonalargument.com/2020/10/21/topics-in-nonstandard-arithmetic-6-the-axioms/)
- [Robinson arithmetic — Grokipedia](https://grokipedia.com/page/Robinson_arithmetic)
- [Weak Systems of Arithmetic — The n-Category Café](https://golem.ph.utexas.edu/category/2011/10/weak_systems_of_arithmetic.html)
- [Robinson Arithmetic Essentials — Number Analytics](https://www.numberanalytics.com/blog/ultimate-guide-robinson-arithmetic-set-theory-proof-theory)
- [The metamathematics of very weak arithmetics — Franks (2005)](https://www.lps.uci.edu/files/grad-alumni/CFranks/veryweak.pdf)
- Documentación interna: [PLANNING.md](PLANNING.md), [DISCUSIONES.md](DISCUSIONES.md), [REFERENCE.md](REFERENCE.md), [TuplasFuncionesYListas.md](TuplasFuncionesYListas.md).

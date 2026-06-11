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

#### Aritméticos extendidos sin factorización (9 axiomas)

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

#### Factorización — Bloque VIII extendido (4 axiomas, 2026-06-06)

| Axioma | Caracteriza | ¿Derivable sin inducción? |
|---|---|---|
| `ax_pow_zero` | `b^0 = 1` | No — define caso base de pow (análogo a ax8 `b·0=0`) |
| `ax_pow_succ` | `b^(σe) = b^e · b` | No — define caso recursivo de pow (análogo a ax9 `b·σm = b·m + b`) |
| `ax_prodp_nil` | `prod_pairs [] = 1` | No — caso base de la recursión sobre listas |
| `ax_prodp_cons` | `prod_pairs ((p,e)::t) = p^e · prod_pairs t` | No — caso recursivo (sólo activo en cabezas con forma `pair p e`) |

Los 4 son **definicionales puros**: no postulan propiedades derivables, sino las dos cláusulas (base + recursiva) que toda definición por recursión primitiva requiere. Auditoría detallada en §3.4.

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

### 3.2 `ax21_mod2_range` (auditado formalmente 2026-06-11)

`∀n. mod2(n) = 0 ∨ mod2(n) = 1`. Sin inducción no podemos extender el caso base (`mod2(0)`, `mod2(1)`) a todo `n`. Es esencialmente el rango de `mod2`, que es global y requiere inducción.

**Auditoría 2026-06-11 (Opción C.2)**: Al intentar derivar `ax21` en `Full/` por inducción surgió un **bloqueante adicional no documentado anteriormente**: `ax16` (`mod2(n)=0 ⇔ mod2(σn)=1`) **sólo captura media alternancia**. En el paso inductivo, caso `mod2(n) = 1`, no podemos concluir `mod2(σn) = 0` ni con inducción simple ni fuerte: por contrapositiva de `ax16` backward sólo obtenemos `mod2(σn) ≠ 1`, y para concluir `= 0` necesitaríamos `mod2(σn) ∈ {0,1}` — que es precisamente `ax21`. Algebraicamente con `ax17(σn) = (div2(n)+1)·2`, podemos descartar `mod2(σn) = 1` por parida (lema `2A ≠ σ(2B)` sí derivable por inducción fuerte), pero **no podemos descartar `mod2(σn) ≥ 2`** sin más axiomas. **Conclusión**: `ax16+ax17` dejan `mod2` subdeterminado; cualquier modelo no estándar con `mod2(σn) = 2` para algún `n` cumple ambos.

**Solución adoptada en `Full/`** (Opción C.2): añadir un único axioma extra `ax_mod2_alternation : ∀n, mod2(σn) + mod2(n) = 1` que caracteriza completamente la recursión. De este y `mod2(0) = 0` (derivable de `ax17 + teo_2_9` sin usar `ax21`) salen `ax21` y `ax24` como teoremas (`mod2_range_thm`, `mod2_of_even_thm` en `Full/Mod2.lean`). El axioma de alternancia es **conservativo respecto a Minimal**: allí derivable de `ax21 + ax16 + teo_1_3`. Ver [NEXT-STEPS.md](NEXT-STEPS.md) Eje 4.

### 3.3 `ax_C3_concat_assoc` y `ax_L3_in_concat`

Ambos son propiedades **uniformes** sobre listas (`(L##M)##N = L##(M##N)`, `In(x, L##M) ⇔ In(x,L) ∨ In(x,M)`). En PA + inducción se demuestran inductando sobre la estructura de `L` (o sobre su longitud vía Cantor). Sin inducción quedan como axiomas testigos.

### 3.4 Los 4 axiomas del Bloque VIII extendido (auditados 2026-06-06)

A diferencia de §3.1-3.3 (axiomas-propiedades que requieren inducción), los 4 nuevos axiomas son **definicionales puros**. La distinción ontológica importa:

> **Axioma-propiedad**: postula que un símbolo *ya definido* tiene una propiedad (`ax21`: el rango de `mod2` es {0,1}). Sin inducción no se obtiene la propiedad para todo `n`.
>
> **Axioma-definicional**: introduce un símbolo nuevo y le da su semántica vía dos cláusulas (caso base + caso recursivo). Sin inducción seguimos pudiendo aplicar las cláusulas; la inducción sólo es necesaria para **demostrar propiedades inductivas** del nuevo símbolo, no para definirlo.

#### 3.4.1 `ax_pow_zero` y `ax_pow_succ`

```text
ax_pow_zero : ∀ b, b^0 = 1
ax_pow_succ : ∀ b, e, b^(σe) = b^e · b
```

**Análisis**: estos dos axiomas son **estructuralmente idénticos** a la pareja `ax8 (b·0 = 0)` + `ax9 (b·σm = b·m + b)` que define la multiplicación. Son la **recursión primitiva mínima** para introducir un símbolo binario sobre `(Term, Term)` recursando en el segundo argumento.

- **¿Eliminables?** No, sin volver a `pow` redundante o no-determinado. Sin `ax_pow_zero`, `b^0` queda libre (cualquier término); sin `ax_pow_succ`, no se relacionan los valores entre potencias sucesivas.
- **¿Reducibles a más sencillos?** No en sentido estricto. Lo único alternativo sería:
  - Sustituir `pow` por una codificación `pow_via_prod_pairs` (definir `pow b e := prod_pairs [(b,e)]`), pero entonces `prod_pairs` toma el papel primitivo y `pow` queda derivada — no se gana, sólo se mueve la primitividad.
  - Definir `pow` con bound recursion en `b` (más rara), o con iteración, pero requiere infraestructura adicional.
- **Comparación con PA-pure**: en `Full/` con inducción general, `pow` puede definirse como **abreviatura** (sin axiomas independientes) usando la β-función de Gödel + inducción para verificar las cláusulas. En `Intermediate/` con `Ax-Ind(Φ)` la situación depende de si `Φ` incluye fórmulas con `pow`; típicamente sí se postula como axioma (igual que `ax8`/`ax9`).
- **Conclusión**: **irreducibles en cualquier sistema sin recursión primitiva como esquema** (la recursión primitiva *como esquema general* sustituiría a estos dos axiomas, pero el sistema crece en otra dirección).

#### 3.4.2 `ax_prodp_nil` y `ax_prodp_cons`

```text
ax_prodp_nil  : prod_pairs [] = 1
ax_prodp_cons : ∀ p, e, t, prod_pairs ((p,e)::t) = p^e · prod_pairs t
```

**Análisis**: análogo a `ax_C1_concat_nil` + `ax_C2_concat_cons` que definen `concat` — la recursión primitiva sobre la estructura de listas (caso `nil` + caso `cons`).

- **Particularidad**: `ax_prodp_cons` sólo se activa cuando la cabeza tiene la forma sintáctica `pair p e`. Para listas con cabezas no-pareadas, `prod_pairs` queda **subdeterminado** (cualquier término satisface los axiomas). Esto es **deliberado**: el predicado `IsFactorization` restringe el dominio.
- **¿Eliminables?** No, salvo que se elimine `prod_pairs` del lenguaje y se exprese `IsFactorization` enteramente vía `In` + `pow` + cuantificación recursiva sobre la longitud (mucho más feo, no compila igualmente).
- **¿Por qué no formular cons general (`ax_prodp_cons_full : ∀ x t, prod_pairs (x::t) = pow (proj1 x) (proj2 x) · prod_pairs t`)?** Porque `proj1`/`proj2` son defs **concretas** en `Block4_C6_C7.lean` (no símbolos opacos), y meterlas en `Axioms.lean` introduciría dependencia circular o requeriría duplicar las defs. La forma restringida vía `pair` evita esto.
- **Conclusión**: **irreducibles** y restringidos por diseño. La alternativa (general con `proj1/2`) cuesta más infraestructura sin beneficio.

#### 3.4.3 Tabla resumen — irreducibilidad de los 4 nuevos

| Axioma | Categoría | Análogo en `Minimal` | Eliminable? |
|---|---|---|---|
| `ax_pow_zero` | Definicional base | `ax8` (`b·0=0`) | No |
| `ax_pow_succ` | Definicional recursiva | `ax9` (`b·σm = b·m + b`) | No |
| `ax_prodp_nil` | Definicional base sobre listas | `ax_C1` (`nil##L=L`) | No |
| `ax_prodp_cons` | Definicional recursiva sobre listas (restringida) | `ax_C2` (`(h::t)##L = h::(t##L)`) | No |

---

## 3.5 · Meta-axiomas vs axiomas-de-la-lista (ontología)

El sistema `Minimal/` tiene **dos niveles ontológicos** de "axioma" que conviene distinguir explícitamente:

### 3.5.1 Axiomas de la lista `axioms : List Formula` (34)

Son `Formula` cerradas (sin variables libres) que se cargan como hipótesis en cada derivación `axioms ⊢ φ`. Son los 34 contabilizados en §2.3 (25 aritméticos + 7 listas + 2 factorización, omitiendo `prodp_nil` y `prodp_cons` que son del bloque factorización). Se manipulan con `ax`, `spec`, `mp`, etc., y son los **axiomas matemáticos en sentido estricto**.

Recuento ajustado: el bloque factorización tiene **2 axiomas aritméticos** (`pow_zero`, `pow_succ`) y **2 axiomas de listas/factorización** (`prodp_nil`, `prodp_cons`). El reparto "25 aritm + 7 listas + 2 factorización" descomprime a "23 aritm core + 2 pow + 7 listas core + 2 prodp". Sería más limpio decir "27 aritm + 7 listas" en algunos contextos, pero mantenemos la triple categorización por trazabilidad histórica.

### 3.5.2 Meta-axiomas Lean (`axiom` declaraciones, 6)

Son declaraciones Lean `axiom name : Type` que el sistema **no demuestra** pero **postula como ciertas**. Se dividen en dos sub-clases:

**Reglas del cálculo deductivo** (5, en `Axioms.lean`):

| Meta-axioma | Tipo | Rol |
|---|---|---|
| `imp_intro` | `(Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)` | Internalización de implicación |
| `gen` | `(∀ n : Term, Γ ⊢ substFormula 0 n A) → Γ ⊢ ∀A` | Generalización (ω-regla) |
| `raa` | `(Γ ⊢ A → Γ ⊢ ⊥) → Γ ⊢ ¬A` | Reducción al absurdo clásica |
| `or_elim` | Eliminación meta-nivel de ∨ | Case split meta |
| `ex_elim` | Eliminación meta-nivel de ∃ | Extracción de testigo |

Estos **no son axiomas matemáticos**: son **reglas del cálculo deductivo** que normalmente vivirían como constructores de `Derives` pero que aquí se externalizan como meta-axiomas Lean por economía. Filosóficamente son equivalentes a una formulación de la deducción natural en estilo Hilbert + reglas estructurales. Documentado en ADR-008.

**Axioma matemático meta-codificado** (1, en `Block8.lean`):

| Meta-axioma | Tipo | Rol |
|---|---|---|
| `ax_p_tfa` | `∀ n, axioms ⊢ lt zero n → ∃ f, IsFactorization f n ∧ (∀ f', IsFactorization f' n → axioms ⊢ f =eq f')` | TFA (existencia y unicidad de factorización) |

Esto **sí es un axioma matemático** — postula un hecho del sistema aritmético. La razón de meta-codificarlo (en lugar de añadirlo como `Formula` a `axioms`) es que `IsFactorization` es **meta-Prop**: combina derivación object-level con cuantificación meta-level sobre `Term`. Expresarlo como `Formula` requeriría un esquema completo de meta-codificación, indistinguible del que necesitaríamos para Gödelización completa.

**Híbrido por necesidad técnica, no por elección filosófica**.

### 3.5.3 Total ontológico

| Categoría | Cantidad | Naturaleza |
|---|---|---|
| Axiomas de `axioms : List Formula` | 34 | Hipótesis aritméticas object-level |
| Meta-reglas del cálculo deductivo | 5 | Reglas estructurales internalizadas |
| Meta-axioma matemático (TFA) | 1 | TFA, meta-Prop |
| **Total compromisos formales** | **40** | — |

> **Nota**: este recuento "40" no es comparable con los conteos de Q (7) o PA⁻ (16): aquellos incluyen sólo axiomas object-level pero asumen reglas del cálculo deductivo *implícitamente*. El recuento honesto de PA⁻ sería ~16 + 5 reglas, y el de Minimal sería ~34 + 5 + 1.

---

## 4 · ¿Cuánto se puede reducir más?

Resumen final del recuento (actualizado 2026-06-06):

| Categoría | Cantidad | ¿Reducible? |
|---|---|---|
| Núcleo Q | 6 (`ax2-5, ax8, ax9`) | NO — base de la aritmética |
| Estructura PA⁻ | 8 (`ax6, ax7, ax10-13, ax18, ax19`) | NO — sin inducción son necesarios |
| Caracterización √ | 2 (`ax14, ax15`) | NO — definen √ por cotas |
| Caracterización div/mod | 2 (`ax16, ax17`) | NO — definen las funciones |
| Caracterización pred | 2 (`ax25, ax26`) | NO — definen pred |
| Caracterización sub | 1 (`ax29`) | NO — define monus por testigo |
| Testigos inductivos aritméticos | 2 (`ax21, ax24`) | NO sin inducción (analizado §3.1-3.2) |
| Axiomas de listas | 7 (`ax_L0-3, ax_C1-3`) | NO sin inducción (estructurales) |
| **Definicionales pow** | 2 (`ax_pow_zero, ax_pow_succ`) | NO — recursión primitiva base (analizado §3.4.1) |
| **Definicionales prod_pairs** | 2 (`ax_prodp_nil, ax_prodp_cons`) | NO — recursión sobre listas (analizado §3.4.2) |
| **TOTAL axiomas object-level** | **34** | — |
| Meta-reglas FOL (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) | 5 | Estructurales, ADR-008 |
| Meta-axioma matemático (`ax_p_tfa`, TFA) | 1 | Híbrido por necesidad técnica (§3.5.2) |
| **TOTAL compromisos formales** | **40** | — |

**Conclusión**: el sistema con **34 axiomas matemáticos + 1 meta-axioma TFA** está en un mínimo local defendible. Para reducir más haría falta:

1. **Restringir la teoría** (eliminar √, mod2, sub, listas, pow, prod_pairs — perdiendo capacidad expresiva). El núcleo PA⁻ puro tiene 16 axiomas pero no expresa Cantor con sub/sqrt/mod2 ni la factorización.
2. **Añadir inducción** restringida o general — pero eso violaría el objetivo de diseño de `Minimal/`. En cuanto se añade inducción, `ax21`, `ax24`, `ax_C3`, `ax_L3` se vuelven teoremas; con inducción fuerte sobre fórmulas no acotadas, `ax_p_tfa` también pasa a teorema. Sería un `Intermediate/` o `Full/` según [PLANNING.md](PLANNING.md).
3. **Cambiar de codificación**: por ejemplo, eliminar `pred` como función primitiva y usar Q3 (predecesor existencial) — ahorra 1 axioma (`ax25`+`ax26` por `Q3`) pero complica todas las pruebas que usan `pred`. O eliminar `pow` y forzar la codificación de exponentes vía iteración explícita (vía listas) — añade complicación a `IsFactorization`.
4. **Eliminar el bloque factorización** (escenario hipotético): si se abandona el TFA en `Minimal/` y se difiere todo lo de factorización a `Intermediate/`, se ahorrarían los 4 axiomas + el meta-axioma TFA, volviendo a 30 + 5 meta-reglas. **No recomendado**: la factorización es necesaria para la codificación de Gödel del Eje `Meta/` (§6 abajo), y mantenerla en `Minimal/` da una base aritmética más uniforme.

---

## 5 · Posición de `Minimal` en el panorama

```text
Q (7 ax)  ⊂  Minimal-núcleo-Q (6 ax compartidos)
   ↓                            ↓ (añade comm/assoc/distrib + orden)
   ↓                       PA⁻ (16 ax)  ⊂  Minimal-PA⁻ (14 ax compartidos)
   ↓                                       ↓ (añade √, div2, mod2, pred, sub, listas, pow, prod_pairs)
   ↓                                  Minimal (34 ax + Ax-P meta)
   ↓                                       ↓ (añade esquema de inducción)
   ↓                                  Intermediate/Full → PA (∞ ax)
```

Más precisamente:

- `Minimal` es un **fortalecimiento conservativo de Q** que añade los axiomas necesarios para que las funciones extras (√, div, mod, pred, sub, cons, concat, In, pow, prod_pairs) tengan semántica determinada, más el TFA como meta-axioma.
- Como teoría, `Minimal` es **estrictamente más débil que PA** (no tiene inducción) pero **estrictamente más fuerte que Q** y que el fragmento universal de PA⁻ (porque tiene más vocabulario).
- En la jerarquía habitual (`Q ⊊ PA⁻ ⊊ EA ⊊ I∆₀ ⊊ I∆₀+Exp ⊊ IΣ₁ ⊊ PA`), `Minimal` no encaja directamente — es un sistema construido **para un propósito** (Cantor + tuplas + listas + factorización constructivos), no para encajar en la jerarquía clásica. La comparación más fina con I∆₀+Exp se discute en §5.5.

### 5.5 Comparación con EFA / I∆₀+Exp (2026-06-06)

Tras la extensión del Bloque VIII (`pow` + TFA), conviene comparar `Minimal` con dos sistemas estándar de la jerarquía clásica que también tienen exponenciación:

#### 5.5.1 EFA (Elementary Function Arithmetic)

EFA = I∆₀ + un axioma que postula la totalidad de la exponenciación (`∀x,y. ∃z. z = x^y`). Equivale a ER (Elementary Recursive Arithmetic) y captura exactamente las funciones recursivas primitivas elementales.

**Diferencias con `Minimal`**:

| Aspecto | EFA | `Minimal` |
|---|---|---|
| Inducción | Esquema sobre fórmulas Δ₀ (acotadas) | **Ninguna** |
| Exponenciación | Función primitiva con axioma de totalidad + propiedades por inducción | Función primitiva con `ax_pow_zero` + `ax_pow_succ` (no totalidad explícita; queda como propiedad de la recursión definicional) |
| Factorización (TFA) | **Teorema demostrable** por inducción en Δ₀ + Exp | **Meta-axioma** (`ax_p_tfa`) |
| Vocabulario | `0, σ, +, ·, exp, <` | `Minimal` + listas, pares, √, div2, mod2, sub, pred |

**Relación**: `EFA` y `Minimal` son **incomparables**:

- EFA es **más fuerte aritméticamente** (tiene inducción Δ₀, demuestra TFA, totalidad de funciones recursivas primitivas elementales).
- `Minimal` es **más rico en vocabulario** (listas, pares, sub, pred, raíz cuadrada, √-cotas).

Esta posición ortogonal es interesante: `Minimal` es **suficiente para enunciar TFA** (por eso pudimos meterlo como meta-axioma) pero **insuficiente para demostrarlo** (porque no tiene inducción). EFA invierte la situación: lo demuestra, pero el enunciado vive en un vocabulario más pobre.

#### 5.5.2 I∆₀+Exp

I∆₀+Exp = I∆₀ extendido con `Exp` (existencia y graph definability de `2^x`). Más débil que IΣ₁ pero todavía demuestra resultados importantes de teoría de números.

**Relación con `Minimal`**: similar a la de EFA pero más débil aún (no necesariamente captura todas las recursivas primitivas elementales). `Minimal + Ax-Ind(Φ)` (= `Intermediate/` planeado) podría situarse cerca de I∆₀+Exp tras añadir las instancias inductivas adecuadas.

#### 5.5.3 Implicación para el roadmap

Esta comparación tiene **consecuencia práctica** para el módulo `Meta/` que arrancará al cerrar `Minimal/` (ver §6):

- **Codificación de Gödel sí es posible** en `Minimal` porque tenemos `pow` y TFA (vía meta-axioma). La función β de Gödel y la codificación primorial `Π pᵢ^aᵢ` están a tiro.
- **La prueba de Gödel I no es internalizable** en `Minimal` solo: requiere inducción sobre la complejidad sintáctica (la fórmula `IsFormula(⌜φ⌝)`). Esto **explica por qué `Meta/` arranca después de `Minimal/` pero usa material que sólo se completa en `Intermediate/` o `Full/`**.

En suma: `Minimal + Ax-P` es **lo más débil donde se puede *enunciar* Gödel I con fluidez**, aunque la *demostración* requiere extender el sistema. Esto justifica formalmente el sándwich `Minimal → Meta (enunciados) → Intermediate (demostraciones)`.

---

## 6 · Próximos pasos relacionados

Actualizado 2026-06-06 tras el cierre del Bloque VIII extendido:

- **Block7** (`IsFunction`, Teo F3): ✅ completado 2026-06-03, sin axiomas nuevos.
- **Bloque VIII extendido** (`pow`, `prod_pairs`, `IsFactorization`, `Ax-P`): ✅ completado 2026-06-06, +4 axiomas y +1 meta-axioma analizados en §3.4 y §3.5.
- **`Meta/` (próximo, arranca al cerrar `Minimal/`)**: Fases 18-19 del spec — Gödelización (G : símbolos → ℕ, ⌜·⌝, IsFormula, Dem). Aprovechará `pow` + TFA. **No introduce nuevos axiomas matemáticos** sobre `Minimal/`, sólo meta-codificación. Diagnóstico completo de hipótesis Gödel I/II en [GODEL-STATUS.md](GODEL-STATUS.md).
- **`Intermediate/`** y **`Full/`** (PLANNING §6, §7): se diseñan precisamente para *eliminar* `ax21, ax24, ax_C3, ax_L3` (vía inducción restringida) y `ax_p_tfa` (vía inducción fuerte), introduciendo inducción restringida primero y general después. Los 4 axiomas definicionales (`ax_pow_zero/succ`, `ax_prodp_nil/cons`) **permanecen** en cualquier nivel que mantenga `pow`/`prod_pairs` como símbolos primitivos.

---

## 7 · Referencias

- [Robinson arithmetic — Wikipedia](https://en.wikipedia.org/wiki/Robinson_arithmetic)
- [Topics in Nonstandard Arithmetic 6: The Axioms — Diagonal Argument](https://diagonalargument.com/2020/10/21/topics-in-nonstandard-arithmetic-6-the-axioms/)
- [Robinson arithmetic — Grokipedia](https://grokipedia.com/page/Robinson_arithmetic)
- [Weak Systems of Arithmetic — The n-Category Café](https://golem.ph.utexas.edu/category/2011/10/weak_systems_of_arithmetic.html)
- [Robinson Arithmetic Essentials — Number Analytics](https://www.numberanalytics.com/blog/ultimate-guide-robinson-arithmetic-set-theory-proof-theory)
- [The metamathematics of very weak arithmetics — Franks (2005)](https://www.lps.uci.edu/files/grad-alumni/CFranks/veryweak.pdf)
- [Elementary function arithmetic — nLab](https://ncatlab.org/nlab/show/elementary+function+arithmetic) (para §5.5 comparación con EFA)
- [Bounded arithmetic — Wikipedia](https://en.wikipedia.org/wiki/Bounded_arithmetic) (para §5.5 comparación con I∆₀+Exp)
- Documentación interna: [PLANNING.md](PLANNING.md), [DISCUSIONES.md](DISCUSIONES.md), [REFERENCE.md](REFERENCE.md), [TuplasFuncionesYListas.md](TuplasFuncionesYListas.md), [GODEL-STATUS.md](GODEL-STATUS.md).

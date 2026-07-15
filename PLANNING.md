# Hoja de Ruta Fundacional — Plan Estratégico

**Última actualización:** 2026-07-14 — Estado global: **83 módulos** (Minimal 11 + Meta 61 + Full 11), **97 jobs**, 0 sorrys, **7 `axiom` de Lean** (`AXIOMS.md`). **MÓDULO A de `NegVerifier` COMPLETO (§43):** el decodificador (`Meta/CodeDecode.lean` biyección de fórmulas + `Meta/ChainDecode.lean` cadenas + ensamblado `decodeChain_prf`). `Minimal/` cerrado; `Full/` deriva el fragmento inductivo + **TFA completo**; `Meta/` tiene la **cadena Gödel REAL** (la capa legacy con D2/D3 postulados fue **RETIRADA en F7a** — era insólida, ver `GODEL-STATUS.md`).

**Gödel I — COMPLETO** (`goedel_first_undecidable_real'`): `⊬G ∧ ⊬¬G`, **sin ningún postulado gödeliano**, con la **reflexión como hipótesis META explícita** (`Reflects`), reducida a **ω‑consistencia clásica + `NegVerifier`** (`Meta/OmegaReflect.lean`). **D1** (`repr_pos'_prf`) y **D2** (`d2_prf`) reales. **Gödel II** (`goedel_second'`) montado, **módulo `axiom d3`**.

**Dos frentes abiertos, ambos con plan escrito y sin incógnitas de diseño:**

1. 📄 **[PLAN-NEGVERIFIER.md](PLAN-NEGVERIFIER.md)** — descargar `NegVerifier` (solidez estructural del verificador + decodificador + inversión de los 21 tags) ⇒ cierra la **indecidibilidad de `G`** desde la ω‑consistencia, y nada más. **Módulo A (decodificador) COMPLETO** (`decodeChain_prf` = cadena aceptada ⟹ `Prf`); **siguiente = módulo B** (los 21 tags, compartido con `hC_dot`/D3). *~7‑10 sesiones restantes.*
2. **D3** — reducida a **UN SOLO lema** (`d3_prf_of_chainOkDot`): falta el cuerpo `lineOkB` de `hC_dot` ⇒ `d3_prf` → `goedel_second_prf` → **F7b** (7→6 `axiom`). *~2‑4 sesiones.*

> 🔗 **Los dos frentes COMPARTEN** el análisis de los **21 tags** de `lineWF` (positivo para D3, negativo para `NegVerifier`): conviene construirlo **una sola vez**. Ver `PLAN-NEGVERIFIER.md` §5.

Estado fino: [NEXT-STEPS.md](NEXT-STEPS.md) (🎯 LO QUE QUEDA), [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md), [GODEL-STATUS.md](GODEL-STATUS.md), [AXIOMS.md](AXIOMS.md). *(El resto de este documento refleja el plan original centrado en `Minimal/`, 2026-06-06.)*
**Autor**: Julián Calderón Almendros

> Este documento describe la visión estratégica y la planificación a largo plazo para los proyectos que se construirán sobre la base del sistema `FOL`.

---

## 1. Visión General

El objetivo es trascender la lógica pura para abordar la **fundamentación de las matemáticas**. Esto implica usar el sistema `FOL=` como cimiento para construir, paso a paso, la aritmética, las estructuras de datos (tuplas, listas) y, eventualmente, teorías más complejas como la de conjuntos.

Para mantener la claridad conceptual y la modularidad, este esfuerzo se dividirá en tres proyectos interconectados pero independientes.

---

## 2. Arquitectura de Proyectos

En lugar de expandir el proyecto `FOL` indefinidamente, adoptaremos una arquitectura de micro-proyectos, donde cada uno tiene un objetivo claro y depende de los anteriores.

### Proyecto 1: `FOL` (Este Proyecto)

- **Rol**: **Fundamento Lógico**.
- **Descripción**: Provee una formalización completa y verificada de la Lógica de Primer Orden con Igualdad (`FOL=`).
- **Estado**: Se considera una dependencia estable y completa. Su desarrollo futuro se limitará a correcciones o mejoras internas, pero su API se mantendrá estable.

### Proyecto 2: `ROBINSON_PlusPlus` (Este Proyecto)

- **Rol**: **Fundamento Aritmético**.
- **Descripción**: Un proyecto dedicado a explorar y formalizar diferentes sistemas axiomáticos para la aritmética, construidos sobre `FOL=`. Su objetivo es fundar rigurosamente los números naturales y, a partir de ellos, las tuplas y listas.
- **Dependencia**: `FOL`.

---

## 3. El Proyecto `ROBINSON_PlusPlus` en Detalle

### 3.1. Filosofía y Justificación

**Embedding desde FOL=**: Es crucial entender que el sistema `Minimal` no se construye desde cero. Se trata de una **extensión** del sistema `FOL=` (Lógica de Primer Orden con Igualdad) formalizado en el proyecto `FOL`. Esto significa que `Minimal` hereda toda la maquinaria lógica de `FOL=`, incluyendo las reglas de deducción natural y las propiedades de la igualdad. El sistema `Minimal` se limita a añadir los axiomas aritméticos sobre este fundamento lógico ya establecido.

Este proyecto aborda la cuestión de "qué se necesita para construir X". La idea de empezar con un sistema minimalista (como la aritmética de Robinson o el sistema de 22 axiomas) no es proponerlo como el sistema final, sino como un ejercicio fundacional para responder a la pregunta: *¿Cuál es la base mínima de la que podemos derivar la función de Cantor y, por tanto, las tuplas y listas?*

La aparente inconsistencia de usar recursión para `+` y `*` pero no para otras funciones es deliberada: se trata de un sistema "eximio" que nos fuerza a adoptar como axiomas propiedades (como la conmutatividad) que intuimos como "obvias" pero que no podemos demostrar sin inducción.

### 3.2. Estructura de Módulos

El proyecto se organizará en tres directorios principales, cada uno representando un sistema axiomático de fortaleza creciente:

1. **`Minimal/`** ✅ **0 sorrys**:
    - **Sistema**: **34 axiomas matemáticos** (25 aritméticos + 7 listas + 2 factorización; tras añadir pow/prod_pairs para Bloque VIII extendido) más 5 meta-reglas de FOL (ADR-008) + 1 meta-axioma Ax-P (TFA) en Block8. No incluye esquema de inducción.
    - **Objetivo cumplido**: Demostrado que este sistema es suficiente para construir la función de Cantor, los pares con proyecciones, las listas con concatenación y pertenencia, las funciones discretas (`IsFunction`), primos (`Dvd`, `IsPrime`) y factorización prima (`IsFactorization` + Ax-P TFA) — Bloques I a VIII Fase 17 completa. Análisis comparativo con Q (7 ax) y PA⁻ (16 ax) en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md).

2. **`Intermediate/`**:
    - **Sistema**: Un sistema reducido (13 axiomas) más un **esquema de inducción restringido** a un conjunto finito de fórmulas, como se describe en el Apéndice B de `TuplasFuncionesYListas.md`.
    - **Objetivo**: Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` son ahora **teoremas** derivables del principio de inducción finito.

3. **`Full/`**:
    - **Sistema**: Los axiomas de Peano puros con el **esquema de inducción general** sobre todas las fórmulas del lenguaje (Apéndice C).
    - **Objetivo**: Demostrar que este es el sistema canónico donde todos los demás axiomas (álgebra, orden, TFA, etc.) se convierten en teoremas.

### 3.3. Objetivo de Paridad

El objetivo final de `ROBINSON_PlusPlus` es establecer formalmente los **embeddings** entre estos sistemas:
`FOL⁼ ⊂ Minimal ⊂ Intermediate ⊂ Full`
Esto se logrará demostrando que los axiomas de un nivel son teoremas en el nivel superior.

### 3.4. Signos que no aparecen en los alfabetos de FOL⁼ pero sí en los axiomas de `Minimal`

- `+`, `*`, `σ`, `τ`, `div2`, `mod2`, `cantor_func` (o `pair`), `π₁`, `π₂`, `Nil`, `Cons`, `In`, `⊕`, `√` .

- `tau_symb` podría cambiarse por `pred_symb` para ser más descriptivo.

- De hecho, el sistema `Minimal`, debería de incluir también símbolos subíndices y superíndices, como $\{ \quad {}^1 , \quad {}^2, \quad {}^{-1}, \quad {}^{-2}, \quad {}_1, \quad {}_2, \ldots\quad \}$. De esta forma no nos haría falta un símbolo como `π₁` o `π₂`, directamente en el alfabeto, sino que tendríamos `π`, y los anteriores subíndices y superíndices para componer nombres de funciones, por ejemplo, o `i-ésimo` elemento de una lista o de un conjunto ordenado.

- El símbolo `In` soy partidario de cambiarlo por `∈` infijo, y `⊕` por `##`. `Cons` podría sustituirse por `::` y `Nil` por `[]`.

- De esta forma, el alfabeto de `Minimal` se mantendría más cercano a la notación  matemática estándar, aunque esto es una cuestión de estilo y no afecta a la fundamentación.

- La función `div2` podría pasar a representarse como $/_2$, igual que `mod2` como `%_2`, para mantener la notación más cercana a la matemática estándar.

---

## 4. El Problema de la Especificación de Lean 4

Un tema transversal a todos los proyectos fundacionales es la necesidad de ser explícitos sobre qué características del sistema anfitrión (Lean 4 y su Cálculo de Construcciones Inductivas) estamos utilizando.

- **Acción**: Cada proyecto (`FOL`, `ROBINSON_PlusPlus`, etc.) deberá mantener un documento `FOUNDATIONS.md`.
- **Contenido**: Este documento actuará como un "diccionario fundacional", explicando el "valor real" de cada primitiva de Lean utilizada. Por ejemplo:
  - "Usamos `inductive Formula ...`. Esto corresponde en nuestra metateoría a la definición de un conjunto por sus reglas de formación y nos concede el principio de inducción estructural sobre las fórmulas."
  - "Usamos `fun x => ...` de Lean, que corresponde al concepto de función en nuestra metateoría."

---

## 5. Plan de Desarrollo Detallado

> Este plan de desarrollo sigue la especificación de `TuplasFuncionesYListas.md`.

### Fase 1: Sistema `Minimal` — Fundamentos y Aritmética Básica

**Objetivo**: Establecer la base axiomática y demostrar las propiedades aritméticas elementales (Bloques I-III).
**Estado**: ✅ **Completado**

**Tareas**:

- [x] **Estructura del Proyecto**: Crear el directorio `ROBINSON_PlusPlus/Minimal/`.
- [x] **Axiomas**: Crear el módulo `Minimal/Axioms.lean` y formalizar los axiomas del sistema.
- [x] **Bloque I (Aritmética)**: Crear `Minimal/Theorems/Block1.lean` y demostrar los Teoremas 1.1 a 3.11.
- [x] **Bloque II (Raíz Cuadrada)**: Crear `Minimal/Theorems/Block2.lean` y demostrar los Teoremas 4.1 a 4.6.
- [x] **Bloque III (div2/mod2)**: Crear `Minimal/Theorems/Block3.lean` y demostrar los Teoremas 5.1 a 5.10.

### Fase 2: Sistema `Minimal` — Función de Cantor

**Objetivo**: Construir la función de apareamiento de Cantor (Bloque IV) y definir las tuplas (Bloque V).
**Estado**: ✅ **Completado**

**Tareas**:

- [x] **Bloque IV (Cantor)**: `Minimal/Theorems/Block4.lean`.
  - [x] Lema de Paridad (Lema P1) — `parity_lemma`.
  - [x] Totalidad de la función de Cantor (Teo C2) — `cantor_totality`.
  - [x] Inyectividad de la función de Cantor (Teo C4) — `cantor_injective_c`.
- [x] **Bloque IV-C5 (Lema C5)**: `Minimal/Theorems/Block4_C5.lean`.
  - [x] Existencia: `∀ c, ∃ w, w(w+1) ≤ 2c < (w+1)(w+2)` — `lemma_C5`.
  - [x] Unicidad: `lemma_C5_unique` (vía monotonía `mono_w_w1` + tricotomía).
  - [x] `cantor_bounds` exportado para uso en C6_C7.
- [x] **Bloque IV-C6/C7 (Sobreyectividad y unicidad)**: `Minimal/Theorems/Block4_C6_C7.lean`.
  - [x] `add_left_cancel` vía ax27.
  - [x] `cantor_uniqueness` (Teo C7) — vía `cantor_bounds` + `lemma_C5_unique` + ax28.
  - [x] `cantor_surjectivity` (Teo C6) — construcción con `sub`/ax29_sub_witness, `parity_lemma`, `le_of_mul_le_mul_left`. **Elimina la dependencia de ax22/ax23 como axiomas temporales** (siguen en la lista por compatibilidad con Block5, pero son demostrables).
- [x] **Bloque V (Tuplas)**: `Minimal/Theorems/Block5.lean`.
  - [x] Lema clave `is_cantor_pair (x y) : mul two (pair x y) =eq cantor_poly x y`.
  - [x] `mod2_of_even`, `proj1_pair_eq_x`, `proj2_pair_eq_y` (Teos C8-C9 vía `cantor_uniqueness`).
  - [x] `pair_proj_eq_c` (Teo C10 vía `cantor_injective_c`).
  - [x] `pair_inj` (Teo C11 vía `cantor_uniqueness`).

### Fase 3: Sistema `Minimal` — Listas

**Objetivo**: Fundamentar las listas (Bloque VI).
**Estado**: ✅ **Completado**

**Tareas**:

- [x] **Bloque VI (Listas)**: `Minimal/Theorems/Block6.lean`.
  - [x] `cons_neq_nil` (Teo L1) — vía ax_L0 + `is_cantor_pair` + teo_2_9 + ax2.
  - [x] `cons_inj` (Teo L2) — vía ax_L0 + `pair_inj` + ax3.
  - [x] `in_cons_self_nil` (Teo L4) — vía ax_L2 triple-spec.
  - [x] `in_cons_nil_imp_eq` (Teo L5) — vía ax_L2 + ax_L1.
  - [x] `concat_singletons` (Teo L6) — vía ax_C1 + ax_C2.
  - [x] `concat_assoc` (Teo L7) — postulado como `ax_C3_concat_assoc` (requiere inducción sobre L; pasará a teorema en `Intermediate/`).
  - [x] `in_concat_iff` (Teo L8) — postulado como `ax_L3_in_concat` (requiere inducción sobre L).

### Fase 4: Sistema `Minimal` — Funciones discretas

**Objetivo**: Bloque VII de `TuplasFuncionesYListas.md`.
**Estado**: ✅ **Completado** (2026-06-03).

**Tareas**:

- [x] **Bloque VII (Funciones)**: `Minimal/Theorems/Block7.lean`.
  - [x] Definir el predicado `IsFunction (f : Term) : Prop` (Def 21) como meta-Prop estilo Block7/8.
  - [x] Definir la relación `Functional (f : Term) : Prop` (Def 24) con `Map` inlineado.
  - [x] Teorema F1: `IsFunction nil` (la lista vacía es función trivial).
  - [x] Teorema F2: evaluación única (de existir un par `(x, y)` en `f` cumpliendo `IsFunction`, `y` está determinado).
  - [x] Teorema F3: isomorfismo `IsFunction ⟺ Functional`.

### Fase 5: Sistema `Minimal` — Primos y factorización

**Objetivo**: Bloque VIII de `TuplasFuncionesYListas.md` (Fase 17 completa con extensión del lenguaje).
**Estado**: ✅ **Completado** (2026-06-03 parcial; 2026-06-06 extensión completa).

**Tareas**:

- [x] **Bloque VIII — Divisibilidad y primalidad** (Def 25): `Minimal/Theorems/Block8.lean`.
  - [x] `Dvd a b : Prop` (Def 25.a): `∃ q, a·q = b`.
  - [x] `IsPrime p : Prop` (Def 25): `p ≥ 2 ∧ ∀ d, Dvd d p → d=1 ∨ d=p`.
  - [x] Lemas básicos: `dvd_refl`, `dvd_one`, `dvd_zero`, `isPrime_zero_inconsistent`, `isPrime_one_inconsistent`.
- [x] **Bloque VIII extendido — Lenguaje** (2026-06-06): `Axioms.lean`.
  - [x] Símbolos `pow_sym = "^"`, `prodp_sym = "Π_p"`.
  - [x] Constructores `pow (b e : Term)`, `prod_pairs (l : Term)`.
  - [x] 4 axiomas: `ax_pow_zero`, `ax_pow_succ`, `ax_prodp_nil`, `ax_prodp_cons`.
  - [x] Sistema 30 → 34 axiomas matemáticos (25 aritm + 7 listas + 2 factorización).
- [x] **Bloque VIII extendido — Factorización** (Def 26 + Ax-P TFA): `Block8.lean`.
  - [x] Lemas básicos: `pow_zero`, `pow_succ`, `prod_pairs_nil`, `prod_pairs_cons`.
  - [x] `IsFactorization (f n : Term) : Prop` (Def 26) como meta-Prop.
  - [x] `isFactorization_nil_one`: caso base `IsFactorization nil one`.
  - [x] Meta-axioma `ax_p_tfa` (TFA): existencia y unicidad de factorización para `n ≥ 1`.
- [x] **Fases 18-19 (Gödelización, autorreferencia)**: documentadas como fuera de scope `Minimal/` (corresponden a un módulo `Meta/` futuro, no a `Intermediate/` ni `Full/`).

### Fase 6: Sistema `Minimal` — Limpieza global

**Objetivo**: Activar el linter `unusedSimpArgs` en todos los módulos y eliminar warnings residuales.
**Estado**: ✅ **Completado** (2026-06-06).

**Tareas**:

- [x] Eliminar 411 warnings de `unusedSimpArgs` en `Block1` (22), `Block2` (274), `Block4_C5` (32), `Block4_C6_C7` (14), `Block5` (2), `Block6` (39), `Block7` (6), `Block8` (22).
- [x] Activar `set_option linter.unusedSimpArgs true` en los 11 módulos.
- [x] Build verde, 0 sorrys, 0 warnings RPP (único persistente: `FOL/Theorems/Eq.lean:130` en librería externa).

---

## 6. Futuro y Consolidación

Con el sistema `Minimal/` **cerrado a 0 sorrys reales, 0 warnings RPP y 34 axiomas matemáticos** (Bloques I-VIII completos), los siguientes pasos están descritos en detalle en [NEXT-STEPS.md](NEXT-STEPS.md). Decisión clave 2026-06-06: **el frente `Meta/` arranca al cerrar `Minimal/`**, en paralelo o antes que `Intermediate/`, porque los niveles B y C de la Gödelización (meta-codificación + predicados de demostrabilidad) no requieren inducción. Ver [GODEL-STATUS.md](GODEL-STATUS.md) para el diagnóstico completo.

Resumen ejecutivo de los ejes:

### 6.1. Eje siguiente — Módulo `Meta/` (corto/medio plazo)

**Estado**: 🔜 **Próxima fase activa** (arranque 2026-06-07).

Implementar Fases 18-19 del spec (`TuplasFuncionesYListas.md §BLOQUE VIII`) en un módulo nuevo `ROBINSON_PlusPlus/Meta/`. Estructura planificada (ver [GODEL-STATUS.md](GODEL-STATUS.md) §2.2):

- **Nivel B — `Meta/Godel.lean`**: asignación de Gödel `G : símbolos → ℕ` (Def 27), corner brackets `⌜·⌝` (Def 28), Teo G1 (inyectividad). **No requiere inducción**.
- **Nivel C — `Meta/Provability.lean`**: predicados `IsFormula`, `Dem`, lema del punto fijo (diagonalización). Algunas propiedades meta-teoréticas podrán postularse como meta-axiomas hasta tener `Intermediate/`.
- **Nivel D — `Meta/Incompleteness.lean`** (requiere `Intermediate/`): Gödel I y II formalizados internamente.

**Por qué `Meta/` antes que `Intermediate/`**: las Fases 18-19 vienen inmediatamente tras la Fase 17 en la spec, y los niveles B+C no necesitan inducción. Esperar a `Intermediate/` retrasaría material que ya se puede formalizar.

**Sinergia con TFA (Ax-P)**: la extensión del Bloque VIII (`pow`, `prod_pairs`, `Ax-P`) realizada 2026-06-06 **prepara explícitamente la codificación primorial de secuencias** usada en Gödel: `(a₁, …, aₖ) ↦ Π pᵢ^aᵢ` con descodificación única vía TFA. Ver [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §5.5.3 y [GODEL-STATUS.md](GODEL-STATUS.md) §3.

### ~~6.2. Sistema `Intermediate`~~ ❌ ELIMINADO (2026-06-11)

**Decisión 2026-06-11**: `Intermediate/` se descarta como sistema autónomo por **redundancia conceptual**. Un sistema con esquema de inducción restringido a Φ finito **es matemáticamente el caso particular** de `Full/` (cualquier instancia inductiva concreta se postula directamente en `Full/`, sin estructura adicional). El prototipo `Intermediate/Induction.lean` confirmó que la inducción general no añade fricción técnica sobre la restringida.

Toda la agenda de Intermediate (derivar ax6, ax7, ax10–12, ax18, ax19, ax21, ax24, ax_C3, ax_L3 como teoremas) **se cumple directamente en `Full/`**. Resultados actuales (ver §6.3): ax6, ax7, ax10–12, ax18, ax19, ax21, ax24 ya son teoremas en Full.

### 6.3. Sistema `Full` (en curso — único eje matemático tras la eliminación de Intermediate)

**Estado**: 🟢 En curso activo. Ver [Eje 4 de NEXT-STEPS.md](NEXT-STEPS.md) y [`Full/Induction.lean`](ROBINSON_PlusPlus/Full/Induction.lean) + [`Full/Mod2.lean`](ROBINSON_PlusPlus/Full/Mod2.lean).

Sistema con **esquema de inducción general object-level** (`ax_induction`) sobre cualquier fórmula del lenguaje. Todos los axiomas postulados en `Minimal/` que requieran inducción se derivan aquí como teoremas.

**Estado de derivación de axiomas de Minimal como teoremas en Full**:

| Axioma | Teorema | Módulo |
|---|---|---|
| ax6 | `add_comm_thm` | Full/Induction.lean |
| ax7 | (vía `add_assoc_ax`) | Full/Induction.lean |
| ax10 | `mul_comm_thm` | Full/Induction.lean |
| ax11 | (vía `mul_assoc_ax`) | Full/Induction.lean |
| ax12 | (vía `mul_distrib_ax`) | Full/Induction.lean |
| ax18 | `lt_irrefl_thm` | Full/Induction.lean |
| ax19 | `lt_trichotomy_thm` | Full/Induction.lean |
| **ax21** | `mod2_range_thm` | **Full/Mod2.lean ✅ (2026-06-11)** |
| **ax24** | `mod2_of_even_thm` | **Full/Mod2.lean ✅ (2026-06-11)** |
| **ax_C3** | `concat_assoc_thm` | **Full/Lists.lean ✅ (2026-06-11)** |
| **ax_L3** | `in_concat_thm` | **Full/Lists.lean ✅ (2026-06-11)** |
| Ax-P (TFA) | ⏳ pendiente | (necesita inducción fuerte) |

**Axiomas extra de Full** (no en Minimal, añadidos para cerrar los derivados):

- `ax_mod2_alternation : ∀n, mod2(σn)+mod2(n)=1` (Opción C.2, 2026-06-11). Conservativo respecto a Minimal: derivable allí de ax21+ax16+teo_1_3.
- `ax_list_induction (φ : Term → Formula) (base) (step) : ∀L, Γ ⊢ φ L` (meta-axioma, 2026-06-11). Inducción estructural sobre listas estilo `imp_intro`/`gen`. La conclusión es sobre todos los Terms (no solo listas), reflejando una elección de Full de tratar Term como generado por nil/cons (análogo a cómo `ax_induction` lo trata como generado por 0/σ).

**Habilita**:

- Cadena de embeddings `FOL⁼ ⊂ Minimal ⊂ Full` (sin Intermediate intermedio).
- **Nivel D de `Meta/`**: Gödel I y II demostrados internamente (requiere la inducción de `Full/`).

### 6.4. Consolidación y nuevas teorías (muy largo plazo)

- **Consolidación**: refactorizar otros proyectos (incluido `FOL`) sobre la base formalmente verificada de `ROBINSON_PlusPlus`.
- **CZF y conjuntos constructivos**: con la base aritmética + listas + factorización, el camino hacia teorías de conjuntos constructivas (Aczel CZF) queda accesible.
- **Análisis constructivo**: extender al continuo con la maquinaria aritmética desarrollada.

### 6.5. Mantenimiento del scope `Minimal/`

Pequeñas tareas de baja prioridad:

- ✅ ~~Arreglar el único warning externo: `FOL/Theorems/Eq.lean:130` (unusedSimpArg `hne`)~~ — **RESUELTO 2026-06-06** (commit `9888c58` en el repo FOL). Build global con 0 warnings.
- Auditar si `pow`/`prod_pairs` admiten reducción de axiomas (descartado en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4 — son irreducibles como recursión primitiva).
- Más teoremas sobre `IsFactorization` usando `ax_p_tfa`: lema de Euclides, multiplicatividad, etc.

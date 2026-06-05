# Hoja de Ruta Fundacional — Plan Estratégico

**Última actualización:** 2026-06-06 — `Minimal/` cerrado a 0 sorrys reales y 0 warnings con **34 axiomas matemáticos** (25 aritm + 7 listas + 2 factorización); 11 módulos (Bloques I–VIII Fase 17 completa con Ax-P TFA).
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

### Fase 4: Sistema `Minimal` — Funciones discretas (pendiente)

**Objetivo**: Bloque VII de `TuplasFuncionesYListas.md`.
**Estado**: ⏳ **Pendiente**.

**Tareas**:

- [ ] **Bloque VII (Funciones)**: `Minimal/Theorems/Block7.lean`.
  - [ ] Definir el predicado `IsFunction`.
  - [ ] Definir la evaluación `F(x)`.
  - [ ] Demostrar el isomorfismo con relaciones funcionales (Teo F3).

---

## 6. Futuro y Consolidación

Con el sistema `Minimal/` completo a **0 sorrys reales**, los siguientes pasos están descritos en detalle en [NEXT-STEPS.md](NEXT-STEPS.md). Resumen ejecutivo:

1. **Cerrar la Fase 4** (corto plazo): añadir `Block7.lean` con `IsFunction` y el isomorfismo con relaciones funcionales (Teo F3). Auditar si algún axioma postulado (`ax28_mul_two_cancel`, `ax_C3`, `ax_L3`) es realmente demostrable en `Minimal` sin inducción.
2. **Implementar el sistema `Intermediate`** (medio plazo): Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` son teoremas derivables de un principio de inducción restringido. Establecer el embedding `Minimal ⊂ Intermediate`.
3. **Implementar el sistema `Full`** (largo plazo): Demostrar que todos los axiomas "induction-bound" (`ax21`, `ax24`, `ax27`, `ax28`, `ax_C3`, `ax_L3`) y propiedades meta-teóricas se vuelven teoremas en un sistema con inducción general. Cadena completa de embeddings `FOL⁼ ⊂ Minimal ⊂ Intermediate ⊂ Full`.
4. **Consolidación**: Usar los resultados de `ROBINSON_PlusPlus` para refactorizar otros proyectos y que se apoyen en una base formalmente verificada desde `FOL=`.
5. **Nuevas Teorías** (muy largo plazo): Con una base sólida para la aritmética y los conjuntos finitos (listas), el camino hacia teorías de conjuntos constructivas como la de Aczel (CZF) se vuelve mucho más claro.

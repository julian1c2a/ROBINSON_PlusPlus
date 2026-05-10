# Hoja de Ruta Fundacional — Plan Estratégico

**Última actualización:** 2026-05-08 18:30
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

1. **`Minimal/`**:
    - **Sistema**: Los 22 axiomas descritos en `TuplasFuncionesYListas.md`. No incluye un esquema de inducción.
    - **Objetivo**: Demostrar que este sistema es suficiente para construir la función de Cantor y, con ella, una teoría de tuplas y listas (Bloques I a VI del documento).

2. **`Intermediate/`**:
    - **Sistema**: Un sistema reducido (13 axiomas) más un **esquema de inducción restringido** a un conjunto finito de fórmulas, como se describe en el Apéndice B de `TuplasFuncionesYListas.md`.
    - **Objetivo**: Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` son ahora **teoremas** derivables del principio de inducción finito.

3. **`Full/`**:
    - **Sistema**: Los axiomas de Peano puros con el **esquema de inducción general** sobre todas las fórmulas del lenguaje (Apéndice C).
    - **Objetivo**: Demostrar que este es el sistema canónico donde todos los demás axiomas (álgebra, orden, TFA, etc.) se convierten en teoremas.

### 3.3. Objetivo de Paridad

El objetivo final de `ROBINSON_PlusPlus` es establecer formalmente los **embeddings** entre estos sistemas:
`Minimal ⊂ Intermediate ⊂ Full`
Esto se logrará demostrando que los axiomas de un nivel son teoremas en el nivel superior.

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
**Estado**: ✅ **Completado** (axiomáticamente)

**Tareas**:

- [x] **Bloque IV (Cantor)**: Crear `Minimal/Theorems/Block4.lean`.
  - [x] Demostrar el Lema de Paridad (Lema P1).
  - [x] Demostrar la totalidad de la función de Cantor (Teo C2).
  - [x] Demostrar la inyectividad de la función de Cantor (Teo C4).
  - [ ] **Demostrar el Lema C5 (existencia y unicidad de `w`)**. (En progreso)
  - [ ] Demostrar la sobreyectividad (Teo C6) y unicidad proyectiva (Teo C7) para eliminar los axiomas temporales.
  - [x] Demostrar las propiedades de las proyecciones (Teos C8, C9, C10) usando los axiomas temporales.
- [x] **Bloque V (Tuplas)**: Crear `Minimal/Theorems/Block5.lean`.
  - [x] Introducir la notación `pair` (alias de `cantor_func`).
  - [x] Definir las proyecciones `π₁` y `π₂`.
  - [x] Demostrar los teoremas de isomorfismo (Teos C8-C11).

### Fase 3: Sistema `Minimal` — Listas y Funciones

**Objetivo**: Fundamentar las listas y las funciones discretas (Bloques VI-VII).
**Estado**: 🔄 **En progreso**

**Tareas**:

- [x] **Bloque VI (Listas)**: Crear `Minimal/Theorems/Block6.lean`.
  - [x] Definir `Nil` y `Cons`.
  - [x] Demostrar las propiedades fundamentales (Teos L1, L2).
  - [x] Demostrar las propiedades de pertenencia (`In`).
  - [x] Demostrar las propiedades de la concatenación (`⊕`). (Parcial, 2 sorries por depender de inducción)
- [ ] **Bloque VII (Funciones)**: Crear `Minimal/Theorems/Block7.lean`.
  - [ ] Definir el predicado `IsFunction`.
  - [ ] Definir la evaluación `F(x)`.
  - [ ] Demostrar el isomorfismo con relaciones funcionales (Teo F3).

---

## 6. Futuro y Consolidación

Una vez completado el sistema `Minimal`, los siguientes pasos a largo plazo son:

1. **Implementar el sistema `Intermediate`**: Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` son teoremas derivables de un principio de inducción restringido.
2. **Implementar el sistema `Full`**: Demostrar que todos los axiomas temporales y propiedades meta-teóricas se vuelven teoremas en un sistema con inducción general.
3. **Consolidación**: Usar los resultados de `ROBINSON_PlusPlus` para refactorizar otros proyectos y que se apoyen en una base formalmente verificada desde `FOL=`.
4. **Nuevas Teorías**: Con una base sólida para la aritmética y los conjuntos finitos (listas), el camino hacia teorías de conjuntos constructivas como la de Aczel (CZF) se vuelve mucho más claro.

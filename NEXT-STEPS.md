# Próximos Pasos — ROBINSON_PlusPlus

**Última actualización:** 2026-05-09
**Autor**: Julián Calderón Almendros

> Este archivo hace un seguimiento de las fases de desarrollo planificadas para el proyecto `ROBINSON_PlusPlus`, comenzando con el sistema `Minimal`.
> **Nota:** La especificación detallada de axiomas y teoremas se encuentra en `TuplasFuncionesYListas.md`.

---

## Fase 1: Sistema `Minimal` — Fundamentos y Aritmética Básica

**Objetivo**: Establecer la base axiomática y demostrar las propiedades aritméticas elementales (Bloques I-III).

**Tareas**:

- [x] **Estructura del Proyecto**: Crear el directorio `ROBINSON_PlusPlus/Minimal/`.
- [x] **Axiomas**: Crear el módulo `Minimal/Axioms.lean` y formalizar los 22 axiomas del sistema.
- [x] **Bloque I (Aritmética)**: Crear `Minimal/Theorems/Block1.lean` y demostrar los Teoremas 1.1 a 3.11.
- [x] **Bloque II (Raíz Cuadrada)**: Crear `Minimal/Theorems/Block2.lean` y demostrar los Teoremas 4.1 a 4.6.
- [x] **Bloque III (div2/mod2)**: Crear `Minimal/Theorems/Block3.lean` y demostrar los Teoremas 5.1 a 5.10.

**Dependencias**: Proyecto `FOL` (estable).
**Complejidad**: Media

---

## Fase 2: Sistema `Minimal` — Función de Cantor

**Objetivo**: Construir la función de apareamiento de Cantor (Bloque IV) y definir las tuplas (Bloque V).

**Tareas**:

- [x] **Bloque IV (Cantor)**: Crear `Minimal/Theorems/Block4.lean`.
  - [x] Demostrar el Lema de Paridad (Lema P1).
  - [x] Demostrar la totalidad de la función de Cantor (Teo C2).
  - [x] Demostrar la inyectividad de la función de Cantor (Teo C4).
  - [ ] Demostrar el Lema C5 (existencia y unicidad de `w`). (En progreso)
  - [ ] Demostrar la sobreyectividad (Teo C6) y unicidad proyectiva (Teo C7) para eliminar los axiomas temporales.
  - [x] Demostrar las propiedades de las proyecciones (Teos C8, C9, C10) usando los axiomas temporales.
- [ ] **Bloque V (Tuplas)**: Crear `Minimal/Theorems/Block5.lean`.
  - [ ] Introducir la notación `⟨x, y⟩`.
  - [ ] Definir las proyecciones `[c].1`, `[c].2`.
  - [ ] Demostrar los teoremas de isomorfismo (Teos C8-C11).

**Dependencias**: Fase 1 completada.
**Complejidad**: Alta

---

## Fase 3: Sistema `Minimal` — Listas y Funciones

**Objetivo**: Fundamentar las listas y las funciones discretas (Bloques VI-VII).

**Tareas**:

- [ ] **Bloque VI (Listas)**: Crear `Minimal/Theorems/Block6.lean`.
  - [ ] Definir `Nil` y `Cons`.
  - [ ] Demostrar las propiedades fundamentales (Teos L1, L2).
  - [ ] Añadir axiomas para `In` y `⊕` y demostrar sus propiedades.
- [ ] **Bloque VII (Funciones)**: Crear `Minimal/Theorems/Block7.lean`.
  - [ ] Definir el predicado `IsFunction`.
  - [ ] Definir la evaluación `F(x)`.
  - [ ] Demostrar el isomorfismo con relaciones funcionales (Teo F3).

**Dependencias**: Fase 2 completada.
**Complejidad**: Media

---

## Resumen de Estado

| Fase | Descripción | Estado |
|-------|-------------|--------|
| 1 | Fundamentos y Aritmética | ✅ Completado |
| 2 | Función de Cantor y Tuplas | ❌ Pendiente |
| 3 | Listas y Funciones | ❌ Pendiente |

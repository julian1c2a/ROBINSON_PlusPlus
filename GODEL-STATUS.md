# Frente Gödel — Estado y Roadmap

**Last updated:** 2026-06-06 — **Niveles B y C implementados** (`Meta/Godel.lean`: G, ⌜·⌝, Teo G1; `Meta/Provability.lean`: formCode, IsFormula, Provable, Dem, lema del punto fijo, sentencia de Gödel). Las propiedades profundas del Nivel C (Dem, diagonalización, representabilidad) se adoptan como **meta-axiomas** según lo previsto. Próximo: Nivel D (requiere `Intermediate/`/`Full/`).
**Author:** Julián Calderón Almendros
**Nivel del documento**: A (diagnóstico documental; no contiene código Lean).

Este documento responde a la pregunta: *¿qué relación tiene el sistema `Minimal/` con los teoremas de incompletitud de Gödel, y qué se va a formalizar al respecto en `Meta/`?*

---

## 1 · ¿Satisface `Minimal` las hipótesis de Gödel I/II?

El primer teorema de incompletitud de Gödel (Gödel I) se aplica a cualquier teoría `T` que cumpla:

| Hipótesis | Significado | ¿La cumple `Minimal`? |
|---|---|---|
| **Recursivamente axiomatizable** | El conjunto de axiomas es decidible algorítmicamente | ✅ `axioms : List Formula` es una lista finita y explícita |
| **Consistente** | No deriva `⊥` | ✅ Asumido (no demostrable internamente — Gödel II) |
| **Expresividad aritmética** | Captura `+`, `·`, `<` con sus propiedades | ✅ Tiene los 34 axiomas matemáticos descritos en `MINIMAL-AXIOMS.md` |
| **Suficiente fuerza** | Representa todas las funciones recursivas primitivas (o al menos las necesarias para la β-función de Gödel) | ⚠️ Discusión: ver §1.1 |

### 1.1 La cuestión de la "suficiente fuerza"

Gödel I exige que `T` represente formalmente todas las funciones recursivas primitivas (o que existan **alternativas equivalentes**, como una versión más débil con codificación primorial). Análisis:

- **Q (Robinson)** ya es suficiente. Es el ejemplo canónico de "teoría minimal con Gödel I". Como `Minimal ⊇ Q-núcleo` (compartimos 6 axiomas básicos) y añadimos más estructura, **Minimal es a fortiori suficiente**.
- **El TFA (Ax-P) en `Minimal`** facilita aún más la codificación: la **función β de Gödel** (que codifica secuencias finitas como un único número) tiene una alternativa más directa usando primos: una secuencia `(a₁, …, aₖ)` se codifica como `Π pᵢ^aᵢ` con `pᵢ` el `i`-ésimo primo. Esta codificación primorial requiere **exactamente lo que añadimos**: `pow`, `prod_pairs` y `Ax-P` (para garantizar unicidad de descodificación).
- **Sin TFA**, la codificación de secuencias en `Minimal` sería posible solo vía Cantor pairing (que ya está) o listas (también). La adición de TFA da una **tercera ruta más natural** para Gödel.

**Conclusión**: ✅ `Minimal` cumple las hipótesis de Gödel I sin reservas.

### 1.2 Gödel II en `Minimal`

Gödel II dice que `T` no puede demostrar su propia consistencia (`Con(T)`) si `T` es consistente y satisface ciertas condiciones de demostrabilidad. Para `Minimal`:

- **Aplica** si y sólo si se puede formalizar internamente la consistencia (`Con(Minimal)`) como una fórmula del lenguaje.
- Eso requiere `IsFormula`, `Dem`, y la sentencia `¬∃p, Dem(p, ⌜⊥⌝)`.
- Estos predicados pertenecen al **nivel B-C** del frente Gödel (ver §3 abajo); en `Minimal/` puro **no están**.

**Conclusión**: Gödel II aplica **estructuralmente** a `Minimal`, pero su formulación requiere material que arrancará en `Meta/`.

---

## 2 · ¿Qué se formaliza en este proyecto sobre Gödel?

La spec original (`TuplasFuncionesYListas.md §BLOQUE VIII Fases 18-19`) define:

- **Def 27**: Función de Gödel `G : Λ → ℕ` (asignación numérica inyectiva a los símbolos del lenguaje).
- **Def 28**: Corner brackets `⌜s₁…sₖ⌝ := Cons(G(s₁), Cons(…Cons(G(sₖ), Nil)…))`.
- **Teo G1**: Inyectividad de ⌜·⌝ — `⌜S⌝ = ⌜S'⌝ ⟹ S = S'`.
- **Fase 19**: Predicados `IsFormula(x)`, `Dem(p, φ)`, lema del punto fijo (diagonalización), sentencia de Gödel.

Estos contenidos **se moverán a un módulo nuevo `Meta/`** del proyecto, que arrancará al cerrar `Minimal/`.

### 2.1 Por qué `Meta/` arranca al cerrar `Minimal/` (no después de `Intermediate/`)

Hay dos consideraciones que apuntan al mismo lado:

1. **Logística de spec**: las Fases 18-19 vienen inmediatamente después de la Fase 17 (Bloque VIII estándar). Mantener el orden de la spec ayuda a la trazabilidad.
2. **Compromiso de scope**: lo que se formaliza en `Meta/` (G, ⌜·⌝, Teo G1) **no requiere inducción**. Es meta-codificación pura. Por tanto puede vivir sobre `Minimal/` sin esperar a `Intermediate/`.

Lo que sí requiere `Intermediate/` o `Full/` es la **demostración** de Gödel I/II como teoremas internos. En `Minimal+Meta/` lo que tendremos es:

- ✅ Codificación operativa.
- ✅ Teo G1 (inyectividad de la asignación).
- ✅ `IsFormula`, `Provable`, `Dem` definidos (`Meta/Provability.lean`); `provable_formCode_iff` demostrado. El lema del punto fijo (`diagonal_lemma`), la sentencia de Gödel `goedelSentence` y la representabilidad (`provFormula_repr`, `dem_iff_provable`) se adoptan como **meta-axiomas** (su demostración requiere Nivel D).

Esta separación es **deliberada**: queremos tener los enunciados de Gödel disponibles tan pronto como sea posible (en `Minimal+Meta/`), incluso si las demostraciones esperan a sistemas más fuertes.

### 2.2 Niveles de ambición para `Meta/`

El frente Gödel se descompone en cuatro niveles (idénticos a la taxonomía discutida en el repaso 2026-06-06):

| Nivel | Contenido | Ubicación | Estado |
|---|---|---|---|
| **A** | Discusión documental: hipótesis Gödel, scope, relación TFA ↔ Gödel | Este documento + `MINIMAL-AXIOMS.md` §5.5 | ✅ 2026-06-06 |
| **B** | Meta-codificación: `G : sym → ℕ`, ⌜·⌝, Teo G1 (inyectividad) | `Meta/Godel.lean` ✅ | ✅ 2026-06-06 |
| **C** | Predicados de demostrabilidad: `IsFormula`, `Dem`, lema del punto fijo | `Meta/Provability.lean` ✅ | ✅ 2026-06-06 (props profundas como meta-axiomas) |
| **D** | Teoremas de incompletitud: Gödel I (mitad esencial) demostrado internamente | `Meta/Incompleteness.lean` ✅ | 🟡 2026-06-12 (Gödel I mitad esencial; otra mitad + Gödel II pendientes) |

La **arquitectura propuesta** para `Meta/`:

```text
Meta/
├── Godel.lean              # Nivel B: G, ⌜·⌝, Teo G1  ✅ (2026-06-06)
├── Provability.lean        # Nivel C: IsFormula, Dem, punto fijo, G_Min  ✅ (2026-06-06)
└── Incompleteness.lean     # Nivel D: Gödel I mitad esencial  🟡 (2026-06-12)
```

### Nivel D — estado detallado (2026-06-12)

`Meta/Incompleteness.lean` deriva la **mitad esencial del Primer Teorema** a
partir de las condiciones de demostrabilidad postuladas en el Nivel C:

- ✅ **`goedel_first_unprovable`** : `Consistent → ¬(axioms ⊢ goedelSentence)`.
  Si el sistema es consistente, la sentencia de Gödel `G` no es demostrable.
  Prueba: `⊢ G` → (D1, `provFormula_repr`) `⊢ Prov(⌜G⌝)`; punto fijo
  (`goedelSentence_fixedpoint`) da `⊢ ¬Prov(⌜G⌝)`; `mp` → `⊢ ⊥`.
- ✅ **`goedel_first_true`** : `G` es verdadera-pero-indemostrable (su código
  no es `Provable`, que es exactamente lo que `G` afirma).
- ✅ **`incompleteness`** : `Consistent → ∃ φ, ¬(axioms ⊢ φ)`.

- ✅ **Gödel II** (`goedel_second`, 2026-06-12): `Consistent → ¬(axioms ⊢ Con)`
  con `Con := ¬Prov(⌜⊥⌝)`. **Postulando D2 y D3** (condiciones de
  Hilbert-Bernays-Löb; D1 ya estaba vía `provFormula_repr`). Lema crucial
  `con_imp_goedelSentence : ⊢ (Con ⇒ G)` (Gödel I formalizado), derivado de
  D1/D2/D3 + punto fijo. Notable: toda la cadena (incl. contrapositiva) se
  construye con `imp_intro`/`mp`, **sin DNE object-level** — funciona en el FOL
  intuicionista.

**Pendiente** (requiere más, documentado en `Incompleteness.lean`):

- ⏳ **Otra mitad de Gödel I** (`⊬ ¬G`): necesita **ω-consistencia** (Gödel) o
  eliminación de doble negación object-level (FOL aquí es **intuicionista** —
  la DNE sólo está con `doubleNegAxiom` en contexto), o el **truco de Rosser**.

**Sutileza ω-lógica** (honestidad): el sistema de RPP usa la meta-regla `gen`
(ω-regla, `FOL/MetaRules.lean`), que hace `axioms ⊢` no finitariamente r.e. El
Nivel D deriva la **lógica** de Gödel I *dadas* las condiciones de
demostrabilidad como postulados — el ejercicio estándar de libro. La
justificación de esos postulados para el sistema concreto (finitario vs
ω-lógico) es una discusión meta-teórica separada.

Los niveles B y C **pueden coexistir con `Minimal/`** porque sólo usan meta-codificación. El nivel D requerirá la maquinaria de `Intermediate/` o `Full/` (inducción para las propiedades de `Dem`).

---

## 3 · TFA (Ax-P) y la codificación de Gödel

Una observación clave del análisis 2026-06-06 (ver `MINIMAL-AXIOMS.md` §5.5.3): la extensión de `Minimal/` con `pow`, `prod_pairs` y TFA **prepara el terreno para Gödel** de manera natural.

### 3.1 Codificación primorial de secuencias

En la formalización clásica de Gödel, la codificación de secuencias usa la **función β** definida sobre el Teorema Chino del Resto. En `Minimal+Ax-P` tenemos una alternativa más limpia:

> Una secuencia `(a₁, a₂, …, aₖ)` se codifica como `prod_pairs [(p₁, a₁), (p₂, a₂), …, (pₖ, aₖ)]`, donde `pᵢ` es el `i`-ésimo primo.

La **descodificación** es única gracias al TFA (`ax_p_tfa`): dada una factorización, la lista de pares está determinada. Esto convierte la β-función en innecesaria para muchos propósitos de Gödelización.

### 3.2 ¿Es Ax-P estrictamente necesario para Meta/Godel.lean?

**No para el Nivel B** (G, ⌜·⌝, Teo G1). En la implementación (`Meta/Godel.lean`), la inyectividad plena `encode_injective` se establece a nivel **meta** (inducción estructural Lean + inyectividad de los constructores `cons`/`func`/`G` vía `injection`), sin TFA ni consistencia; la versión object-level `encode_cons_inj` reutiliza `cons_inj` (Block6.lean). Pasar de la object-level a la conclusión meta `S = S'` sí requeriría `Con(axioms)`, por lo que esa conexión interna se difiere al Nivel C/D.

**Sí para usos avanzados** del Nivel C: si queremos demostrar propiedades sobre la decodificación de secuencias (longitud única, posiciones únicas), TFA es la herramienta natural.

**Sí para conexión con la formalización clásica**: cualquier presentación moderna de Gödel I (por ejemplo Smullyan, Boolos) usa codificación primorial vía TFA.

Decisión: **mantener TFA como meta-axioma en `Minimal/`** facilita Meta/ ahora y futuro.

---

## 4 · Lo que NO está en scope

Para mantener el proyecto manejable, los siguientes temas se **declaran fuera de scope** explícitamente:

| Tema | Razón |
|---|---|
| **Demostración interna de Gödel II** | Requiere condiciones de demostrabilidad de Löb, inducción fuerte, y maquinaria que va más allá de `Full/`. Posible proyecto independiente futuro. |
| **Teorema de Rosser** (versión sin ω-consistencia) | Variante técnica de Gödel I; no añade contenido conceptual al proyecto. |
| **Teoremas de indefinibilidad de Tarski** (definibilidad de la verdad) | Relacionado con Gödel pero ortogonal al objetivo de `Meta/`. |
| **Teorías más fuertes** (PA + Π₁-reflection, ZFC, etc.) | Fuera del alcance de un proyecto sobre aritmética minimal. |

---

## 5 · Roadmap del frente Gödel

| Fecha (planificada) | Hito | Módulo |
|---|---|---|
| **2026-06-06** | Cierre `Minimal/` con Ax-P y diagnóstico del frente Gödel (Nivel A) | `MINIMAL-AXIOMS.md` §5.5, este documento |
| **2026-06-06** | ✅ `Meta/Godel.lean` (Nivel B: G, ⌜·⌝, Teo G1) **completado** | `Meta/Godel.lean` |
| **2026-06-06** | ✅ `Meta/Provability.lean` (Nivel C: IsFormula, Provable, Dem, punto fijo, G_Min) **completado** | `Meta/Provability.lean` |
| **TBD** | `Intermediate/` paralelo: derivación de los 9+3 axiomas inductivos | `Intermediate/Axioms.lean` |
| **TBD** | `Meta/Incompleteness.lean` (Nivel D: Gödel I formalmente) | requiere `Intermediate/` |

Los plazos para el Nivel C y D dependen del ritmo del proyecto; con el **Nivel B completado** (2026-06-06, `Meta/Godel.lean`), el siguiente paso concreto es el **Nivel C** (`Meta/Provability.lean`: IsFormula, Dem, lema del punto fijo).

---

## 6 · Referencias técnicas

- Gödel, K. (1931). *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*.
- Smullyan, R. (1992). *Gödel's Incompleteness Theorems*. Oxford University Press. — Tratamiento moderno con codificación primorial.
- Boolos, G., Burgess, J., Jeffrey, R. (2007). *Computability and Logic* (5ª ed.). Cambridge. — Capítulos 17-18 sobre representabilidad y Gödel.
- [Incompleteness theorems — Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/goedel-incompleteness/)
- [Gödel numbering — Wikipedia](https://en.wikipedia.org/wiki/G%C3%B6del_numbering)
- Documentación interna: [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §5.5, [PLANNING.md](PLANNING.md) §6.3, [TuplasFuncionesYListas.md](TuplasFuncionesYListas.md) §BLOQUE VIII Fases 18-19.

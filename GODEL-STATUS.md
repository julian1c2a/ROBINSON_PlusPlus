# Frente Gödel — Estado y Roadmap

> ## ESTADO REAL — 2026-09-04 · rama A cerrada · PROMOCIÓN: B0, B0b, B9, B1, B8 y **B2** hechas
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 123 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **109 módulos activos** (Minimal 11 + Meta 87 + Full 11) **+ 0 en `cuarentena/` + 57 en `sondeos/`.**
> **7 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **0 módulos en `cuarentena/`** (D3 y Gödel II aún fuera de la cadena activa). NO borrados.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

**Last updated:** 2026-07-20 — ⚠️ **DOCUMENTO HISTÓRICO/DIAGNÓSTICO.** El estado vivo está en [NEXT-STEPS.md](NEXT-STEPS.md) (bloque «🎯 LO QUE QUEDA»), [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md), [AXIOMS.md](AXIOMS.md) y [CHANGELOG.md](CHANGELOG.md); si algo de aquí discrepa, **mandan esos**. Resumen al día: **Gödel I da SÓLO `⊬G`** (`goedel_first_real'`, real y sin postulado gödeliano alguno) — **la mitad `⊬¬G` NO está en la cadena real** (ver la corrección de auditoría 2026-07-13 en §N de abajo); su reducción existe (`reflects_of_omega`: `Reflects ⇐ ω‑consistencia + `NegVerifier`) pero **`NegVerifier` aún no está construido** (`PLAN-NEGVERIFIER.md`: módulo A ✅ COMPLETO, módulo B en curso). **D1** (`repr_pos'_prf`) y **D2** (`d2_prf`) reales sobre el cálculo finitario `Prf`. **Gödel II** (`goedel_second'`) montado **módulo el único postulado gödeliano vivo, `axiom d3`**, ya reducido a UN SOLO lema (`d3_prf_of_chainOkDot`). **7 `axiom` de Lean** — el ancla de codificación es hoy `ax_axiomsCodeT_eq` (⊢) / `prf_axiomsCodeT_eq` (`Prf`); **el `ax_inAxC` que se cita más abajo ya NO es axioma, es teorema**. Build **101 jobs**, **87 módulos**, 0 sorrys, Lean v4.31.0. — (previo 2026-06-24) **NIVEL D REAL muy avanzado** (este documento, escrito 2026-06-06, describía el Nivel C con meta-axiomas; el proyecto ha progresado mucho — el contenido §1–§N de abajo es histórico). Estado actual: **Gödel I REAL sin postulados gödelianos** sobre el cálculo de Hilbert **finitario `Prf`** (`goedel_first_real`/`goedel_first_real'`; `#print axioms` = ω-reglas ambiente + `Full.ax_induction` + `ax_inAxC`, **sin** `diagonal_lemma`/`provFormula`/D2/D3). **D1 real** a nivel ⊢ (`repr_pos'`) **y finitario** (`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`). **D2 real ⊢** (`d2`). **Teorema de deducción finitario** (`Meta/HilbertDeduction.lean`) + **regla de confinamiento ∀ `qconf`** integrada en el verificador. **Fix de solidez FOL**: `subst_lift_cancel_formula` (axioma falso) → teorema. La vía clásica/legacy (Gödel I/II con `Dem`/`provFormula`/D2/D3 postulados) coexiste como andamiaje. **Pendiente para Gödel II 100% real** (`goedel_second_prf : ConsistentH → ¬ Prf Con'`): lema de Barendregt → inducción de listas en `Prf` → `d2_prf`/`d3_prf`. Estado vivo: [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md), [NEXT-STEPS.md](NEXT-STEPS.md), [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md), [CHANGELOG.md](CHANGELOG.md). — (histórico, 2026-06-06) Niveles B y C implementados con meta-axiomas.
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
| **D** | Teoremas de incompletitud | **cadena REAL** (`Meta/DiagonalTwo.lean`, `Meta/GodelTwo.lean`) | 🔶 **Gödel I: sólo `⊬G`** (`goedel_first_real'`, ω‑consistencia). **Gödel II**: `goedel_second'`, módulo `axiom d3`. ⚠ La mitad `⊬¬G` **NO está en la cadena real** — ver nota abajo |

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

- 🗑️ **`goedel_first_unprovable`** : *(capa LEGACY, **eliminada** en F7a)*
  `Consistent → ¬(axioms ⊢ goedelSentence)`.
  Si el sistema es consistente, la sentencia de Gödel `G` no es demostrable.
  Prueba: `⊢ G` → (D1, `provFormula_repr`) `⊢ Prov(⌜G⌝)`; punto fijo
  (`goedelSentence_fixedpoint`) da `⊢ ¬Prov(⌜G⌝)`; `mp` → `⊢ ⊥`.
- 🗑️ **`goedel_first_true`** : *(capa LEGACY, **eliminada** en F7a — el símbolo ya no existe)*
  `G` es verdadera-pero-indemostrable. Se apoyaba en el postulado **falso** `provFormula_repr`.
- 🗑️ **`incompleteness`** : *(capa LEGACY, **eliminada** en F7a)* `Consistent → ∃ φ, ¬(axioms ⊢ φ)`.

- ✅ **Gödel II** (`goedel_second`, 2026-06-12): `Consistent → ¬(axioms ⊢ Con)`
  con `Con := ¬Prov(⌜⊥⌝)`. **Postulando D2 y D3** (condiciones de
  Hilbert-Bernays-Löb; D1 ya estaba vía `provFormula_repr`). Lema crucial
  `con_imp_goedelSentence : ⊢ (Con ⇒ G)` (Gödel I formalizado), derivado de
  D1/D2/D3 + punto fijo. Notable: toda la cadena (incl. contrapositiva) se
  construye con `imp_intro`/`mp`, **sin DNE object-level** — funciona en el FOL
  intuicionista.

- ⚠️ **CORRECCIÓN DE AUDITORÍA (2026-07-13, `repasa_y_proyecta`): la mitad `⊬¬G` NO está en la
  cadena real.** Se demostró el 2026-06-13 (`goedel_first_unrefutable` / `goedel_first_undecidable`,
  vía `dne` clásica), pero **en la capa LEGACY** (`Meta/Incompleteness.lean`, que postulaba D2 y D3),
  y esa capa se **RETIRÓ en F7a** (commit `f03eacf`, 2026-07-09) junto con el módulo. Hoy **esos dos
  teoremas no existen en el código**. La cadena real establece **sólo `⊬G`** (`goedel_first_real'`,
  `Meta/DiagonalTwo.lean`).

- 🚫 **NO recuperar F7a — fue un ARREGLO DE SOLIDEZ, no una limpieza.** La prueba legacy descansaba en
  `provFormula_repr`, postulado como **bicondicional** `(axioms ⊢ Prov⌜φ⌝) ↔ (axioms ⊢ φ)`. La
  dirección **`.mp`** (`⊢Prov⌜φ⌝ → ⊢φ`) es la **representabilidad NEGATIVA / reflexión**, que **NO se
  sigue de la consistencia simple** — exige ω‑consistencia/soundness. Pero el teorema se enunciaba bajo
  **`Consistent`** (consistencia simple) ⇒ **afirmaba MÁS de lo que Gödel permite** (por eso existe
  **Rosser**: para obtener ambas mitades desde consistencia simple hay que **cambiar de sentencia**).
  `provFormula_repr` era, pues, un **postulado falso en general** — misma familia que
  `subst_lift_cancel_formula` (axioma FOL general FALSO) y `ax_lineWF_gen` (incondicional ⇒ `Prov`
  total). Restaurarlo reintroduciría el postulado malo.

- ⏳ **TAREA ABIERTA (independiente de D3): construir `repr_neg`.** Para re‑derivar `⊬¬G` **con la
  hipótesis honesta** falta la **representabilidad NEGATIVA**, que **no existe** en la cadena real:
  `repr_neg : ConsistentOmega → Prf (provCodeC' φ) → Prf φ`. Con ella el argumento se porta tal cual
  (~8 líneas): `⊢¬G` →(punto fijo) `⊢¬¬Prov⌜G⌝` →(`dne`) `⊢Prov⌜G⌝` →(**`repr_neg`**) `⊢G` →(con `⊢¬G`)
  `⊥`. Ya están el **punto fijo real** —hoy **`godelCN_fixedpoint`**, el `godelC'_fixedpoint` de
  entonces murió con ADR‑012—, **D1** (`repr_pos'_prf`) y `dne`.
  `repr_neg` debería salir de la **fidelidad del verificador** + `ConsistentOmega`; hay groundwork en
  `Meta/CodeDistinct.lean` («aritmética negativa de códigos»).
- 📜 **(histórico, capa legacy retirada)** Lo que se probó el 2026-06-13 fue:
  `Consistent → ⊬ ¬G`, luego `⊬ G ∧ ⊬ ¬G` (`G` **indecidible**).
  Resuelto añadiendo **`dne`** (eliminación de doble negación clásica) a
  `FOL/MetaRules.lean`. Diagnóstico: el obstáculo no era ω-consistencia sino el
  **intuicionismo** del FOL (`¬¬Prov⌜G⌝ → Prov⌜G⌝` no es intuicionista); Rosser
  habría sido peor (Muro 1 + comparación acotada de pruebas). `dne` es el
  setting clásico estándar de Gödel, sólido para ℕ (coherente con la ω-lógica).
  Prueba: `⊢ ¬G` → (punto fijo) `⊢ ¬¬Prov⌜G⌝` → (`dne`) `⊢ Prov⌜G⌝` →
  (reflexión) `⊢ G` → `⊥`.

**Pendiente** (documentado):

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

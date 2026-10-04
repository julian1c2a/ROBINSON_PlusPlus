# ROBINSON_PlusPlus

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md))
>
> `axiomsCodeT` queda anclado por un axioma objeto DIAGONAL (L2‑3): `axioms` = **142** = los 141 de siempre
> (`axiomsBase`) y `ax_axiomsCodeT_def`, el último. El ancla de antes, la hipótesis de clase `AnclaEq`, es hoy
> el teorema `prf_ancla` (la clase se retiró con ADR‑118), y `goedel_first_prf` y `goedel_second_prf` ya no la llevan:
> su footprint sigue siendo los tres de Lean, y **F1 ya no los hace vacuos**. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 axiomas son consistentes, y no hay modelo; y `⊬¬G` sigue sin existir en
> ningún cálculo (irá por Rosser, sobre `Prf`).
>
> ### 2026‑10‑02 · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md)) · ⛔ **Gödel I/II sobre `Prf`: VACUOS** por `[AnclaEq]` hasta ADR‑117 (F1, [ADR‑114](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arregla** *(hasta ADR‑117, 2026‑10‑04)*: `goedel_first_prf` y `goedel_second_prf` llevan la clase
> `[AnclaEq]`, y `AnclaEq` **da `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`) ⇒ hoy
> los dos teoremas son **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) es lo siguiente.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; lo primero vuelve a serlo desde ADR‑117), y `⊢`
> ya no está en RPP. Se conserva:
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 117 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio. En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **104 módulos activos** (Minimal 1 + Meta 100 + Full 3) **+ 0 en `cuarentena/` + 85 en `sondeos/`.**
> **0 `axiom` de Lean · 142 axiomas objeto** en `axioms` (los 141 de `axiomsBase` más el ancla, ADR‑117; `axioms_len`).
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
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

[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-in%20progress-yellow)](CURRENT-STATUS-PROJECT.md)

> **Status**: See [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) for complete details

Una implementación formal de una **Aritmética Fundacional** en Lean 4, construida sobre una base de Lógica de Primer Orden (`FOL`) y sin dependencias de Mathlib.

## Description

> ⚠️ **Corregido el 2026‑09‑11 por la auditoría.** Este apartado —la **declaración de propósito del
> proyecto**— describía un proyecto que ya no es éste: hablaba sólo de fundar los naturales, las
> listas y el TFA, **sin mencionar la incompletitud**, que hoy es **el 83 % del árbol** (`Meta/`,
> 106 de 128 módulos); citaba un directorio `Intermediate/` **eliminado el 2026‑06‑11**; y daba
> «34 axiomas» sin decir que son los **matemáticos** (`coreAxioms`), porque `axioms` tiene **141** (hoy 142: ADR‑117).
> Ver `doc/AUDITORIA-2026-09-11.md` **F‑3**.

Este proyecto formaliza en Lean 4 —**sin Mathlib**, sobre una implementación propia y verificada de
lógica de primer orden con igualdad (`FOL`)— la cadena que va de una aritmética **débil** hasta los
**teoremas de incompletitud de Gödel**, con la disciplina de que **cada paso se demuestra desde la
base o se declara pendiente con nombre y firma**.

**Las tres capas, y qué hace cada una:**

| capa | qué es | tamaño |
|---|---|---|
| **`Minimal/`** | la teoría objeto **Q++**: aritmética de Robinson extendida, **sin esquema de inducción**. `axioms` = **142** fórmulas = **34 matemáticas** (`coreAxioms`) **+ 107 ecuaciones de codificación** (`codingAxioms`; juntas, los 141 de `axiomsBase`) **+ el ancla diagonal** de `axiomsCodeT` (`ax_axiomsCodeT_def`, la última: ADR‑117) | 1 módulo (`Axioms`; los diez `Block`, todo teoremas sobre `⊢`, se retiraron con ADR‑115) |
| **`Full/`** | lo que queda tras [ADR‑115](DECISIONS.md): `primAxioms` y las longitudes del censo, los lemas de sustitución e `inductionFormula` (`Full/Induction.lean`), `numeral` (`Full/Numerals.lean`) y la teoría de números en ℕ pura (`Full/PrimeFactor.lean`). 🗑️ El esquema de inducción sobre `⊢`, el censo certificado sobre `⊢` y el TFA objeto se retiraron con esa capa | 3 módulos |
| **`Meta/`** | la **aritmetización de la sintaxis** y la cadena de Gödel: verificador de demostraciones interno, punto fijo, **D1, D2 y D3 demostradas**, Gödel I y Gödel II | 100 módulos |

**Lo que sostiene el resultado, dicho sin adornos:**

- 🗑️ **Gödel I sobre `⊢`** (`goedel_first_numeral`) quedó retirado con esa capa (ADR‑115). El de hoy es `goedel_first_prf` (abajo), sobre `Prf`.
  ⬜ La otra mitad (`⊬¬G`) **no está cerrada**: `NegVerifier` (ADR‑097) iba **sobre `⊢`** y con meta‑reglas refutadas en
  su footprint —no estaba demostrado— y se retiró con esa capa; sobre `Prf` hay que rehacerla, y ⛔ la ω‑consistencia NO puede enunciarse como antes:
  sobre `Prf` esa definición es refutable (L1‑4, `sondeos/OmegaConsistentRefutable.lean`).
- 🏁 **Las tres condiciones de derivabilidad (D1, D2, D3) son TEOREMAS**, ninguna postulada. ⚠️ D1
  (`repr_pos'_prf`) y D3 (`d3_prf_real`) llevaban la hipótesis de clase `[AnclaEq]`; D2 (`d2_prf`) no. 🏁 Desde
  ADR‑117 el ancla es el teorema `prf_ancla`, y desde ADR‑118 la clase no existe: ninguna firma la lleva.
- 🏁🏁 **La cadena de Gödel, ENTERAMENTE FINITARIA** (`Meta/GodelTwoPrf.lean`):

  ```lean
  goedel_first_prf  (hcon : ConsistentH) : ¬ Prf godelCN
  goedel_second_prf (hcon : ConsistentH) : ¬ Prf consistencyFormula'
  ```

  🏁 **Desde ADR‑117 (2026‑10‑04), una sola hipótesis, la mínima**: `ConsistentH := ¬ Prf ⊥`. Hasta ese día eran
  **dos**, con la clase `[AnclaEq]`, y **no podían valer a la vez** (F1, abajo). ⚠️ Siguen siendo **CONDICIONALES**:
  `ConsistentH` sólo vale si los 142 axiomas son consistentes, y no hay modelo. **Ninguna hipótesis suelta**: el
  punto fijo y la necesitación se descargan ahí.
  ⭐ `prf_godelCN_fixedpoint` es **net‑0 PURO**, y el footprint de los dos teoremas es
  **`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]`** — **un solo axioma del
  proyecto**, el ancla de codificación *(entonces; desde ADR‑026 el ancla fue la clase `[AnclaEq]`, y desde ADR‑117
  es el teorema `prf_ancla`; el footprint, los tres de Lean)*. ⛔⛔ **Y el 2026‑10‑02 se supo que `[AnclaEq]` daba
  `Prf ⊥`** (F1, ADR‑114): los dos teoremas fueron **vacuos** hasta ADR‑117.
- ⛔⛔ **Y una advertencia que hay que leer antes de citar nada de este repo** *(hasta el 2026‑10‑02: ese día
  la capa `⊢` se retiró de RPP precisamente por esto, ADR‑115)*: el cálculo `axioms ⊢`
  —el que se usaba como herramienta de trabajo— era **sintácticamente COMPLETO**: decide **toda**
  sentencia (`Meta/OmegaStrength.lean`, medido). La causa no es aritmética: es que los meta‑axiomas
  `raa` e `imp_intro` toman como premisa una **función de Lean**, así que lo que el cálculo no
  prueba, lo **refuta**. ⇒ **ningún resultado de incompletitud puede enunciarse sobre `⊢`** — por eso
  el `goedel_second'` de `Meta/GodelTwo.lean` **no es** el Segundo Teorema, y el que sí lo es vive
  sobre `Prf`. Detalle en `doc/AUDITORIA-2026-09-11.md` **F‑1**.
- **0 `axiom` de Lean** en todo el árbol (los 3 que había vivían sobre `⊢` y se retiraron con esa capa, ADR-115), **0 `sorry`**.
- ⚠️ **No es una prueba de consistencia**: se retiró una inconsistencia **conocida y localizada**
  (ADR‑012/013), lo que no es lo mismo.

**Características principales:**

- **Base Lógica Sólida**: Utiliza una implementación completa y verificada de Lógica de Primer Orden (`FOL`) como dependencia.
- **Aritmética Minimalista**: Formaliza un sistema de 34 axiomas sin un esquema de inducción general, forzando una construcción desde primeros principios.
- **Desarrollo Progresivo**: El proyecto está estructurado para avanzar desde sistemas débiles (`Minimal`) hacia sistemas más fuertes con principios de inducción (`Intermediate`, `Full`).
- **Metaprogramación**: Hereda y utiliza las tácticas de automatización del proyecto `FOL` para agilizar las demostraciones.

## Modules

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Minimal/Axioms.lean` | `ROBINSON_PlusPlus.Minimal.Axioms` | `FOL.FOL`, `FOL.Theorems.Eq` | ✅ El lenguaje y los 142 axiomas objeto (los 141 de `axiomsBase` y el ancla diagonal `ax_axiomsCodeT_def`, ADR‑117). **0 `axiom` de Lean** (los «meta‑axiomas» de FOL ya no se importan: ADR‑115) |
| ~~`Minimal/Theorems/Block1–8.lean`~~ (10 ficheros) | — | — | 🗑️ **RETIRADOS el 2026‑10‑02** ([ADR‑115](DECISIONS.md)): todo eran teoremas `axioms ⊢ …` |

## Project Structure

```text
ROBINSON_PlusPlus/
├── Minimal/
│   ├── Axioms.lean            # Lenguaje + los 142 axiomas objeto (34 matemáticos + 107 de codificación + el ancla)
│   └── (Theorems/Block1–8 — 🗑️ retirados con la capa `⊢`, ADR‑115)
├── Meta/                      # Gödelización + Gödel I/II en `Prf`: G, ⌜·⌝, incompletitud, cadena HBL (D1/D2, D3 en curso)
└── Full/                      # Induction (primAxioms, inductionFormula), Numerals, PrimeFactor (ℕ pura)
```

> As the project grows, organize modules into thematic subdirectories.
> See AI-GUIDE.md §19 for the directory organization protocol.

## Installation

```bash
git clone https://github.com/julian1c2a/ProjectName.git
cd ProjectName
lake build
```

## Requirements

- **Lean 4**: v4.28.0 or later
- **Lake**: Included with Lean 4

## Development Workflow

```bash
# Initialize lock system (first time only)
bash git-lock.bash init

# Create a new module (supports subdirectories)
bash new-module.bash ModuleName
bash new-module.bash Topic/SubModule

# Build
make build

# Check for sorry
make sorry

# Show locked files and sorry status
make status

# Regenerate root import file
bash gen-root.bash
```

> See [WORKFLOW.md](WORKFLOW.md) for the complete development workflow.

## Documentation

| Document | Purpose |
|----------|---------|
| [WORKFLOW.md](WORKFLOW.md) | ⭐ **Complete development workflow** (start here after setup) |
| [REFERENCE.md](REFERENCE.md) | Technical reference for all definitions and theorems |
| [AI-GUIDE.md](AI-GUIDE.md) | Documentation standards, naming conventions, and AI assistant guide |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | Full Mathlib-style naming dictionary and formation rules |
| [CHANGELOG.md](CHANGELOG.md) | Change history |
| [DEPENDENCIES.md](DEPENDENCIES.md) | Module dependency diagrams |
| [DECISIONS.md](DECISIONS.md) | Architectural Decision Records (ADR) |
| [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) | Current project status and metrics |
| [NEXT-STEPS.md](NEXT-STEPS.md) | Planned development phases |
| [THOUGHTS.md](THOUGHTS.md) | Design journal and ideas |

## Naming Conventions

This project follows [Mathlib4 naming conventions](https://leanprover-community.github.io/contribute/naming.html).
See [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) for the full reference.

**Quick summary:**

| Entity | Convention | Example |
|--------|------------|---------|
| Module | `UpperCamelCase` | `CoreAxioms.lean` |
| Namespace | `UpperCamelCase` | `ProjectName.Topic` |
| Type / Prop predicate | `UpperCamelCase` | `IsSet`, `IsFun` |
| Function / value def | `lowerCamelCase` | `powerset`, `dom` |
| Axiom | `TAG_ShortName` | `ZF_Ext`, `MK_Pair` |
| Theorem | `subject_predicate` | `mem_pair_iff` |

## License

This project is under the MIT License. See [LICENSE](LICENSE) for details.

## Author

Julián Calderón Almendros

## Credits

### Educational Resources

- [add resources here]

### Bibliographic References

- [add references here]

### AI Tools

- Claude Code AI (Anthropic)

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-09-10 — Build ✅ **145 jobs**, **0 errores**, **0 warnings**, **0 `sorry`** (verificado con el `check-sorry.bash` reparado, AI‑GUIDE §27.1), **5 `axiom` de Lean**, Lean **v4.31.0** (política: última estable). **131 módulos activos** (Minimal/ 11 + Meta/ 109 + Full/ 11) + 0 en `cuarentena/` + 61 en `sondeos/`. ✅ **CI en verde** (`.github/workflows/build.yml`, con los dos checkouts hermanos que `FOL` necesita).*

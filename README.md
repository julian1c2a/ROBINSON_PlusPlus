# ROBINSON_PlusPlus

> ## ESTADO REAL — 2026-08-23 · repatriación en curso
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.25.
>
> **Build 112 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **98 módulos activos** (Minimal 11 + Meta 76 + Full 11) **+ 12  + 10 .**
> **7 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **6 módulos en `cuarentena/`** (D3 y Gödel II aún fuera de la cadena activa). NO borrados.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. Quedan 6.
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-in%20progress-yellow)](CURRENT-STATUS-PROJECT.md)

> **Status**: See [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) for complete details

Una implementación formal de una **Aritmética Fundacional** en Lean 4, construida sobre una base de Lógica de Primer Orden (`FOL`) y sin dependencias de Mathlib.

## Description

Este proyecto está dedicado a explorar y formalizar diferentes sistemas axiomáticos para la aritmética. Su objetivo es fundar rigurosamente los números naturales y, a partir de ellos, construir estructuras de datos como tuplas y listas.

La estrategia consiste en partir de un sistema minimalista (`Minimal/`) con 34 axiomas y sin inducción, para demostrar que es suficiente para construir la función de apareamiento de Cantor, una teoría de tuplas y listas, y la formalización de la factorización prima (TFA vía Ax-P).

**Características principales:**

- **Base Lógica Sólida**: Utiliza una implementación completa y verificada de Lógica de Primer Orden (`FOL`) como dependencia.
- **Aritmética Minimalista**: Formaliza un sistema de 34 axiomas sin un esquema de inducción general, forzando una construcción desde primeros principios.
- **Desarrollo Progresivo**: El proyecto está estructurado para avanzar desde sistemas débiles (`Minimal`) hacia sistemas más fuertes con principios de inducción (`Intermediate`, `Full`).
- **Metaprogramación**: Hereda y utiliza las tácticas de automatización del proyecto `FOL` para agilizar las demostraciones.

## Modules

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Minimal/Axioms.lean` | `ROBINSON_PlusPlus.Minimal.Axioms` | `FOL.FOL` | ✅ Complete (5 meta-axiomas intencionales) |
| `Minimal/Theorems/Block1.lean` | `ROBINSON_PlusPlus.Minimal.Theorems.Block1` | `Minimal.Axioms`, `FOL.Tactics` | ✅ Complete |
| `Minimal/Theorems/Block2.lean` | `Minimal.Theorems.Block2` | `Minimal.Axioms`, `Block1` | ✅ Complete |
| `Minimal/Theorems/Block3.lean` | `Minimal.Theorems.Block3` | `Minimal.Axioms`, `Block1` | ✅ Complete (verboso: enumera div2/mod2 por numeral, sin inducción) |
| `Minimal/Theorems/Block4.lean` | `Minimal.Theorems.Block4` | `Minimal.Axioms`, `Block1`, `Block3` | ✅ Complete |
| `Minimal/Theorems/Block4_C5.lean` | `Minimal.Theorems.Block4_C5` | `Block1`, `Block2`, `Block3` | ✅ Complete — `lemma_C5` (∃) + `lemma_C5_unique` + `cantor_bounds` |
| `Minimal/Theorems/Block4_C6_C7.lean` | `Minimal.Theorems.Block4_C6_C7` | `Block1..4`, `Block4_C5` | ✅ Complete — `add_left_cancel`, `mod2_of_even`, `proj1`/`proj2` (defs), `proj_is_cantor`, `cantor_uniqueness`, `cantor_surjectivity` |
| `Minimal/Theorems/Block5.lean` | `Minimal.Theorems.Block5` | `Block1..4`, `Block4_C5`, `Block4_C6_C7` | ✅ Complete — `proj1/2_pair`, `pair_proj_eq_c`, `pair_inj`, `is_cantor_pair` |
| `Minimal/Theorems/Block6.lean` | `Minimal.Theorems.Block6` | `Block1`, `Block4`, `Block5` | ✅ Complete — listas, pertenencia, concat (assoc/in_concat vía ax_C3/ax_L3 postulados) |
| `Minimal/Theorems/Block7.lean` | `Minimal.Theorems.Block7` | `Block1`, `Block4`, `Block4_C6_C7`, `Block5` | ✅ Complete — `IsFunction`, `Functional`, F1/F2/F3 (Bloque VII spec) |
| `Minimal/Theorems/Block8.lean` | `Minimal.Theorems.Block8` | `Block1`, `Block2`, `Block4_C5` | ✅ Complete — `Dvd`, `IsPrime`, `IsFactorization`, `pow`/`prod_pairs` (Bloque VIII Fase 17 + Ax-P TFA) |

## Project Structure

```text
ROBINSON_PlusPlus/
├── Minimal/
│   ├── Axioms.lean            # Lenguaje + 34 axiomas + 5 meta-axiomas (reglas de deducción)
│   └── Theorems/
│       ├── Block1.lean        # Block I: Aritmética básica, constantes
│       ├── Block2.lean        # Block II: Raíz cuadrada, cotas, unicidad
│       ├── Block3.lean        # Block III: div2, mod2 (enumeración por numeral)
│       ├── Block4.lean        # Block IV: Cantor — totalidad e inyectividad
│       ├── Block4_C5.lean     # Lema C5: ∃ w, w(w+1) ≤ 2c < (w+1)(w+2) ✅
│       ├── Block4_C6_C7.lean  # add_left_cancel + Cantor sobreyectividad/unicidad
│       ├── Block5.lean        # Pares y proyecciones (proj1/2_pair, pair_inj)
│       ├── Block6.lean        # Listas (cons_neq_nil, concat_assoc, in_concat)
│       ├── Block7.lean        # Funciones discretas (IsFunction, Functional, F1/F2/F3)
│       └── Block8.lean        # Primos y factorización (Dvd, IsPrime, IsFactorization, Ax-P TFA)
├── Meta/                      # Gödelización + Gödel I/II en `Prf`: G, ⌜·⌝, incompletitud, cadena HBL (D1/D2, D3 en curso)
├── Intermediate/              # (Planned, paralelo a Meta/) System with restricted induction
└── Full/                      # (Planned) System with full Peano induction
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
*Last updated: 2026-07-05 — Build ✅ **0 sorrys** (67 jobs), Lean **v4.31.0** (política: última estable). **~54 módulos** (Minimal/ 11 + Meta/ 30 + Full/ 11 + barrels). **Minimal/** (34 axiomas, sin inducción) cierra Bloques I–VIII + TFA. **Full/** (inducción general) deriva ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 y cierra el **Teorema Fundamental de la Aritmética** (`tfa_numeral`). **Meta/** formaliza la Gödelización completa: codificación, demostrabilidad, los **dos Teoremas de Incompletitud**, y el **Nivel D REAL** sobre un cálculo de Hilbert finitario `Prf`. **Primer Teorema de Gödel REAL sin postulados**: verificador `validProofFn`/`runFn` sólido → `repr_pos`/D1 → **lema diagonal real** (`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`) → **`goedel_first_real : ConsistentOmega → ¬ Prf G`**. **Hacia Gödel II REAL**: **D1** (`repr_pos'_prf`) y **D2** (`d2_prf`) finitarias reales sin postulados; **D3** reducida (`d3_prf_of_sigma1`) a la Σ₁-completitud del verificador (`hC`/`hI`). En curso (**Opción A**, ver `GODEL-D3-TRACKED-DESIGN.md`): predicado de demostrabilidad con **testigo rastreado** (`tcFn`/`substfc`) para cerrar `hI`/`hC` → `d3_prf` → `goedel_second_prf : ConsistentH → ¬ Prf Con'`. Las meta-reglas ω viven en `FOL/MetaRules.lean`.*

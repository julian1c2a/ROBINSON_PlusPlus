# ROBINSON_PlusPlus

> ## ESTADO REAL — 2026‑09‑11 · `master` · 🏁 **C3 (7/7)** · 🏁 **D3 PROBADA** · **5 `axiom` de Lean** · ⛔ **Gödel II montado pero NO ensamblado** ([auditoría F‑1](doc/AUDITORIA-2026-09-11.md))
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 142 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **128 módulos activos** (Minimal 11 + Meta 106 + Full 11) **+ 0 en `cuarentena/` + 61 en `sondeos/`.**
> **5 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
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
> «34 axiomas» sin decir que son los **matemáticos** (`coreAxioms`), porque `axioms` tiene **141**.
> Ver `doc/AUDITORIA-2026-09-11.md` **F‑3**.

Este proyecto formaliza en Lean 4 —**sin Mathlib**, sobre una implementación propia y verificada de
lógica de primer orden con igualdad (`FOL`)— la cadena que va de una aritmética **débil** hasta los
**teoremas de incompletitud de Gödel**, con la disciplina de que **cada paso se demuestra desde la
base o se declara pendiente con nombre y firma**.

**Las tres capas, y qué hace cada una:**

| capa | qué es | tamaño |
|---|---|---|
| **`Minimal/`** | la teoría objeto **Q++**: aritmética de Robinson extendida, **sin esquema de inducción**. `axioms` = **141** fórmulas = **34 matemáticas** (`coreAxioms`) **+ 107 ecuaciones de codificación** | 11 módulos |
| **`Full/`** | Q++ **más el esquema de inducción** como axioma objeto. Aquí los **10** axiomas *derivables* de `coreAxioms` pasan a **teoremas** (9 de ellos **certificados** sobre los 24 primitivos), y se construye el TFA | 11 módulos |
| **`Meta/`** | la **aritmetización de la sintaxis** y la cadena de Gödel: verificador de demostraciones interno, punto fijo, **D1, D2 y D3 demostradas**, Gödel I y Gödel II | 106 módulos |

**Lo que sostiene el resultado, dicho sin adornos:**

- 🏁 **Gödel I, la mitad `⊬G`**: `goedel_first_numeral`, real y **sin ningún postulado gödeliano**.
  ⬜ La otra mitad (`⊬¬G`) **no está cerrada**: depende de `NegVerifier`, hoy reducido a **dos
  obligaciones con nombre**.
- 🏁 **Las tres condiciones de derivabilidad (D1, D2, D3) son TEOREMAS**, ninguna postulada.
- ⚠️ **Gödel II está montado pero NO ensamblado**: `goedel_second'` vive sobre el cálculo **ω** y su
  hipótesis `hgi` **no la puede dar** el Gödel I de este árbol, que es **finitario**. Es el hallazgo
  **F‑1** de `doc/AUDITORIA-2026-09-11.md`, y la pieza que falta está identificada.
- **5 `axiom` de Lean** en todo el árbol, **0 `sorry`**, y ninguno de los cinco es gödeliano.
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
*Last updated: 2026-09-10 — Build ✅ **142 jobs**, **0 errores**, **0 warnings**, **0 `sorry`** (verificado con el `check-sorry.bash` reparado, AI‑GUIDE §27.1), **5 `axiom` de Lean**, Lean **v4.31.0** (política: última estable). **128 módulos activos** (Minimal/ 11 + Meta/ 106 + Full/ 11) + 0 en `cuarentena/` + 61 en `sondeos/`. ✅ **CI en verde** (`.github/workflows/build.yml`, con los dos checkouts hermanos que `FOL` necesita).*

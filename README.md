# ROBINSON_PlusPlus

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-in%20progress-yellow)](CURRENT-STATUS-PROJECT.md)

> **Status**: See [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) for complete details

Una implementación formal de una **Aritmética Fundacional** en Lean 4, construida sobre una base de Lógica de Primer Orden (`FOL`) y sin dependencias de Mathlib.

## Description

Este proyecto está dedicado a explorar y formalizar diferentes sistemas axiomáticos para la aritmética. Su objetivo es fundar rigurosamente los números naturales y, a partir de ellos, construir estructuras de datos como tuplas y listas.

La estrategia consiste en partir de un sistema minimalista (`Minimal/`) con 21 axiomas y sin inducción, para demostrar que es suficiente para construir la función de apareamiento de Cantor, y con ella, una teoría de tuplas y listas.

**Características principales:**

- **Base Lógica Sólida**: Utiliza una implementación completa y verificada de Lógica de Primer Orden (`FOL`) como dependencia.
- **Aritmética Minimalista**: Formaliza un sistema de 21 axiomas sin un esquema de inducción general, forzando una construcción desde primeros principios.
- **Desarrollo Progresivo**: El proyecto está estructurado para avanzar desde sistemas débiles (`Minimal`) hacia sistemas más fuertes con principios de inducción (`Intermediate`, `Full`).
- **Metaprogramación**: Hereda y utiliza las tácticas de automatización del proyecto `FOL` para agilizar las demostraciones.

## Modules

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Minimal/Axioms.lean` | `ROBINSON_PlusPlus.Minimal.Axioms` | `FOL.FOL` | ✅ Complete |
| `Minimal/Theorems/Block1.lean` | `ROBINSON_PlusPlus.Minimal.Theorems.Block1` | `Minimal.Axioms`, `FOL.Tactics` | ✅ Complete |
| `Minimal/Theorems/Block2.lean` | `ROBINSON_PlusPlus.Minimal.Theorems.Block2` | `Minimal.Axioms`, `Block1` | 🔶 Partial |
| `Minimal/Theorems/Block3.lean` | `ROBINSON_PlusPlus.Minimal.Theorems.Block3` | `Minimal.Axioms`, `Block1` | 🔄 In progress |

## Project Structure

```text
ROBINSON_PlusPlus/
├── Minimal/
│   ├── Axioms.lean            # Language and 21 axioms of the minimal system
│   └── Theorems/
│       └── Block1.lean        # Block I: Basic Arithmetic Proofs
│       └── Block2.lean        # Block II: Square Root Proofs
│       └── Block3.lean        # Block III: div2/mod2 Proofs
├── Intermediate/              # (Planned) System with restricted induction
└── Full/                      # (Planned) System with full Peano induction
```

> As the project grows, organize modules into thematic subdirectories.
> See AI-GUIDE.md §22 for the directory organization protocol.

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
*Last updated: 2026-04-25 21:30*

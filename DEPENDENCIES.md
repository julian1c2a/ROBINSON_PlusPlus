# Dependency Diagram — ProjectName

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

## Project Structure

```
ProjectName/
├── Prelim.lean         # Preliminary definitions
├── _template.lean      # Module template (not imported)
├── Core/               # (subdirectory example)
│   └── Basic.lean
└── Topic/              # (subdirectory example)
    ├── Basic.lean
    └── Advanced.lean
ProjectName.lean        # Root module
```

## Dependency Graph

```mermaid
graph TD
    subgraph "Project: FOL"
        direction LR
        FOL_FOL["FOL.lean"]
        FOL_Tactics["Tactics.lean"]
    end

    subgraph "Project: ROBINSON_PlusPlus"
        direction TB
        Axioms["Minimal/Axioms.lean"]
        Block1["Minimal/Theorems/Block1.lean"]
        Block2["Minimal/Theorems/Block2.lean"]
        Block3["Minimal/Theorems/Block3.lean"]
        Block4["Minimal/Theorems/Block4.lean"]
    end

    FOL_FOL --> Axioms
    Axioms --> Block1
    Axioms --> Block2
    Axioms --> Block3
    Axioms --> Block4
    Block1 --> Block2
    Block1 --> Block3
    Block1 --> Block4
    Block3 --> Block4
    FOL_Tactics --> Block1
    FOL_Tactics --> Block2
    FOL_Tactics --> Block3
    FOL_Tactics --> Block4
```

*(Update this diagram as modules are added. Use subdirectory grouping:)*

```mermaid
graph TD
    subgraph Core
        CB[Core.Basic]
    end
    subgraph Topic
        TB[Topic.Basic]
        TA[Topic.Advanced]
    end
    P[Prelim.lean]
    CB --> P
    TB --> P
    TB --> CB
    TA --> TB
    Z[ProjectName.lean] --> P
    Z --> CB
    Z --> TB
    Z --> TA
```

## Namespace Hierarchy

### 1. **ProjectName** (root)

```lean
-- ProjectName.lean imports all modules
```

### 2. **ProjectName.Prelim**

```lean
namespace ProjectName.Prelim
  -- Preliminary definitions
```

*(Add sub-namespaces as subdirectories are created)*

## Dependencies by Level

### Level 0: Foundations

- `Prelim.lean` — no dependencies

### Level 1: Core

- *(modules that depend only on Prelim)*

### Level 2: Derived

- *(modules that depend on Level 1)*

### Level N: Root

- `ProjectName.lean` — imports all modules

## Exports by Module

### Prelim.lean

```lean
export ProjectName.Prelim (
  -- exported names here
)
```

## Design Notes

1. **Separation of concerns**: each module handles one aspect
2. **Minimal dependencies**: only import what is strictly needed
3. **Selective exports**: only public definitions and theorems are exported
4. **No Mathlib** (unless explicitly required — add to lakefile.lean)
5. **One namespace per module**: mirrors file path (see ADR-005)

## Verification Commands

```bash
make build          # build full project
make sorry          # check for sorry
make status         # lock status + sorry
```

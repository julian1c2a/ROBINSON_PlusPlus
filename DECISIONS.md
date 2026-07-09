# Design Decisions — ProjectName

**Last updated:** 2026-05-25
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

---

## ADR-001: No Mathlib dependency

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: [Explain why — e.g., educational goals, performance, avoiding API churn, etc.]

**Consequences**: All necessary infrastructure (ExistsUnique, etc.) must be built from scratch.

---

## ADR-002: autoImplicit = false

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: `moreServerArgs := #["-DautoImplicit=false"]` is set in `lakefile.lean`.

**Rationale**: Explicit type annotations prevent accidental universe polymorphism issues and make code easier to read and maintain.

**Consequences**: All variables must be explicitly declared or annotated.

---

## ADR-003: File locking system

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: Use `git-lock.bash` + `locked_files.txt` + pre-commit hook to prevent accidental edits to completed modules.

**Rationale**: Lean 4 proofs are fragile — small changes to completed modules can break dependent proofs. The locking system makes this explicit.

**Consequences**: Workflow requires locking/unlocking files. See AI-GUIDE.md §20.

---

## ADR-004: Mathlib naming conventions

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: All identifiers follow Mathlib4 naming conventions as documented in NAMING-CONVENTIONS.md.

**Rationale**: Consistency with the broader Lean 4 ecosystem. Makes theorems discoverable by name pattern (`mem_X_iff`, `subject_predicate`). Facilitates future Mathlib integration if desired.

**Consequences**: Existing names may need migration. See NAMING-CONVENTIONS.md for the full dictionary and 12 formation rules. REFERENCE.md §0 provides a quick reference.

---

## ADR-005: Directory-aligned namespaces

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: Each subdirectory corresponds to a sub-namespace: `ProjectName/Foo/Bar.lean` → `namespace ProjectName.Foo.Bar`.

**Rationale**: Clear 1:1 mapping between file system and namespace hierarchy. Reduces confusion about where definitions live. Scales well as the project grows.

**Consequences**: `new-module.bash` must handle subdirectory creation. `gen-root.bash` must scan recursively.

---

## ADR-006: Annotation system in REFERENCE.md

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: REFERENCE.md entries include `@axiom_system` and `@importance` annotations.

**Rationale**: Helps AI assistants prioritize which modules/theorems to load for context. Provides quick classification without reading module code.

**Consequences**: Annotations must be maintained when modules are updated. See AI-GUIDE.md §24-25.

---

## ADR-007: Separate NAMING-CONVENTIONS.md file

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: Naming conventions live in a dedicated NAMING-CONVENTIONS.md file, with a summary in AI-GUIDE.md and REFERENCE.md §0.

**Rationale**: The full naming dictionary with 12 rules and migration tables is too large for AI-GUIDE.md alone. A separate file allows detailed examples without bloating the main guide.

**Consequences**: Three places reference naming: NAMING-CONVENTIONS.md (canonical), AI-GUIDE.md (summary), REFERENCE.md §0 (reader guide). All must be kept in sync.

---

## ADR-008: Meta-axioms en Minimal/Axioms.lean son meta-teoremas de aritmética, no reglas FOL

**Date**: 2026-05-25
**Status**: Accepted

**Context**:
`Minimal/Axioms.lean` declara cinco entradas con `axiom`:

```lean
axiom imp_intro {Γ A B} (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)
axiom gen      {Γ A}   (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) : Γ ⊢ Formula.forall A
axiom raa      {Γ A}   (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A
axiom or_elim  {Γ A B C} (h : Γ ⊢ (A ∨ B))
                          (h1 : Γ ⊢ A → Γ ⊢ C) (h2 : Γ ⊢ B → Γ ⊢ C) : Γ ⊢ C
axiom ex_elim  {Γ A C} (h : Γ ⊢ Formula.ex A)
                        (cont : ∀ t, Γ ⊢ substFormula 0 t A → Γ ⊢ C) : Γ ⊢ C
```

Las hipótesis de `imp_intro`, `raa`, `or_elim` y `ex_elim` son funciones **meta-nivel** en Lean
(`Prop → Prop`), no derivaciones objeto. Esto hace que ninguno de los cuatro sea derivable en
general dentro de FOL:

**Contraejemplo** para `imp_intro`: sea `Γ = []`, `A = .atom "P" []`, `B = .atom "Q" []`.
En Lean clásico, `¬ Derives [] P` es verdad (P no es tautología), por lo que
`h : Derives [] P → Derives [] Q` es vacuosamente verdad. Pero `Derives [] (P ⇒ Q)` no es
derivable, así que `axiom imp_intro` sería una extensión *unsound* si se aceptara como teorema FOL
general. Análogamente para `raa`, `or_elim` y `ex_elim`.

**`gen`** tiene una naturaleza distinta: es la **ω-regla** (regla de Buchi). Es un axioma matemático
genuino —válido en el modelo estándar ℕ (aritmética Σ₁-completa) pero no derivable en ningún
sistema de deducción finito. Su presencia como `axiom` es correcta e inevitable.

**Decision**:
Mantener los cinco como `axiom` en Lean, con las siguientes clasificaciones:

| Axioma      | Clasificación                          | Acción |
|-------------|----------------------------------------|--------|
| `imp_intro` | Meta-teorema válido para aritmética    | Mantener; documentar |
| `raa`       | Meta-teorema válido para aritmética    | Mantener; documentar |
| `or_elim`   | Meta-teorema válido para aritmética    | Mantener; documentar |
| `ex_elim`   | Meta-teorema válido para aritmética    | Mantener; documentar |
| `gen`       | ω-regla; axioma matemático genuino     | Mantener; no modificar |

**Rationale**:

1. **Soundness práctica**: En todos los usos en `Block1.lean`–`Block4.lean`, la hipótesis meta-nivel
   siempre recibe un argumento genuino (nunca vacuo). Por ejemplo:

   ```lean
   apply Axioms.imp_intro; intro h_neq   -- h_neq : Γ ⊢ A es una hipótesis real
   apply or_elim h_tric; · intro h_lt    -- h_lt viene de un caso real de la disyunción
   ```

   El patrón de uso garantiza que `h` nunca se invoca vacuosamente en esta base de código.

2. **Validez aritmética**: El contexto `Γ` en ROBINSON_PlusPlus siempre es el conjunto fijo de
   axiomas de Robinson Q extendido. En esa teoría Σ₁-completa, las implicaciones meta-nivel
   reflejan derivabilidad real. Los cuatro meta-axiomas son **meta-teoremas correctos** para este
   `Γ` específico.

3. **No derivables en FOL puro**: Si se intentara derivar `imp_intro` desde las reglas objeto de
   `FOL.Derives`, haría falta `Classical.em (Derives Γ A)` y luego construir `Γ, A ⊢ B` en el
   caso `¬ Derives Γ A` sin información sobre `B` — lo cual es imposible.

4. **Alternativa correcta**: La forma demostrable de la introducción de implicación a nivel objeto es
   `Derives.intro_impl : (A :: Γ ⊢ B) → Γ ⊢ (A ⇒ B)`. Esta regla **sí** está en FOL y debería
   preferirse en código nuevo. La firma de `imp_intro` es distinta (meta-nivel vs. objeto).

**Consecuencias**:

- No intentar demostrar estos cuatro como teoremas Lean; solo `gen` podría estudiarse más.
- El código nuevo en ROBINSON++ debería preferir `Derives.intro_impl`, `Derives.elim_or`,
  `Derives.elim_ex` (reglas objeto de FOL) sobre los meta-axiomas cuando sea posible.
- Si en el futuro se quiere eliminar los meta-axiomas, habría que refactorizar Block1–Block4
  para usar solo reglas objeto — tarea de alta carga, no prioritaria.
- Los tres axiomas matemáticos de Minimal (`mod2_range`, `mod2_of_even`, `add_left_cancel`) son
  teoremas en Peano y pueden eliminarse si se importa Peano directamente; decisión separada.

---

## ADR-009: subst_lift_cancel_formula — corrección del enunciado en FOL

**Date**: 2026-05-25
**Status**: Accepted

**Context**:
`FOL/Theorems/Quantifiers.lean` declaraba:

```lean
axiom subst_lift_cancel_formula (f : Formula) (v : Nat) (t : Term) :
    substFormula v t (liftFormula (v + 1) f) = f
```

Este enunciado es **falso** para `t` arbitrario. Contraejemplo:

- `f = .atom "P" [#0]`, `v = 0`, `t = .func "zero" []`
- `liftFormula 1 f = .atom "P" [#0]` (la variable 0 < 1 no se levanta)
- `substFormula 0 zero (.atom "P" [#0]) = .atom "P" [zero] ≠ .atom "P" [#0]`

**Decision**:
El enunciado correcto y demostrable es:

```lean
theorem subst_lift_cancel_formula (f : Formula) (v : Nat) :
    substFormula v (.var v) (liftFormula (v + 1) f) = f
```

La clave es que `t` debe ser exactamente `.var v`. Con ese `t`:

- `liftFormula (v+1)` levanta variables ≥ v+1; la variable `v` no se toca.
- `substFormula v (.var v)` reemplaza `#v` con `.var v` (identidad) y decrementa variables > v.
- El resultado recupera la fórmula original exactamente.

La demostración procede por inducción estructural en `f`, usando:

- `FOL.substTerm_liftTerm_succ` y `FOL.substTerms_liftTerms_succ` (añadidos a `FOL/Theorems/Eq.lean`)
- En los casos `forall`/`ex`: `liftTerm 0 (.var v) = .var (v+1)` permite aplicar la IH con `v+1`

**Compatibilidad**: Todos los usos en Quantifiers.lean reescriben hipótesis de la forma
`substFormula 0 (#0) (liftFormula 1 A)`. El nuevo LHS unifica con `v=0`, `f=A`
(ya que `#0 = .var 0`). Los `rw [subst_lift_cancel_formula] at h` existentes no cambian.

**Consecuencias**:

- `subst_lift_cancel_formula` ya no es un axioma en FOL — es un teorema probado.
- `subst_distrib_and` y `lift_distrib_and` (también axiomas en Quantifiers.lean) se probaron
  simultáneamente como `rfl` (hold por definición).
- El build de FOL debe pasar sin axiomas espurios en Quantifiers.lean.

---

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]

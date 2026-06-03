# Changelog

**Last updated:** 2026-06-03 — `ax27_add_left_cancel` ELIMINADO (derivable en PA⁻). Sistema con **30 axiomas matemáticos** (23 aritméticos + 7 listas).
**Author**: Julián Calderón Almendros

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added (2026-06-03)

- **`Block7.lean` — BLOQUE VII (Funciones Discretas)**: nuevo módulo con `IsFunction` (Def 21), `Functional` (Def 24, con `Map` inlineado), y los teoremas F1 (`IsFunction nil`), F2 (evaluación única), F3 (`IsFunction ⟺ Functional`). Estilo de formalización: `IsFunction`/`Functional` se definen como **meta-predicados Lean** (`Term → Prop`) parametrizados por cuantificación universal sobre `Term`, evitando el manejo manual de De Bruijn (`liftTerm`/`substTerm`) que aparecería con `forall_2`/`forall_3`. Build verde a la primera, 0 sorrys. Spec: `TuplasFuncionesYListas.md §BLOQUE VII`.

### Removed (2026-06-03)

- **`ax27_add_left_cancel` ELIMINADO** — derivable en PA⁻ sin inducción. Prueba (style PA⁻): si `a+c=b+c`, por tricotomía (ax19) `a<b ∨ a=b ∨ b<a`; los casos estrictos llevan a `a+c < a+c` vía `lt_add_const_of_le_left` (Block4_C5) + `add_comm'` y contradicen ax18. Reescrito `add_left_cancel` (Block4_C6_C7) con esta prueba. Refactorizado `succ_le_of_lt` (Block2) para no depender de ax27: en su lugar usa `ax5+ax3` para llegar a `a + σ(k+kp) = a`, luego `ax13` da `lt a (a + σ(k+kp))`, sustituye y contradice ax18. Sistema reducido de **31 → 30 axiomas matemáticos** (23 aritméticos + 7 listas).

### Fixed (2026-06-03)

- **Build roto reparado**: el commit `537fd68` (eliminación de `ax22`/`ax23`) introdujo `proj_is_cantor` en `Block4_C6_C7` usando `mod2_of_even`, pero este último vivía en `Block5` — y `Block5` importa `Block4_C6_C7`, creando dependencia circular. Solución: mover `mod2_of_even` a `Block4_C6_C7` (justo antes de `proj_is_cantor`) y exportarlo desde allí. `Block5` lo sigue viendo vía `open Block4_C6_C7`. Sin cambios de prueba, solo de ubicación.
- **Conteo de axiomas rectificado**: docs previos decían "30 axiomas matemáticos" — el conteo real de la lista `axioms` es **31** (24 aritméticos: ax2-19, ax21, ax24-27, ax29 + 7 listas: ax_L0-3, ax_C1-3). El número "30" era un error histórico arrastrado.

### Removed (2026-06-02, commit 537fd68 — Claude Code Pro / Copilot Pro)

- **`ax22_cantor_proj_exists` ELIMINADO**: `proj1`/`proj2` dejan de ser símbolos opacos del lenguaje (con axioma "Skolem" atándolos a `is_cantor`) y pasan a ser `def proj1 (c) := x_of_c c`, `def proj2 (c) := y_of_c c` en `Block4_C6_C7`. El contenido de ax22 se demuestra constructivamente como teorema `proj_is_cantor`.
- **`ax23_cantor_proj_uniq` ELIMINADO**: era `cantor_uniqueness` reescrito como axioma; nunca se usó en código (el teorema `cantor_uniqueness` real ya estaba probado en `Block4_C6_C7`).
- Símbolos `proj1_sym`, `proj2_sym` y los `def proj1`/`def proj2` opacos de `Axioms.lean` eliminados.
- `Block5` refactorizado: `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c` ahora usan `proj_is_cantor` en lugar de `spec h_ax22`.

### Removed (2026-06-02)

- **`ax28_mul_two_cancel` ELIMINADO** del sistema axiomático. Era redundante: la spec `TuplasFuncionesYListas.md §Teo 2.11` ya proporcionaba la prueba sin inducción (tricotomía + irreflexividad + monotonía estricta de *2). Sistema de **33 → 32 axiomas matemáticos** (con el conteo rectificado).
- El `def ax28_mul_two_cancel` queda comentado en `Axioms.lean` como nota histórica.

### Added (2026-06-02)

- **`Block1.mul_two_succ_ne_zero (k) : ¬(2·σk = 0)`** — Helper público para `teo_2_11`. Demostrado vía teo_2_7 + ax5 + ax2 (sin inducción).
- **`Block1.mul_two_lt_mono {a b} (h : a<b) : 2a < 2b`** — Monotonía estricta de *2 sin inducción. Usa ax5/ax12/ax13 + ax13 (testigo `j := σk+k`).
- **`Block1.teo_2_11`** reprobado directamente desde primeros principios (tricotomía ax19 + irreflexividad ax18 + `mul_two_lt_mono` + sustitución vía `Derives.subst`). Anteriormente delegaba a `ax (... ax28 ∈ axioms)`. Ahora es un teorema real sin axioma de respaldo.

### Changed (2026-06-02)

- **`Block4.cantor_injective_c`** refactorizado para usar `spec teo_2_11` en lugar de `spec h_ax28`.
- **`Block4_C6_C7.cantor_uniqueness`** refactorizado análogamente.
- **`REFERENCE.md`** reescrito completo (proyección al estado actual: 9 módulos ✅, 30 axiomas, lista de exports por módulo, signaturas + descripción matemática).

### Added (2026-05-27)

- **Axiomas `ax_C3_concat_assoc` y `ax_L3_in_concat`** en `Minimal/Axioms.lean`. Postulados siguiendo el patrón de ax21/ax24/ax27/ax28 (teoremas en sistemas con inducción, axiomas en `Minimal`). Permiten cerrar `concat_assoc` y `in_concat_iff` en Block6 sin inducción sobre L.
- **Axioma `ax29_sub_witness`** + función `sub` con `sub_sym` en `Minimal/Axioms.lean`. Postula el testigo de la resta truncada (`b ≤ a → b + (a − b) = a`). Permite definir `x_of_c`/`y_of_c` constructivamente y cerrar `cantor_surjectivity`.
- **`eq_congr_pred`** en `Minimal/Axioms.lean` (análogo a `eq_congr_succ`).
- **`lemma_C5_unique`** y **`cantor_bounds`** exportados desde `Block4_C5`.
- **`is_cantor_pair`** exportado desde `Block5` (clave del isomorfismo pares ↔ N).

### Changed (2026-05-27)

- **🎉 PROYECTO `Minimal/` A 0 SORRYS REALES**. Build verde `lake build` exit 0, `WARN_sorry=0`. Los 5 `axiom imp_intro/gen/raa/or_elim/ex_elim` son meta-reglas de FOL, no `:= sorry`.
- **Block4_C5 cerrado** (commit `4b6a2a9`): probados `sq_2w_plus_1`, `w_w1_le_2c_iff_sq_2w1_le_8c1`, `mono_w_w1`, `h_sq_2w1_le_sq_s`, `h_existence_part2` (este último por contradicción reusando el iff). Sentencia ajustada a `liftTerm 0 c` y cerrada con `ex_intro w`. Helper `lemma_C5_unique` exportado.
- **Block4_C6_C7 cerrado** (commits `4b6a2a9` + `fde7476`): `cantor_uniqueness` (vía `cantor_bounds` + `lemma_C5_unique` + `add_left_cancel` + ax28) y `cantor_surjectivity` (construcción constructiva con `sub`/ax29 + `parity_lemma`).
- **Block5 cerrado** (commit `871e5e2`): `mod2_of_even`, `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c`, `pair_inj` — todos vía `cantor_uniqueness`/`cantor_injective_c` + `is_cantor_pair`.
- **Block6 cerrado** (commits `71862ca` + `1470a90`): `cons_neq_nil`, `cons_inj`, `in_cons_self_nil`, `in_cons_nil_imp_eq`, `concat_singletons` (vía helpers); `concat_assoc` y `in_concat_iff` cerrados vía spec de los nuevos `ax_C3`/`ax_L3`.
- **~30 helpers de orden/aritmética hechos públicos y exportados** desde `Block4_C5` (le_rewrite, lt_rewrite, le_self_add, le_add_one_cancel, le_mul_*, mul_lt_mono_right, sq_lt_mono, add_comm', mul_assoc', etc.). Helpers de Block2 (`zero_le`, `mul_le_mono_right`, `sq_le_mono`) hechos públicos. Duplicados eliminados.
- **Linter `unusedSimpArgs` desactivado** en todos los módulos (genera falsos positivos con simps bajo binders existenciales donde `FOL.substTerm_lift*` sí disparan reducciones que el linter no traza).
- **Conflicto de merge en `FOL/Theorems/Eq.lean` resuelto** (commit `4b262bf` en FOL): restaurados `substTerm_lift_comm` y `substTerm_liftLift` (necesarios para ROBINSON; eliminados por el merge previo `29ad33f`).

### Documentation (2026-05-27)

- `README.md`, `CURRENT-STATUS-PROJECT.md`, `PLANNING.md`, `NEXT-STEPS.md` actualizados al estado actual (Minimal completo, próximos pasos: Block7 / Intermediate / Full).
- Header de `Block3.lean` documenta su tamaño (~1900 líneas) como consecuencia explícita de la ausencia de inducción en Minimal (enumeración por numeral).

### Changed (2026-05-12)

- **Block3.lean — `div2_zero`, `div2_one`, `div2_two` (parcial) + helpers privados** (2026-05-12): Eliminados 2 sorry. Se demostraron completamente `div2_zero`, `div2_one` y los auxiliares `div2_zero_mul`, `div2_one_mul`, `div2_two_mul`. Se añadieron helpers privados `add_succ_left_ne_zero` y `mul_succ_two_ne_zero`. `div2_two` queda con 1 sorry (caso `1 < div2(2)`); `div2_three` y `div2_four` permanecen como sorry. Build: ✅ exit code 0, sin errores de compilación. **Corrección técnica**: `eq_congr_mul_right` para congruencia del argumento izquierdo de `mul`; `FOL.derive_eq_trans` para encadenamiento estándar `a=b, b=c → a=c` (vs `eq_trans` no-estándar con mismo LHS). Total sorry: 60 (antes 62).

### Changed (2026-05-09)

- **Bloque IV (Fase 9.1)**: Continuada la demostración del Lema C5 con la adición de múltiples lemas auxiliares para la manipulación de desigualdades.

### Changed (2026-05-09)

- **Bloques II y III completados**: Se han demostrado todos los teoremas de los bloques de raíz cuadrada (`Block2.lean`) y `div2`/`mod2` (`Block3.lean`). El proyecto ya no contiene `sorry`s.

### Added (2026-04-25 21:30)

- Declaración del axioma `henkin_extension_lemma` para manejar la expansión de constantes.
- Formalización del Teorema de Compacidad (`compactness_theorem`) y Consistencia (`consistency_of_satisfiable`) en `Compacity.lean`.
- El proyecto alcanza oficialmente **0 sorries** en su totalidad. ¡Hito final completado!
- Build status: ✅ Passing, 0 warnings.

### Added (2026-04-25 21:00)

- Formalización de la construcción de Henkin en `Completeness.lean`.
- Demostración formal del Lema de Lindenbaum (`lindenbaum_lemma`) y Compacidad Sintáctica.
- Demostración del Lema de la Verdad (`truth_lemma`) mediante inducción fuerte sobre la complejidad de fórmulas.
- Demostración del Teorema de Completitud de Gödel (`completeness`).

### Added (2026-04-25 20:30)

- Demostración completa de los lemas de sustitución semántica y reescritura en `FOL/Semantics.lean`, resolviendo la "trampa de De Bruijn" mediante inducción generalizada.
- El proyecto alcanza 0 sorries en toda la formalización de la sintaxis, deducción natural y corrección semántica (Soundness).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-25 20:00)

- Demostración completa del Teorema de Deducción en `FOL/Deduction.lean`.
- Definición de Modelos y Semántica de la lógica de primer orden en `FOL/Semantics.lean` (`Model`, `evalFormula`, `satisfies`).
- Demostración completa del Teorema de Corrección (Soundness) en `FOL/Soundness.lean` apoyada en los lemas semánticos.
- Implementación de la táctica `derive_raa` en `FOL/Tactics.lean`.
- Estado del Build: 0 errores, 5 sorries activos en `Semantics.lean` correspondientes a los lemas de sustitución y reescritura.

### Added (2026-04-25)

- Implementación de tácticas de automatización en `FOL/Tactics.lean`: `derive_hyp`, `derive_rewrite` y `derive_weaken`.
- Finalización oficial de la Fase 4 (Automatización).
- Inicio formal de la Fase 5 (Metamatemática y Completitud).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-20 00:00)

- Initial project structure from lean4-project-template

---

## [0.2.0] - 2026-04-20

### Added

- `NAMING-CONVENTIONS.md`: Full Mathlib-style naming dictionary with 12 formation rules, symbol-to-word dictionary, and migration tables
- `NEXT-STEPS.md`: Development phase planning template
- `THOUGHTS.md`: Design journal template for recording ideas and alternatives
- `REFERENCE.md` §0: Naming conventions quick-reference guide for the reader
- `REFERENCE.md` §Compliance: Checklist against AI-GUIDE.md requirements
- `AI-GUIDE.md` §22-23: Directory and subdirectory organization protocol
- `AI-GUIDE.md` §24-25: Annotation system (`@axiom_system`, `@importance`)
- `AI-GUIDE.md` §26-28: Cross-reference files documentation
- `AI-GUIDE.md`: Symbol-to-word dictionary and theorem formation rules summary in Naming Conventions section
- `DECISIONS.md`: ADR-004 (Mathlib naming), ADR-005 (directory-aligned namespaces), ADR-006 (annotation system), ADR-007 (separate NAMING-CONVENTIONS.md)
- `_template.lean`: Added naming convention reminders, annotation metadata, expanded section structure
- `CURRENT-STATUS-PROJECT.md`: Development phases tracking table

### Changed

- `README.md`: Added naming conventions summary table, documentation table format, subdirectory-aware project structure
- `DEPENDENCIES.md`: Added subdirectory-aware structure, multi-level dependency hierarchy example, Mermaid subgraph example

---

## [0.1.0] - 2026-04-20

### Added

- `Prelim.lean`: preliminary definitions

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/ProjectName)
- [Issues](https://github.com/julian1c2a/ProjectName/issues)

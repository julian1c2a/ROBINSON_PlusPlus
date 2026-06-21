# Current Project Status — ROBINSON_PlusPlus

**Last updated:** 2026-06-19
**Author**: Julián Calderón Almendros

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total modules | 41 (Minimal/ 11 + Meta/ 19 [Godel, Provability, Incompleteness, Hilbert, HilbertSeq, CodeArith, SubstArith, StepArith, CheckArith, Representability, Necessitation, Diagonal, CodeDistinct, Induction, ProofChain, DerivCond, Representability2, Reflection, GodelTwo] + Full/ 11) |
| Modules sin sorry | 41 / 41 ✅ |
| Sorry reales (total) | **0** 🎉 |
| Meta-reglas FOL (ω) | 6 en **`FOL/MetaRules.lean`** (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`, `dne`) — re-export desde `Minimal.Axioms` |
| Meta-axiomas matemáticos | `ax_p_tfa` (Block8); `ax_induction`/`ax_mod2_alternation`/`ax_list_induction` (Full); `Dem`/`dem_iff_provable`/`provFormula`/`provFormula_repr`/`diagonal_lemma` (Provability C, **legacy**); `D2`/`D3` (Incompleteness D, **legacy**). Las 6 ecuaciones recursivas de coding (`substtc`/`substtsc`) están **integradas en `Minimal.axioms`** (extensión definicional) — `SubstArith` sin `axiom` local |
| Axiomas matemáticos | **34** en `Minimal/`; en `Full/` **ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3** son **teoremas** + **TFA completo** (`tfa_numeral`) |
| Gödel | **A, B, C, D** ✅ (legacy I/II vía D2/D3 postulados). **Nivel D REAL — Gödel I REAL sin postulados**: cadena completa sobre Hilbert finitario `Prf` — verificador `validProofFn` (**19 reglas**, sólido vía `coreAxioms`; `ind` vía `Full.ax_induction`) + `repr_pos`/**D1** (`Meta/Necessitation.lean`) + **lema diagonal real** `tc_arith`→`diag_arith`→`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G` (`Meta/Diagonal.lean`) + **`goedel_first_real : ConsistentOmega → ¬ Prf G`** (`#print axioms` = ω-reglas ambiente + `Full.ax_induction`; NINGÚN `diagonal_lemma`/`provFormula`/D2/D3). **Regla `ind` integrada** (`Prf.ind`/`Rule.ind`/`ax_vpf_ind`/`vpf_ind`, `Meta/Induction.lean` + stack): `provCodeC` rastrea **IΣ₁**. Además **aritmética negativa de códigos** `formCode_ne` (`Meta/CodeDistinct.lean`). **Hacia D2/D3/Gödel II — verificador estructural `runFn`/`chainOk`** (`Meta/ProofChain.lean`, R1–R3) + **D1 y D2 reales sobre `provCodeC'`**: **D2** `⊢ provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B)` (`Meta/DerivCond.lean`) y **D1 = `repr_pos' : Prf φ → ⊢ provCodeC' φ`** (`Meta/Representability2.lean`; `#print axioms` = solo estándar), con validez de las 19 reglas (`lineWF`/`premsOf` fieles). **Gödel II — núcleo lógico ✅ con D3 POSTULADO** (`Meta/GodelTwo.lean`): `con_imp_godel'`/`goedel_second'` vía **D2 real** + `d3` (único axioma gödeliano) + hipótesis explícitas (punto fijo, necesitación, ⊬G ω); mejora sobre legacy (postulaba D2 y D3). Pendiente Gödel II 100% real: refactor `Prf.thy → axioms` + punto fijo `provCodeC'` + **D3 real** (Σ₁-completitud provable) |
| Build status | ✅ Passing (**55 jobs**, 0 errores, **0 warnings**, 0 sorrys) |
| Lean version | v4.29.1 |
| Naming convention | Mathlib-style (see `NAMING-CONVENTIONS.md`) |

> **Nota**: Todos los módulos compilan sin errores. Las 5 meta-reglas ω y los meta-axiomas matemáticos son `axiom` (intencionales, no provables), NO `sorry`s (ADR-008).

---

## Status by Module

| Module | Sorry | Status |
|--------|------:|--------|
| `Minimal/Axioms.lean` | 0 | ✅ Complete (5 `axiom` declarations son meta-reglas, no sorrys) |
| `Minimal/Theorems/Block1.lean` | 0 | ✅ Complete |
| `Minimal/Theorems/Block2.lean` | 0 | ✅ Complete |
| `Minimal/Theorems/Block3.lean` | 0 | ✅ Complete (verboso: enumera div2/mod2 por numeral, sin inducción) |
| `Minimal/Theorems/Block4.lean` | 0 | ✅ Complete |
| `Minimal/Theorems/Block4_C5.lean` | 0 | ✅ Complete — `lemma_C5`, `lemma_C5_unique`, `cantor_bounds` |
| `Minimal/Theorems/Block4_C6_C7.lean` | 0 | ✅ `add_left_cancel`, `mod2_of_even`, `proj1`/`proj2` (defs), `proj_is_cantor`, `cantor_uniqueness`, `cantor_surjectivity` |
| `Minimal/Theorems/Block5.lean` | 0 | ✅ `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c`, `pair_inj`, `is_cantor_pair` (mod2_of_even movido a Block4_C6_C7 el 2026-06-03) |
| `Minimal/Theorems/Block6.lean` | 0 | ✅ Todos probados (`concat_assoc` e `in_concat_iff` vía ax_C3/ax_L3 nuevos) |
| `Minimal/Theorems/Block7.lean` | 0 | ✅ `IsFunction`, `Functional`, `teo_F1`, `teo_F2`, `teo_F3` (Bloque VII spec) |
| `Minimal/Theorems/Block8.lean` | 0 | ✅ `Dvd`, `IsPrime`, `IsFactorization`, `ax_p_tfa` (TFA), pow/prod_pairs + **10 teoremas** (álgebra de `Dvd`, corolarios TFA) — Bloque VIII Fase 17 completa |
| `Meta/Godel.lean` | 0 | ✅ Nivel B Gödelización: `Sym`, `gNat`, `numeral`, `G`, `encode` (`⌜·⌝`), `encode_injective` (Teo G1) |
| `Meta/Provability.lean` | 0 | ✅ Nivel C: `formCode`+inyectividad, `IsFormula`, `Provable` (+iff), `Dem`, `diagonal_lemma`, `goedelSentence` (props profundas = meta-axiomas) |
| `Full/Induction.lean` | 0 | 🔄 Inducción general object-level: `ax_induction`, composición generalizada, **ax6/7/10/11/12/18/19** derivados + lemas de orden |
| `Full/Mod2.lean` | 0 | ✅ Opción C.2 (2026-06-11): `ax_mod2_alternation` + **ax21 (mod2_range) y ax24 (mod2_of_even) derivados como teoremas** |
| `Full/Lists.lean` | 0 | ✅ Listas (2026-06-11): meta-axioma `ax_list_induction` + **ax_C3 (concat_assoc) y ax_L3 (in_concat) derivados como teoremas** |
| **Total** | **0** | 🎉 |

*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending

---

## Recent Achievements

- **2026-06-11 — `Full/Lists.lean`: ax_C3 y ax_L3 derivados (inducción estructural)**: nuevo módulo (330 líneas) con **meta-axioma `ax_list_induction`** (estilo `imp_intro`/`gen`, parametrizado por `φ : Term → Formula`, conclusión sobre todos los Terms). Helpers de congruencia (`eq_congr_cons_right_full`, `eq_congr_concat_left/right`, `eq_subst_in`) + helper local `iff_intro`. **`concat_assoc_thm : ⊢ ax_C3_concat_assoc`** y **`in_concat_thm : ⊢ ax_L3_in_concat`** derivados por inducción estructural sobre L. Cobertura del fragmento aritmético + listas de Minimal en Full: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅. Build verde (29 jobs). Pendientes: Ax-P (TFA, inducción fuerte), Gödel Nivel D.

- **2026-06-11 — `Intermediate/` ELIMINADO + `Full/Mod2.lean` (Opción C.2)**: borrado el módulo prototipo `Intermediate/Induction.lean` y el directorio (decisión 2026-06-11: el sistema con Φ finito es caso particular de Full, mantener un nivel separado era burocracia conceptual). Nuevo módulo `Full/Mod2.lean` (290 líneas) con `ax_mod2_alternation : ∀n, mod2(σn)+mod2(n)=1` y derivación de **ax21 (mod2_range) y ax24 (mod2_of_even) como teoremas**. Auditoría 2026-06-11 (en `MINIMAL-AXIOMS.md §3.2`) documenta el hallazgo: `ax16+ax17` dejan `mod2` subdeterminado (modelos no estándar con mod2≥2 cumplen ambos), por eso `ax21` no es derivable sin axioma extra. Conservativo respecto a Minimal. Build verde (28 jobs).

- **2026-06-07 — `Full/Induction.lean`: ax19 (tricotomía del orden) derivado**: `lt_trichotomy_ax`/`lt_trichotomy_thm : axioms ⊢ ax19_lt_trichotomy`, por inducción object-level sobre `a` con `∀b` interno y `or_elim` 3-vías. Nuevos lemas de orden auxiliares: `zero_lt_succ`, `zero_or_succ_ax` (`∀n. n=0 ∨ ∃k. n=σk`), `lt_succ_cases` (`a<b → σa<b ∨ σa=b`) y `lt_intro`. Con ax18, el **fragmento de orden de PA⁻ queda derivado de la inducción**. Build verde (28 jobs, 0 sorrys/warnings).

- **2026-06-07 — `Full/Induction.lean`: inducción general object-level + axiomas derivados**: inducción general como **axioma object-level** (`ax_induction`), codificación lift-aware de `φ(σn)` y **composición De Bruijn generalizada** (`substFormula_succ_lift_gen` + `step_reduce`, que admite fórmulas no-ecuacionales). Derivados como **teoremas** (sin usar el axioma respectivo): **ax6** (add_comm), **ax7** (add_assoc), **ax10** (mul_comm), **ax11** (mul_assoc), **ax12** (mul_distrib) — algebraicos ecuacionales — y **ax18** (lt_irrefl) — primer no-ecuacional. + lemas de orden auxiliares (`lt_succ_self`, `not_lt_zero`, `lt_succ_of_lt`). Build verde (28 jobs).

- **2026-06-07 — `Intermediate/Induction.lean`: prototipo de inducción** (luego eliminado 2026-06-11): meta-axioma `peano_induction` (forma híbrida) + derivación de `zero_add`, `succ_add`, `add_comm` (= ax6). Hallazgo confirmado: la inducción general (Full) es de menor fricción técnica que la restringida a Φ → el trabajo continúa en `Full/`. Tras el prototipo, el módulo se elimina como conceptualmente redundante (caso finito de Full).

- **2026-06-06 — `Meta/Provability.lean` (Nivel C Gödelización) AÑADIDO**: codificación estructural de Gödel de la sintaxis FOL (`formCode`/`termCode`/`strCode`) con **inyectividad demostrada** (consistency-free, vía `injection`); `IsFormula`, `Provable` + teorema `provable_formCode_iff`; `Dem` + Teo Meta `dem_iff_provable`; lema del punto fijo `diagonal_lemma`; sentencia de Gödel `goedelSentence` + `goedelSentence_fixedpoint`. 5 meta-axiomas nuevos (Dem, dem_iff_provable, provFormula, provFormula_repr, diagonal_lemma) para las propiedades profundas (Nivel D). Barrel `Meta.lean` creado. Build verde, 0 sorrys.

- **2026-06-06 — `Meta/Godel.lean` (Nivel B Gödelización) AÑADIDO**: nuevo módulo `ROBINSON_PlusPlus.Meta.Godel` con Def 27 (`Sym`, `gNat`+`gNat_injective`, `numeral`+`numeral_injective`, `G`+`G_injective`), Def 28 (`encode`/`⌜·⌝`), y Teo G1 (`encode_injective`, meta-inyectividad consistency-free vía `injection`; + versiones object-level `encode_cons_inj`/`encode_cons_neq_nil` vía Block6). No añade axiomas matemáticos. Build verde a la primera. Ver `GODEL-STATUS.md`.

- **2026-06-06 — Block8 +10 teoremas**: álgebra de `Dvd` (`dvd_trans`, `dvd_mul_right/left`, `dvd_mul_of_dvd_left/right`, `dvd_add`) y corolarios del TFA (`factorization_exists/unique`, `lt_zero_one`, `factorization_one_eq_nil`). Euclides/multiplicatividad fuera de scope (requieren `prod_pairs_concat` → inducción).

- **2026-06-06 — Linter `unusedSimpArgs` a `false` global + warning FOL cerrado**: los 12 módulos pasan a `set_option linter.unusedSimpArgs false`. Cerrado el último warning externo `FOL/Theorems/Eq.lean:130` (commit FOL `9888c58`). Build global con 0 warnings.

- **2026-06-06 — Bloque VIII extendido (Fase 17 completa)**: `Axioms.lean` +`pow`/`prod_pairs` y 4 axiomas (sistema 30→34); `Block8.lean` +`IsFactorization` (Def 26) + meta-axioma `ax_p_tfa` (TFA). Limpieza de warnings previa 411→0.

- **2026-06-03 — Block8 (BLOQUE VIII Fase 17 parcial — Primos) AÑADIDO**: `Dvd` (divisibilidad), `IsPrime` (Def 25), lemas básicos. Pendientes documentados en header: Def 26 `IsFactorization` (necesita `pow`/`prod_list`), Ax-P (TFA), Fases 18-19 (Gödelización → módulo `Meta/` futuro). Build verde, 0 sorrys.

- **2026-06-03 — Block7 (BLOQUE VII Funciones Discretas) AÑADIDO**: nuevo módulo con `IsFunction`/`Functional` (meta-predicados Lean) y los 3 teoremas F1 (`IsFunction nil`), F2 (evaluación única `IsFunction F ∧ In ⟨x,y⟩ F ∧ In ⟨x,y'⟩ F → y=y'`), F3 (bicondicional `IsFunction ⟺ Functional`). Compiló a la primera, 0 sorrys. Cierra el alcance Cantor + Pares + Listas + Funciones declarado en `TuplasFuncionesYListas.md`.

- **2026-06-03 — `ax27_add_left_cancel` ELIMINADO**: derivable en PA⁻ sin inducción (tricotomía + monotonía + irreflexividad). Reescrito `add_left_cancel` (Block4_C6_C7) con prueba PA⁻; refactorizado `succ_le_of_lt` (Block2) para usar truco `ax13 + ax3 + ax18` (deriva `lt a a` y contradice). Sistema reducido **31 → 30 axiomas matemáticos**.

- **2026-06-03 — Build verde restaurado tras `537fd68`**: el commit del 2026-06-02 introdujo `proj_is_cantor` en `Block4_C6_C7` usando `mod2_of_even` (Block5), creando dependencia circular. Solución: mover `mod2_of_even` a `Block4_C6_C7` (justo antes de `proj_is_cantor`). Ningún cambio de prueba, solo de ubicación. **Recuento canónico rectificado: 31 axiomas** (los docs previos decían "30" por un error histórico de conteo; el sistema siempre tuvo 33 antes de eliminar ax22/ax23/ax28).

- **2026-06-02 — `ax22`/`ax23` ELIMINADOS** (commit `537fd68`, Claude Code Pro / Copilot Pro): `proj1`/`proj2` ya no son símbolos opacos del lenguaje sino `def proj1 (c) := x_of_c c` y `def proj2 (c) := y_of_c c` en `Block4_C6_C7`. El contenido de ax22 se demuestra constructivamente como teorema `proj_is_cantor`. `ax23` (`cantor_proj_uniq`) nunca se usó en código (la unicidad real estaba probada como `cantor_uniqueness`). `Block5` refactorizado para usar `proj_is_cantor` en lugar de `spec h_ax22`.

- **2026-06-02 — `ax28_mul_two_cancel` ELIMINADO**: la spec `TuplasFuncionesYListas.md §Teo 2.11` ya proporcionaba la prueba sin inducción (tricotomía + irreflexividad + monotonía estricta de *2). Reprobado `teo_2_11` directamente en Block1 (con nuevos helpers `mul_two_succ_ne_zero` y `mul_two_lt_mono`). Refactorizados `cantor_injective_c` (Block4) y `cantor_uniqueness` (Block4_C6_C7) para usar `teo_2_11` real.

- **2026-06-02 — REFERENCE.md proyectado**: reescritura completa, sustituyendo la versión severamente stale (todos los módulos marcados 🔄 In progress, fechado 2026-05-12). Ahora refleja 9/9 módulos ✅ Complete, 30 axiomas, lista de exports por módulo con signatura Lean + descripción matemática + dependencias.

- **2026-05-27 — 🎉 PROYECTO A 0 SORRYS REALES**: Cerrados los 2 últimos pendientes (`concat_assoc` e `in_concat_iff`) postulando `ax_C3_concat_assoc` y `ax_L3_in_concat` en Axioms.lean. Ambos son teoremas en sistemas con inducción; en Minimal se postulan (mismo patrón que ax21/ax24/ax27/ax28). Los 5 `axiom imp_intro/gen/raa/or_elim/ex_elim` son meta-reglas de FOL, no `sorry`. Build verde, WARN_sorry=0.

- **2026-05-27 — Block6 5/7 (sólo quedan los inductivos)**: Probados `cons_neq_nil` (vía ax_L0 + `is_cantor_pair` + teo_2_9 + ax9/ax5 + ax2), `cons_inj` (vía ax_L0 + `pair_inj` + ax3), `in_cons_self_nil` y `in_cons_nil_imp_eq` (vía ax_L2 triple-spec + ax_L1 para el caso falso), y `concat_singletons` (vía ax_C1 + ax_C2 + helper `eq_congr_cons_right`). Quedan `concat_assoc` y `in_concat_iff`: no derivables en Minimal sin inducción sobre L. Patrón del proyecto: postular como axiomas (candidatos a `ax_C3_concat_assoc` y `ax_L3_in_concat_iff`).

- **2026-05-27 — Block5 COMPLETO (0 sorrys)**: Probados `mod2_of_even` (vía ax24), `proj1_pair_eq_x`, `proj2_pair_eq_y` (vía `cantor_uniqueness` + ax22 + lema clave `is_cantor_pair`), `pair_proj_eq_c` (vía `cantor_injective_c` + ax22 + `is_cantor_pair`), y `pair_inj` (vía `cantor_uniqueness` tras `eq_congr_mul_left` para transportar al mismo `c = pair x y`). Lema clave nuevo `is_cantor_pair (x y) : mul two (pair x y) =eq cantor_poly x y` derivado de `cantor_poly_is_even` + `mod2_of_even` + ax17 + ax4 + `mul_comm'`.

- **2026-05-27 — Block4_C6_C7 COMPLETO (0 sorrys)**: `cantor_surjectivity` cerrado. Construcción: `w` desde `lemma_C5`, `k` desde `parity_lemma w` (`w(w+1)=2k`), `y := sub c k` con `k ≤ c` (de `2k ≤ 2c` y `ax28`/`le_of_mul_le_mul_left`), `x := sub w y` con `y ≤ w` (tricotomía + contradicción usando `expand_succ_succ` y `h_w_hi`). Verificación de `is_cantor` por cadena ecuacional `(x+y)(x+y+1) = w(w+1) = 2k`, luego `2k + 2y = 2c` vía `ax29_sub_witness` + `ax12_mul_distrib`. Sentencia ajustada a `liftTerm 0 (liftTerm 0 c)` bajo ∃∃; cierre con `ex_intro x; ex_intro y; simp + FOL.substTerm_liftTerm/liftLift`.

- **2026-05-27 — Infraestructura de resta añadida**: `sub_sym`, `def sub (a b)`, `ax29_sub_witness : ∀ a b, b ≤ a → b + (a − b) = a`. Permite cerrar `cantor_surjectivity` sin postular axiomas adicionales del estilo `sub_zero`/`sub_succ` (la unicidad determinada por el axioma testigo basta).

- **2026-05-27 — Block4_C5 completo (0 sorrys)**: Demostrados `sq_2w_plus_1`, `w_w1_le_2c_iff_sq_2w1_le_8c1`, `mono_w_w1`, `h_sq_2w1_le_sq_s`, `h_existence_part2` (este último por contradicción reusando el iff). Sentencia de `lemma_C5` corregida a `liftTerm 0 c` (era bare `c`, mal-formada en De Bruijn) y cerrada con `ex_intro w`. Eliminado `h_uniqueness` (código muerto: la meta es `∃` no `∃!`). Exportados además `lemma_C5_unique` y `cantor_bounds`.

- **2026-05-27 — Block4_C6_C7: `cantor_uniqueness` ✅**: Probado vía `cantor_bounds` + `lemma_C5_unique` + `add_left_cancel` + ax28. Helper local `add_comm_c`.

- **2026-05-27 — Conflicto de merge en FOL resuelto**: `FOL/Theorems/Eq.lean` tenía marcadores `<<<<<<<`/`=======`/`>>>>>>>` sin resolver entre dos `mutual` blocks (`substTerm_liftTerm_succ` HEAD vs `substTerm_lift_comm` incoming). Conservados ambos. También arreglados errores menores en `FOL/Theorems/Quantifiers.lean` (sintaxis `<;> [tac; tac]` → `<;> first | tac | tac`).

- **Block1–Block4 completados** (2026-05): Los cuatro bloques base (aritmética, raíz cuadrada, div2/mod2, auxiliares Cantor) están completamente probados sin sorrys.

- **Block4_C6_C7.lean — `add_left_cancel`** (2026-05-11): Demostrado el teorema de cancelación por la izquierda. Lema A privado (`lift_01_eq_00`) para triple `spec` sobre axiomas `forall_3`.

---

## Pending Work

**`Minimal/` y `Meta/` (Niveles B, C) completos.** Trabajo activo en `Full/` (Eje 4, inducción general): orden ya derivado (**ax18** irreflexividad + **ax19** tricotomía, con lemas auxiliares `zero_lt_succ`/`zero_or_succ_ax`/`lt_succ_cases`/`lt_intro`); pendientes **ax21/24** (mod2), **listas** (ax_C3/ax_L3 — esquema de inducción sobre listas), **Ax-P** (TFA) por inducción fuerte; luego **Nivel D** de Gödel (Gödel I/II internos). La infraestructura (`step_reduce` general) ya soporta fórmulas no-ecuacionales.

---

## Architecture

```
ROBINSON_PlusPlus/
├── Minimal/
│   ├── Axioms.lean          # 34 axiomas + pow/prod_pairs + 5 meta-reglas FOL
│   └── Theorems/
│       ├── Block1.lean      # Aritmética básica, constantes, orden ✅
│       ├── Block2.lean      # Raíz cuadrada, cotas, unicidad ✅
│       ├── Block3.lean      # div2, mod2 ✅
│       ├── Block4.lean      # Lemas auxiliares de Cantor ✅
│       ├── Block4_C5.lean   # Lema C5: ∃!w, w(w+1)≤2c<(w+1)(w+2) ✅
│       ├── Block4_C6_C7.lean# add_left_cancel, proj1/2, proj_is_cantor, mod2_of_even ✅
│       ├── Block5.lean      # Pares: proj1/2_pair, pair_proj, pair_inj, is_cantor_pair ✅
│       ├── Block6.lean      # Listas: cons_neq_nil, cons_inj, concat_assoc, in_concat ✅
│       ├── Block7.lean      # Funciones: IsFunction, Functional, F1/F2/F3 ✅
│       └── Block8.lean      # Primos+factorización: Dvd, IsPrime, IsFactorization, Ax-P TFA, +10 teoremas ✅
├── Meta.lean               # Barrel de Meta/ (Godel + Provability)
├── Meta/
│   ├── Godel.lean           # Nivel B Gödelización: G, ⌜·⌝, Teo G1 (encode_injective) ✅
│   └── Provability.lean     # Nivel C: formCode+iny., IsFormula, Provable, Dem, punto fijo, G_Min ✅
└── Full/
    ├── Induction.lean       # Inducción general object-level: ax6/7/10/11/12/18/19 derivados ✅
    ├── Mod2.lean            # Opción C.2 (2026-06-11): ax_mod2_alternation + ax21/24 derivados ✅
    └── Lists.lean           # Listas (2026-06-11): ax_list_induction + ax_C3/L3 derivados ✅
```

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-06-07 — Build ✅ (28 jobs), 0 sorrys, 0 warnings, 34 axiomas Minimal + meta-axiomas (incl. inducción), 15 módulos.*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

# Current Project Status — ROBINSON_PlusPlus

**Last updated:** 2026-07-09c
**Author**: Julián Calderón Almendros

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total modules | **62** (Minimal/ 11 + Meta/ 40 + Full/ 11) + barrel `Meta.lean` |
| Modules sin sorry | 62 / 62 ✅ |
| Sorry reales (total) | **0** 🎉 |
| Declaraciones `axiom` de Lean | **7** (tras F7a): 3 esquemas de inducción `Full/`, TFA `Block8`, 2 anclas de codificación, `d3`. Inventario en **`AXIOMS.md`**. Ninguna es un `sorry` (ADR-008) |
| Meta-reglas FOL (ω) | 6 en **`FOL/MetaRules.lean`** (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`, `dne`) — re-export desde `Minimal.Axioms` |
| Meta-axiomas matemáticos | Tras F7a: `ax_p_tfa` (Block8); `ax_induction`/`ax_mod2_alternation`/`ax_list_induction` (Full); `ax_inAxC` (⊢) / `prf_inAxC` (Prf) — pertenencia de coding a `axiomsCodeT`; `d3` (GodelTwo, único gödeliano vivo). Los 7 postulados legacy (`Dem`/`dem_iff_provable`/`provFormula`/`provFormula_repr`/`diagonal_lemma` + `D2`/`D3`) **retirados**. `qconf`/`Full.ax_induction` integrados como reglas del verificador. Inventario completo en **`AXIOMS.md`** |
| Axiomas matemáticos | **34** en `Minimal/`; en `Full/` **ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3** son **teoremas** + **TFA completo** (`tfa_numeral`) |
| Gödel | ⚠️ **Auditado 2026-07-13.** **Gödel I: sólo `⊬G`** — `goedel_first_real'` (`Meta/DiagonalTwo.lean`), real y **sin postulado gödeliano alguno**, vía punto fijo real `godelC'_fixedpoint`. **La mitad `⊬¬G` (indecidibilidad) NO está en la cadena real**: se probó en la capa LEGACY (`Meta/Incompleteness.lean`) con el postulado **falso en general** `provFormula_repr`, y se **retiró en F7a** — *no revertir, fue un arreglo de solidez*. Para recuperarla falta **`repr_neg : ConsistentOmega → Prf (provCodeC' φ) → Prf φ`**. — **D1** `repr_pos'_prf` ✅ y **D2** `d2_prf` ✅ **reales** sobre el cálculo finitario `Prf` (verificador estructural `runFn`/`chainOk`, `provCodeC'` rastrea IΣ₁). **Gödel II**: `goedel_second'` ✅ montado, **módulo `axiom d3`** (único postulado gödeliano vivo). **D3 reducida a UN SOLO lema** `d3_prf_of_chainOkDot` (ruta B dotada): `hI_dot` ✅ cerrado, lógica interna completa ✅ (§39, incl. inducción), intro del `∀` acotado ✅ (§40). **Falta**: el cuerpo `lineOkB` de `hC_dot` (el átomo `lineWF` = 21 casos de tag, subproyecto) → `d3_prf` → `goedel_second_prf` → **F7b** (7→6 `axiom`). Ver `NEXT-STEPS.md` §🎯 LO QUE QUEDA |
| Build status | ✅ Passing (**97 jobs**, 0 errores, **0 warnings**, 0 sorrys) |
| `NegVerifier` (módulo A) | ✅ **Decodificador COMPLETO** (§43): `Meta/CodeDecode.lean` (biyección de fórmulas: round‑trips + inyectividad `decodeForm_inj`) + `Meta/ChainDecode.lean` (cadenas: `decodeChain` + secciones `thy`/`mp`/`gen` + ensamblado `decodeChain_checkProof`/`decodeChain_prf`). Hallazgo: `lineJustif` es *lossy* ⟹ vale la **sección**, no el retract. Siguiente = módulo B (21 tags) |
| D3 / plan 12‑A | Fases **1a ✅ 1b ✅ 2 ✅** (verificador Δ₀ sin acumulador). **Fase 3 en curso**: ✅ puente `d3_prf_of_reflect_bounded` (D3 ⇐ reflejar `boundedIn`/`chainOkB`) + ✅ átomo `=eq` rastreado (`Sigma1AtomPrf`); ⏳ reflexividad libre de muro, átomos `<`/`lineWF`, cuantificadores acotados, inducción estructural → `d3_prf` → `goedel_second_prf` |
| Limpieza F7 | **F7a ✅ HECHA (2026-07-09)**: retirados los 7 postulados legacy (14→7 `axiom`); `Meta/Incompleteness.lean` eliminado + 5 postulados de `Meta/Provability.lean`. Cadena real verificada intacta (`#print axioms`). **F7b bloqueada** (`GodelTwo.d3` es portante; espera a D3 real) |
| Lean version | v4.31.0 |
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
| `Meta/Provability.lean` | 0 | ✅ Nivel C (núcleo real): `formCode`+inyectividad, `IsFormula`, `Provable` (+`provable_formCode_iff`). Capa legacy (`Dem`/`diagonal_lemma`/`goedelSentence`/…) retirada en F7a |
| `Meta/NumListPrf.lean` | 0 | ✅ 12‑A/1a: `prf_lenc_nil/cons`, `prf_nthc_zero/succ` |
| `Meta/NatArithPrf.lean` | 0 | ✅ 12‑A/1b: toolkit de `<` en `Prf` (`prf_nat_induction`, `prf_add_zero_left`, `prf_lt_iff`, `prf_succ_lt_succ_of_lt`, `prf_not_lt_zero`, …) |
| `Meta/BoundedInPrf.lean` | 0 | ✅ 12‑A/1b: **`prf_In_iff_boundedIn`** + `prf_zero_or_eq_succ_pred` |
| `Meta/RunFnBoundedPrf.lean` | 0 | ✅ 12‑A/2 (`In`): `prf_runFn_nil_cons` (map de `carc`), `prf_nthc_runFn`, **`prf_In_runFn_iff`** |
| `Meta/ChainOkBoundedPrf.lean` | 0 | ✅ 12‑A/2 (`chainOk`): `prf_premOk_cons_iff`, `prf_allIn_iff_boundedAllIn`, **`prf_chainOk_iff_chainOkB`** |
| `Meta/CodeDecode.lean` | 0 | ✅ `NegVerifier` A.1 (§43): `decodeNat`/`decodeChars`/`decodeStr`/`decodeTerm`/`decodeForm` + round‑trips + **inyectividad** ⟹ `decodeForm` es una **biyección** |
| `Meta/ChainDecode.lean` | 0 | ✅ `NegVerifier` A.2 (§43): `decodeRule`/`decodeLine`/`decodeChain`, `DecidableEq Term`/`Formula` + `findIdx`, secciones `thy`/`mp`/`gen`, ensamblado **`decodeChain_prf`** (cadena aceptada ⟹ `Prf`) |
| `Full/Induction.lean` | 0 | 🔄 Inducción general object-level: `ax_induction`, composición generalizada, **ax6/7/10/11/12/18/19** derivados + lemas de orden |
| `Full/Mod2.lean` | 0 | ✅ Opción C.2 (2026-06-11): `ax_mod2_alternation` + **ax21 (mod2_range) y ax24 (mod2_of_even) derivados como teoremas** |
| `Full/Lists.lean` | 0 | ✅ Listas (2026-06-11): meta-axioma `ax_list_induction` + **ax_C3 (concat_assoc) y ax_L3 (in_concat) derivados como teoremas** |
| **Total** | **0** | 🎉 |

*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending

---

## Recent Achievements

- **2026-07-09c — 12‑A fase 3: puente D3→forma acotada + átomo `=eq` rastreado**:
  **`Meta/Sigma1BoundedPrf.lean`** (NUEVO): **`d3_prf_of_reflect_bounded`** — como la fase 1/2 dio los
  `⇔` (`prf_In_iff_boundedIn`, `prf_chainOk_iff_chainOkB`) y `pcc_imp` sube implicaciones a
  `provCodeC'`, D3 se reduce a reflejar la forma **Δ₀ acotada** `boundedIn`/`chainOkB`.
  **`Meta/Sigma1AtomPrf.lean`** (NUEVO): toolkit RASTREADO del átomo `=eq` (`eqCodeFn` + congruencia +
  transporte + `prf_provCodeC'_eq_of_tracked`), espejo del de `In`. **Hallazgo confirmado en código:**
  la reflexión de `=eq` para términos abstractos es imposible **libre de muro** (Tarski: `termCode`
  sin congruencia object) → se rastrea con `tcFn` (que sí la tiene) y el puente `tcFn t =eq termCode t`
  lo descarga la inducción de fase 5 (numerales, `prf_tc_numeral`). `#print axioms` limpios. Plan
  restante en `GODEL-D3-TRACKED-DESIGN.md` §15.4. Build **76 jobs**, 0 sorrys, v4.31.0.

- **2026-07-09 — F7a: retirada la capa Gödel legacy (14 → 7 `axiom`)**:
  Auditado con `#print axioms` que la cadena real (`goedel_first_real'`, `d2_prf`, `goedel_second'`)
  no cita ninguno de los 7 postulados legacy. **Eliminado** el módulo `Meta/Incompleteness.lean`
  (Gödel I/II vía D2/D3 postulados) y retirados los 5 postulados de `Meta/Provability.lean`
  (`Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma` + `goedelSentence`/
  `goedelSentence_fixedpoint`); se conserva el núcleo real de codificación (`formCode`/`IsFormula`/
  `Provable`). Nuevo **`AXIOMS.md`** (registro autoritativo de los 7 axiomas restantes + las 6
  meta-reglas ω de FOL). Cadena real verificada intacta. **F7b** (retirar `d3`) sigue bloqueada
  hasta D3 real. Build verde (**74 jobs**), 0 sorrys, v4.31.0.

- **2026-07-08 — 12‑A FASES 1b y 2 COMPLETAS: el verificador ya es Δ₀ y sin acumulador**:
  Cerrado el **único punto de diseño del plan 12‑A que no estaba verificado en código**.
  **`Meta/NatArithPrf.lean`** (NUEVO): toolkit aritmético de `<` en `Prf` — hallazgo de escala,
  `lt a b := ∃k. a+σk=b` y `add` recurre por la derecha ⇒ **`0+n=n` NO es teorema de Q** y hay que
  reconstruirlo con `Prf.ind`. **`Meta/BoundedInPrf.lean`** (NUEVO): **`prf_In_iff_boundedIn`**
  (`In x L ⇔ ∃i<lenc L. nthc L i =eq x`) + `prf_zero_or_eq_succ_pred` (case-split de índice sin `∃`).
  **`Meta/RunFnBoundedPrf.lean`** (NUEVO): *corrección al diseño §12.3 —* **no hace falta β‑función**:
  `runFn nil p` no es recursión con acumulador, es el ***map* de `carc` sobre `p`**
  (`prf_runFn_nil_cons`, vía `prf_runFn_weaken`) ⇒ **`prf_In_runFn_iff`**, acotado por `lenc p`.
  **`Meta/ChainOkBoundedPrf.lean`** (NUEVO): (a) `prf_allIn_iff_boundedAllIn`, (b)
  `prf_in_concat_singleton_iff`, (0) `boundedCarcLt` (cota arbitraria), (c)
  `prf_boundedCarcLt_cons_succ_iff`, (d) **`prf_chainOk_iff_chainOkB`** — *el acumulador desaparece*:
  `chainOk c p ⇔ ∀i<lenc p. (lineWF (nthc p i) ∧ ∀j<lenc (premsOf …). (In … c ∨ ∃k<i. carc (nthc p k) =eq …))`,
  la formulación Δ₀ de libro. Inducción de listas con acumulador **`∀c` interno**, HI instanciada en
  `c ++ [carc line]`; el paso `cons` se apoya en el lema puntual `prf_premOk_cons_iff` (fusiona (b)+(c)).
  Todos `#print axioms` = `[propext, choice, Quot.sound]`. Nuevo `ESCALANDO_EL_PROYECTO.md` (enlace con
  DeepArith sobre el kernel FOL⁼ común). Build verde (**75 jobs**), 0 sorrys, v4.31.0.
  Siguiente: fases 3‑5 (`num` + evaluación provable + Δ₀‑completitud atómica → inducción estructural
  → `d3_prf` → `goedel_second_prf`).

- **2026-07-05c/d — D3: investigación de atajos (§11–§12) + arranque Σ₁‑completitud estándar (12‑A fase 1a)**:
  Investigación rigurosa: **no hay atajo para D3** (atajo por teorema de deducción imposible — D1
  exige `Prf` cerrado, D1‑con‑contexto es falsa = esa brecha es D3; enfoque `tcFn` descartado —
  `tcFn L =eq termCode L` stuck para `L` abstracta). Hallazgo central: **codificar el testigo ≡
  representar el verificador** sobre números (Δ₀), pero el verificador es estructural sobre listas.
  Decidida la **Opción 12‑A (capa numérica Δ₀ del verificador)**. **Fase 1a hecha**: `lenc`/`nthc`
  (longitud/índice de lista‑código) — defs + 4 axiomas en `Minimal/Axioms` (extensión conservadora,
  `axioms_eq` rfl preservado, **build entero verde: verificador/D1 intactos**) + ecuaciones `Prf`
  (`Meta/NumListPrf.lean`). Además `Meta/TrackedCorePrf.lean` extendido con `atom2CodeFn` (infra de
  códigos). Diseño completo en `GODEL-D3-TRACKED-DESIGN.md` §11–§12. Build verde (**71 jobs**),
  0 sorrys, v4.31.0. Siguiente: fase 1b (caracterización acotada de `In`).

- **2026-07-05b — Gödel II / Opción A: A‑F3 `pcc_exIntro_code` + verificación concreta RIESGO‑1**:
  `Meta/ExIntroCodePrf.lean` cierra la **A‑F3** (∃‑intro de la regla Q2 al nivel de código con
  testigo‑código arbitrario cerrado; `#print axioms` = estándar). `Meta/Sigma1TrackedPrf.lean`
  (NUEVO) verifica el ∃‑intro rastreado para testigos **concretos** (`pcc_exIntro_code_bridge`/
  `_objList`). **Hallazgo:** el testigo **abstracto** no lo cubre esta pieza — `tcFn #0` no es
  cerrado y todo combinador base produce `termCode` meta (transporte a `tcFn` stuck para lista
  abstracta) → `hI_tracked` abstracto requiere la **Opción A de raíz** (`provFormulaC'ₜ`/D1ₜ).
  Limpieza F7 (retirar `GodelTwo.d3` legacy) sigue BLOQUEADA hasta `goedel_second_prf` real.
  Build verde (**69 jobs**), 0 sorrys, Lean v4.31.0.

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

**`Minimal/`, `Full/` y `Meta/` (Niveles A–D) completos.** Gödel I es REAL y sin postulados; D1 y D2
son teoremas reales. **Lo único vivo es D3** (Σ₁‑completitud provable del verificador), en
construcción por el plan **12‑A** (`GODEL-D3-TRACKED-DESIGN.md` §12–§14):

| Fase 12‑A | Contenido | Estado |
|-----------|-----------|--------|
| 1a | `lenc`/`nthc` + ecuaciones `Prf` | ✅ |
| 1b | toolkit `<` en `Prf` → `prf_In_iff_boundedIn` | ✅ |
| 2 | `prf_In_runFn_iff` + `prf_chainOk_iff_chainOkB` (verificador Δ₀, sin acumulador) | ✅ |
| 3 puente | `d3_prf_of_reflect_bounded` (D3 ⇐ reflejar `boundedIn`/`chainOkB`) | ✅ |
| 3 átomo `=eq` | `Sigma1AtomPrf`: `eqCodeFn` + `prf_provCodeC'_eq_of_tracked` (rastreado) | ✅ |
| 3‑4 resto | reflexividad libre de muro, átomos `<`/`lineWF`, cuantificadores acotados | ⏳ |
| 5 | inducción estructural sobre `boundedIn`/`chainOkB` → `d3_prf` → `goedel_second_prf` | ⏳ |

*Nota honesta:* 12‑A ≈ portar la Σ₁‑completitud provable de IΣ₁ — trabajo de varias sesiones, pero ya
no queda ningún punto del plan sin verificar en código. **Alternativa siempre disponible**: consolidar
Gödel II **módulo el axioma D3** (`goedel_second'`), estado ya publicable.

Trabajo de limpieza: **F7a ✅ HECHA** (2026-07-09; 14→7 `axiom`, `Meta/Incompleteness.lean`
eliminado + 5 postulados de `Provability`). **F7b** (`GodelTwo.d3`) espera a D3 real (12‑A fase 5).

---

## Architecture

```text
ROBINSON_PlusPlus/
├── Minimal/
│   ├── Axioms.lean          # 34 axiomas + pow/prod_pairs + carc/cdrc + lenc/nthc + 5 meta-reglas FOL
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
├── Meta.lean                # Barrel de Meta/ (40 módulos)
├── Meta/                    # Nivel B + Nivel C (núcleo real) + Nivel D REAL (40 módulos)
│   ├── Godel.lean           # Nivel B: G, ⌜·⌝, Teo G1 (encode_injective) ✅
│   ├── Provability.lean     # Nivel C núcleo real: formCode+iny., IsFormula, Provable ✅ (legacy retirada F7a)
│   ├── Hilbert.lean … CheckArith.lean         # cálculo finitario Prf + verificador (19 reglas)
│   ├── Representability.lean … Diagonal.lean  # D1 + punto fijo + goedel_first_real
│   ├── ProofChain.lean … DiagonalTwo.lean     # verificador estructural runFn/chainOk + Gödel I real'
│   ├── HilbertDeduction.lean … DerivCondPrf.lean  # PrfH + deducción + D1/D2 finitarias reales
│   ├── ReflectionPrf.lean … Sigma1TrackedPrf.lean # D3 reducida + reflexión Σ₁ (tcFn: descartado)
│   ├── NumListPrf.lean      # 12‑A/1a: ecuaciones Prf de lenc/nthc ✅
│   ├── NatArithPrf.lean     # 12‑A/1b: toolkit aritmético de `<` en Prf ✅
│   ├── BoundedInPrf.lean    # 12‑A/1b: prf_In_iff_boundedIn ✅
│   ├── RunFnBoundedPrf.lean # 12‑A/2: prf_In_runFn_iff (runFn nil = map de carc) ✅
│   ├── ChainOkBoundedPrf.lean # 12‑A/2: prf_chainOk_iff_chainOkB (sin acumulador) ✅
│   ├── Sigma1BoundedPrf.lean # 12‑A/3 puente: d3_prf_of_reflect_bounded ✅
│   ├── Sigma1AtomPrf.lean   # 12‑A/3 núcleo: átomo =eq rastreado (eqCodeFn) 🔄
│   └── GodelTwo.lean        # Gödel II núcleo: goedel_second' (D2 real + `axiom d3`) 🔶
└── Full/                    # Eje 4: inducción general object-level + TFA (11 módulos)
    ├── Induction.lean       # ax6/7/10/11/12/18/19 derivados ✅
    ├── Mod2.lean            # ax_mod2_alternation + ax21/24 derivados ✅
    ├── Lists.lean           # ax_list_induction + ax_C3/L3 derivados ✅
    └── … Numerals / Bounded / Divisibility / Division / PrimeFactor / Primality / Factorization (tfa_numeral) ✅
```

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-07-09c — Build ✅ (76 jobs), 0 errores, 0 sorrys, 0 warnings, 62 módulos, Lean v4.31.0. F7a: 14 → 7 axiomas (AXIOMS.md). 12‑A fases 1a/1b/2 ✅ + fase 3 en curso (puente + átomo `=eq`).*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

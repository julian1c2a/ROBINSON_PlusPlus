# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-06-23 (46 módulos, 59 jobs) — **GÖDEL NIVEL D REAL — `repr_pos'_prf` COMPLETO (D1 re-nivelada a `Prf`)**. Toda la representabilidad positiva sube al cálculo finitario `Prf` (necesario para Gödel II real: `provCodeC'` rastrea `Prf`, `¬⊢Con'` es falso): **`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`** (`#print axioms` = estándar + único meta-axioma `prf_inAxC`, espejo del `repr_pos'` ⊢-level). Dos módulos nuevos: `Meta/ArithPrf.lean` (porte finitario de toda la aritmetización, ~50 lemas; hallazgo: `numeral_lt` es finitario —∃-intro vía `q2`— por lo que toda la aritmética de códigos sube a Prf) y `Meta/Representability2Prf.lean` (tracking `prf_runFn_track`/`prf_chainOk_track` 19 casos + `provCodeC'_intro_prf` + ensamblaje). En `Meta/ReprPrf.lean`: 32 esquemas `lineWF`/`premsOf` portados. **Próximo (cadena Gödel II en Prf)**: `d2_prf` (añadir regla de inducción de listas en `Prf`, como se hizo con `ind`) → punto fijo + necesitación en Prf → `goedel_second_prf` (`ConsistentH → ¬ Prf Con'`) → **D3 real**. Ver [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

**(2026-06-19, 35 módulos, 49 jobs)** — **GÖDEL NIVEL D REAL — PRIMER TEOREMA DE GÖDEL REAL SIN POSTULADOS**. Cadena completa sobre el cálculo de Hilbert finitario `Prf`: verificador `validProofFn` sólido (18 reglas, `thy` vía `coreAxioms`) → `repr_pos`/**D1** (`Necessitation`) → **lema diagonal real** (`Diagonal`: `tc_arith` código-del-código → `diag_arith` → `godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`) → **`goedel_first_real : ConsistentOmega → ¬ Prf G`**. Además aritmética negativa de códigos `formCode_ne` (`CodeDistinct`). `#print axioms` de los resultados = solo ω-reglas ambiente; ningún `diagonal_lemma`/`provFormula`/D2/D3.

**(2026-06-12)** — **TFA COMPLETO CERRADO** (existencia object ∧ unicidad ℕ, sobre numerales, autocontenido sin Mathlib/Peano): `tfa_numeral` (`Full/Factorization.lean`). Unicidad ℕ vía Euclides (`Full/PrimeFactor.lean`: `euclid`, `factorization_perm_unique`). Capa de teoría de números completa sobre la representabilidad: `Primality` (`isPrime_numeral`), `Division` (`division_numeral`), `PrimeFactor` (ℕ pura: factor primo, factorización, **Euclides + unicidad**), `Factorization` (`tfa_exists_numeral`, `tfa_numeral`). Cimientos: `Numerals` (homomorfismo `+,·,^,<,≠`), `Bounded` (`le_numeral_split`), `Divisibility` (`numeral_dvd`, `divisor_le`), F1 `StrongInduction`. Reencuadre **numerales + representabilidad** (Gödel-aware) disuelve los Muros 1/2. Fragmento aritmético + listas de Minimal en Full: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅. Sistema con **34 axiomas matemáticos** en Minimal + meta-axiomas, **24 módulos** (Minimal/ 11 + Meta×2 + Full ×11), 0 sorrys, 0 warnings (37 jobs). **Próximo**: Gödel Nivel D (Meta/Incompleteness) sobre esta base; o consolidar.

---

## Situación actual

Build: ✅ `lake build` exit 0. **0 sorrys reales** y **0 warnings RPP** en los 11 módulos. Los 5 `axiom` de `Axioms.lean` (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) son meta-reglas de FOL; `ax_p_tfa` en `Block8.lean` es un meta-axioma adicional (TFA). Ninguno es `:= sorry`.

El sistema `Minimal/` cumple su objetivo declarado en [PLANNING.md](PLANNING.md): **34 axiomas matemáticos sin esquema de inducción son suficientes para construir la función de Cantor, las tuplas con proyecciones, las listas con concatenación y pertenencia, las funciones discretas, los primos y la factorización prima** (TFA vía Ax-P).

---

## Eje 1 — Consolidar `Minimal/` ✅ CERRADO (2026-06-06)

Todos los hitos completados:

- [x] **Bloque VII — Funciones discretas**: `Block7.lean` con `IsFunction`, `Functional`, F1/F2/F3 (2026-06-03).
- [x] **Bloque VIII — Primos**: `Block8.lean` con `Dvd`, `IsPrime`, lemas básicos (2026-06-03).
- [x] **Bloque VIII extendido — Factorización**: `pow`, `prod_pairs`, `IsFactorization`, `Ax-P` (TFA). Sistema 30 → **34 axiomas matemáticos** (2026-06-06). Auditoría profunda en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4-3.5.
- [x] **Limpieza warnings global**: 411 → 0 warnings RPP, linter `unusedSimpArgs true` global (2026-06-06).
- [x] **Diagnóstico frente Gödel (Nivel A)**: `Minimal/` satisface las hipótesis de Gödel I; relación con TFA y EFA/I∆₀+Exp analizada en [GODEL-STATUS.md](GODEL-STATUS.md) y [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §5.5.

**Estado de auditoría de axiomas no-induction-bound** (resuelto):

| Axioma | Estado | Comentario |
| --- | --- | --- |
| `ax21_mod2_range` | postulado | requiere inducción (irreducible — analizado en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.2) |
| `ax24_mod2_of_even` | postulado | requiere inducción sobre `k` (auditado 2026-06-03, irreducible) |
| `ax_C3_concat_assoc` | postulado | requiere inducción sobre `L` (irreducible) |
| `ax_L3_in_concat` | postulado | requiere inducción sobre `L` (irreducible) |
| `ax_pow_zero`, `ax_pow_succ` | postulados | definicionales puros (recursión primitiva base — [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4.1) |
| `ax_prodp_nil`, `ax_prodp_cons` | postulados | definicionales puros sobre listas (§3.4.2) |
| `ax_p_tfa` (TFA) | meta-axioma | requiere inducción fuerte; pasa a teorema en `Full/` |
| ~~`ax20`, `ax22`, `ax23`, `ax27`, `ax28`~~ | **ELIMINADOS** | derivables sin inducción o redundantes (ver CHANGELOG) |

**Pendientes menores** (no bloquean cierre):

- ✅ ~~Arreglar warning externo `FOL/Theorems/Eq.lean:130`~~ — **RESUELTO 2026-06-06** (eliminado el simp arg `hne` no usado en `substTerm_liftLift`; commit `9888c58` en el repo FOL). Build global con **0 warnings** (incl. FOL externo).
- ✅ ~~Más teoremas sobre `IsFactorization`/`Dvd` usando `ax_p_tfa`~~ — **HECHO 2026-06-06**: +10 teoremas en Block8 (álgebra de `Dvd`: `dvd_trans`, `dvd_mul_right/left`, `dvd_mul_of_dvd_left/right`, `dvd_add`; corolarios TFA: `factorization_exists/unique`, `lt_zero_one`, `factorization_one_eq_nil`). Lema de Euclides y multiplicatividad **fuera de scope** (requieren `prod_pairs_concat` → inducción).

---

## Eje 2 — Módulo `Meta/` (Niveles B y C ✅ 2026-06-06; próximo Nivel D)

**Objetivo**: implementar Fases 18-19 del spec (`TuplasFuncionesYListas.md §BLOQUE VIII`) — Gödelización y autorreferencia. Diagnóstico completo y arquitectura en [GODEL-STATUS.md](GODEL-STATUS.md).

**Decisión 2026-06-06**: `Meta/` arranca **al cerrar `Minimal/`**, no después de `Intermediate/`. Justificación: los niveles B-C (codificación + Dem) no requieren inducción, sólo meta-codificación. El nivel D (teoremas de incompletitud demostrados internamente) sí requiere `Intermediate/` o `Full/`.

### 2.1. Nivel B — `Meta/Godel.lean` (primer hito) ✅ COMPLETADO 2026-06-06

- [x] **Asignación de Gödel** `G : símbolos → ℕ` (Def 27 spec). `inductive Sym` (12 símbolos) + `gNat` (tabla ∀→2, ∃→3, =→10, …, m→111) + `gNat_injective`; `numeral`+`numeral_injective`; `G := numeral ∘ gNat` + `G_injective`.
- [x] **Corner brackets** `⌜·⌝ : List Sym → Term` (Def 28): `encode [] = nil`, `encode (s::S) = cons (G s) (encode S)`; notación scoped `⌜·⌝`.
- [x] **Teorema G1** (inyectividad): `encode_injective` (meta-inyectividad consistency-free, vía `injection` + inducción estructural) + versiones object-level `encode_cons_inj` (usa `cons_inj`, Block6) y `encode_cons_neq_nil`. Ver `GODEL-STATUS.md` §2 sobre la elección meta vs objeto.

**No introduce nuevos axiomas matemáticos** sobre `Minimal/`. Aprovecha `pow` + TFA para codificación primorial alternativa (ver [GODEL-STATUS.md](GODEL-STATUS.md) §3.1).

### 2.2. Nivel C — `Meta/Provability.lean` (segundo hito) ✅ COMPLETADO 2026-06-06

- [x] **Codificación estructural** de Gödel: `formCode : Formula → Term` (+ `termCode`/`termsCode`/`strCode`/`charsCode`), con **inyectividad demostrada** (`formCode_injective`, `termCode_injective`, … vía `injection`, consistency-free).
- [x] Predicado `IsFormula(x)` (Def 29): `∃ φ, x = formCode φ`. + `Provable x` y el teorema real `provable_formCode_iff` (`Provable ⌜φ⌝ ↔ axioms ⊢ φ`).
- [x] Predicado `Dem(d, x)` (Def 30) — **meta-axioma** (codifica árboles de derivación, requiere Nivel D). + **Teo Meta** `dem_iff_provable` (`axioms ⊢ φ ↔ ∃ d, Dem d ⌜φ⌝`), meta-axioma.
- [x] **Lema del punto fijo** (`diagonal_lemma`): `∀ φ, ∃ ψ, ⊢ ψ ⇔ φ[⌜ψ⌝]` — meta-axioma.
- [x] **Sentencia de Gödel** `goedelSentence` := punto fijo de `¬provFormula`; `goedelSentence_fixedpoint` (`⊢ G_Min ⇔ ¬Prov(⌜G_Min⌝)`) demostrado a partir de `diagonal_lemma`. `provFormula`/`provFormula_repr` postulados.

**Meta-axiomas nuevos (5)**: `Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma`. Justificados: la aritmetización de demostraciones y la diagonalización requieren inducción → pasarán a teoremas en el **Nivel D** (`Intermediate/`/`Full/`). Lo demostrado sin postular: toda la codificación + inyectividad + `provable_formCode_iff`.

### 2.3. Nivel D — `Meta/Incompleteness.lean` (requiere `Intermediate/` o `Full/`)

- [ ] **Gödel I**: `Minimal ⊬ G_Min` y `Minimal ⊬ ¬G_Min` (asumiendo consistencia).
- [ ] **Gödel II**: `Minimal ⊬ Con(Minimal)`.

Esto se queda para más adelante; la formalización requiere inducción sobre la complejidad sintáctica de las demostraciones.

---

## ~~Eje 3 — Sistema `Intermediate/`~~ ❌ ELIMINADO (2026-06-11)

**Decisión 2026-06-11**: `Intermediate/` se elimina por **redundancia conceptual**. El sistema con esquema de inducción restringido a Φ finito **es el caso particular** de `Full/` (cualquier instancia inductiva concreta que necesitemos se obtiene postulando sólo la φ pertinente en `Full/`, sin necesidad de un sistema separado). El prototipo `Intermediate/Induction.lean` confirmó que la inducción general no añade fricción técnica sobre la restringida — por lo tanto no hay coste por colapsar los dos niveles.

Todo lo que iba a desarrollarse en `Intermediate/` (derivar ax6, ax7, ax10-12, ax18, ax19, ax21, ax24, ax_C3, ax_L3 como teoremas) **se desarrolla directamente en `Full/`**. Resultados actuales en Full: ax6, ax7, ax10, ax11, ax12, ax18, ax19, **ax21, ax24** ✅ (ver Eje 4).

`Intermediate/Induction.lean` y el directorio `Intermediate/` quedan **borrados** del repositorio.

---

## Eje 4 — Sistema `Full/` (EN CURSO — arranque object-level 2026-06-07)

> **✅ `Full/Induction.lean` + `Full/Mod2.lean` + `Full/Lists.lean` (2026-06-07 + 2026-06-11)** — Inducción general como **axioma object-level** (`ax_induction : ⊢ inductionFormula φ`), con codificación **lift-aware** de `φ(σn)`. Composición De Bruijn generalizada (`substFormula_succ_lift_gen` + `step_reduce`). **Derivados como teoremas en forma object-level pura**: ax6 (`add_comm_thm`), ax7 (`add_assoc_ax`), ax10/11/12 (mul algebraicos), ax18 (`lt_irrefl_thm`), ax19 (`lt_trichotomy_thm`), y — **2026-06-11 vía Opción C.2** con axioma extra `ax_mod2_alternation : ∀n, mod2(σn)+mod2(n)=1` — `mod2_range_thm : ⊢ ax21_mod2_range` y `mod2_of_even_thm : ⊢ ax24_mod2_of_even`, y — **2026-06-11 vía meta-axioma `ax_list_induction`** (inducción estructural sobre listas, estilo `imp_intro`/`gen` parametrizado por `φ : Term → Formula`) — `concat_assoc_thm : ⊢ ax_C3_concat_assoc` y `in_concat_thm : ⊢ ax_L3_in_concat`. Lemas auxiliares: `mod2_zero_aux`, `a_plus_one_eq_one`, `eq_congr_mod2`, `eq_congr_cons_right_full`, `eq_congr_concat_left/right`, `eq_subst_in`, `iff_intro` (helper local). **`Intermediate/` eliminado** (caso finito de Full). **Estado**: fragmento aritmético + listas de Minimal totalmente cubierto en Full salvo Ax-P (TFA) y los testigos `ax21`/`ax24`/`ax_C3`/`ax_L3` que ya son teoremas. Siguiente: **Ax-P (TFA, inducción fuerte)**, Gödel Nivel D.

**Objetivo (PLANNING §6.3)**: Axiomas de Peano puros + **esquema de inducción general** sobre todas las fórmulas del lenguaje. Todos los axiomas postulados en `Minimal/` (ax21, ax24, ax_C3, ax_L3) y el meta-axioma `ax_p_tfa` (TFA) se vuelven teoremas. Habilita el **Nivel D** del frente Gödel: Gödel I y II demostrados internamente.

### 4.1. Roadmap de Ax-P / TFA — reencuadre **numerales + representabilidad** (2026-06-11)

**Obstrucción foundational detectada** al intentar F2 meta-nivel: en FOL=, (Muro 1) los existenciales object no dan testigos meta — `ex_elim` sólo concluye `axioms ⊢ C`; y (Muro 2) las disyunciones object (tricotomía) no se eliminan a conclusión meta. Por eso `strong_induction_meta` con case-split **no funciona**, y derivar el `ax_p_tfa` *meta* de Block8 con testigos usables es **equivalente a la maquinaria de representabilidad de Gödel** (no hay atajo).

**Decisión (Opción A, Gödel-aware)**: como Gödel Nivel D necesita representabilidad de todos modos, se construye esa capa una vez y TFA cae como corolario. Se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con **cómputo meta en ℕ + transferencia** vía homomorfismo. Disuelve los dos muros (lo decisional/constructivo ocurre en ℕ). Reutiliza Peano como cómputo meta.

**Capa de representabilidad (cimientos) — HECHO 2026-06-11**:

- [x] **F1 — Inducción fuerte object** (`Full/StrongInduction.lean`): `strong_induction` derivada de `ax_induction` sin axioma nuevo + `substFormula_liftFormula` + `lt_succ_split`.
- [x] **Numerales** (`Full/Numerals.lean`): `numeral : ℕ → Term` + homomorfismo `numeral_add/mul/pow`, orden `numeral_lt`, separación `numeral_ne`. El puente meta↔object.
- [x] **Cuantificación acotada** (`Full/Bounded.lean`): `le_numeral_split` — `d ≤ numeral n` ⇒ casos finitos `d = numeral i`. Convierte ∀ acotado en análisis finito.
- [x] **Divisibilidad** (`Full/Divisibility.lean`): `numeral_dvd` (meta ∣ → object Dvd) + `divisor_le` (divisor de positivo es ≤).

**Capa de teoría de números — HECHO 2026-06-12**:

- [x] **Primalidad representada** (`Full/Primality.lean`): `isPrime_numeral` — `p` primo (meta, hipótesis `2≤p` + divisores triviales, sin Mathlib) ⇒ `IsPrime (numeral p)`. Vía `divisor_le` + `le_numeral_split` + split anidado sobre el cofactor.
- [x] **División con resto** (`Full/Division.lean`): `division_numeral` — `numeral n = numeral(n/d)·numeral d + numeral(n%d)`, `numeral(n%d) < numeral d`. Trivial vía homomorfismo (cómputo `n/d`, `n%d` en ℕ).
- [x] **Factor primo + factorización META** (`Full/PrimeFactor.lean`, ℕ pura sin Mathlib): `exists_prime_factor` (∀ n≥2, ∃ factor primo) + `primeFactorList` (∀ n≥1, ∃ lista plana de primos con producto n), por inducción fuerte (`Nat.strongRecOn`).
- [x] **TFA-existencia transferida** (`Full/Factorization.lean`): `toTerm` (encoding lista de pares `(numeral p, 1)`), `prod_pairs_toTerm` (`⊢ prod_pairs (toTerm ps) =eq numeral (natProd ps)`), y **`tfa_exists_numeral`** — `∀ n≥1, ∃ ps, (∀p∈ps, IsPrimeNat p) ∧ ⊢ prod_pairs (toTerm ps) =eq numeral n`. Autocontenido (sin Peano).

**UNICIDAD + TFA completo — HECHO 2026-06-12**:

- [x] **Unicidad ℕ** (`Full/PrimeFactor.lean`): `euclid` (lema de Euclides vía `Nat.Coprime.dvd_of_dvd_mul_left` de core), `euclid_list`, `prime_dvd_prime_eq`, `natProd_erase`, `count_unique` (misma multiplicidad de cada primo) y **`factorization_perm_unique`** (dos factorizaciones del mismo `n` son permutaciones). Todo ℕ puro, sin Mathlib.
- [x] **TFA completo** (`Full/Factorization.lean`): **`tfa_numeral`** — `∀ n≥1, ∃ ps, (∀p∈ps, IsPrimeNat p) ∧ (⊢ prod_pairs (toTerm ps) =eq numeral n) ∧ (∀ qs factorización de n → ps.Perm qs)`. Existencia object + unicidad ℕ. La unicidad usa hipótesis meta `natProd qs = n` (evita reflejar igualdad de numerales, que necesitaría `Con(axioms)`).

> **`ax_p_tfa` de Block8** (membership object + testigo único object) queda como la forma **idealizada**: no admite discharge constructivo por el Muro 1 (object→meta). `tfa_numeral` es la realización constructiva equivalente para todos los usos reales (numerales/códigos).

### 4.2. Restantes tras TFA

- [x] **Nivel D Gödel — Gödel I (mitad esencial)** (`Meta/Incompleteness.lean`, 2026-06-12): `goedel_first_unprovable` (`Consistent → ⊬ G`), `goedel_first_true`, `incompleteness`. Derivado de D1 + diagonalización del Nivel C.
- [x] **Gödel II** (`goedel_second`, 2026-06-12): `Consistent → ⊬ Con` (`Con := ¬Prov(⌜⊥⌝)`). **Postulando D2/D3**; lema crucial `con_imp_goedelSentence : ⊢ Con⇒G`.
- [x] **Gödel I completo** (`goedel_first_unrefutable`, `goedel_first_undecidable`, 2026-06-13): `⊬ ¬G`, luego `⊬ G ∧ ⊬ ¬G` (G indecidible). Vía **`dne`** (DNE clásica añadida a `FOL/MetaRules.lean`) + reflexión. El obstáculo era el intuicionismo del FOL, no ω-consistencia; Rosser habría sido peor.
- [ ] **Cadena de embeddings**: `FOL⁼ ⊂ Minimal ⊂ Full`.
- [x] **[Deuda menor]** Refactor meta-axiomas FOL → ✅ HECHO 2026-06-12 (`FOL/MetaRules.lean`).

---

## Eje 4.3 — Gödel Nivel D REAL: aritmetización de D1–D3 (EN CURSO, 2026-06-13)

**Motivación**: D1/D2/D3 estaban **postulados** (meta-axiomas opacos). El `provFormula_repr` bicondicional era además imposible por Tarski (rastrea verdad en ℕ). Decisión (Opción A): **aritmetización total** — `demFormula` será una `Formula` Σ₁ concreta con `Dem d x → ⊢ᴴ demFormula[⌜d⌝,⌜x⌝]` demostrada. Plan completo y descomposición en [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

**Reencuadre clave**: el `axioms ⊢` del proyecto usa la **ω-regla** `gen` (premisas infinitas) → no es r.e. → no aritmetizable. Por eso Gödel se aplica a un **cálculo de Hilbert finitario `⊢ᴴ` nuevo, en paralelo**; el ω-sistema queda intacto.

- [x] **Fase 0** (`Meta/Hilbert.lean`): `Prf₀` (Hilbert intuicionista) + `Prf` (clásico). Puentes `prf0_to_derives`/`prf_to_derives : Prf φ → axioms ⊢ φ` usando **solo constructores de `Derives`**; `dne` aparece en **un único punto** (esquema P3), verificado por `#print axioms` (diferencia exacta entre ambos puentes = `{dne}`). `consistentH_of_omega`: la consistencia se hereda.
- [x] **Fase 1** (`Meta/HilbertSeq.lean`): `Rule` (líneas anotadas, evita invertir la sustitución) + verificador decidible `checkProof` + `Derivation`. **Solidez** `derivation_to_prf` + **completitud** `prf_to_derivation` (con `checkAux_append`/`checkAux_shift` para combinar subpruebas) ⟹ `prf_iff_derivation : Prf φ ↔ ∃ rs, Derivation rs φ`. Coding `ruleCode`/`rulesCode` → `Term`, `Dem` **concreto**, `dem_tracks : (∃d, Dem d ⌜φ⌝) ↔ Prf φ` (reemplaza `Dem`/`dem_iff_provable` postulados; solo axiomas estándar de Lean).
- [x] **Fase 2.1** (`Meta/CodeArith.lean`): `numeral_bridge` (Meta.Godel.numeral = Full.numeral) + `gnum_ne`/`gnum_lt`/`gnum_add`/`gnum_mul`/`gnum_refl` (aritmética de códigos re-expuesta de `Full.Numerals`).
- [x] **Fase 2.2 nivel término** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): funciones object `varc`/`funcc`/`substtc`/`substtsc` y sus ecuaciones recursivas **integradas en `Minimal.axioms`** (re-derivadas como teoremas vía `ax`+`spec`; `forall_4` requirió el lema de triple lift `substTerm_liftLiftLift`). `substTerm_arith`/`substTerms_arith` (cómputo `⊢ substtc ⌜v⌝ ⌜s⌝ ⌜t⌝ = ⌜substTerm v s t⌝`) por inducción meta mutua. **`#print axioms substTerm_arith` = solo axiomas estándar de Lean** (0 postulados nuevos).
- [x] **Fase 2.2 nivel fórmula** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): `liftc`/`liftsc` (lift aritmetizado) + `substfc` con los 8 constructores de código de fórmula (`botc`..`exc`); 13 ecuaciones recursivas más en `Minimal.axioms` (re-derivadas como teoremas). `liftTerm_arith` + `substFormula_arith` (binders ∀/∃ con `succ`-nivel y `liftc zero`-substituyendo, vía congruencias de `cons` y `congr_substfc_arg2`). `#print axioms substFormula_arith` = solo Lean estándar.
- [x] **Fase 2.3** (`Meta/StepArith.lean`): reconocimiento de instancias de axioma — `q1/q2/leibniz_concl_code` (esquemas de sustitución vía `substFormula_arith`); los proposicionales son definicionales.
- [x] **Fase 2.4** (`Meta/CheckArith.lean` + `Minimal/Axioms`): `numeralM`, extractores `carc`/`cdrc`; **`validProofFn`** + `forall_5` + 17 ecuaciones del verificador (params directos; MP/Gen condicionados por `In`) + 17 step lemmas `vpf_*` + lema 4-lift `substTerm_liftLiftLiftLift`; **`provFormulaC`** (demostrabilidad Σ₁) + `provCodeC`. **Pendiente regla `thy`**: nudo de capas (`formCode`/Meta vs `Minimal.axioms`); plan `formCode` a nivel Minimal vía `numeralM`.
- [x] **Fase 2.4-thy + soundness de `thy`** (`Minimal/Axioms` + `Meta/CheckArith`): verificador completo (18 reglas). `thy` recorre `coreAxioms` y es condicional a `In c axiomsCodeT` (`provCodeC` fiel). `formCodeM` + clausura De Bruijn estructural (numerales gigantes de símbolos Unicode).
- [x] **Fase 2.5** (`Meta/Representability.lean`): representabilidad positiva `repr_pos : Prf φ → axioms ⊢ provCodeC φ` (encoder object a medida `proofCode`/`lineCode` + inducción de seguimiento `vpf_run`). `#print axioms` = estándar.
- [x] **Fase 3 (D1)** (`Meta/Necessitation.lean`): `d1`/`necessitation` (= `repr_pos`) + Gödel I modular `goedel_first_unprovable_real`.
- [x] **Lema diagonal real** (`Meta/Diagonal.lean`): `tcFn`/`tc_arith` + `diag_arith` + **`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`** + **`goedel_first_real : ConsistentOmega → ¬ Prf G`** (sin postulados gödelianos).
- [x] **Fase 2.6 cimiento** (`Meta/CodeDistinct.lean`): aritmética negativa de códigos `formCode_ne` + familia.
- [x] **Fase 5 — regla `ind` INTEGRADA** (`Meta/Induction.lean` + stack): `ind_concl_code` + `Prf.ind`/`Rule.ind`/**`ax_vpf_ind`** sólida + `vpf_ind` + caso ind de `vpf_run`. **Verificador: 19 reglas.** `provCodeC` rastrea **IΣ₁**. `repr_pos`/`vpf_ind` `#print axioms` = estándar; `goedel_first_real` cita además `Full.ax_induction` (honesto: Prf modela IΣ₁).
- **D2/D3 → Gödel II real — rediseño honesto del verificador (EN CURSO, 2026-06-21)**.
  Hallazgo: `validProofFn` (opaca/condicional) sirve para la dirección positiva pero
  **bloquea** la inducción sobre testigos de prueba arbitrarios que D2/D3 exigen. Nuevo
  verificador estructural `runFn` (líneas `cons ⌜concl⌝ justif`, reduce vía `carc`).
  - [x] **R1** (`Meta/ProofChain.lean`): `runFn` + ecuaciones + **compositividad**
    `runFn c (p++s) =eq runFn (runFn c p) s` (inducción con acumulador ∀-object).
  - [x] **R2**: predicados `allIn`/`lineWF`/`premsOf`/`lineOk`/`chainOk` + ecuaciones +
    **monotonía** `In_mono`/`allIn_mono`/`lineOk_mono` (para línea arbitraria).
  - [x] **R3**: `concat_nil_right`, `In_mono_right`, **debilitamiento** `runFn c p =eq c++runFn nil p`,
    **composición** `chainOk c (p++s) ⇔ chainOk c p ∧ chainOk (runFn c p) s`, `chainOk_mono`.
  - [x] **R4 — D1 = `repr_pos'`** (`Meta/Representability2.lean`): `Prf φ → ⊢ provCodeC' φ`.
    Encoder `proofCode'` + `runFn_track` (rule-agnóstico) + `chainOk_track` (19-casos) +
    validez de las 19 reglas (`lineWF`/`premsOf`, fieles). `#print axioms` = solo estándar.
  - [x] **R5 — D2** (`Meta/DerivCond.lean`): `⊢ provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B)`
    (`r = p++q++[mp]`, vía `chainOk_concat`/`chainOk_mono`/`runFn_concat`/`runFn_weaken`).
  - [x] **Gödel II — núcleo lógico** (`Meta/GodelTwo.lean`): `con_imp_godel'`/`goedel_second'`
    vía **D2 real** + **D3 postulado** (`axiom d3`) + hipótesis explícitas honestas
    (`fp_bwd` punto fijo, `nec1` necesitación, `hgi` ⊬G ω). Mejora sobre legacy (postulaba D2 y D3).
  - **Camino a Gödel II 100% real** (descubierto al analizar D3):
    - [x] **Refactor `Prf.thy → axioms`** ✅ (2026-06-21): `Prf₀.thy` recorre todo `axioms`
      (core++coding); la teoría razona sobre su propia maquinaria (como IΣ₁). Ancla gigante
      `ax_axiomsCodeT` ELIMINADA, `axiomsCodeT` opaco, nuevo meta-axioma
      `ax_inAxC (a ∈ axioms) : ⊢ In (formCodeM a) axiomsCodeT` (sin término gigante ni
      auto-referencia; sonda validó el lift en un paso). Fixes thy en
      `Hilbert`/`HilbertSeq`/`Representability`/`Representability2`. Build 55 jobs.
    - [x] **Punto fijo real para `provCodeC'`** ✅ (`Meta/DiagonalTwo.lean`): `godelC'`/`godelC'_fixedpoint`
      (`⊢ G' ⇔ ¬provCodeC' G'`, sin postulados) + `goedel_first_real'` (Gödel I real estructural).
    - **HALLAZGO de niveles (2026-06-22)**: Gödel II requiere RE-NIVELAR la cadena HBL a `Prf`
      (no ⊢): `provCodeC'` rastrea la demostrabilidad finitaria `Prf`; `¬⊢G'`/`¬⊢Con'` son FALSOS
      (el ω-sistema es sólido y los prueba). Gödel II correcto = `ConsistentH → ¬ Prf Con'`, vía
      `con_imp` a nivel **Prf**, que necesita:
      - [ ] `repr_pos'_prf : Prf φ → Prf (provCodeC' φ)` (re-derivar `repr_pos'`/`chainOk_track` en `Prf`;
        el refactor `Prf.thy → axioms` lo habilitó).
      - [ ] `d2_prf`, punto fijo en `Prf` (`Prf (G' ⇔ ¬provCodeC' G')`).
      - [ ] `con_imp_prf : Prf (Con' ⇒ G')` → `goedel_second_prf : ConsistentH → ¬ Prf Con'` (D3 postulado a nivel Prf).
      - [ ] **D3 real** (Σ₁-completitud provable, núcleo).
    - [ ] **R6 — D3 real** (Σ₁-completitud provable): `⊢ ∀q. (R(q) ⇒ Prov(⌜R(q)⌝))` por inducción
      OBJECT sobre `q` (internaliza `repr_pos'`/`chainOk_track`) + ∃-intro interno + ex_elim.
      La pieza más grande del proyecto. (NOTA: `d3_of_sigma1` en `Reflection.lean` fue descomposición
      errónea —ex_elim sobre witness opaco—; superada por este plan.)
  - [ ] **R7**: replicar `con_imp_goedelSentence`/`goedel_second` con `provCodeC'`/`godelC` → **Gödel II real** (`⊬ Con`).
- [ ] **⊬¬G real** (reflexión / ω-soundness) + representabilidad **negativa** plena.

> **Integración ✅ (2026-06-13)**: las ecuaciones recursivas de las funciones de coding están ahora en `Minimal.axioms` (extensión definicional conservadora), por lo que `⊢ᴴ` también las tiene (vía `Prf.thy`). Ya no hay `axiom` local en `SubstArith`.

---

## Eje 5 — Más allá (muy largo plazo)

Sobre la base consolidada `Full/`:

1. **Teorías de conjuntos constructivas** (CZF de Aczel) usando listas y funciones como cimiento.
2. **Cardinalidad y números enteros/racionales**.
3. **Análisis constructivo elemental** (sucesiones, límites).

---

## Problemas técnicos recurrentes (referencia)

Heredados del trabajo en `Minimal/`. Útiles para `Intermediate/` y `Full/`.

| Problema | Síntoma | Solución |
| --- | --- | --- |
| `Block2.Γ` vs `Block4_C5.Γ` | `apply` falla con unificación | Usar `exact` (igualdad definitional) |
| `eq_trans` no-estándar | cadena `a=b, b=c` falla | Usar `FOL.derive_eq_trans` |
| `substTerm` bajo binder no reducido | `simp` deja `substTerm 0 t s` | añadir `FOL.substTerm_liftTerm`, `FOL.substTerm_liftLift` al simp set |
| `and_elim_*` ambiguo | error de elaboración | usar `Axioms.and_elim_left/right` |
| `Γ ⊢ t ≤ t'` parsing | `(Γ ⊢ t) ≤ t'` | paréntesis: `Γ ⊢ (t ≤ t')` |
| Implicación bajo `=eq` | `⇒` parsea más fuerte que `=eq` | paréntesis: `(A ⇒ (B =eq C))` |
| Triple `spec` (`forall_3`) | doble lift no se cancela | añadir `← lift_01_eq_00` o `FOL.substTerm_liftLift` |
| Caché de `lake build` | "Replayed" oculta cambios sin compilar | `lake clean && lake build` cuando hay dudas |

---

**Author**: Julián Calderón Almendros

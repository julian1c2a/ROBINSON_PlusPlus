# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-06-12 — **TFA COMPLETO CERRADO** (existencia object ∧ unicidad ℕ, sobre numerales, autocontenido sin Mathlib/Peano): `tfa_numeral` (`Full/Factorization.lean`). Unicidad ℕ vía Euclides (`Full/PrimeFactor.lean`: `euclid`, `factorization_perm_unique`). Capa de teoría de números completa sobre la representabilidad: `Primality` (`isPrime_numeral`), `Division` (`division_numeral`), `PrimeFactor` (ℕ pura: factor primo, factorización, **Euclides + unicidad**), `Factorization` (`tfa_exists_numeral`, `tfa_numeral`). Cimientos: `Numerals` (homomorfismo `+,·,^,<,≠`), `Bounded` (`le_numeral_split`), `Divisibility` (`numeral_dvd`, `divisor_le`), F1 `StrongInduction`. Reencuadre **numerales + representabilidad** (Gödel-aware) disuelve los Muros 1/2. Fragmento aritmético + listas de Minimal en Full: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅. Sistema con **34 axiomas matemáticos** en Minimal + meta-axiomas, **24 módulos** (Minimal/ 11 + Meta×2 + Full ×11), 0 sorrys, 0 warnings (37 jobs). **Próximo**: Gödel Nivel D (Meta/Incompleteness) sobre esta base; o consolidar.

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

- [ ] **Nivel D Gödel** (`Meta/Incompleteness.lean`): desbloqueado por TFA. Gödel I + II internos.
- [ ] **Cadena de embeddings**: `FOL⁼ ⊂ Minimal ⊂ Full`.

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

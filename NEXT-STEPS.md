# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-06-06 — Block8 **+10 teoremas** (álgebra de `Dvd` + corolarios TFA); **`Meta/Godel.lean` creado** (Nivel B Gödelización: G, ⌜·⌝, Teo G1). Linter `unusedSimpArgs false` global; warning `FOL/Eq.lean:130` cerrado (commit FOL `9888c58`). Sistema con **34 axiomas matemáticos**, **12 módulos**, 0 sorrys reales, 0 warnings (incl. FOL externo).

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

## Eje 2 — Módulo `Meta/` (Nivel B ✅ 2026-06-06; próximo Nivel C)

**Objetivo**: implementar Fases 18-19 del spec (`TuplasFuncionesYListas.md §BLOQUE VIII`) — Gödelización y autorreferencia. Diagnóstico completo y arquitectura en [GODEL-STATUS.md](GODEL-STATUS.md).

**Decisión 2026-06-06**: `Meta/` arranca **al cerrar `Minimal/`**, no después de `Intermediate/`. Justificación: los niveles B-C (codificación + Dem) no requieren inducción, sólo meta-codificación. El nivel D (teoremas de incompletitud demostrados internamente) sí requiere `Intermediate/` o `Full/`.

### 2.1. Nivel B — `Meta/Godel.lean` (primer hito) ✅ COMPLETADO 2026-06-06

- [x] **Asignación de Gödel** `G : símbolos → ℕ` (Def 27 spec). `inductive Sym` (12 símbolos) + `gNat` (tabla ∀→2, ∃→3, =→10, …, m→111) + `gNat_injective`; `numeral`+`numeral_injective`; `G := numeral ∘ gNat` + `G_injective`.
- [x] **Corner brackets** `⌜·⌝ : List Sym → Term` (Def 28): `encode [] = nil`, `encode (s::S) = cons (G s) (encode S)`; notación scoped `⌜·⌝`.
- [x] **Teorema G1** (inyectividad): `encode_injective` (meta-inyectividad consistency-free, vía `injection` + inducción estructural) + versiones object-level `encode_cons_inj` (usa `cons_inj`, Block6) y `encode_cons_neq_nil`. Ver `GODEL-STATUS.md` §2 sobre la elección meta vs objeto.

**No introduce nuevos axiomas matemáticos** sobre `Minimal/`. Aprovecha `pow` + TFA para codificación primorial alternativa (ver [GODEL-STATUS.md](GODEL-STATUS.md) §3.1).

### 2.2. Nivel C — `Meta/Provability.lean` (segundo hito)

- [ ] Predicado `IsFormula(x)`: `x` es el código de Gödel de una fórmula bien formada.
- [ ] Predicado `Dem(p, φ)`: `p` es el código de una demostración formal de `φ` en `Minimal`.
- [ ] **Lema del punto fijo** (diagonalización): para todo `φ(x)` existe `ψ` tal que `Minimal ⊢ ψ ⇔ φ(⌜ψ⌝)`.
- [ ] **Sentencia de Gödel** `G_Min := el punto fijo de "¬Dem(p, x)"`.

Algunas propiedades meta-teoréticas de `Dem` (cierre por modus ponens, etc.) pueden postularse como **meta-axiomas** hasta tener `Intermediate/` con inducción para demostrarlas.

### 2.3. Nivel D — `Meta/Incompleteness.lean` (requiere `Intermediate/` o `Full/`)

- [ ] **Gödel I**: `Minimal ⊬ G_Min` y `Minimal ⊬ ¬G_Min` (asumiendo consistencia).
- [ ] **Gödel II**: `Minimal ⊬ Con(Minimal)`.

Esto se queda para más adelante; la formalización requiere inducción sobre la complejidad sintáctica de las demostraciones.

---

## Eje 3 — Sistema `Intermediate/` (medio plazo, paralelo a `Meta/`)

**Objetivo (PLANNING §6.2)**: Sistema reducido (~22 axiomas) + **esquema de inducción restringido** a un conjunto finito de fórmulas (Ax-Ind sobre Φ con |Φ|=13). Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` se vuelven **teoremas**. Reducción esperada: 34 axiomas → ~22 axiomas + Ax-Ind(Φ) + Ax-P.

### 2.1. Diseño previo

- [ ] **Decidir la formalización del esquema de inducción restringido** en Lean. Opciones:
  - (a) Familia indexada de axiomas `induction_phi : Formula` por cada fórmula `φ` del conjunto finito.
  - (b) Un único esquema parametrizado por una etiqueta `Fin n` enumerando los `φ`s.
  - (c) Función Lean a nivel meta `induction (φ : Formula) : Γ ⊢ ... ⇒ ...` con guard sobre `φ`.

### 2.2. Estructura mínima

- [ ] Crear `Intermediate/Axioms.lean` (13 axiomas + esquema de inducción restringido).
- [ ] `Intermediate/Theorems/` con un módulo por cada axioma algebraico de `Minimal` que aquí pasa a ser teorema:
  - `add_comm` (ax6), `add_assoc` (ax7), `mul_comm` (ax10), `mul_assoc` (ax11), `mul_distrib` (ax12), `lt_irrefl` (ax18), `lt_trichotomy` (ax19), `sqrt_le` (ax14), `lt_succ_sqrt` (ax15).
- [ ] **Embedding `Minimal ⊂ Intermediate`**: módulo que demuestra que toda derivación en `Minimal.axioms` se transporta a `Intermediate.axioms`.

### 2.3. Embedding de `Minimal/` en `Intermediate/`

- [ ] Demostrar que cada axioma de `Minimal/` es teorema en `Intermediate/`.
- [ ] Establecer formalmente `Minimal.axioms ⊆ Intermediate.theorems`.

---

## Eje 4 — Sistema `Full/` (largo plazo)

**Objetivo (PLANNING §6.3)**: Axiomas de Peano puros + **esquema de inducción general** sobre todas las fórmulas del lenguaje. Todos los axiomas postulados en `Minimal/` (ax21, ax24, ax_C3, ax_L3) y el meta-axioma `ax_p_tfa` (TFA) se vuelven teoremas. Habilita el **Nivel D** del frente Gödel: Gödel I y II demostrados internamente.

### 3.1. Diseño

- [ ] **Esquema de inducción universal**: meta-axioma `induction (φ : Formula) : (φ(0) ⇒ (∀n, φ(n) ⇒ φ(σn)) ⇒ ∀n, φ(n))`.
- [ ] Mínimo de axiomas de Peano (los 6 clásicos: σ inyectivo, σ ≠ 0, + y · por recursión, inducción).

### 3.2. Plan

- [ ] Crear `Full/Axioms.lean`.
- [ ] Re-demostrar como teoremas: `mod2_range`, `mod2_of_even`, `add_left_cancel`, `mul_two_cancel`, `concat_assoc`, `in_concat_iff`, y todos los algebraicos de `Intermediate/`.
- [ ] **Cadena completa de embeddings**: `FOL⁼ ⊂ Minimal ⊂ Intermediate ⊂ Full`.

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

# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-06-03 — `ax27_add_left_cancel` ELIMINADO (derivable en PA⁻); sistema con **30 axiomas matemáticos** y 0 sorrys reales.

---

## Situación actual

Build: ✅ `lake build` exit 0. **0 sorrys reales** en los 9 módulos. Los 5 `axiom` de `Axioms.lean` (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) son meta-reglas de FOL, no `:= sorry`.

El sistema `Minimal/` cumple su objetivo declarado en [PLANNING.md](PLANNING.md): **30 axiomas matemáticos sin esquema de inducción son suficientes para construir la función de Cantor, las tuplas con proyecciones, y las listas con concatenación y pertenencia**.

---

## Eje 1 — Consolidar `Minimal/` (corto plazo)

### 1.1. Bloque VII — Funciones discretas (nuevo módulo)

Pendiente desde [PLANNING.md §5 Fase 3](PLANNING.md#fase-3-sistema-minimal--listas-y-funciones).

- [ ] **Crear `Minimal/Theorems/Block7.lean`**.
  - [ ] Definir el predicado `IsFunction (R : Term) : Formula` sobre relaciones funcionales (gráfica + univaluación).
  - [ ] Definir la evaluación `F(x)` vía proyección de la única pareja con primera componente `x`.
  - [ ] Demostrar el isomorfismo con relaciones funcionales (Teo F3 de `TuplasFuncionesYListas.md`).
- **Dependencias**: Block5 (pares ↔ N) + Block6 (listas) — ambos completos.
- **Bloqueos previstos**: ninguno mayor; es trabajo de codificación con la maquinaria ya disponible.

### 1.2. Auditar los axiomas "no-induction-bound"

Revisar si alguno de los axiomas matemáticos actuales es realmente **demostrable** en `Minimal/` sin inducción y se postula por error/comodidad. Candidatos a auditar (orden de probabilidad creciente de ser demostrables sin inducción):

| Axioma | Estado | Comentario |
| --- | --- | --- |
| `ax21_mod2_range` | postulado | requiere inducción sobre `n` |
| ~~`ax22_cantor_proj_exists`~~ | **ELIMINADO 2026-06-02** | proj1/proj2 ahora defs concretas; `proj_is_cantor` lo demuestra |
| ~~`ax23_cantor_proj_uniq`~~ | **ELIMINADO 2026-06-02** | nunca usado; `cantor_uniqueness` ya probado |
| `ax24_mod2_of_even` | postulado | requiere inducción sobre `k` (auditado 2026-06-03: irreducible) |
| ~~`ax27_add_left_cancel`~~ | **ELIMINADO 2026-06-03** | derivable en PA⁻ vía tricotomía + monotonía + ax18 |
| ~~`ax28_mul_two_cancel`~~ | **ELIMINADO 2026-06-02** | reprobado como `teo_2_11` sin inducción |
| `ax_C3_concat_assoc` | postulado | requiere inducción sobre `L` |
| `ax_L3_in_concat` | postulado | requiere inducción sobre `L` |

**Próxima acción**: arrancar `Block7.lean` (Funciones, `IsFunction`, Teo F3). Los axiomas que quedan (`ax21`, `ax24`, `ax_C3`, `ax_L3`) son irreducibles sin inducción — todos requieren `n + m ≥ n ∀m` o equivalente. Ver [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) para el análisis completo.

### 1.3. Limpieza de simp args no usados

Aunque el linter `unusedSimpArgs` está desactivado, hay ~46 args genuinamente no usados en simp calls que sobreviven a la sesión. Pasada de limpieza para reducir ruido:

- [ ] Reactivar el linter temporalmente (`set_option linter.unusedSimpArgs true`).
- [ ] Limpiar warnings reales en cada módulo.
- [ ] Volver a desactivar el linter (sigue siendo poco fiable bajo binders existenciales).

---

## Eje 2 — Sistema `Intermediate/` (medio plazo)

**Objetivo (PLANNING §3.2)**: Sistema reducido (~13 axiomas) + **esquema de inducción restringido** a un conjunto finito de fórmulas. Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` se vuelven **teoremas**.

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

## Eje 3 — Sistema `Full/` (largo plazo)

**Objetivo (PLANNING §3.2)**: Axiomas de Peano puros + **esquema de inducción general** sobre todas las fórmulas del lenguaje. Todos los axiomas postulados en `Minimal/` (ax21, ax24, ax27, ax28, ax_C3, ax_L3, etc.) se vuelven teoremas.

### 3.1. Diseño

- [ ] **Esquema de inducción universal**: meta-axioma `induction (φ : Formula) : (φ(0) ⇒ (∀n, φ(n) ⇒ φ(σn)) ⇒ ∀n, φ(n))`.
- [ ] Mínimo de axiomas de Peano (los 6 clásicos: σ inyectivo, σ ≠ 0, + y · por recursión, inducción).

### 3.2. Plan

- [ ] Crear `Full/Axioms.lean`.
- [ ] Re-demostrar como teoremas: `mod2_range`, `mod2_of_even`, `add_left_cancel`, `mul_two_cancel`, `concat_assoc`, `in_concat_iff`, y todos los algebraicos de `Intermediate/`.
- [ ] **Cadena completa de embeddings**: `FOL⁼ ⊂ Minimal ⊂ Intermediate ⊂ Full`.

---

## Eje 4 — Más allá (muy largo plazo)

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

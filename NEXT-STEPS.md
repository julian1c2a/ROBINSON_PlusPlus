# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-05-22

---

## Situación actual

Build: ✅ (exit code 0). Sorry activos: **28** (en 5 módulos).

Los bloques base (Block1–Block4) están completamente probados. El trabajo restante se concentra en Block4_C5 (Lema C5) y sus dependientes.

---

## Prioridades

### 1. Block4_C5 — Completar Lema C5 (8 sorrys)

**Objetivo**: `∀c, ∃!w, w(w+1) ≤ 2c < (w+1)(w+2)`

El módulo compila. Los sorrys son matemáticamente no triviales; cada uno requiere trabajo de elaboración de tipos, no solo matemáticas.

#### 1a. `h_sq_2w1_le_sq_s`: `(2w+1)² ≤ s²`

**Estrategia**: Demostrar `2w+1 ≤ s` y luego usar `sq_le_mono`.

**Bloqueo conocido**: Dentro del bloque `ex_elim h_s_is_succ`, la hipótesis `h_s_eq_spw` tiene tipo con `substTerm 0 p_witness s` no reducido. Esto ocurre porque `s = sqrt(...)` es una variable libre bajo el ligador existencial: dentro de `Formula.ex`, `s` aparece como `liftTerm 0 s`, pero simp no reduce `substTerm 0 p_witness (liftTerm 0 s)` a `s` cuando `s` es una expresión no-trivial.

**Solución propuesta**: Añadir `have h_simp : substTerm 0 p_witness (liftTerm 0 s) = s := FOL.substTerm_liftTerm ...` explícitamente y reescribir con `rw` antes de usar la hipótesis. Ver REFERENCE.md §3.11.7 (patrón hS).

#### 1b. `h_existence_part2`: `2c < (w+1)(w+2)`

**Estrategia**: `w = div2(pred s)`, `s = sqrt(8c+1)`, `s² ≤ 8c+1 < (s+1)²`. Manipular para obtener `2c < (w+1)(w+2)`.

**Dependencias**: `sqrt_sq_le`, cota superior de `sqrt`.

#### 1c. `h_uniqueness`: `w'(w'+1) ≤ 2c < (w'+1)(w'+2) → w' = w`

**Bloqueo conocido**: `Block2.Γ` vs `Block4_C5.Γ` en `lt_le_trans`/`le_lt_trans` y `and_elim_*`.

**Solución**: Usar `exact` para teoremas cross-módulo (Block2). Añadir `simp [mul, substTerm, liftTerm]` después de `intro h_w'_bounds` para normalizar términos antes de `and_elim_*`. O re-probar los lemas localmente con `exact`.

#### 1d. Scaffolding `∃!w`

Combinar `h_existence` y `h_uniqueness` con `ex_intro w`. Bloqueo previo: `substTerm 0 w c` no se reduce para `c` opaco — necesita `simp [substTerm, liftTerm, ...]` más agresivo o `rw` explícito.

---

### 2. Block4_C6_C7 — Cantor surjectivity/uniqueness (3 sorrys)

**Dependencia directa**: Requiere Block4_C5 completo.

**Bloqueos conocidos**: Aritmética de restas en FOL (sin resta primitiva; simular con existenciales y sumas).

---

### 3. Block5 y Block6 (12 sorrys combinados)

**Dependencia**: Requieren Block4_C5 + Block4_C6_C7. Posponer hasta entonces.

---

## Problemas técnicos recurrentes

| Problema | Síntoma | Solución |
| -------- | ------- | -------- |
| `Block2.Γ` vs `Block4_C5.Γ` | `apply` falla con unificación | Usar `exact` (igualdad definitional) |
| `eq_trans` no-estándar | cadena `a=b, b=c` falla | Usar `FOL.derive_eq_trans` |
| `substTerm` no reducido | `simp` deja `substTerm 0 t s` | `rw [FOL.substTerm_liftTerm]` explícito |
| `and_elim_*` ambiguo | Error de elaboración | Usar `Axioms.and_elim_left/right` |
| `Γ ⊢ t ≤ t'` parsing | `(Γ ⊢ t) ≤ t'` | Paréntesis: `Γ ⊢ (t ≤ t')` |
| `Formula.forall_` | Constructor inexistente | Usar `Formula.forall` |
| `neg_intro` | Táctico inexistente | Usar `Axioms.imp_intro` |

---

## Orden de trabajo recomendado

1. `Block4_C5` — `h_uniqueness` (lógica ya escrita, solo problemas de tipos)
2. `Block4_C5` — `h_sq_2w1_le_sq_s` (patrón liftTerm/substTerm)
3. `Block4_C5` — `h_existence_part2` (aritmética de cotas)
4. `Block4_C5` — scaffolding `∃!w`
5. `Block4_C6_C7` — surjectivity/uniqueness
6. `Block5`, `Block6`

---

**Author**: Julián Calderón Almendros

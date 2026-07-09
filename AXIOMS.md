# Registro central de axiomas — ROBINSON_PlusPlus

**Last updated:** 2026-07-09 — **F7a completada: 14 → 7 `axiom` de Lean.**
**Author:** Julián Calderón Almendros

Registro autoritativo de **todas** las declaraciones `axiom` de Lean que sostienen
el proyecto: qué son, por qué son legítimas (o pendientes), y en qué módulo viven.

> **Por qué NO están todas en un solo módulo.** El instinto de «todos los axiomas
> en un sitio» choca con la estratificación deliberada del proyecto. Los axiomas
> pertenecen a **capas conceptualmente distintas** y su domicilio es una decisión
> de diseño, no descuido:
>
> - **Minimal vs Full es una frontera.** `Minimal/` está *definido* como el sistema
>   débil SIN inducción general (≈ Robinson Q). El esquema de inducción vive en
>   `Full/` porque es justo lo que Full **añade**; moverlo a Minimal arrastraría
>   toda la maquinaria de Full y borraría la frontera.
> - **Teoría objeto vs metateoría.** Los esquemas aritméticos son de la teoría
>   objeto; `d3` es metamatemático (sobre demostrabilidad). Son niveles distintos.
> - **Dos cálculos.** `Derives` (`⊢`) y `Prf` necesitan cada uno su ancla de
>   codificación (`ax_inAxC` / `prf_inAxC`); no son un duplicado a fusionar.
>
> Este fichero es el «sitio único» **documental**: la fuente de verdad sobre el
> inventario, aunque el código mantenga cada axioma en su capa correcta.

---

## 1 · Axiomas de Lean en ROBINSON_PlusPlus (7)

| # | Axioma | Módulo | Familia | Naturaleza |
|---|--------|--------|---------|------------|
| 1 | `ax_induction` | `Full/Induction.lean` | Esquema de inducción | Axioma legítimo de la teoría objeto (IΣ₁/PA): `axioms ⊢ inductionFormula φ` |
| 2 | `ax_list_induction` | `Full/Lists.lean` | Esquema de inducción | Inducción estructural sobre listas del objeto |
| 3 | `ax_mod2_alternation` | `Full/Mod2.lean` | Esquema de inducción | `∀n. mod2(σn)+mod2(n)=1`; con él se derivan ax21/ax24 como **teoremas** |
| 4 | `ax_p_tfa` | `Minimal/Theorems/Block8.lean` | Teoría objeto | Teorema Fundamental de la Aritmética (teorema en Full, postulado en Minimal) |
| 5 | `ax_inAxC` | `Minimal/Axioms.lean` | Ancla de codificación | `a ∈ axioms → axioms ⊢ In (formCodeM a) axiomsCodeT` (extensión conservadora, cálculo `⊢`) |
| 6 | `prf_inAxC` | `Meta/Representability2Prf.lean` | Ancla de codificación | Análogo de (5) para el cálculo finitario `Prf` |
| 7 | `d3` | `Meta/GodelTwo.lean` | Postulado gödeliano | **Única pieza pendiente**: condición D3 de Hilbert-Bernays-Löb para `provCodeC'`. En construcción por el plan 12‑A |

### Detalle por familia

- **Esquemas de inducción (1–3, en `Full/`).** Son *la* inducción que el sistema
  `Full` añade sobre el débil `Minimal`. No pueden vivir en `Minimal/` sin destruir
  la frontera de diseño (Minimal = sin inducción general). `ax_mod2_alternation`
  es un axioma-puente que permite derivar `ax21`/`ax24` como teoremas.
- **Teoría objeto (4).** `ax_p_tfa` es el TFA; teorema en presencia de inducción,
  enunciado como axioma en la capa `Minimal` (que carece de ella).
- **Anclas de codificación (5–6).** Extensión **conservadora**: afirman que el
  código de un axioma pertenece a la lista opaca `axiomsCodeT`. Una por cálculo
  (`⊢` y `Prf`). Sustituyen a un ancla gigante anterior (`ax_axiomsCodeT`) por un
  contenido positivo sin término explícito.
- **Postulado gödeliano vivo (7).** `d3` es la única condición de derivabilidad
  aún postulada. Su prueba real (Σ₁-completitud provable del verificador) es el
  objetivo del plan **12‑A** (`GODEL-D3-TRACKED-DESIGN.md` §12–§14); fases 1a/1b/2
  ✅ completas. Cuando `d3` pase a teorema, **F7b** lo retirará (6 axiomas).

---

## 2 · Meta-reglas ω (6) — en la librería `FOL`, no en RPP

Las reglas de deducción de la lógica ω viven en **`FOL/MetaRules.lean`** (proyecto
`FOL`, sibling) y RPP las **re-exporta** desde `Minimal/Axioms.lean`. NO cuentan
entre los 7 `axiom` de RPP.

| Regla | Rol |
|-------|-----|
| `imp_intro` | Introducción de `⇒` (deducción) |
| `gen` | Generalización ω (`∀n. Γ ⊢ A[n] → Γ ⊢ ∀A`) |
| `raa` | Reducción al absurdo |
| `dne` | Eliminación de doble negación (clásica) |
| `or_elim` | Eliminación de `∨` |
| `ex_elim` | Eliminación de `∃` |

Son **reglas del cálculo**, no postulados matemáticos falsables (ADR-008).

---

## 3 · Capa Gödel LEGACY — RETIRADA en F7a (2026-07-09)

Auditado con `#print axioms`, la cadena **real** (`goedel_first_real'`, `d2_prf`,
`goedel_second'`) **no citaba** ninguno de estos símbolos; solo los usaba la capa
Gödel vieja (Gödel I/II vía D2/D3 postulados). Retirados:

| Símbolo | Estaba en | Reemplazado por (real) |
|---------|-----------|------------------------|
| `Dem`, `dem_iff_provable` | `Meta/Provability.lean` | `HilbertSeq.Dem`/`ProvableH` (concreto) |
| `provFormula`, `provFormula_repr` | `Meta/Provability.lean` | `provCodeC'` + D1 `repr_pos'_prf` |
| `diagonal_lemma` | `Meta/Provability.lean` | `godelC'_fixedpoint` (`DiagonalTwo`) |
| `goedelSentence`, `goedelSentence_fixedpoint` | `Meta/Provability.lean` | `godelC'` + su punto fijo |
| `D2` | `Meta/Incompleteness.lean` (**módulo borrado**) | `d2_prf` (`DerivCondPrf`) real |
| `D3` | `Meta/Incompleteness.lean` (**módulo borrado**) | `d3_prf_of_sigma1` (reducido) + plan 12‑A |

El módulo `Meta/Incompleteness.lean` (Gödel I/II legacy completo) se eliminó; sus
teoremas (`goedel_first_unprovable`, `incompleteness`, `con_imp_goedelSentence`,
`goedel_second`) tenían equivalentes reales (`goedel_first_real'`, `goedel_second'`).

---

## 4 · Estado de la cadena real (auditoría 2026-07-09, `#print axioms`)

```text
goedel_first_real'  : [propext, choice, Quot.sound,
                       FOL.MetaRules.{dne, gen, imp_intro},
                       Full.ax_induction, Full.ax_list_induction, ax_inAxC]
goedel_second'      : [propext, choice, Quot.sound,
                       FOL.MetaRules.{ex_elim, gen, imp_intro, or_elim},
                       Full.ax_list_induction, d3]
```

Ningún postulado gödeliano salvo `d3` en `goedel_second'` (F7b, pendiente de D3
real). Gödel I es **real y sin postulado gödeliano alguno**.

---

## Véase también

- `MINIMAL-AXIOMS.md` — análisis de minimalidad de los 34 axiomas de la **teoría
  objeto** `Minimal` (distinto de las declaraciones `axiom` de Lean listadas aquí).
- `GODEL-D3-TRACKED-DESIGN.md` — plan 12‑A hacia `d3` real (retirada de F7b).
- `CURRENT-STATUS-PROJECT.md`, `REFERENCE.md` §3.17–§3.18 — estado y proyección.

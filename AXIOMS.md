# Registro central de axiomas — ROBINSON_PlusPlus

> ## ESTADO REAL — 2026-08-31 · 🏁 rama A CERRADA: `pcc_eval_substfc` + no-vacuidad (vía CERO axiomas)
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 120 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **106 módulos activos** (Minimal 11 + Meta 84 + Full 11) **+ 0 en `cuarentena/` + 57 en `sondeos/`.**
> **7 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **0 módulos en `cuarentena/`** (D3 y Gödel II aún fuera de la cadena activa). NO borrados.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

**Last updated:** 2026-07-22 — **nueva §1.1: por qué la inducción de `Full/` es el mínimo teórico de Gödel II** (Q no satisface D2/D3; reparto verificado con `#print axioms`: D1 y D2 limpios, Gödel I/II usan `Full.ax_induction`+`ax_list_induction`). Sin cambios en el inventario: siguen **7**. — (previo 2026-07-20) **`prf_inAxC` → `prf_axiomsCodeT_eq`** (espejo `Prf` del ancla de igualdad; `prf_inAxC` pasa a **teorema**, **net‑0 axiomas**; lo exige el `In`‑reflect de `axiomsCodeT`). Total **7** `axiom`, sin cambio de número. (previo 2026-07-13: `ax_inAxC` → `ax_axiomsCodeT_eq`, net‑0, desbloquea `⊬¬G`. Previo 2026-07-09: F7a, 14 → 7.)
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
>   codificación (`ax_axiomsCodeT_eq` / `prf_axiomsCodeT_eq`); no son un duplicado a fusionar.
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
| 5 | `ax_axiomsCodeT_eq` | `Minimal/Axioms.lean` | Ancla de codificación | **`axioms ⊢ (axiomsCodeT =eq listFormCodeM axioms)`** — `axiomsCodeT` **es** el código de la lista de axiomas (extensión conservadora, cálculo `⊢`). **Reemplaza a `ax_inAxC`** (2026‑07‑13), que pasa a ser **teorema** derivado; a diferencia de `ax_inAxC` (sólo positivo), da **ambas direcciones** — la negativa `neg_In_axiomsCodeT` (que SÓLO los axiomas están) desbloquea `⊬¬G` (ver `PLAN-NEGVERIFIER.md`). El término gigante NO se materializa (recursión estructural, `Meta/AxiomListCode.lean`) |
| 6 | `prf_axiomsCodeT_eq` | `Minimal/Axioms.lean` | Ancla de codificación | **`Prf (axiomsCodeT =eq listFormCodeM axioms)`** — espejo `Prf` de (5) para el cálculo finitario. **Reemplaza a `prf_inAxC`** (2026‑07‑20, `25d255b`), que pasa a ser **teorema** derivado (**net‑0 axiomas**). D1 `repr_pos'_prf` cita ahora éste |
| 7 | `d3` | `Meta/GodelTwo.lean` | Postulado gödeliano | **Única pieza pendiente**: condición D3 de Hilbert-Bernays-Löb para `provCodeC'`. En construcción por el plan 12‑A |

### Detalle por familia

- **Esquemas de inducción (1–3, en `Full/`).** Son *la* inducción que el sistema
  `Full` añade sobre el débil `Minimal`. No pueden vivir en `Minimal/` sin destruir
  la frontera de diseño (Minimal = sin inducción general). `ax_mod2_alternation`
  es un axioma-puente que permite derivar `ax21`/`ax24` como teoremas.
  **No son andamiaje opcional: son el mínimo teórico de Gödel II — ver §1.1.**

### 1.1 · Por qué la inducción es IMPRESCINDIBLE (y no un lujo del formalizador)

> Pregunta recurrente: *si `Minimal` ≈ Robinson Q y Q es esencialmente indecidible,
> ¿no debería alcanzarse Gödel II sin inducción?* **No.** Y conviene dejarlo escrito
> porque el diseño en dos capas invita a pensar lo contrario.

**Hecho clásico.** Q es Σ₁‑completa *externamente*, pero **no satisface las condiciones
de derivabilidad de Hilbert–Bernays–Löb**: en particular **no prueba su propia
Σ₁‑completitud** (D3). Gödel II requiere D1–D3, y para D2/D3 hace falta inducción —
IΣ₁ (o EA/IΔ₀+exp) es el mínimo habitual. Gödel **I** sí llega sobre Q (vía Rosser);
Gödel **II**, no. Por tanto *«Gödel II sobre Q sin inducción»* no es un objetivo
pendiente de este proyecto: es un **enunciado falso**.

**Dónde entra exactamente, verificado con `#print axioms`** (no por conjetura):

| resultado | ¿usa `Full.ax_induction` / `ax_list_induction`? |
|---|---|
| **D1** `repr_pos'_prf` | **NO** — limpio (sólo el ancla de codificación) |
| **D2** `d2_prf` | **NO** — limpio (`[propext, choice, Quot.sound]`) |
| `goedel_first_numeral` (Gödel I) | **SÍ** |
| `goedel_second'` | **SÍ** (+ el `d3` pendiente) |

El reparto encaja con la teoría: **D1 es la Σ₁‑completitud *externa*** (aplicar el
verificador a una derivación concreta = cómputo finito, sin inducción); **D3 es la
Σ₁‑completitud *provable*** — razonar dentro de la teoría sobre *todas* las líneas y
sobre funciones recursivas de la sintaxis (`substfc`, `runFn`, …), y **eso exige
inducción**. Es exactamente el muro con el que se topó B.3c en los tags `q1`/`q2`/`q3`/
`leibniz`/`ind`/`qconf`/`listInd` (ver `NEXT-STEPS.md`).

**Consecuencia arquitectónica (importante, y no obvia).** `ax_induction` tiene la forma
`axioms ⊢ inductionFormula φ`: **extiende la relación de derivabilidad del objeto**. Es
decir, la teoría cuya demostrabilidad aritmetiza `provCodeC'` **no es Q pelada, es
Q++ + inducción** (perfil IΣ₁) siempre que la cadena cite esos axiomas. `Minimal/` sigue
siendo la *lista* de axiomas débil y la frontera de diseño se mantiene, pero el sujeto
del teorema de incompletitud, en la cadena real, es el sistema **con** inducción.
Esto es lo correcto y lo esperado — sólo faltaba decirlo explícitamente.

**Corolario práctico:** al construir la Σ₁‑completitud provable **está permitido y es
necesario** usar la inducción de `Full/`. Lo que *no* está permitido es añadir axiomas
*nuevos* para esquivarla; en particular, la inducción fuerte sobre **códigos** es
**derivable sin axiomas nuevos** (`ax_L0_cons_def` ancla `cons h t = pair h (succ t)`
con `pair = cantor_func`, luego los códigos son números y vale `ax_induction`).
- **Teoría objeto (4).** `ax_p_tfa` es el TFA; teorema en presencia de inducción,
  enunciado como axioma en la capa `Minimal` (que carece de ella).
- **Anclas de codificación (5–6).** Extensión **conservadora**. `ax_axiomsCodeT_eq`
  (cálculo `⊢`) es una **igualdad**: `axiomsCodeT` ES el código de la lista de
  axiomas — da **ambas** direcciones (positiva `ax_inAxC`, ahora **teorema**; y
  negativa `neg_In_axiomsCodeT`, que SÓLO los axiomas están). El término gigante
  `listFormCodeM axioms` **no se materializa** en las pruebas (recursión estructural,
  `Meta/AxiomListCode.lean`), evitando el coste que retiró el `ax_axiomsCodeT`
  original en `7ae7b7b`. **`prf_axiomsCodeT_eq`** (cálculo `Prf`) es su espejo exacto:
  desde 2026‑07‑20 (`25d255b`) sustituye al antiguo `prf_inAxC` —que era sólo
  positivo y ahora es **teorema** derivado—, también **net‑0 axiomas**. Lo exige el
  `In`‑reflect de `axiomsCodeT` (`Meta/InAxiomsCodePrf.lean`), que necesita las **dos**
  direcciones dentro de `Prf`.
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

Auditado con `#print axioms`, la cadena **real** (entonces `goedel_first_real'`, hoy
**`goedel_first_numeral`** tras la reparación de ADR‑012; `d2_prf`; `goedel_second'`) **no citaba**
ninguno de estos símbolos; solo los usaba la capa
Gödel vieja (Gödel I/II vía D2/D3 postulados). Retirados:

| Símbolo | Estaba en | Reemplazado por (real) |
|---------|-----------|------------------------|
| `Dem`, `dem_iff_provable` | `Meta/Provability.lean` | `HilbertSeq.Dem`/`ProvableH` (concreto) |
| `provFormula`, `provFormula_repr` | `Meta/Provability.lean` | `provCodeC'` + D1 `repr_pos'_prf` |
| `diagonal_lemma` | `Meta/Provability.lean` | hoy **`godelCN_fixedpoint`** (`DiagonalNumeral`) — el `godelC'_fixedpoint` de entonces también murió con ADR‑012 |
| `goedelSentence`, `goedelSentence_fixedpoint` | `Meta/Provability.lean` | hoy **`godelCN`** + `godelCN_fixedpoint` |
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
                       Full.ax_induction, Full.ax_list_induction, ax_axiomsCodeT_eq]
goedel_second'      : [propext, choice, Quot.sound,
                       FOL.MetaRules.{ex_elim, gen, imp_intro, or_elim},
                       Full.ax_list_induction, d3]
```

Ningún postulado gödeliano salvo `d3` en `goedel_second'` (F7b, pendiente de D3
real).

**Gödel I — precisión (auditoría 2026-07-13):** la mitad **`⊬G`** (`goedel_first_real'`) es **real y
sin postulado gödeliano alguno** ✅. La mitad **`⊬¬G`** (indecidibilidad) **NO está en la cadena real**:
se probó en la capa LEGACY (`Meta/Incompleteness.lean`) apoyándose en `provFormula_repr` —postulado
**bicondicional** cuya dirección `.mp` (representabilidad **negativa**) **no se sigue de la
consistencia simple**—, y se retiró en **F7a** junto con el módulo. **No revertir F7a: fue un arreglo
de solidez.** Para recuperarla honestamente falta construir
`repr_neg : ConsistentOmega → Prf (provCodeC' φ) → Prf φ`. Ver `GODEL-STATUS.md`.

---

## Véase también

- `MINIMAL-AXIOMS.md` — análisis de minimalidad de los 34 axiomas de la **teoría
  objeto** `Minimal` (distinto de las declaraciones `axiom` de Lean listadas aquí).
- `GODEL-D3-TRACKED-DESIGN.md` — plan 12‑A hacia `d3` real (retirada de F7b).
- `CURRENT-STATUS-PROJECT.md`, `REFERENCE.md` §3.17–§3.18 — estado y proyección.

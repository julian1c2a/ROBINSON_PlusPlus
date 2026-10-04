# TEOREMAS CABECERA — y **quién descarga cada hipótesis** (P‑2)

> ## ESTADO REAL — 2026‑10‑04 · `master` · **117 jobs · 104 módulos · 0 sorry · 0 `axiom` de Lean**
>
> 🏁 **En una línea**: Gödel I (`⊬G`) y Gödel II están **derivados** sobre `Prf`, su footprint son sólo los
> tres de Lean, y su ÚNICA hipótesis es `ConsistentH` ([ADR‑117](DECISIONS.md): el ancla es el teorema
> `prf_ancla`). ⚠️ Ya no son vacuos por F1, pero son **CONDICIONALES**: `ConsistentH` sólo vale si los 142
> axiomas son consistentes, y no hay modelo. La mitad `⊬¬G` **no existe** sobre `Prf`. *(Hasta ADR‑117
> llevaban además la clase `[AnclaEq]`, que daba `Prf ⊥` —F1, [ADR‑114](DECISIONS.md)—: eran VACUOS.)*

**Creado:** 2026‑09‑11 · **Autor:** Julián Calderón Almendros
**Last updated:** 2026-10-05 — ADR‑118: la clase `AnclaEq` retirada; D1 y D3 ya no llevan ninguna hipótesis de clase. Antes, 2026-10-04 — ADR‑117: el ancla es un TEOREMA (`prf_ancla`) y Gödel I/II ya no llevan
`[AnclaEq]`: su única hipótesis es `ConsistentH` (banner, §1, §4–§6); D1 y D3 sí la llevan, rellenada por la
instancia (§3). Antes, 2026-10-02 — reescrito entero: la capa `⊢` se retiró ([ADR‑115](DECISIONS.md)) y con ella
toda la mitad `⊬¬G` que vivía allí; F1 está compilado (`[AnclaEq]` ⇒ `Prf ⊥`), y **D1 y D3 también
llevan `[AnclaEq]`** — este documento decía «ninguna» desde ADR‑026 (2026‑09‑12), y era falso.

---

## 0 · Por qué existe este documento

La auditoría del 2026‑09‑11 encontró **F‑1**: `goedel_second'` llevaba meses anunciado como el
Segundo Teorema, y su hipótesis `hgi` **no la podía dar ninguna pieza del árbol**. No lo vio ningún
control, y **no podía verlo**: documentación y código **decían lo mismo**. No había desincronía —
había un hueco.

🔑 **La pregunta que lo destapa, y que este documento mecaniza a mano:**

> *Por cada teorema cabecera: **¿quién descarga cada una de sus hipótesis, y con qué?***
> Si la respuesta es «nadie», el teorema está **montado, no ensamblado** — y hay que decirlo
> **donde se anuncia el resultado**, no en un plan.

⭐ **Y la pregunta que faltaba** (2026‑10‑02, F1): *¿pueden valer **a la vez**?* Una hipótesis que nadie
descarga es información; dos hipótesis **incompatibles** hacen el teorema **vacuo**, con footprint
limpio y todos los controles en verde. `#print axioms` no ve las hipótesis de clase.

⚠️ **Regla de mantenimiento**: este documento se actualiza **en el mismo commit** que añade o cambia
un teorema cabecera. Una fila con «⬜ nadie» es información, no un fallo; una fila **ausente** sí es
un fallo.

---

## 1 · Gödel I (`⊬G`) y Gödel II — sobre el cálculo finitario `Prf`

| teorema | hipótesis | ¿quién la descarga? |
|---|---|---|
| **`goedel_first_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentH` | ⬜ nadie, y es correcto: es la hipótesis del teorema, y la **mínima** (`¬ Prf ⊥`). Nada del árbol la prueba: es el frente del **modelo de los 142** (A2–A5) |
| | ~~`[AnclaEq]`~~ | 🏁 **fuera de la firma desde ADR‑117** (2026‑10‑04): el ancla es el teorema `prf_ancla` (§4). Hasta ese día, ⛔⛔ **NADIE, y NO PODÍA**: `AnclaEq` ⇒ `Prf ⊥` sobre los 141 (`sondeos/AnclaEqInconsistente.lean`, hoy REGISTRO: `anclaEq_prf_bot`, y `hipotesis_goedel_insatisfacibles` — `[AnclaEq]` y `ConsistentH` **no valían a la vez**) |
| | *(el punto fijo)* | ✅ `prf_godelCN_fixedpoint`, **net‑0 PURO** |
| **`goedel_second_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentH` | ⬜ ídem |
| | ~~`[AnclaEq]`~~ | 🏁 ídem: fuera de la firma desde ADR‑117 |
| | *(punto fijo · necesitación · `Con' ⇒ G`)* | ✅ `prf_godelCN_fixedpoint` · `repr_pos'_prf` (D1) · `prf_con_imp_godel`, sobre `d2_prf` (D2) y `d3_prf_real` (D3) — D1 y D3 llevan todavía la ligadura `[AnclaEq]`, que rellena la instancia `instAnclaEq` (ADR‑117, §3); `prf_con_imp_godel`, ya no |

**Footprint** (medido, `check-footprints.bash`): `goedel_first_prf`, `goedel_second_prf`,
`prf_godelCN_fixedpoint`, `d3_prf_real`, `prf_ancla` y `f1_traduccion_refutada` → `[propext, Classical.choice,
Quot.sound]`. ⇒ **ningún axioma del proyecto**, y hasta ADR‑117, aun así, **vacuos**: lo que fallaba era la
hipótesis de clase, que el footprint no ve. 🔑 *Un footprint limpio no dice que el teorema diga algo* — y hoy
tampoco dice que `ConsistentH` se cumpla.

---

## 2 · Gödel I, la mitad `⊬¬G` — ⛔ NO EXISTE sobre `Prf`

Hasta el 2026‑10‑02 vivía entera sobre `⊢`: `goedel_first_undecidable_numeral`,
`goedel_first_undecidable_omega`, `reflects_of_omega` y `NegVerifier`, con `ConsistentOmega` y
`OmegaConsistent` como hipótesis. ⚠️ `NegVerifier` (ADR‑097) **no estaba demostrado**: la prueba de
`negVerifier_proved` llevaba en su footprint meta‑reglas refutadas, así que era teorema de un entorno
inconsistente. Sobre `Prf` hay que hacerla de nuevo (la de `1dac85a` sirve de guía de casos, no de prueba). **Se retiró con la capa `⊢`** (ADR‑115), y no se
pierde nada que significara algo: las meta‑reglas de `⊢` son refutables (L1‑3). Y la definición de
`OmegaConsistent` tiene un defecto propio (L1‑4: testigos sólo `StdChain`, `A := #0 = 1`), aunque **sobre `⊢`**
la refutación compilada pasaba por axiomas refutados y no prueba nada.

⛔ **Lo limpio es la misma definición trasladada a `Prf`, que SÍ es refutable**: `not_omegaConsistentPrf`
(`sondeos/OmegaConsistentRefutable.lean`, compilado, sin nada de `⊢`). ⇒ La mitad `⊬¬G` sobre `Prf`
**no puede** enunciarse con esa ω‑consistencia. Las dos salidas: **`OmegaConsistentProv`** (sólo el `∃`
que se usa, `provBody`) o **Rosser** (las dos mitades desde consistencia simple, cambiando de sentencia).

---

## 3 · Las condiciones de derivabilidad — sobre `Prf`

| | teorema | hipótesis |
|---|---|---|
| **D1** | **`repr_pos'_prf`** (`Meta/Representability2Prf.lean`) | ninguna desde ADR‑118 (hasta entonces `[AnclaEq]`, que desde ADR‑117 descargaba el teorema `prf_ancla`) |
| **D2** | **`d2_prf`** (`Meta/DerivCondPrf.lean`) | ninguna |
| **D3** | **`d3_prf_real`** (`Meta/PremsBdAllPrf.lean`) | ninguna desde ADR‑118, ídem (D3 fue el `axiom` `d3` sobre `⊢` hasta el 2026‑09‑10g; `d3_prf_real` nació teorema) |

Las versiones sobre `⊢` (`repr_pos'`, `d2`, `d3`) se retiraron con esa capa. La ligadura `[AnclaEq]` de D1 y D3,
y las demás del árbol (426), se retiraron con la clase el 2026‑10‑05 ([ADR‑118](DECISIONS.md)).

---

## 4 · ⚠️ Las hipótesis que quedan, y qué son exactamente

| hipótesis | definición | qué es de verdad |
|---|---|---|
| **`ConsistentH`** | `¬ Prf ⊥` | la de los dos teoremas, y desde ADR‑117 la ÚNICA: consistencia del cálculo **finitario** sobre los 142 axiomas, la **mínima honesta**. Nada la prueba todavía (A4: solidez de `Prf` por inducción sobre `Prf`; A5: con un modelo de los 142) |
| **`[AnclaEq]`** | `Prf (axiomsCodeT =eq listFormCodeM axioms)` | 🏁 **Ya no es un supuesto: es TEOREMA** desde ADR‑117 (2026‑10‑04), `prf_ancla` (`Meta/Representability2Prf.lean`), por el axioma objeto DIAGONAL `ax_axiomsCodeT_def`, el último de los 142 (`prf_deltaD`: su δ es el código del propio axioma); la clase, con su instancia, se retiró el 2026‑10‑05 (ADR‑118). Control: `f1_traduccion_refutada` —si la traducción de F1 conservara el ancla —si su imagen fuera teorema—, ya habría `Prf ⊥`: el argumento de F1 no da `⊥` sin partir de él; no prueba la consistencia—. Hasta ese día era ⛔⛔ **INCONSISTENTE** (F1: daba `Prf ⊥` sobre los 141) y no tenía instancia; y hasta ADR‑026 (2026‑09‑12) fue el `axiom prf_axiomsCodeT_eq`, que ese ADR movió del footprint a la FIRMA sin quitar el supuesto |

🗑️ **Retiradas con la capa `⊢`** (ADR‑115): `ConsistentOmega` (`¬ (axioms ⊢ ⊥)`), `OmegaConsistent`,
`NegVerifier`, `Reflects`.

---

## 5 · `axiom` de Lean — **0**

Los tres que quedaban vivían sobre `⊢` y se retiraron con esa capa (ADR‑115): `ax_induction_prim`,
`ax_list_induction` (**falso**: daba `[] ⊢ ⊥`, L1‑2) y `ax_axiomsCodeT_eq`. Registro completo en
[`AXIOMS.md`](AXIOMS.md). ⇒ **Ningún postulado gödeliano, y ningún `axiom`**: lo único supuesto de la
cadena es `ConsistentH` (§4; hasta ADR‑117 eran dos, con `[AnclaEq]`). Lo que ancla `axiomsCodeT` es hoy un
axioma OBJETO de la teoría —el último de los 142, `ax_axiomsCodeT_def`—, no un `axiom` de Lean ni una hipótesis.

---

## 6 · 🗑️ Registro de lo retirado

| | |
|---|---|
| ~~`goedel_second'`~~, ~~`con_imp_godel'`~~ | retirados el 2026‑09‑11 ([ADR‑024](DECISIONS.md), opción (b)): su `hgi : ¬(axioms ⊢ G)` decía «el cálculo refuta `G`», porque `axioms ⊢` era completo |
| ~~`goedel_first_numeral`~~, ~~`goedel_first_undecidable_numeral`~~, ~~`goedel_first_undecidable_omega`~~, ~~`reflects_of_omega`~~, ~~`negVerifier_proved`~~ | retirados el 2026‑10‑02 con la capa `⊢` ([ADR‑115](DECISIONS.md)) |
| ~~`[AnclaEq]`~~ en `goedel_first_prf`, `goedel_second_prf` y `prf_con_imp_godel` | retirada de las tres firmas el 2026‑10‑04 ([ADR‑117](DECISIONS.md)): el ancla es el teorema `prf_ancla` |
| ~~`class AnclaEq`~~, ~~`instAnclaEq`~~ y sus 426 ligaduras | retiradas el 2026‑10‑05 ([ADR‑118](DECISIONS.md)): un commit mecánico; los tres usos de `AnclaEq.eq`, a `prf_ancla` |

---

**Véase también:** `PLAN-PRUEBAS.md` §4 (lo que ningún control garantiza), `doc/AUDITORIA-2026-09-11.md`
F‑1, `DECISIONS.md` ADR‑022/023/024/026/114/115/117.

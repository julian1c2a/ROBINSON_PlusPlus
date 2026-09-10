# `cuarentena/` — ✅ **VACÍA** (2026-08-23)

**Last updated:** 2026-08-23 — repatriación COMPLETA
**Autor:** Julián Calderón Almendros

> ## Los 31 módulos han vuelto. Este directorio ya no contiene código.
>
> Se conserva el `README` como registro del episodio, porque es material del libro
> (`PLAN-LIBRO.md`, Parte IV) y porque la lección de método vale más que los ficheros.

## Qué pasó

La reparación de la inconsistencia ([ADR‑012](../DECISIONS.md)) retiró `ax_tc_cons`, y con él la
**lectura sintáctica de `tcFn`**. Eso rompió **31 módulos** — los 14 tags de `pcc_lineWF_tracked`,
`hI_dot`, el chasis `CTree`, el KIT — que se apartaron aquí en vez de borrarse
([ADR‑013](../DECISIONS.md)).

Sus teoremas eran **formalmente correctos** pero se habían demostrado sobre una teoría que probaba
`⊥`: eran **vacuos**. Apartarlos no perdió trabajo; reconoció que el suelo cedía.

## Cómo volvieron

| hito | cuarentena |
|---|---:|
| reparación ejecutada | 31 |
| refundar el keystone `Sigma1CorePrf` (a.1) | 21 |
| paso 1 · `EvalListPrf` + 6 en cascada | 14 |
| paso 2 · `EvalNthcPrf` (`pcc_rw_imp`) | 12 |
| paso 3 · `D3InDotPrf` (conversión en la frontera) | 10 |
| pasos 4‑5 · `LineWFTrackedPrf` + el KIT | 6 |
| paso 6 · `CodeTreeReflect`, `LineWFEfqPrf` | 3 |
| paso 7 · `InAxiomsCodePrf` + cascada final | **0** ✅ |

**Todo con el footprint sancionado** (`[propext, choice, Quot.sound, prf_axiomsCodeT_eq]`), sobre la
teoría **reparada**, y **sin cambiar ningún enunciado público**.

## Las tres sub‑familias, y cómo se sustituyó cada una

| familia | sustituto |
|---|---|
| `prf_tc_cons'` | **`pcc_dot_cons`** — la misma ecuación, pero **dentro de `Prov`**. Moldes: `pcc_rw_dot_cons_un` (unario, `Prf`), `pcc_rw_dot_cons_nthc` (binario, `PrfH`), vía **`pcc_rw_imp`** |
| `prf_tc_form` | `prf_tc_form_numeral` (net‑0) + **conversión en la FRONTERA** (`pcc_to_formCode_imp`), porque el lado derecho está fijado por `D3DottedPrf` y **es el objetivo de D3** |
| KIT `prf_tc_nul`/`_un`/`_bin` | `pcc_dot_nul`/`_un`/`_bin` — **por composición de `pcc_dot_cons`, sin inducción nueva** |

## Las lecciones que deja (material del libro)

1. **El transporte cambia de NIVEL, no de nombre.** Lo que era una igualdad de **código** (fuera de
   `Prov`) pasa a ser una reescritura **interna** (dentro). No es un reemplazo textual: cada sitio
   debe aportar su código‑contexto y su ecuación de `substfc`.
2. **Antes de sustituir un puente, comprobar si el lema lo NECESITABA.** Varias invariancias
   `substtc` sólo lo usaban de atajo: `formCode φ` y `listFormCodeM L` son **cerrados**, y su
   invariancia sale directamente de `substCodeT_closed`, sin tocar `tcFn`.
3. **Los pasos componen.** `pcc_eq_symm_code_internal`, que el KIT necesitaba, volvió con
   `BdAllIntroPrf` en el paso 3. Hacerlos en orden de cascada dejó cada herramienta a mano justo
   cuando hacía falta.
4. **Medir antes de comprometerse.** Las tres familias se midieron en `sondeos/` (`CarcPayoff`,
   `TcFormPayoff`, `KitPayoff`) **antes** de tocar producción. Ninguna medición falló, y una
   (`prf_tc_form`) cambió la estrategia por completo.

## ▶ Lo que queda, y no está aquí

🏁🏁 **NADA. Se cerró todo** (actualizado 2026‑09‑10h).

Lo que esta sección describía como abierto —«D3 reducida a UN SOLO lema»; los **7 reflectores**
(`q1 q2 q3 leibniz ind qconf listInd`) como «un problema abierto de verdad, no mecánico», porque
llevan `substfc`/`liftfc` sobre argumento **abstracto** y necesitaban un `pcc_eval_substfc` que
«**no existe**»— está **todo hecho**:

| pieza | cuándo | dónde |
|---|---|---|
| `pcc_eval_substfc` | 2026‑08‑31 | `Meta/EvalSubstfcPrf.lean` — **vía de CERO axiomas** ([ADR‑015](../DECISIONS.md)) |
| los **7 reflectores** ⇒ `pcc_lineWF_tracked` **INCONDICIONAL** (C3) | 2026‑09‑10e | `Meta/SubstTreeReflect.lean` §11ter |
| **D3 DEMOSTRADA** ⇒ `axiom d3` **RETIRADO** (7 → 6) | 2026‑09‑10g | `d3_prf_real`, `Meta/PremsBdAllPrf.lean` §10 |

⚠️ **Este párrafo llevaba obsoleto desde el 2026‑08‑23**, y lo cazó la auditoría del libro
(`doc/book/AUDITORIA-2026-09-10.md` §5, contradicción #9). Es la misma lección que el propio
episodio de la cuarentena enseña: **un documento da fe de lo que su autor creía en una fecha**.
Estado vivo: `NEXT-STEPS.md`. Memoria: `project-substfc-wall` (histórico), `project-d3-probada`.

# `cuarentena/` — la capa RASTREADA, apartada (no borrada)

**Last updated:** 2026-08-23 — tras repatriar `EvalListPrf` (paso 1); grafo recalculado por máquina
**Autor:** Julián Calderón Almendros

**Estos 14 módulos NO están en el build.** Se apartaron al ejecutar la reparación de la
inconsistencia ([ADR‑012/013](../DECISIONS.md)). **No se han borrado**: vuelven cuando se repare su
raíz.

**Historial:** fueron **31**. Refundar el keystone `Sigma1CorePrf` devolvió **10** (→ 21).
Repatriar `EvalListPrf` con `pcc_dot_cons` devolvió **7** más (→ 14, 2026‑08‑23): él mismo, más
`EvalLtPrf`, `EvalRunFnPrf`, `EvalBoundedPrf`, `Delta0ReflectPrf`, `PropCodePrf` y **`D3DottedPrf`**
— estos seis **sin tocar una línea**, sólo por quedar libres.

## Por qué se apartaron

Todos dependen —directa o transitivamente— de la **lectura sintáctica de `tcFn`**, es decir de
`ax_tc_cons`, que es la ecuación que hacía **inconsistente** la teoría objeto: `tcFn` no puede
recurrir a la vez sobre estructura NUMERAL (`ax_tc_succ`) y sobre estructura de CÓDIGO
(`ax_tc_cons`), porque en ℕ el mismo valor es ambas cosas (`cons 0 nil = 2 = σσ0`).

## ⚠️ Lo que contienen NO está perdido — estaba sobre arena

Los teoremas de estos módulos (los 14 tags de `pcc_lineWF_tracked`, `hI_dot`, el chasis `CTree`, el
KIT) son **formalmente correctos**, pero se demostraron sobre una teoría que probaba `⊥`, así que
**eran vacuos**. Apartarlos no pierde trabajo: reconoce que el suelo cedía.

---

## El grafo de recuperación (verificado por máquina, 2026-08-23)

> ⚠️ **Corrección de la auditoría 2026‑08‑22:** la cifra «6 raíces» que circulaba **era incorrecta**
> (eran 8, hoy 7 tras repatriar `EvalListPrf`). El recuento buscaba sólo `prf_tc_cons` y perdía
> `CodeTreeReflect` y `LineWFEfqPrf`, que usan la sub‑familia del KIT. *Lección: contar por la
> familia entera, y filtrando comentarios.*

### Las 7 RAÍCES que quedan — usan la familia `tc` retirada **en código**

| raíz | sub‑familia | usos | desbloquea |
|---|---|---:|---:|
| **`EvalNthcPrf`** | `prf_tc_cons'` ⚠️ **bajo binder** | 2 | **13** |
| `D3InDotPrf` | `prf_tc_form` | 3 | 11 |
| `LineWFTrackedPrf` | `prf_tc_cons'` + `prf_tc_eqc` | 6 | 8 |
| `CodeCtorKit` | KIT (`nul`/`un`/`bin`) + `prf_tc_cons'` | 12 | 4 |
| `CodeTreeReflect` | KIT | 3 | 2 |
| `InAxiomsCodePrf` | `prf_tc_form` | 2 | 2 |
| `LineWFEfqPrf` | KIT | 2 | 1 |

### Los 7 NO‑RAÍZ — caen solos

`BdAllIntroPrf` · `EvalCarcNthcPrf` · `LineWFAssemblePrf` · `LineWFMpPrf` · `LineWFPropPrf` ·
`LineWFSchemaPrf` · `LineWFThyPrf`

### ⚠️ Son TRES sub‑familias, no dos

| familia | sustituto | estado |
|---|---|---|
| `prf_tc_cons'` | **`pcc_dot_cons`** (+ el molde `pcc_rw_dot_cons_un`) | ✅ **resuelta y validada** |
| KIT: `prf_tc_nul`/`_un`/`_bin` | `pcc_dot_nul`/`_un`/`_bin` — esperables por composición | ⏳ **sin medir** |
| `prf_tc_form` | *sin diseñar* | ⏳ **sin mirar** |

### ✅ `EvalListPrf` — REPATRIADO (2026‑08‑23)

Era la **base**: sin dependencias dentro de la cuarentena, con los otros 20 colgando de él, y donde
se **definía** `prf_tc_cons'` — el origen literal de la contaminación. Hoy vive en
`Meta/EvalListPrf.lean`, con `prf_tc_cons'` **borrado** (su cuerpo era `prf_tc_cons`, que ya no
existe) y los tres transportes rehechos con el molde **`pcc_rw_dot_cons_un`**.

---

## Cómo se recuperan — la vía está VERIFICADA

La vía candidata (a) —probar la Σ₁‑completitud **internalizada**, dentro de `Prov`, en vez de con la
ecuación `tc` sintáctica— **está construida y medida**. Es la **escalera (a.2)**, ✅ completa:

```lean
pcc_eval_add  (a b : Term) : Prf (provFromCode (evalAddCode a b))    -- Meta/EvalArithPrf.lean
pcc_eval_mul  (a b : Term) : Prf (provFromCode (evalMulCode a b))    -- Meta/EvalMulPrf.lean
pcc_thm_inst  … sobre prf_div2_double_all                            -- el atajo de div2
pcc_dot_cons  (h t : Term) :                                         -- Meta/DotConsPrf.lean
    Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (tcFn (cons h t))))
```

**El rédito está comprobado, no supuesto** — `sondeos/CarcPayoff.lean` reconstruye `pcc_eval_carc`
con el **mismo enunciado y el mismo footprint**; los pasos 1‑3 del original (instancia de `ax_carc`
vía `pcc_axiom_inst2` + los dos `substfc` computados) quedan **intactos** y sólo cambia el cierre.

### El patrón de arreglo

```lean
-- ANTES (código, fuera de Prov):
prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_carcT (prf_eq_symm (prf_tc_cons' h t))) (prf_refl _))) hbase

-- AHORA (interno, dentro de Prov):
refine pcc_rw (fun s => eqc (carcT s) (tcFn h)) ?_ _ _ (pcc_dot_cons h t) hbase
intro s
…  -- la ecuación de substfc del contexto, mecánica con los prf_substtc_*
```

⚠️ **No es un reemplazo textual ciego.** El transporte pasa de ser **de código** (un
`prf_provCode_congr`) a ser **interno** (un `pcc_leibniz_apply`), así que cada sitio debe aportar su
contexto `G` y la ecuación `substfc zero s (G (varc 0)) =eq G s` — trivial con los `prf_substtc_*`,
pero hay que escribirla.

### ✅ El molde, ya validado en los tres sitios de `EvalListPrf`

Los tres usos tenían la **misma forma** —un constructor de código **unario** `F` aplicado al `cons`,
con un lado derecho `R` fijo—, así que se cerraron con un solo lema:

```lean
pcc_rw_dot_cons_un (F : Term → Term) (hFs …) (hFc …) (R : Term) (hR …) (h t : Term)
    (hbase : Prf (provFromCode (eqCodeFn (F (consT (tcFn h) (tcFn t))) R))) :
    Prf (provFromCode (eqCodeFn (F (tcFn (cons h t))) R))
```

Instanciado en `carcT`, `cdrcT` y `lencT`. **Reutilizable** en cualquier sitio con esa forma.

### ⚠️ Faltan DOS sustitutos más

* **KIT** (`prf_tc_nul m`, `prf_tc_un m a`, `prf_tc_bin m a b`, aridad 0/1/2): lo usan `CodeCtorKit`,
  `CodeTreeReflect` y `LineWFEfqPrf`. Como los tres son `cons`‑árboles (ése era el hallazgo del KIT),
  lo esperable es que salgan **por composición de `pcc_dot_cons`**, sin inducción nueva — **sin medir**.
* **`prf_tc_form`**: lo usan `D3InDotPrf` (3) e `InAxiomsCodePrf` (2). **Sin mirar todavía.**

## Orden de repatriación propuesto

| # | módulo | qué hay que hacer |
|--:|---|---|
| 1 | ✅ **`EvalListPrf`** | **HECHO** — 3 sitios (no 6), cerrados con un único molde `pcc_rw_dot_cons_un`. Arrastró 6 módulos en cascada |
| 2 | ▶ `EvalNthcPrf` → `EvalCarcNthcPrf` | ⚠️ **NO es el mismo patrón**: los 2 usos van sobre `.var 2`/`.var 1` **bajo binder**, dentro de `PrfH`. Hay que mirarlo antes de asumir |
| 3 | **KIT**: `pcc_dot_nul`/`_un`/`_bin` | *medir primero* si salen por composición de `pcc_dot_cons` → desbloquea `CodeCtorKit`, `CodeTreeReflect`, `LineWFEfqPrf` |
| 4 | `LineWFTrackedPrf` + los 14 tags | caen con 1–3 |
| 5 | `D3InDotPrf`, `InAxiomsCodePrf` | los dos que quedan |
| 6 | `D3DottedPrf` → **D3** → **Gödel II** → **F7b** | el objetivo |

Ver [`PLAN-FRENTE-A.md`](../PLAN-FRENTE-A.md), [`NEXT-STEPS.md`](../NEXT-STEPS.md) y
[`doc/REFERENCE-Incompleteness.md`](../doc/REFERENCE-Incompleteness.md) §3.25.

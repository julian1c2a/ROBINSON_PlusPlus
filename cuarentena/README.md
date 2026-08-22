# `cuarentena/` — la capa RASTREADA, apartada (no borrada)

**Last updated:** 2026-08-22 23:55 (HEAD `68fa43c`) — grafo recalculado por máquina
**Autor:** Julián Calderón Almendros

**Estos 21 módulos NO están en el build.** Se apartaron al ejecutar la reparación de la
inconsistencia ([ADR‑012/013](../DECISIONS.md)). **No se han borrado**: vuelven cuando se repare su
raíz. Fueron 31; refundar el keystone `Sigma1CorePrf` devolvió 10 de golpe.

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

## El grafo de recuperación (verificado por máquina, 2026-08-22)

> ⚠️ **Corrección de la auditoría 2026‑08‑22:** la cifra «**6 raíces**» que venía propagándose por
> `NEXT-STEPS.md`, `PLAN-FRENTE-A.md` y este mismo fichero **era incorrecta**. Son **8**. Se habían
> perdido `CodeTreeReflect` y `LineWFEfqPrf` porque el recuento buscaba sólo `prf_tc_cons`, y esos
> dos usan la **otra** sub‑familia — `prf_tc_nul`/`prf_tc_un`/`prf_tc_bin`, los constructores del
> KIT. *Lección: contar por la familia entera, y filtrando comentarios.*

### Las 8 RAÍCES — usan la familia `tc` retirada **en código**

| raíz | qué sub‑familia usa | usos | desbloquea (cierre transitivo) |
|---|---|---:|---:|
| **`EvalListPrf`** | `prf_tc_cons'` — **y lo DEFINE** (`:48`) | 6 | **20** — *todos los demás* |
| `EvalNthcPrf` | `prf_tc_cons'` | — | 13 |
| `D3InDotPrf` | `prf_tc_form`/`prf_tc_cons'` | — | 11 |
| `LineWFTrackedPrf` | familia `tc` | — | 8 |
| `CodeCtorKit` | `prf_tc_nul`/`un`/`bin` | — | 4 |
| **`CodeTreeReflect`** ⚠️ | `prf_tc_nul`/`un`/`bin` | 3 | 2 |
| `InAxiomsCodePrf` | familia `tc` | — | 2 |
| **`LineWFEfqPrf`** ⚠️ | `prf_tc_bin`/`prf_tc_nul` | 2 | 1 |

⚠️ = raíz que el recuento anterior no vio.

### Los 13 NO‑RAÍZ — caen solos al repararse sus raíces

`BdAllIntroPrf` · `D3DottedPrf` · `Delta0ReflectPrf` · `EvalBoundedPrf` · `EvalCarcNthcPrf` ·
`EvalLtPrf` · `EvalRunFnPrf` · `LineWFAssemblePrf` · `LineWFMpPrf` · `LineWFPropPrf` ·
`LineWFSchemaPrf` · `LineWFThyPrf` · `PropCodePrf`

### 🔑 `EvalListPrf` es la BASE, no sólo el keystone

No tiene **ninguna** dependencia dentro de la cuarentena, y **los otros 20 dependen de él**
transitivamente. Es además donde se **define** `prf_tc_cons'` (`:48`) — el origen literal de la
contaminación. **Nada vuelve antes que él.**

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

### ⚠️ Falta un segundo sustituto: el KIT

`pcc_dot_cons` cubre **`prf_tc_cons'`**. Pero dos raíces (`CodeCtorKit`, `CodeTreeReflect`) y
`LineWFEfqPrf` usan la **otra** sub‑familia: `prf_tc_nul m`, `prf_tc_un m a`, `prf_tc_bin m a b` —
los constructores de código de aridad 0/1/2. Necesitan **su propia versión internalizada**, análoga
a `pcc_dot_cons`. Como los tres son `cons`‑árboles (ése era el hallazgo del KIT), lo esperable es que
salgan **por composición de `pcc_dot_cons`**, sin inducción nueva — pero **está sin medir**.

## Orden de repatriación propuesto

| # | módulo | qué hay que hacer |
|--:|---|---|
| 1 | **`EvalListPrf`** | sustituir los 6 usos de `prf_tc_cons'` por `pcc_rw` + `pcc_dot_cons`. El de `pcc_eval_carc` ya está **hecho y compilado** en `sondeos/CarcPayoff.lean`; falta `pcc_eval_cdrc` y los demás |
| 2 | `EvalNthcPrf` → `EvalCarcNthcPrf` | mismo patrón |
| 3 | **KIT**: `pcc_dot_nul`/`_un`/`_bin` | *medir primero* si salen por composición de `pcc_dot_cons` → desbloquea `CodeCtorKit`, `CodeTreeReflect`, `LineWFEfqPrf` |
| 4 | `LineWFTrackedPrf` + los 14 tags | caen con 1–3 |
| 5 | `D3InDotPrf`, `InAxiomsCodePrf` | los dos que quedan |
| 6 | `D3DottedPrf` → **D3** → **Gödel II** → **F7b** | el objetivo |

Ver [`PLAN-FRENTE-A.md`](../PLAN-FRENTE-A.md), [`NEXT-STEPS.md`](../NEXT-STEPS.md) y
[`doc/REFERENCE-Incompleteness.md`](../doc/REFERENCE-Incompleteness.md) §3.25.

# `cuarentena/` — la capa RASTREADA, apartada (no borrada)

**Estos 31 módulos NO están en el build.** Se apartaron al ejecutar la reparación de la
inconsistencia (rama `reparacion/c-godel-i-consistente`). **No se han borrado**: si el frente (a)
prospera, vuelven.

## Por qué se apartaron

Todos dependen —directa o transitivamente— de la **lectura sintáctica de `tcFn`**, es decir de
`ax_tc_cons`, que es la ecuación que hacía **inconsistente** la teoría objeto: `tcFn` no puede
recurrir a la vez sobre estructura NUMERAL (`ax_tc_succ`) y sobre estructura de CÓDIGO
(`ax_tc_cons`), porque en ℕ el mismo valor es ambas cosas (`cons 0 nil = 2 = σσ0`).

**Las 8 raíces** (las que usan directamente la familia retirada):

`CodeCtorKit` · `D3InDotPrf` · `EvalListPrf` · `EvalNthcPrf` · `InAxiomsCodePrf` ·
`LineWFTrackedPrf` · `OmegaReflect` · `Sigma1CorePrf`

Los otros 23 caen por dependencia.

## ⚠️ Lo que contienen NO está perdido — estaba sobre arena

Los teoremas de estos módulos (los 14 tags de `pcc_lineWF_tracked`, `hI_dot`, el chasis `CTree`,
el KIT) son **formalmente correctos**, pero se demostraron sobre una teoría que probaba `⊥`, así
que **eran vacuos**. Apartarlos no pierde trabajo: reconoce que el suelo cedía.

## Qué haría falta para recuperarlos

El piloto `sondeos/PilotoRastreada.lean` midió el nudo: `pcc_eval_carc (h t)` usa
`prf_tc_cons' h t` con `h`,`t` **ABSTRACTOS**, y esa ecuación es **incompatible** con la lectura
numeral (se demuestra que daría un código de cabeza `⌜::⌝` igual a uno de cabeza `⌜σ⌝`).

**Los 13 sitios embudan en 5 lemas** (`prf_tc_cons'`, `prf_tc_nul/un/bin`, `prf_tc_eqc`), así que
si se encuentra un sustituto para esos 5, **el chasis de encima vuelve sin tocarse**.

La vía candidata es **(a)**: probar la Σ₁‑completitud internalizada con **inducción interna**
—`PrfH.ind` y `PrfH.listInd` **existen**— en vez de con la ecuación `tc` sintáctica. Sin medir.
Ver `PLAN-SORTES.md` y la memoria `project-reparacion-via-numeral`.

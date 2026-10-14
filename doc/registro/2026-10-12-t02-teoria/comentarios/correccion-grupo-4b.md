# Corrección de comentarios · grupo 4b (guardas de ADR‑020 y otros)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

He revisado los 13 hallazgos del grupo 4b contra el fuente y los 13 se sostienen. Hay 21 ediciones en los 10 ficheros de la lista, todas dentro de comentarios, más una frase caducada que encontré aparte (NUEVA‑1). No toqué ningún otro fichero, no ejecuté lake ni lean y git sólo lo usé para leer. Las ediciones las hice con un script (`scratchpad/suelo/comentarios/g4b/edita.py`) que exige que el texto viejo aparezca una sola vez, conserva CRLF/LF y comprueba los `/-` y `-/`. Las notas usan el guion U+2011.

## Hallazgos

**4b‑01** · `ForallElimCodePrf.lean:41` · **NOTA**
- Evidencia: hoy `prf_lineWF_q1 (concl A t) (hwA : Prf (hasWitF A)) (hwt : Prf (hasWit t))` (`ReprPrf.lean:785`). Antes de `bb0e483` (ADR‑020, 2026‑09‑05) no tenía guardas, así que la frase fue cierta cuando se escribió.
- Texto nuevo: «(✏️ 2026‑10‑14, ADR‑134: ya no los admite arbitrarios. Desde ADR‑020 `prf_lineWF_q1` pide las guardas `hwA : Prf (hasWitF A)` y `hwt : Prf (hasWit t)` (`Meta/ReprPrf.lean`); sigue sin `termCode`.)»

**4b‑02** · `ForallElimCodePrf.lean:84‑86` · **CORREGIDO** (error de tipo B)
- Evidencia: la firma pide `hwF` y `hwT` sobre los liftados (:88‑89). La frase venía de `pcc_forallElim_code'` (con `hAc`, commit `294490e`) y quedó pegada a la versión `_open`, que nunca tuvo `hAc` (`7467fb5`).
- Texto nuevo: «`substfc zero w Ac`. No pide `Ac` cerrado (eso es `pcc_forallElim_code'`, con `hAc`): pide las guardas de ADR‑020 sobre el cuerpo y el testigo LIFTEADOS, `hwF` y `hwT`. (✏️ 2026‑10‑14: decía «Sólo pide `Ac` cerrado (`hAc`)», frase heredada de la versión cerrada.)»

**4b‑03** · `PropCodePrf.lean:31‑33` y `:127‑128` · **NOTA** (×2)
- Evidencia: `prf_lineWF_ind … (hwa)` (`ReprPrf:871`); q1, q2 y leibniz también llevan guardas (:785, :806, :848); p1, p2, j3, efq y eqrefl no; `pcc_ind_code … (hwA)` (:144). El ⚠️ que ya había en `pcc_ind_code` cubre el teorema, pero no las dos cabeceras.
- Texto en :31: «(✏️ 2026‑10‑14, ADR‑134: desde ADR‑020 «códigos arbitrarios» vale para `p1`, `p2`, `j3`, `efq` y EQREFL, no para Q1/Q2/LEIBNIZ ni para `ind` (tag 18): sus `prf_lineWF_*` (`Meta/ReprPrf.lean`) piden las guardas `hasWitF`/`hasWit`, y `pcc_ind_code` pide `hwA`.)»
- Texto en :127: «(✏️ 2026‑10‑14, ADR‑134: `a` ya no es arbitrario: desde ADR‑020, `prf_lineWF_ind (concl a) (hwa : Prf (hasWitF a))`; ver el ⚠️ de `pcc_ind_code`.)»

**4b‑04** · `ExIntroCodePrf.lean:32‑33` · **NOTA**
- Evidencia: la cabecera es de `e3cf39f`; el ensamblaje se hizo el mismo día en `0e6f932`, y hoy son `pcc_exIntro_code'` (:89) y `pcc_exIntro_code` (:178).
- Texto nuevo: «(✏️ 2026‑10‑14, ADR‑134: ya no es un plan: el ensamblaje está hecho abajo, en `pcc_exIntro_code'` y su corolario `pcc_exIntro_code`; ver la nota de la sección.)»

**4b‑05** · `ExIntroCodePrf.lean:79‑88` · **CORREGIDO + NOTA**
- Evidencia:
  - La firma pide `hAc`, `hwF` y `hwT`, y no `hw`. El docstring era el de `pcc_exIntro_code (hAc hw)` y pasó a la versión con prima en `0bca4ed` (2026‑07‑10).
  - `d3` era `axiom d3 … : axioms ⊢ …` (`GodelTwo.lean`); desde `9ca5e66` fue `theorem d3 [AnclaEq]` y se retiró en `b1dedd1` (ADR‑115). Hoy no hay ninguna declaración `d3`.
  - D3DottedPrf:77 y D3InDotPrf:81/140 usan `pcc_exIntro_code_open`.
- Texto nuevo: «para `Ac` cerrado a todo nivel (`hAc`) y testigo `w` ABIERTO, con las guardas de ADR‑020 `hwF : Prf (hasWitF Ac)` y `hwT : Prf (hasWit (liftTerm 0 w))`, de la demostrabilidad … `exc Ac` (✏️ 2026‑10‑14: decía «para `Ac`, `w` cerrados a todo nivel (`hAc`, `hw`)», la firma de entonces de `pcc_exIntro_code`, de la que esta versión heredó el docstring). Es el ladrillo … en `d3` (✏️ 2026‑10‑14, ADR‑134: `d3`, D3 sobre `⊢`, se retiró con ADR‑115; D3 es hoy `d3_prf_real` (`Meta/PremsBdAllPrf.lean`), y los módulos de D3 (`D3DottedPrf`, `D3InDotPrf`) usan la variante sin `hAc`, `pcc_exIntro_code_open` (`Meta/Delta0ReflectPrf.lean`)).»

**4b‑06** · `Div2ParityPrf.lean:119‑120` · **CORREGIDO**
- Evidencia: L1 sólo se usa en :164 y :177 (dentro de L2). No hay más usos ni en `ROBINSON_PlusPlus/` ni en `sondeos/`, y el propio fichero dice «No usa L1» en :188.
- Texto nuevo: «Lo consume L2 (cancelación); L3 no lo usa (ver L3). (✏️ 2026‑10‑14: decía «Lo consumen L2 (cancelación) y el caso `mod2 = 1` de L3».)»

**4b‑07** · `Div2ParityPrf.lean:32‑34` · **NOTA**
- Evidencia: `prf_cons_eval` (`CodeNumeralPrf:102`) usa `prf_div2_numeral`; `goedel_I` (`Consistencia:53`); `goedel_I_neg` (`SolidezVerificador:558`).
- Texto nuevo: «(✏️ 2026‑10‑14, ADR‑134: registro — la cadena está cerrada: `prf_cons_eval` está probado en `Meta/CodeNumeralPrf.lean` con L5 (`prf_div2_numeral`), y Gödel I va entero y sin hipótesis: `goedel_I` (`Meta/Consistencia.lean`) y `goedel_I_neg` (`Meta/SolidezVerificador.lean`).)»

**4b‑08** · `ListEtaPrf.lean:198‑199` · **NOTA**
- Evidencia: `PremsOfTagPrf.lean:106/109` (`prf_eta_lenc`, `prf_nthc1_carc_cdrc`) y :85 (`etaAt`). El comentario es de `f355fe0`, seis minutos antes que el consumidor (`f6515c5`).
- Texto nuevo: «(✏️ 2026‑10‑14, ADR‑134: ya no es previsto: lo consume `Meta/PremsOfTagPrf.lean`, con `etaAt`, `prf_eta_lenc` y `prf_nthc1_carc_cdrc`.)»

**4b‑09** · `MpCodePrf.lean:305‑306` · **CORREGIDO** (punteros, sin nota)
- Evidencia: hoy están en `Axioms.lean:531/534/537/543/546`, no en 500…515.
- Texto nuevo: «`ax_substfc_impl`/`_and`/`_or` (`Minimal/Axioms.lean`), y también `ax_substfc_atom` y `ax_substfc_eq`.»

**4b‑10** · `ReprPrf.lean:272‑274` · **CORREGIDO**
- Evidencia: `ax_lineWF_thy` lleva `lenc = 2̄` (`Axioms:1418`), que `prf_lineWF_thy` descarga en línea (:522). Entre los 21 esquemas las longitudes son 2 (×1), 3 (×7), 4 (×10) y 5 (×3).
- Texto nuevo: «Se tabulan las de 3, 4 y 5; la cuarta que aparece, 2 (sólo la línea `thy`), se descarga en línea en `prf_lineWF_thy`. (✏️ 2026‑10‑14: decía «las tres longitudes que aparecen (3, 4 y 5)».)»

**4b‑11** · `Representability2.lean:47‑52`, más las cuatro cabeceras vacías en :99, :104, :109 y :130 · **NOTA** (×5)
- Evidencia: `b1dedd1` quitó de aquí `runFn_track`, `In_runFn_of_mem`, `chainOk_track` y `repr_pos'`. Sus versiones sobre `Prf` están en `Representability2Prf`:67/96/245/462.
- Texto en :47: «✏️ 2026‑10‑14 (ADR‑134): registro — el tracking y D1 ya no están aquí. ADR‑115 retiró sus versiones sobre `⊢` (`runFn_track`, `In_runFn_of_mem`, `chainOk_track`, `repr_pos'`), y las vigentes, sobre `Prf`, viven en `Meta/Representability2Prf.lean`: `prf_runFn_track`, `prf_In_runFn_of_mem`, `prf_chainOk_track` y D1, `repr_pos'_prf`. Este módulo sólo conserva el encoder (`lineJustif`, `lineCode'`, `proofCode'`) y las dos guardas de ADR‑020; las cuatro secciones vacías de abajo son su rastro.»
- Texto en cada cabecera vacía: «✏️ 2026‑10‑14 (ADR‑134): vacía desde ADR‑115; hoy `<nombre>`, en `Meta/Representability2Prf.lean`.», con `prf_runFn_track`, `prf_In_runFn_of_mem`, `prf_chainOk_track` y `repr_pos'_prf` respectivamente.

**4b‑12** · `RunFnBoundedPrf.lean:26‑29` · **NOTA**
- Evidencia: el módulo se importa en `Meta.lean:79`, `ChainOkBoundedPrf` y `EvalRunFnPrf`. Los cuatro lemas están en :61, :78, :197 y :274; `prf_nthc_runFn` lleva la guarda `i < lenc p`.
- Texto nuevo: «✏️ 2026‑10‑14 (ADR‑134): registro — ya no es un sondeo: el módulo está en el build (lo importan `Meta/ChainOkBoundedPrf.lean` y `Meta/EvalRunFnPrf.lean`) y la hipótesis está PROBADA aquí mismo: `prf_runFn_nil_cons`, `prf_lenc_runFn`, `prf_nthc_runFn` (bajo `i < lenc p`) y la forma acotada `prf_In_runFn_iff`. Lo que sigue es el planteamiento del 2026‑07‑08.»

**4b‑13** · `InAxiomsCodePrf.lean:64`, `:78` y `:220` · **NOTA** (×3)
- Evidencia: no hay ninguna declaración `prf_tc_form`. La retiró `6f66e61` (2026‑08‑18, ADR‑012). La cabeza usa `pcc_tc_formCode_internal f` en :291, y su prueba pasa por `prf_tc_form_numeral` y `pcc_to_formCode` (:177‑183).
- Texto en :64: «(✏️ 2026‑10‑14, ADR‑134: `prf_tc_form` ya no existe —se retiró con ADR‑012, el 2026‑08‑18—; ese tramo se hace hoy DENTRO de `Prov` con `pcc_tc_formCode_internal`, vía `prf_tc_form_numeral` y `pcc_to_formCode`.)»
- Texto en :78: «(✏️ 2026‑10‑14, ADR‑134: hoy el tercer tramo es `pcc_tc_formCode_internal f`, ya en forma INTERNA; ver `pcc_in_head_swap`).»
- Texto en :220: «(✏️ 2026‑10‑14, ADR‑134: el último tramo ya no es `prf_tc_form`, retirado con ADR‑012: es la hipótesis INTERNA `haform`, que para `a = formCodeM f` da `pcc_tc_formCode_internal f`).»

## NUEVA

**NUEVA‑1** · `ExIntroCodePrf.lean:75‑77` · **NOTA**
- La cabecera de la sección `### pcc_exIntro_code` daba la firma `(hAc hw)` sin guardas, y atribuía el ensamblaje a `pcc_exIntro_code`, que hoy es un corolario.
- Evidencia: `0bca4ed` y `bb0e483`, más :178‑182.
- Texto nuevo: «(✏️ 2026‑10‑14, ADR‑134: desde el 2026‑07‑10 este ensamblaje es la prueba de `pcc_exIntro_code'`, con testigo abierto, y `pcc_exIntro_code` es su corolario; desde ADR‑020 los dos piden además las guardas `hwF`/`hwT`, así que `w` tampoco es del todo arbitrario.)»

## Ficheros tocados

Todos en `ROBINSON_PlusPlus/Meta/`. Las columnas `/-` y `-/` comparan el recuento antes y después; los finales se comprobaron por bytes después de editar.

| Fichero | `git diff --stat` | `/-` | `-/` | Finales |
|---|---|---|---|---|
| `ForallElimCodePrf.lean` | 6 | 8 → 8 | 8 → 8 | CRLF |
| `PropCodePrf.lean` | 6 | 15 → 15 | 15 → 15 | CRLF |
| `ExIntroCodePrf.lean` | 22 | 9 → 9 | 9 → 9 | CRLF |
| `Div2ParityPrf.lean` | 6 | 35 → 35 | 35 → 35 | CRLF |
| `ListEtaPrf.lean` | 3 | 14 → 14 | 14 → 14 | LF |
| `MpCodePrf.lean` | 4 | 23 → 23 | 23 → 23 | LF |
| `ReprPrf.lean` | 4 | 70 → 70 | 70 → 70 | CRLF |
| `Representability2.lean` | 23 | 14 → 14 | 14 → 14 | CRLF |
| `RunFnBoundedPrf.lean` | 5 | 21 → 21 | 21 → 21 | LF |
| `InAxiomsCodePrf.lean` | 12 | 20 → 20 | 20 → 20 | CRLF |

En los ficheros CRLF el número de CR sigue siendo igual al de LF, y los tres LF siguen sin ningún CR. El aviso «LF will be replaced by CRLF» que da git en esos tres viene de la configuración de git, no de estos cambios.

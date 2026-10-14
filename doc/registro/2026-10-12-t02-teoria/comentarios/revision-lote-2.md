# Revisión adversarial del lote de comentarios · parte 2

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

He revisado el parche `lote2.patch` entero (35 ficheros). Hay 14 defectos: 1 falso (A), 4 inexactos (M) y 9 menores (m). Uno de los menores no es una frase sino una clase: punteros `fichero:línea` que el propio lote ha desplazado. La sintaxis está bien: ningún `/-` ni `-/` nuevo (el recuento es el mismo que en HEAD en los 35 ficheros) y ninguna línea `+` con acentos graves desparejados.

## Defectos

**1. A** · `Meta/D3BodyPrf.lean:317-318`
- Frase: «Consumen además `PremsBdAllPrf` —…— y `ChainNegPrf` —`prf_lineWF_of_chainOk`—.»
- Por qué es falsa: `ChainNegPrf` importa y abre `D3BodyPrf`, pero no usa en código ninguna de sus 12 declaraciones (lo he medido con un grep que quita los comentarios). Sus cuatro menciones de `prf_lineWF_of_chainOk` (:67, :195, :199, :221) están dentro de docstrings: su gemelo `prf_boundedPremsIn_of_chainOk` repite la derivación en vez de usarla.
- Reemplazo: «Consumen además `PremsBdAllPrf` —`premsPsi`, `pcc_bnd_bridge_at`, `PrfH_pcc_rw`, `prf_lineWF_of_chainOk`…—; `ChainNegPrf` lo importa, pero sólo cita `prf_lineWF_of_chainOk` en docstrings, como molde de su gemelo `prf_boundedPremsIn_of_chainOk`.)»

**2. M** · `Meta/D3ChainDotPrf.lean:69-70`
- Frase: «la paga `DEUDA_chainOkBDot_of_hbody hwP_chainOkBPsi hbody_prems`, que construye `d3_prf_real`.»
- Por qué es inexacta: `d3_prf_real` no menciona `hbody_prems`, que no tiene ningún uso en código (sólo aparece en el `export` y en `#print axioms`). La cadena real es `d3_prf_of_halves` → `d3_prf_of_hbody φ hwP_chainOkBPsi (hbody_of_halves hA_lineWFDotAt hB_premsDotAt)` (`D3ChainDotPrf.lean:1180-1186`, `1023-1028`).
- Reemplazo: «la paga, dentro de `d3_prf_real` (vía `d3_prf_of_halves` → `d3_prf_of_hbody`), el término `DEUDA_chainOkBDot_of_hbody hwP_chainOkBPsi (hbody_of_halves hA_lineWFDotAt hB_premsDotAt)`, que es el cuerpo de `hbody_prems`.)»

**3. M** · `Meta/D3InDotPrf.lean:56-59`
- Frase: la línea corregida sigue diciendo «el cuerpo vía `pcc_eq_tracked`+`pcc_eval_carc_nthc`+…», y la nota de al lado dice «la prueba de Step B no usa `pcc_eq_tracked`».
- Por qué: el texto contradice a su propia nota. `pcc_eq_tracked` no aparece en el código del fichero; sólo en esas dos líneas de comentario.
- Reemplazo: «…y el cuerpo vía `pcc_eval_carc_nthc`+`prf_tc_form_numeral`+`pcc_to_formCode_imp`, por congruencia objeto (aquí entra `chainOk`…). (✏️ 2026‑10‑14, ADR‑134: decía «vía `pcc_eq_tracked`+…+`prf_tc_form`»; `prf_tc_form` murió con `ax_tc_cons` —«El sustituto de `prf_tc_form`», abajo— y Step B no usa `pcc_eq_tracked`.)»

**4. M** · `Meta/EvalLiftcPrf.lean:44-45`
- Frase: «hoy esta en `Meta/LiftcCodePrf.lean:1278`, un cuarto valor.»
- Por qué: el mismo lote añade 9 líneas a `LiftcCodePrf` antes de esa línea, así que `PrfH_congr_targetLift` está hoy en `:1287`. El puntero nace ya mal, justo en el párrafo que advierte de que los números de línea se mueven. Además contradice la frase siguiente («Los numeros que quedan apuntan a `sondeos/`»).
- Reemplazo: «(✏️ 2026‑10‑14: hoy vive en `Meta/LiftcCodePrf.lean`; se cita por nombre, porque el número volvió a moverse con las notas de este mismo día.)»

**5. M** · `Meta/EvalNthcPrf.lean:62-63`
- Frase: «la evaluación acotada `pcc_eval_nthc`, que consumen `D3BodyPrf` y `PremsBdAllPrf`.»
- Por qué: la lista es demasiado corta. La consumen 10 módulos del build: `EvalCarcNthcPrf`, `HasWitTrackedPrf`, `HasWitFTrackedPrf`, `LineWFMpPrf`, `LineWFSchemaPrf`, `LineWFThyPrf`, `LineWFTrackedPrf`, `TrackedAtomsPrf`, `D3BodyPrf` y `PremsBdAllPrf`.
- Reemplazo: «…`pcc_eval_nthc`, que consumen diez módulos del build —la capa rastreada de C3 (`LineWFTrackedPrf`, `TrackedAtomsPrf`, `HasWitTrackedPrf`/`HasWitFTrackedPrf`…) y D3 (`D3BodyPrf`, `PremsBdAllPrf`); grep del 2026‑10‑14—.)»

**6. m** · `Meta/EvalLiftfcPrf.lean:10`
- Frase: «`pcc_eval_liftfc : DEUDA_evalLiftfc`, §11».
- Por qué: `pcc_eval_liftfc` está en §10 (cabecera de `:1243`); no hay ningún §11. La nota repite un error que ya estaba en `:1267` y `:1310` («(§11)»), en el mismo bloque §12 que la nota toca.
- Reemplazo: «§10» en las tres líneas.

**7. m** · `Meta/HasWitFTrackedPrf.lean:1197-1198`
- Frase: «con los siete de sustitución en §10 y §10bis de ese módulo».
- Por qué: en `SubstTreeReflect`, q1 está en §8, q2/leibniz en §9, q3/qconf en §10 e ind/listInd en §10bis.
- Reemplazo: «…en §8–§10bis de ese módulo» (es lo que ponen las notas de `LineWFAssemblePrf` y `SubstTreeReflect`).

**8. m** · `Meta/D3ChainDotPrf.lean:1237-1239`
- Frase: «estos dos sólo se usan entre sí, en este módulo».
- Por qué: no es un uso mutuo. `pcc_bdCarcLt_reflect` sólo lo usa `pcc_premsBody_reflect` (:543); éste sólo lo usa `pcc_premsBody_reflect_at` (:554), que no tiene consumidor.
- Reemplazo: «…`pcc_bdCarcLt_reflect` sólo lo usa `pcc_premsBody_reflect`, y éste sólo `pcc_premsBody_reflect_at`, que no tiene consumidor; grep del 2026‑10‑14.)»

**9. m** · `Meta/D3ChainDotPrf.lean:31`
- Frase: «—hoy, error en su l. 355, `sondeos/pasadas/tabla_adr129.txt`—».
- Por qué: esa tabla se midió el 2026‑10‑05, no hoy (las notas de `HasWitTrackedPrf` y `TrackedAtomsPrf` sí lo dicen bien).
- Reemplazo: «—en la última pasada medida (2026‑10‑05, `tabla_adr129.txt`), error en su l. 355—».

**10. m** · `Meta/EvalSubstfcPrf.lean:1614-1616`
- Frase: «usa `pcc_eval_substfc_wit` en `PrfH_tc_objAt` y `pcc_congr_substfcT_arg2_code`, los dos en `Meta/SubstTreeReflect.lean`».
- Por qué: se lee como si `pcc_congr_substfcT_arg2_code` fuera un sitio de uso dentro de `SubstTreeReflect`. En realidad se declara en este mismo módulo (:105) y lo consumen `PrfH_tc_objAt` (:505) y `PrfH_dotVN` (:632). Además falta un consumidor: `EvalLiftfcPrf` usa `descenso_bin1`/`descenso_bin2`/`descenso_un`, cualificados (:572, :600…).
- Reemplazo: «C3 consume de aquí `pcc_eval_substfc_wit` (en `PrfH_tc_objAt`) y `pcc_congr_substfcT_arg2_code` (en `PrfH_tc_objAt` y `PrfH_dotVN`), en `Meta/SubstTreeReflect.lean`; `Meta/EvalLiftfcPrf.lean` usa `descenso_bin1`/`_bin2`/`descenso_un`, cualificados; y el sondeo…»

**11. m** · `Meta/SubstTreeReflect.lean:19`
- Frase: «consume su forma con guardas, `pcc_eval_liftfc_wit`».
- Por qué: `pcc_eval_liftfc` y `pcc_eval_liftfc_wit` llevan la misma guarda `hasWitF X`. `_wit` es «la forma desplegada» (su propio docstring, `EvalLiftfcPrf.lean:1253`).
- Reemplazo: «consume su forma desplegada, `pcc_eval_liftfc_wit`».

**12. m** · `Meta/TrackedCorePrf.lean:55-56`
- Frase: «(`liftFormula_provFromCode_open`, `substFormula_provFromCode_open`, `atom2CodeFn`, `prf_congr_atom2CodeFn`; entre otros, en `Meta/D3ChainDotPrf.lean`)».
- Por qué: `substFormula_provFromCode_open` no se usa en `D3ChainDotPrf`; los otros tres sí.
- Reemplazo: «…; los tres primeros, entre otros sitios, en `Meta/D3ChainDotPrf.lean`, y `substFormula_provFromCode_open` en `PremsBdAllPrf`, `LiftcCodePrf`…».

**13. m** · `Meta/CodeTreeReflect.lean:52-53`
- Frase: «decía «`prf_tc_objAt`», que no existe».
- Por qué: sí existió (`2a77df2`); cayó al retirar `ax_tc_cons` (`6f66e61`, a cuarentena) y se reescribió dentro de `Prov`. Las reglas piden «`X` (retirado, ADR‑N)».
- Reemplazo: «(✏️ 2026‑10‑14: decía «`prf_tc_objAt`», retirado con `ax_tc_cons` (ADR‑012); hoy es `pcc_tc_objAt`)».

**14. m** · `Meta/LiftcCodePrf.lean:29`
- Frase: «es el módulo promovido el 2026‑09‑02, como dice el párrafo de abajo».
- Por qué: el commit que lo añade, `21c8a6b`, es del 2026‑09‑03 a las 11:43. La nota repite una fecha sin medirla.
- Reemplazo: «…promovido en `21c8a6b` (2026‑09‑03; el párrafo de abajo dice 2026‑09‑02)…».

**15. m, clase** · punteros correctos en HEAD que este lote ha desplazado (al meter líneas en los ficheros de destino):
- `Meta/ChainNegPrf.lean:195` y `:221`: `Meta/D3BodyPrf.lean:78` → hoy 80 (`prf_lineWF_of_chainOk`).
- `Meta/D3ChainDotPrf.lean:13`: `D3InDotPrf.lean:524` → 528 (`d3_prf_of_chainOkDot`).
- `Meta/D3ChainDotPrf.lean:60`: `LineWFAssemblePrf.lean:104` → 115 (`pcc_lineWF_tracked_modulo_7`). Está en el mismo párrafo que una nota nueva.
- `Meta/D3ChainDotPrf.lean:96`: `D3DottedPrf.lean:87` → 91 (`chainOkDot`).
- `Meta/EvalLiftfcPrf.lean:70`: `EvalArithPrf.lean:184` → 189 (`substfcT`). En `:71`, `LiftcCodePrf.lean:111` ya estaba mal en HEAD (113) y hoy es 120.
- `Meta/LiftcCodePrf.lean:131` y `:134`: `CodeCtorKit.lean:60` y `:64` → 61 y 65 (`unT`, `binT`).
- Fuera de los `.lean` del build: `PLAN-LIBRO.md:177` (`CodeWitnessPrf.lean:2142` → 2150), `DECISIONS.md:6102`, `NEXT-STEPS.md:3170` y `sondeos/InTracked.lean:24` (`D3InDotPrf.lean:334` → 336), y los punteros de `doc/AUDITORIA-SUELO-2026-10-12.md` (:302, :303, :538, :539…), que son registro fechado.
- Arreglo propuesto: citar por símbolo (`` `d3_prf_of_chainOkDot` (`Meta/D3InDotPrf.lean`) ``), sin número.

## Lo que se sostiene

Comprobé contra el fuente unas 230 afirmaciones; se sostienen unas 216. Entre otras:
- Las cifras medidas: 32 llamadas a `prf_congr_binT` en 8 módulos de `ROBINSON_PlusPlus/`; las 74 copias del kit ternario en `sondeos/` (9+9+11+7+8+8+8+7+7); los 36 nombres declarados en `EvalLiftcPrf`.
- Los «nadie lo usa» de los lemas A5 y de `hGuard_of_slots`.
- Los consumidores de `SubstTreeReflect`, `TrackedAtomsPrf`, `HasWitTrackedPrf` (tags 9, 10 y 13) y `D3ChainDotPrf`.
- La vacuidad de `hI`/`hbI` (`sondeos/D3Sigma1Vacuo.lean`, con `MNV V₀`).
- Las fechas y commits citados: `e08a1e2`, `6c07958`, `c937b30`, `e68c313`, `178b10b`, `03f9523`; B6b cerrada en `17c3e64` (2026‑09‑11); «once minutos después» (13:31 → 13:42 del 2026‑07‑10).
- Los «compila, build del 2026‑10‑14» de `SubstfcWitnessPrf`: los `.olean` son de hoy, 19:24–19:26, posteriores a las ediciones.

Los «hechos de hoy» de `INSTRUCCIONES.md` que toca este lote son correctos. Sólo se han movido sus números de línea (`SubstTreeReflect:1157` → 1170, `PremsBdAllPrf:1300` → 1302, `ReflectionPrf:80` → 90, `Sigma1BoundedPrf:83` → 95…); ninguna línea `+` los copió.

Mis dos scripts de apoyo (un grep que quita comentarios y un detector de punteros desplazados) están en `<tmp>\scratchpad\rev2\`.

Resumen: comprobé unas 230 afirmaciones y se sostienen unas 216; los 14 defectos son 1 A, 4 M y 9 m, contando como uno la clase de punteros desplazados (8 punteros en los `.lean`).

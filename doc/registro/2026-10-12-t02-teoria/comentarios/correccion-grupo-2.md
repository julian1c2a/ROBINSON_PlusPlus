# Corrección de comentarios · grupo 2 (C3 y D3)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

# Informe del grupo 2 (C3 y D3: lineWF, la reflexión y la cadena punteada)

Los 23 hallazgos se sostienen al compararlos con el fuente: ninguno RECHAZADO ni OMITIDO. Añado además 2 hallazgos NUEVOS. Sólo he tocado comentarios y docstrings de los 14 ficheros de mi lista, sin lake, sin lean y con git sólo de lectura. Las rutas son de `ROBINSON_PlusPlus/Meta/` y las líneas son las del árbol ya editado.

## Hallazgos

**2‑01 · `D3ChainDotPrf.lean`. NOTA en cabecera, en 6 tablas o docstrings, y en el `export`.**
- Evidencia:
  - `PremsBdAllPrf.lean:1300`: `d3_prf_real φ := d3_prf_of_halves φ hA_lineWFDotAt hB_premsDotAt`.
  - `hbody_of_halves` se usa en `PremsBdAllPrf.lean:1297`.
  - `SubstTreeReflect.lean` §11ter: `pcc_lineWF_tracked (t)` no tiene hipótesis.
  - Git: C3 en `9a608c9` y D3 en `9ca5e66`, los dos del 2026‑09‑10; el módulo nació en `33d799d` (2026‑09‑07).
- Consumo medido con grep: lo consumen D3BodyPrf (`lineWFDotAt`, `premsDotAt`) y PremsBdAllPrf (7 nombres).
- `DEUDA_chainOkBDot` no tiene un teorema propio: la prueba es `DEUDA_chainOkBDot_of_hbody hwP_chainOkBPsi hbody_prems`.
- Notas añadidas:
  - **:19 (cabecera):** «✏️ 2026‑10‑14 (ADR‑134): registro — **D3 está PROBADA desde el 2026‑09‑10**: `d3_prf_real` (`Meta/PremsBdAllPrf.lean`) es `d3_prf_of_halves` (§13 de este módulo) con `hA_lineWFDotAt` (`Meta/D3BodyPrf.lean`) y `hB_premsDotAt` (`Meta/PremsBdAllPrf.lean`), y `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean`, C3) no tiene hipótesis. Lo que sigue describe el estado del día en que se escribió cada sección (del 2026‑09‑07 al 2026‑09‑10): sus «queda», «falta» y ⬜ son registro.»
  - **:67** (tras «Lo que este módulo NO hace»): «(✏️ 2026‑10‑14, ADR‑134: hoy `pcc_lineWF_tracked` existe sin condicionar —C3 se cerró el 2026‑09‑10, `Meta/SubstTreeReflect.lean`— y las dos obligaciones están pagadas: (1) en `hA_lineWFDotAt` y (2) en `hB_premsDotAt`. `DEUDA_chainOkBDot` no tiene teorema con nombre: la paga `DEUDA_chainOkBDot_of_hbody hwP_chainOkBPsi hbody_prems`, que construye `d3_prf_real`.)»
  - **:207 (§3.1):** «✏️ 2026‑10‑14 (ADR‑134): registro — hoy no queda nada: la cota es §4 (`PrfH_chainOkB_bnd_bridge`), (a) es `hA_lineWFDotAt` y (b) `hB_premsDotAt`; lo que sigue describe el estado del 2026‑09‑09f.»
  - **:275, :710 y :776** (docstrings que dicen «D3 queda/baja a N»): «(✏️ 2026‑10‑14, ADR‑134: registro — hoy D3 está probada, `d3_prf_real`.)»
  - **:935 (§10.6):** «✏️ 2026‑10‑14 (ADR‑134): registro — las dos ⬜ están pagadas: `hPsiId` en §11 (`hPsiId_chainOkBPsiDot`) y `hbody` en `Meta/PremsBdAllPrf.lean` (`hbody_prems`); lo que sigue describe el estado del 2026‑09‑09i.»
  - **:1032 (§11.1):** «✏️ 2026‑10‑14 (ADR‑134): registro — `hwP` es `hwP_chainOkBPsi` (§12), (a) `hA_lineWFDotAt` y (b) `hB_premsDotAt`; lo que sigue describe el estado del 2026‑09‑10, antes de §12.»
  - **:1092 (§12.1):** «✏️ 2026‑10‑14 (ADR‑134): registro — las dos mitades están probadas: (a) `hA_lineWFDotAt`, con `pcc_lineWF_tracked` ya sin hipótesis (`ind` y `listInd` incluidos), y (b) `hB_premsDotAt`; §13.1 corrige además lo que aquí se dice de (b).»
  - **:1243 (§13.2–§13.3):** «✏️ 2026‑10‑14 (ADR‑134): registro — (b) también está probada, `hB_premsDotAt`, y las tres piezas de §13.3 existen: B1 es `pcc_eval_premsOf` (`Meta/PremsOfDotPrf.lean`), B2 `pcc_bnd_bridge` (`Meta/D3BodyPrf.lean`) y B3 `hbdAllPrems_of_body` con `premsBody_deuda` (`Meta/PremsBdAllPrf.lean`); `d3_prf_real` cierra D3. Las dos tablas describen el estado del 2026‑09‑10, con B1 aún ⬜.»
  - **:1274 (`export`):** «✏️ 2026‑10‑14 (ADR‑134): hoy es por CONSUMO (grep del 2026‑10‑14): lo consumen `Meta/D3BodyPrf.lean` (`lineWFDotAt`, `premsDotAt`) y `Meta/PremsBdAllPrf.lean` (`d3_prf_of_halves`, `hbody_of_halves`, `pcc_bdEx_carc_reflect_gen`, `hW_chainOkBPsi`, `hL_chainOkBPsi`, `chainOkBPsiDot`, `premsDotAt`). D3 se cerró por esta vía: `d3_prf_real` = `d3_prf_of_halves`, que acaba en `d3_prf_of_chainOkBDot`.»
- Las líneas :40‑42 y :202‑204 quedan cubiertas por las notas de :19 y :207.

**2‑02 · `D3ChainDotPrf.lean:30` · NOTA.**
- Evidencia: `sondeos/pasadas/tabla_adr129.txt` da `A3IsFCBTracked.lean|1|9|…:355:4: error`. Las tablas adr121, adr127 y d7 dan lo mismo, y `doc/AUDITORIA-BASE-2026-10-02.md` §3 ya lo daba como ❌.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: el sondeo es hoy registro: no compila en ninguna pasada medida desde la del 2026‑10‑02 —hoy, error en su l. 355, `sondeos/pasadas/tabla_adr129.txt`—; lo que usa el build es `pcc_bdAll_intro` mismo.)»
- La cita se conserva.

**2‑03 · `D3BodyPrf.lean:25‑28` · CORREGIDO, con nota.**
- Evidencia: `D3BodyPrf.lean:117` usa `pcc_lineWF_tracked (nthc q i)`. Según `git show 9a608c9`, la prueba cambió de `_modulo_other … hOther` al incondicional sin tocar la cabecera.
- Texto: «2. **El reflector**, `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean`, sin hipótesis), que da `Prov(⌜lineWF (nthc q i)⌝)` con el código en forma de **reflexión pura** `(nthc q i)˙`. (✏️ 2026‑10‑14, ADR‑134: decía «`pcc_lineWF_tracked_modulo_other`», que pedía la hipótesis `hOther`; la prueba usa el incondicional desde el cierre de C3, el 2026‑09‑10.)»

**2‑04 · `D3BodyPrf.lean:280` · NOTA.**
- Evidencia: `PremsBdAllPrf.lean:1287‑1289` usa `PrfH_bdAllCode_congr_bnd … (pcc_bnd_bridge_at q i)` dentro de `hB_premsDotAt`.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: ya la consume, en `hB_premsDotAt`, `Meta/PremsBdAllPrf.lean`.)»

**2‑05 · `D3BodyPrf.lean:315` · NOTA.**
- Evidencia:
  - `PremsBdAllPrf.lean:1301`.
  - Grep en PremsBdAllPrf: `premsPsi`, `premsDotAt_split`, `pcc_bnd_bridge(_at)`, `PrfH_pcc_rw`, `hG_premsOfT` y `prf_lineWF_of_chainOk`.
  - Grep en ChainNegPrf: `prf_lineWF_of_chainOk`, en :186‑210.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: ya lo es: `d3_prf_real` (`Meta/PremsBdAllPrf.lean`) es `d3_prf_of_halves φ hA_lineWFDotAt hB_premsDotAt`. Consumen además `PremsBdAllPrf` —`premsPsi`, `pcc_bnd_bridge_at`, `PrfH_pcc_rw`…— y `ChainNegPrf` —`prf_lineWF_of_chainOk`—.)»

**2‑06 · `D3DottedPrf.lean:46` · NOTA.**
- Evidencia: `hI_dot` es teorema (`D3InDotPrf.lean:517`). La cadena es `d3_prf_of_chainOkDot` → `d3_prf_of_dotted_atoms` (`D3InDotPrf.lean:524‑528`) → `d3_prf_of_dotted`.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: los dos están pagados: `hI_dot` (`Meta/D3InDotPrf.lean`) y `hC_dot`, que sale de `hC_dot_of_chainOkBDot` (`Meta/D3ChainDotPrf.lean`). `d3_prf_real` pasa por este keystone: `d3_prf_of_chainOkDot` → `d3_prf_of_dotted_atoms` → `d3_prf_of_dotted`.)»

**2‑07 · `D3InDotPrf.lean:56‑59` y `:377‑380` · CORREGIDO, con nota.**
- Evidencia:
  - `prf_tc_form` no está declarado en ningún sitio.
  - :164 dice «murió con `ax_tc_cons`».
  - La prueba usa `prf_tc_form_numeral` (:436) y `pcc_to_formCode_imp` (:458).
- Texto en :56: «…`pcc_eq_tracked`+`pcc_eval_carc_nthc`+`prf_tc_form_numeral` +`pcc_to_formCode_imp` (aquí entra `chainOk`, que `pcc_eval_carc_nthc` necesita). (✏️ 2026‑10‑14, ADR‑134: decía «`prf_tc_form`», que murió con `ax_tc_cons` —«El sustituto de `prf_tc_form`», abajo—; y la prueba de Step B no usa `pcc_eq_tracked`: el cuerpo sale por congruencia objeto.)»
- Texto en :377: «…(`PrfH_congr_tcFn` + `prf_tc_form_numeral` + cancelación del `liftc` con `prf_liftc_tcFn`) y `PrfH_provCode_congr`; la forma NUMERAL pasa a la `formCode` en la frontera, dentro de `Prov`, con `pcc_to_formCode_imp` (✏️ 2026‑10‑14: decía «`prf_tc_form`», que murió con `ax_tc_cons`).»

**2‑08 · `D3InDotPrf.lean:298` · CORREGIDO (errata, sin nota).**
- Evidencia: sólo existe `substCodeF_boundedCarcIn_at` (:342); el nombre sin `_at` no aparece ni en RPP, ni en los sondeos, ni en FOL.
- Texto: «`substCodeF_boundedCarcIn_at`».

**2‑09 · `PremsBdAllPrf.lean:41` · NOTA.**
- Evidencia: `premsBody_deuda : DEUDA_premsBody` (:1013), y `hB_premsDotAt` y `d3_prf_real` (:1275 y :1300).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: la salda este mismo módulo, `premsBody_deuda` (§8 de §9bis), y con ella cierra D3: `hB_premsDotAt` y `d3_prf_real`, en el último §3, «D3, PROBADA».)»

**2‑10 · `PremsOfDotPrf.lean:1044` · NOTA.**
- Evidencia: `D3BodyPrf.lean:227` y `PremsBdAllPrf.lean:686`, dentro de `pcc_premsOfT_bridge` (:665).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: ya lo consume: B2 es `pcc_bnd_bridge` (`Meta/D3BodyPrf.lean`), y `Meta/PremsBdAllPrf.lean` usa `pcc_eval_premsOf` en `pcc_premsOfT_bridge`; las dos usan también `premsOfT` y sus lemas de congruencia y testigo.)»

**2‑11 · `EvalRunFnPrf.lean:47` · NOTA.**
- Evidencia:
  - `hI_dot_at` usa `prf_boundedCarcIn_of_In_runFn` (`D3InDotPrf.lean:510`).
  - `pcc_eval_runFn` no aparece en ningún sitio.
  - Fuera del módulo sólo se usa `prf_substtc_termCode_nil` (EvalLiftcPrf:262, EvalNthcPrf:105, LiftcCodePrf:770…).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: registro — `hI_dot` es teorema (`Meta/D3InDotPrf.lean`) y no pasa por aquí: convierte `In ⌜φ⌝ (runFn nil p)` en el `∃` acotado `boundedCarcIn` (`prf_boundedCarcIn_of_In_runFn`) y refleja ése. La evaluación general, `pcc_eval_runFn`, no existe y nada la pide; de este módulo el build sólo consume `prf_substtc_termCode_nil` (EvalLiftcPrf, EvalNthcPrf, LiftcCodePrf; grep del 2026‑10‑14). La recursión codificada, `pcc_runFn_cons_code`, sí está, abajo.)»

**2‑12 · `LineWFAssemblePrf.lean:32`, `:98` y `:112` · NOTA, con la marca [HISTÓRICO] de `LineWFGuardPrf:39`.**
- Evidencia:
  - `pcc_eval_substfc` está en `EvalSubstfcPrf.lean:1524`.
  - Los 7 reflectores son `_q1_imp` … `_listInd_imp`, en `SubstTreeReflect` §8–§10bis.
  - `pcc_lineWF_tracked` usa `pcc_lineWF_tracked_of_branches`, y `pcc_tag_vacuous` cubre `n+21`.
  - El único uso de `modulo_7` en el código del build es `SubstTreeReflect.lean` (`modulo_2`).
- Texto en :32: «⚠️ **[HISTÓRICO — C3 se cerró el 2026‑09‑10: `pcc_lineWF_tracked` es INCONDICIONAL (`Meta/SubstTreeReflect.lean` §11ter), `pcc_eval_substfc` existe (`Meta/EvalSubstfcPrf.lean`) y los 7 tags están cerrados en SubstTreeReflect §8–§10bis.]** (✏️ 2026‑10‑14, ADR‑134: lo que sigue describe el estado de antes; el ensamblador genérico de este módulo es el que usa hoy C3.)»
- Texto en :98: «(✏️ 2026‑10‑14, ADR‑134: la instanciación real es `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean` §11ter): usa `pcc_lineWF_tracked_of_branches` directamente y paga los `k ≥ 21` con `pcc_tag_vacuous`, sin `hOther`.)»
- Texto en :112: «(✏️ 2026‑10‑14, ADR‑134: registro — los 7 están probados (`Meta/SubstTreeReflect.lean` §8–§10bis) y `pcc_eval_substfc` existe (`Meta/EvalSubstfcPrf.lean`). En el build, hoy sólo usa este lema `pcc_lineWF_tracked_modulo_2` (SubstTreeReflect §11).)»

**2‑13 · `LineWFGuardPrf.lean:204` · NOTA.**
- Evidencia: `pcc_hGuardT … (hin : i < n)` (`HasWitTrackedPrf:1209`), `pcc_hGuardF` (`HasWitFTrackedPrf:1136`) y `hGuard_of_slots` (:1169).
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — las dos están probadas (para `i < n`): `pcc_hGuardT` (`Meta/HasWitTrackedPrf.lean`) y `pcc_hGuardF` (`Meta/HasWitFTrackedPrf.lean`), y `hGuard_of_slots` cierra la cascada sin deudas; ver la cabecera.»

**2‑14 · `LineWFTrackedPrf.lean:414‑417` · CORREGIDO, con nota.**
- Evidencia: :455 `PrfH_congr_tcFn hEQ` y :471 `pcc_dot_eqc_symm`. :259‑261 dice «Aquí vivía `prf_tc_eqc`» (2026‑08‑23).
- Texto: «…la hipótesis `=eq` reescribe el valor vía `PrfH_congr_tcFn` y, dentro de `Prov`, `pcc_dot_eqc_symm`, y el encaje final es la congruencia diagonal `pcc_congr_eqcT_diag_code_imp` + Leibniz interno. (✏️ 2026‑10‑14, ADR‑134: decía «vía `prf_tc_eqc`», que se retiró el 2026‑08‑23 —«El sustituto de `prf_tc_eqc`», arriba—.)»

**2‑15 · `LineWFTrackedPrf.lean:613` · NOTA.**
- Evidencia: `| 12 => exact pcc_lineWF_tracked_eqrefl_imp t` en `SubstTreeReflect.lean:1184` y en `LineWFAssemblePrf.lean` (`modulo_7`).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: ya lo invoca: tag 12 de `pcc_lineWF_tracked`, `Meta/SubstTreeReflect.lean` §11ter, y de `pcc_lineWF_tracked_modulo_7`.)»

**2‑16 · `LineWFCases.lean:41` · NOTA.**
- Evidencia: lo importan sólo ChainNegPrf, GodelTwoPrf y Meta.lean. Los usos son `tagConcl` (ChainNegPrf:551…) y `prf_imp_trans` (GodelTwoPrf:113; su única definición está en LineWFCases:214).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: el frente D3 tampoco lo usa: D3 se cerró por `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean`), que despacha los tags con su propio `match`, y ningún módulo de D3 importa éste. Hoy lo importan `ChainNegPrf` (`tagConcl`) y `GodelTwoPrf` (`prf_imp_trans`); grep del 2026‑10‑14.)»

**2‑17 · `SubstTreeReflect.lean:17` (cabecera) y `:329` (§4) · NOTA.**
- Evidencia:
  - `inductive STree` tiene `lift` y `tcm`.
  - `pcc_eval_liftfc_wit` se usa en :544, dentro de `PrfH_tc_objAt`.
  - `pcc_eval_liftfc` está en `EvalLiftfcPrf.lean:1251`; ya no en la :1241 que dan los hechos de hoy, porque el fichero se ha movido.
- Texto en :17: «✏️ 2026‑10‑14 (ADR‑134): registro — **C3 está CERRADO desde el 2026‑09‑10**: los 7 reflectores están en §8–§10bis y `pcc_lineWF_tracked` (§11ter) no tiene hipótesis. `pcc_eval_liftfc` existe (`Meta/EvalLiftfcPrf.lean`) y este módulo consume su forma con guardas, `pcc_eval_liftfc_wit`, en `PrfH_tc_objAt` (§5); `STree` tiene hoy también los nodos `lift` y `tcm`. Lo que sigue en esta cabecera describe el estado de antes del nodo `lift` (2026‑09‑09e).»
- Texto en :329: «(✏️ 2026‑10‑14, ADR‑134: «hoy» es antes del nodo `lift`; los siete árboles están declarados en este módulo: estos tres, `treeQ3`/`treeQconf` justo abajo y `treeInd`/`treeListInd` en §10bis.)»

**2‑18 · `SubstTreeReflect.lean:1211` (`export`) · NOTA.**
- Evidencia: `D3BodyPrf.lean:117` (`pcc_lineWF_tracked`) y `PremsOfDotPrf.lean:1037` (`pcc_tag_vacuous`, dentro de `pcc_eval_premsOf`).
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — el módulo entrega hoy los **siete** (§8–§10bis) y `pcc_lineWF_tracked` sin hipótesis (§11ter); `pcc_eval_liftfc` existe (`Meta/EvalLiftfcPrf.lean`). Y hay consumo (grep del 2026‑10‑14): `Meta/D3BodyPrf.lean` (`pcc_lineWF_tracked`, en `hA_lineWFDotAt`) y `Meta/PremsOfDotPrf.lean` (`pcc_tag_vacuous`, en `pcc_eval_premsOf`).»

**2‑19 · `SubstTreeReflect.lean:11‑12` (comentario `--` del import) y `:1053` · NOTA.**
- Evidencia: §11bis (`modulo_other` cablea `_ind_imp` y `_listInd_imp`) y §11ter.
- Texto en :11: «--    (✏️ 2026‑10‑14, ADR‑134: hoy se le cablean los SIETE, §11bis; de aquí sale también / --    `pcc_lineWF_tracked_of_branches`, con el que §11ter prueba `pcc_lineWF_tracked`.)»
- Texto en :1053: «(✏️ 2026‑10‑14, ADR‑134: los dos están cerrados en §10bis; `hbody`(a) de D3 es hoy `hA_lineWFDotAt` (`Meta/D3BodyPrf.lean`), que usa `pcc_lineWF_tracked`, §11ter.)»

**2‑20 · `CodeTreeReflect.lean:52` · CORREGIDO, con nota.**
- Evidencia: `pcc_tc_objAt` (:225) es un teorema dentro de `Prov`; `prf_tc_objAt` no está declarado.
- Texto: «* `pcc_tc_objAt` — el «código del código» del árbol, dentro de `Prov` (✏️ 2026‑10‑14: decía «`prf_tc_objAt`», que no existe);»

**2‑21 · `CodeTreeReflect.lean:380` · NOTA.**
- Evidencia: `pcc_lineWF_tracked_of_tree` se usa 10 veces en `LineWFPropPrf.lean` (:36…:132).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: hecho: lo instancian los diez reflectores de `Meta/LineWFPropPrf.lean`, y C3 está cerrado, `pcc_lineWF_tracked`.)»

**2‑22 · `CodeCtorKit.lean:49` · NOTA.**
- Evidencia: `pcc_lineWF_tracked` no tiene hipótesis.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: hoy no queda ningún tag pendiente: C3 está cerrado, `pcc_lineWF_tracked`, `Meta/SubstTreeReflect.lean`.)»

**2‑23 · `CodeCtorKit.lean:155‑158` · CORREGIDO, con nota.**
- Medido con grep, quitando la definición, el `export` y las menciones entre acentos graves: 32 llamadas en 8 módulos.
  - CodeCtorKit 5, CodeTreeReflect 3, EvalLiftfcPrf 15, HasWitFTrackedPrf 1, HasWitTrackedPrf 2, LiftcCodePrf 1, LineWFEfqPrf 2, SubstTreeReflect 3.
- Texto: «Tiene 32 call-sites reales en ocho modulos (grep del 2026‑10‑14: `CodeCtorKit`, `CodeTreeReflect`, `EvalLiftfcPrf`, `HasWitFTrackedPrf`, `HasWitTrackedPrf`, `LiftcCodePrf`, `LineWFEfqPrf`, `SubstTreeReflect`; ✏️ 2026‑10‑14: decía «11 call-sites reales en cuatro modulos»).»

## Hallazgos NUEVOS

**N1 · `D3ChainDotPrf.lean:547` (docstring de `pcc_premsBody_reflect_at`, «consumirá») · NOTA.**
- Evidencia: el grep no encuentra ningún uso de este nombre fuera de su propia línea.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: no la consumió: el chasis interior (`Meta/PremsBdAllPrf.lean`) va por `pcc_bdEx_carc_reflect_gen` (§5bis), y este lema no tiene consumidor; grep del 2026‑10‑14.)»

**N2 · `D3ChainDotPrf.lean:1236` (§13.1: «`pcc_bdCarcLt_reflect` y `pcc_premsBody_reflect` … seguirán haciendo falta») · NOTA.**
- Evidencia: los dos sólo se usan el uno al otro dentro del módulo (:543 y :552). PremsBdAllPrf sólo los cita en comentarios (:546 y :650) y usa `pcc_bdEx_carc_reflect_gen` (:994).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: no hicieron falta: el chasis interior (`Meta/PremsBdAllPrf.lean`) usa el genérico `pcc_bdEx_carc_reflect_gen` (§5bis), y estos dos sólo se usan entre sí, en este módulo; grep del 2026‑10‑14.)»

En 2‑07 añadí además que `pcc_eq_tracked` no se usa en la prueba de Step B; el grep da 0 usos en `D3InDotPrf`.

**Visto y no editado:**
- La cabecera de `LineWFGuardPrf.lean:35` dice que `pcc_hGuardT`/`F` están probadas «desde 2026‑09‑08», pero git las data el 2026‑09‑07 (`517b235` y `19d2536`). Puede ser la convención de días de sesión del proyecto; lo dejo a tu criterio.
- `CodeTreeReflect.lean:40` («17 tags pendientes») es la motivación de entonces, y `D3InDotPrf.lean:519` describe lo que hace el teorema: los dejo como registro.

## Ficheros tocados (`git diff --stat`)

| Fichero | Líneas |
|---|---|
| `CodeCtorKit.lean` | 9 ++-- |
| `CodeTreeReflect.lean` | 7 +++- |
| `D3BodyPrf.lean` | 14 +++++-- |
| `D3ChainDotPrf.lean` | 59 ++++…---- |
| `D3DottedPrf.lean` | 4 ++ |
| `D3InDotPrf.lean` | 14 ++++--- |
| `EvalRunFnPrf.lean` | 6 +++ |
| `LineWFAssemblePrf.lean` | 15 ++++++- |
| `LineWFCases.lean` | 5 +++ |
| `LineWFGuardPrf.lean` | 4 ++ |
| `LineWFTrackedPrf.lean` | 9 ++-- |
| `PremsBdAllPrf.lean` | 4 +- |
| `PremsOfDotPrf.lean` | 4 +- |
| `SubstTreeReflect.lean` | 22 +++++++++- |

En total, 14 ficheros con 146 inserciones y 30 borrados.

## Comprobaciones

**Delimitadores `/-` y `-/`:** los mismos antes y después en los 14 ficheros. Los recuentos están en `scratchpad/suelo/comentarios/g2/antes.txt` y `despues.txt`, y `diff` sale vacío.

| Fichero | `/-` y `-/` |
|---|---|
| D3ChainDotPrf | 91 y 91 |
| D3BodyPrf | 17 y 17 |
| D3DottedPrf | 10 y 10 |
| D3InDotPrf | 41 y 41 |
| PremsBdAllPrf | 59 y 59 |
| PremsOfDotPrf | 60 y 60 |
| EvalRunFnPrf | 12 y 12 |
| LineWFAssemblePrf | 7 y 7 |
| LineWFGuardPrf | 21 y 21 |
| LineWFTrackedPrf | 46 y 46 |
| LineWFCases | 11 y 11 |
| SubstTreeReflect | 62 y 62 |
| CodeTreeReflect | 28 y 28 |
| CodeCtorKit | 32 y 32 |

**Finales de línea:** comprobados byte a byte. D3ChainDotPrf, D3DottedPrf y LineWFCases siguen enteros en CRLF (1325/1325, 149/149 y 240/240); los otros 11, enteros en LF y sin BOM. Los avisos «LF will be replaced by CRLF» de `git diff` vienen del autocrlf del repositorio y ya salían antes, porque esos ficheros ya estaban en LF.

**Nombres:** no escribí `prf_axiomsCodeT_eq` en ningún sitio.

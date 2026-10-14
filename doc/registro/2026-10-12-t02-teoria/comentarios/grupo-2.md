# Grupo 2 · C3 y D3: lineWF, la reflexión y la cadena punteada

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros (sólo éstos), en `ROBINSON_PlusPlus/Meta/`: `D3ChainDotPrf.lean`, `D3BodyPrf.lean`, `D3DottedPrf.lean`,
`D3InDotPrf.lean`, `PremsBdAllPrf.lean`, `PremsOfDotPrf.lean`, `EvalRunFnPrf.lean`, `LineWFAssemblePrf.lean`,
`LineWFGuardPrf.lean`, `LineWFTrackedPrf.lean`, `LineWFCases.lean`, `SubstTreeReflect.lean`, `CodeTreeReflect.lean`,
`CodeCtorKit.lean`.

Contexto: C3 CERRADO el 2026‑09‑10 (`pcc_lineWF_tracked`, SubstTreeReflect, SIN HIPÓTESIS) y D3 PROBADA el mismo día
(`d3_prf_real` = `d3_prf_of_halves`, PremsBdAllPrf:1300 y D3ChainDotPrf:1148). Muchos comentarios de estos módulos
se escribieron mientras se construían y dan por pendiente lo que hoy es teorema. Patrón: NO borrar la historia; nota
✏️ en la cabecera del módulo o del bloque, y notas puntuales donde una frase en presente sea falsa.

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

- 2‑01 · `D3ChainDotPrf.lean` (también T32 de la auditoría): :12‑17, :40‑42, :50‑57 («`pcc_lineWF_tracked`… no existe
  sin condicionar»), :192‑200, :202‑204, :255‑259, :689‑691, :756, :919‑920, :1010‑1014, :1062‑1072, :1212‑1224 y
  :1228‑1232 («Nada consume todavía este módulo»). Evidencia: D3 está probada a través de este mismo módulo;
  `hbody_of_halves` (≈ :1126) se usa en PremsBdAllPrf (≈ :1297), y `d3_prf_of_halves` (≈ :1148) es `d3_prf_real`.
  → ✏️ en la cabecera: «D3 PROBADA (2026‑09‑10): `d3_prf_real` = `d3_prf_of_halves` (§13); lo que sigue es
  registro»; las tablas de estado, a ✅ o con nota; y el export, «por CONSUMO: D3BodyPrf, PremsBdAllPrf» (compruébalo).
  **A**
- 2‑02 · `D3ChainDotPrf.lean:23` (T10 de la auditoría) · dice en presente que `sondeos/A3IsFCBTracked.lean` «probó»
  algo; hoy ese sondeo no compila (rc 1, error en su :355; `sondeos/pasadas/tabla_adr129.txt`). Nota: «(✏️ …: el
  sondeo es hoy registro: no compila desde …)». No borres la cita. **M**
- 2‑03 · `D3BodyPrf.lean:25` · «El reflector, `pcc_lineWF_tracked_modulo_other`» · La prueba usa
  `pcc_lineWF_tracked` (≈ :115). **A**
- 2‑04 · `D3BodyPrf.lean:276‑277` · «consumirá» · Ya lo consume `hB_premsDotAt`. **M**
- 2‑05 · `D3BodyPrf.lean:311` · «consumidor previsto» · Ya lo es: `d3_prf_real`. **M**
- 2‑06 · `D3DottedPrf.lean:41‑44` · «hC_dot/hI_dot — siguiente ladrillo» · Están cerrados; D3 pasa por este keystone.
  **M**
- 2‑07 · `D3InDotPrf.lean:56` y `:375‑376` · «+`prf_tc_form`» · No existe; la prueba usa `prf_tc_form_numeral` y
  `pcc_to_formCode_imp` (compruébalo). **A**
- 2‑08 · `D3InDotPrf.lean:296` · el nombre correcto es `substCodeF_boundedCarcIn_at` (compruébalo). **m**
- 2‑09 · `PremsBdAllPrf.lean:39‑41` · «una sola obligación abierta, `DEUDA_premsBody`» · La prueba este mismo fichero
  (≈ :1013), junto con `d3_prf_real` (:1300). **A**
- 2‑10 · `PremsOfDotPrf.lean:1042` · «Consumidor previsto: B2» · Ya lo consumen D3BodyPrf (≈ :225) y PremsBdAllPrf
  (≈ :684). **M**
- 2‑11 · `EvalRunFnPrf.lean:32‑34` y `:44‑45` · «`hI_dot` necesita…» · `hI_dot` ya es teorema (D3InDotPrf ≈ :517);
  `pcc_eval_runFn` no existe y nada lo pide. **M**
- 2‑12 · `LineWFAssemblePrf.lean:32‑40`, `:89` y `:95‑103` · «Los 7 tags que faltan… bloqueados tras
  `pcc_eval_substfc`… el único trabajo restante» · `pcc_eval_substfc` existe y los 7 están en SubstTreeReflect
  §8–§10bis. → la marca [HISTÓRICO] que ya lleva LineWFGuardPrf:39 (mírala y usa la misma forma). **A**
- 2‑13 · `LineWFGuardPrf.lean:202` · «LAS DOS OBLIGACIONES QUE QUEDAN» · Están probadas. **M**
- 2‑14 · `LineWFTrackedPrf.lean:413‑415` · `prf_tc_eqc` · No existe; la prueba usa `PrfH_congr_tcFn` y
  `pcc_dot_eqc_symm`. **A**
- 2‑15 · `LineWFTrackedPrf.lean:610` · «invocará» · Ya lo invoca. **m**
- 2‑16 · `LineWFCases.lean:31‑36` · «sus dos consumidores… D3/hC_dot» · Ningún módulo de D3 lo importa
  (compruébalo). **M**
- 2‑17 · `SubstTreeReflect.lean:15‑18`, `:29‑39` y `:319` · «⛔ `pcc_eval_liftfc`… bloquea 4 de 7; `STree` trae sólo
  `sub`» · Ya existe y se usa aquí mismo (≈ :533; ≈ :854 «Lo único que faltaba»); `STree` tiene `lift` y `tcm`. **A**
- 2‑18 · `SubstTreeReflect.lean:1186‑1196` (export) · «entrega tres de los siete… `pcc_eval_liftfc`, que no existe…
  sigue condicional. Nada lo consume» · Falso en las tres cosas: el módulo entrega los 7 y `pcc_lineWF_tracked`, y lo
  consumen D3BodyPrf (≈ :115) y PremsOfDotPrf (≈ :1037). **A**
- 2‑19 · `SubstTreeReflect.lean:1040‑1042` y `:8‑10` · `ind`/`listInd` «a la misma distancia» · Están cerrados. **M**
- 2‑20 · `CodeTreeReflect.lean:52` · «`prf_tc_objAt`» · No existe; es `pcc_tc_objAt` (≈ :225). **m**
- 2‑21 · `CodeTreeReflect.lean:378‑379` · «lo único que queda por hacer» · Ya está hecho (LineWFPropPrf; C3 cerrado).
  **D**
- 2‑22 · `CodeCtorKit.lean:49` · «18 tags pendientes» · Ya no queda ninguno. **M**
- 2‑23 · `CodeCtorKit.lean:154‑155` · «11 call‑sites en cuatro módulos» · el verificador cuenta unos 30 en 8 módulos:
  mídelo con grep y escribe la cifra con su fecha, o quita la cifra. **m**

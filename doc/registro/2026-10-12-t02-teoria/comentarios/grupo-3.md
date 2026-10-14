# Grupo 3 · las evaluaciones y los testigos (Eval*, *Witness*, LiftcCode)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros (sólo éstos), en `ROBINSON_PlusPlus/Meta/`: `EvalArithPrf.lean`, `EvalLiftcPrf.lean`, `EvalLiftfcPrf.lean`,
`EvalNthcPrf.lean`, `EvalSubstfcPrf.lean`, `SubstfcWitnessPrf.lean`, `LiftcCodePrf.lean`, `LiftfcWitnessPrf.lean`,
`CodeWitnessPrf.lean`.

Contexto: C3 CERRADO el 2026‑09‑10 (`pcc_lineWF_tracked`, SIN HIPÓTESIS); `pcc_eval_liftfc` probado
(EvalLiftfcPrf:1241). Muchos comentarios se escribieron mientras se construían. NO borrar la historia; nota ✏️.
La deuda «B6b» (monotonía/debilitamiento de `PrfH`) está pagada: `PrfH_mono` y `PrfH_w1` existen
(`Meta/HilbertDeduction.lean:76/96`); compruébalo antes de escribirlo.
Para los footprints, la tabla de referencia es la que lee `check-footprints.bash` (búscala con grep en la raíz).

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

- 3‑01 · `EvalArithPrf.lean:32`, `:46` y `:52` · «base de `+`… el paso inductivo queda para…» · El módulo prueba el
  paso y `pcc_eval_add` (≈ :536). **A**
- 3‑02 · `EvalArithPrf.lean:154‑156` y `:547‑548` · «Retira 74 copias» · Las copias siguen en los sondeos (compruébalo:
  si siguen, «retira del build»; no escribas una cifra que no midas). **M**
- 3‑03 · `EvalLiftcPrf.lean:871‑874` · «Nada lo consume todavía» · Lo consume EvalLiftfcPrf (≈ :1205, :1223, :1226).
  **A**
- 3‑04 · `EvalLiftcPrf.lean:97‑101` y `:850‑854` · «sale a la raíz… los ocho lemas GENÉRICOS» · El export no los
  saca: bajaron a SubstfcWitness y CodeWitness (compruébalo). **A**
- 3‑05 · `EvalLiftcPrf.lean:884‑891` · «salen con CUATRO» y en la misma línea «hoy no hay cuarto» · Se contradice;
  son los tres de Lean. **A**
- 3‑06 · `EvalLiftcPrf.lean:51‑63` (29 nombres; hoy 36), `:208` (cuatro `rfl`; son cinco), `:132‑141` y punteros en
  :44, :300, :364 y :751 · cuéntalos tú y corrige (o quita la cifra). **m**
- 3‑07 · `EvalLiftfcPrf.lean:6‑9` y `:27‑29` · «`pcc_eval_liftfc` es lo único que separa a C3… deja la obligación
  enunciada» · Este mismo módulo lo prueba (:1241). **A**
- 3‑08 · `EvalLiftfcPrf.lean:1252‑1268` · «Ni la mitad TÉRMINO a nivel arbitrario existe» · Existe; ≈ :1279 ya dice
  SALDADA. **M**
- 3‑09 · `EvalLiftfcPrf.lean:1312‑1316` · «…cerraría los cuatro tags… Nada lo consume» · SubstTreeReflect (≈ :533) lo
  usa. **A**
- 3‑10 · `EvalLiftfcPrf.lean:493` y `:918` · «No se descarga en este tramo» · Se descarga en §9.2. **D**
- 3‑11 · `EvalLiftfcPrf.lean:749` · B6b dada por abierta. **A**
- 3‑12 · `EvalNthcPrf.lean:55‑59` · «`pcc_nthc_succ_code`… — pendiente… siguiente ladrillo» · Está todo en el fichero:
  ≈ :121 y `pcc_eval_nthc` (≈ :367, que usa PremsBdAllPrf ≈ :693). **A**
- 3‑13 · `EvalNthcPrf.lean:243` y `:259` · sustitución mecánica rota: «sustituto de `pcc_dot_cons` (antes
  `prf_tc_cons'`…)» · arregla la frase. **M**
- 3‑14 · `EvalSubstfcPrf.lean:37` · `bridge_isTC1` sólo existe en sondeos. **m**
- 3‑15 · `EvalSubstfcPrf.lean:292`, `:500`, `:506`, `:1576` y `:1581` · `pcc_eval_substtsc'`, con prima, sólo existe en
  sondeos (compruébalo; el del build, sin prima o con otro nombre). **m**
- 3‑16 · `EvalSubstfcPrf.lean:1521‑1523` · «CERO axiomas de Lean… cero hipótesis» · El footprint es `[propext,
  Classical.choice, Quot.sound]` y el teorema tiene dos hipótesis (compruébalo). → «Footprint: los tres de Lean;
  ningún `axiom` del proyecto; sólo las dos guardas.» **A**
- 3‑17 · `EvalSubstfcPrf.lean:1590` y `:1607` · «ningún sondeo consume… consumidor previsto C3» · Lo consume C3
  (SubstTreeReflect ≈ :471). **M**
- 3‑18 · `SubstfcWitnessPrf.lean:398‑400` · «`prf_nil_or_cons` vive en EvalLiftcPrf, en rojo» · Es al revés: se
  declara aquí (≈ :422). **A**
- 3‑19 · `SubstfcWitnessPrf.lean:1481` · «`PrfH_congr_substfc3` vive en BdAllIntroPrf, en ROJO» · Vive en
  NumCodeClosedPrf (≈ :88). **A**
- 3‑20 · `SubstfcWitnessPrf.lean:543` · «Al promover…» · Ya está promovido. **M**
- 3‑21 · `LiftcCodePrf.lean:27` · «CONTENIDO EXACTO PROPUESTO» · Ya es el módulo promovido. **M**
- 3‑22 · `LiftcCodePrf.lean:58‑59` · colisión con un gemelo que se borró en B8b (compruébalo). **A**
- 3‑23 · `LiftcCodePrf.lean:227` · «al promover B2…» · Ya se promovió. **M**
- 3‑24 · `LiftcCodePrf.lean:1426` · B6b dada por abierta. **A**
- 3‑25 · `LiftcCodePrf.lean:40` · «cuatro axiomas»; son cinco (compruébalo). **D**
- 3‑26 · `LiftcCodePrf.lean` punteros en :53, :613, :655, :760, :1271 y :1297 · compruébalos y corrígelos o pásalos a
  símbolo. **m**
- 3‑27 · `LiftfcWitnessPrf.lean:17` · `prf_hasWitArgs_liftsc (v Y)` · No existe; es `prf_hasWitArgs_liftsc_of (w v Y)`
  (≈ :357), con otro antecedente. **A**
- 3‑28 · `CodeWitnessPrf.lean:41` · «Cero axiomas de Lean» · Su fila de footprint es `[propext, Quot.sound]`; el
  proyecto ya corrigió esta misma frase en EvalPredPrf:29 (mírala). → «cero `axiom` del proyecto». **D**
- 3‑29 · `CodeWitnessPrf.lean:50‑53` (T31) · nombra secciones y namespaces que no existen (compruébalo). **M**
- 3‑30 · `CodeWitnessPrf.lean:1396` · «el análogo del sort FÓRMULA, que no existe» · Existe: `prf_hasWitF_liftfc`. **M**
- 3‑31 · `CodeWitnessPrf.lean:2038` · cita `Probe/`, que no está versionado (compruébalo con `git ls-files Probe`). **D**
- 3‑32 · `CodeWitnessPrf.lean:2170‑2173` · cifras sin fecha («214… 50 de 57») · ponles ámbito («medido el …» si sabes
  cuándo, con `git blame`) o márcalas. **m**

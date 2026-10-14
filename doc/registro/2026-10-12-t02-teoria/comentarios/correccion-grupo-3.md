# Corrección de comentarios · grupo 3 (evaluaciones y testigos)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

## Informe · grupo 3 (Eval\*, \*Witness\*, LiftcCode)

Los 32 hallazgos se sostienen contra el fuente: no rechazo ni omito ninguno. Sólo he tocado comentarios y sólo en mis nueve ficheros. No ejecuté `lake` ni `lean`, y git sólo en lectura. En los nueve, el número de `/-` y de `-/` es el mismo antes y después, y se conservan los finales de línea (CRLF en EvalLiftcPrf, EvalLiftfcPrf y LiftcCodePrf; LF en los demás). Todas las notas llevan el guion U+2011.

Al retomar tras el corte, `git diff` mostraba editado sólo `EvalArithPrf` (3‑01 y 3‑02). No repetí nada.

### Por hallazgo (línea = la de después de editar)

**EvalArithPrf**
- **3‑01** · :53 · NOTA. Evidencia: `pcc_eval_add_succ_imp` (:452), `prf_eval_add_all` (:528), `pcc_eval_add` (:541); `pcc_ax5_inst` = `pcc_axiom_inst2` de `ax5` (MpCodePrf:250‑254). Texto: «(✏️ 2026‑10‑14, ADR‑134: hoy el módulo no se queda en la base; más abajo están el paso, `pcc_eval_add_succ_imp` (sobre `pcc_ax5_computed`, que instancia `pcc_ax5_inst`, el `pcc_axiom_inst2` de `ax5`), la inducción interna `prf_eval_add_all` y la evaluación para `a`, `b` arbitrarios, `pcc_eval_add`. El título y «cierra la BASE» son los de §21.)»
- **3‑02** · :159‑161 y :552‑557 · CORREGIDO + «decía». Evidencia: el commit `178b10b` sólo tocó EvalArithPrf (`git show --stat`). Medí hoy, con el criterio del commit (por cada uno de los nueve nombres, los sondeos que lo declaran): las **74** copias siguen en `sondeos/`.
  - :159‑161: «Promoverlos una vez los hace innecesarios en todos ellos (✏️ 2026‑10‑14: decía «los quita de todos ellos»; B3 no tocó `sondeos/` y las copias siguen allí, nueve de cada uno, medido el 2026‑10‑14).»
  - :552‑557: «Deja obsoletas 74 copias…» seguido de «-- (✏️ 2026‑10‑14: decía «Retira»; B3 no borró ninguna: las 74 siguen en `sondeos/`, medido el 2026‑10‑14 con el criterio del commit `178b10b`: por cada uno de los nueve nombres, los sondeos que lo declaran.)»

**EvalLiftcPrf**
- **3‑03** · :897‑900 · NOTA. Evidencia: EvalLiftfcPrf:1205 (`DESCENSO_at_lista_imp`) y :1223/:1226 (`DESCENSO_at_imp`). `pcc_eval_liftc_at`, `pcc_eval_liftsc_at` y `DESCENSO_at_hasWit` no los usa ningún código (grep en `ROBINSON_PlusPlus/` y `sondeos/`). Texto: «(✏️ 2026‑10‑14, ADR‑134: ya lo consume `Meta/EvalLiftfcPrf.lean`: `DESCENSO_at_lista_imp` en `casoAtomL_thm` y `DESCENSO_at_imp`, dos veces, en `casoEqL_thm`. `pcc_eval_liftc_at`, `pcc_eval_liftsc_at` y `DESCENSO_at_hasWit` no los usa ningun codigo de `ROBINSON_PlusPlus/` ni de `sondeos/`, medido con grep; solo los citan comentarios.)»
- **3‑04** · :105‑107 y :872‑876 · NOTA. Evidencia: declarados en SubstfcWitnessPrf:402‑422 y CodeWitnessPrf:617/629/673/702; los exportan SubstfcWitnessPrf:2079 y CodeWitnessPrf:2178‑2183; los dos `substF_*` los exporta LiftcCodePrf:1665.
  - :105: «(✏️ 2026‑10‑14, ADR‑134: ya no los entrega este modulo: bajaron a `Meta/SubstfcWitnessPrf.lean` (ADR‑019, ver §2), que los exporta a la raiz.)»
  - :872: «(✏️ 2026‑10‑14, ADR‑134: el `export` de abajo ya no saca (c) ni la mitad de (b). De (b) quedan `liftF_targetLift`/`liftF_targetLiftsc`: los dos `substF_*` los exporta `LiftcCodePrf`. Los ocho de (c) llegan a la raiz por los `export` de `Meta/SubstfcWitnessPrf.lean` (los cuatro de §2) y de `Meta/CodeWitnessPrf.lean`, `SinWTs` (los cuatro de §3–§4). Salen ademas `PrfH_congr_targetLiftsc` y los cinco de A5, §7bis.)»
- **3‑05** · :910‑914 · NOTA de cabecera del bloque. Evidencia: en la tabla de `check-footprints.bash`, todos los sustantivos del módulo dan `Classical.choice,Quot.sound,propext` y los puentes dan `-`; el build de hoy (`build_1014b`) da lo mismo. La lista ya había perdido el cuarto en la edición de ADR‑026 (`24b3550`). Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — hoy los resultados sustantivos salen con los TRES de Lean, `[propext, Classical.choice, Quot.sound]`, sin cuarto ni hipotesis de ancla (la clase `AnclaEq` se retiro con ADR‑118), y los tres puentes de la tabla de `check-footprints.bash`, con ninguno; lo que sigue describe el estado de antes de ADR‑026, cuando el cuarto era el axioma del ancla (la lista ya lo perdio en ADR‑026), y su aviso contra «net-0 puro» ya no vale.»
- **3‑06** · NOTA y CORREGIDO, en seis sitios:
  - :65 · el módulo declara hoy 36 nombres (los conté): «(✏️ 2026‑10‑14, ADR‑134: hoy declara **36**: los 6 puentes, 19 de los 23 —los cuatro `nilOrCons*`/`prf_nil_or_cons*` de §2 bajaron a `Meta/SubstfcWitnessPrf.lean` (ADR‑019)— y los 11 de A5, §7bis.)»
  - :223 · el «cuatro» se refiere a los cuatro `*_es_el_del_sondeo`, así que lo aclaro sin cambiar el sentido: «Estos cuatro `rfl` —los `*_es_el_del_sondeo`; el quinto, `iz_inv_es_…`, es el del duplicado— son la MEDIDA…».
  - :136‑143 · tabla de `import`: nota de registro con lo que se ha movido (medido con grep; en `075778a` estaban donde dice la tabla). `PrfH_lt_subst2` está hoy en ChainPrf y de BoundedInPrf el módulo ya no usa nada; `objList` está en Minimal/Axioms; `prf_substtc_termCode_zero` en CodeCtorKit; `prf_eq_*` se declaran en ReprPrf, no en ArithPrf, y de los tres sólo se usa `prf_eq_symm`; nueve símbolos más ya no aparecen en el código.
  - :44 · «(✏️ 2026‑10‑14: hoy esta en `Meta/LiftcCodePrf.lean:1278`, un cuarto valor.)»
  - Punteros quitados y citados por nombre: :316 (`:680 y :692`; hoy :617/:629), :380 (`:195,203`; hoy :192/:200) y :767 (`:752, :757` y `:158, :161`; hoy LiftcCodePrf:1173/1178 y Representability:104/107).

**EvalLiftfcPrf**
- **3‑07** · :10‑12 y :32‑33 · NOTA. Evidencia: `pcc_eval_liftfc` (:1252), `pcc_lineWF_tracked` (SubstTreeReflect:1157, «SIN HIPÓTESIS»).
  - :10: «(✏️ 2026‑10‑14, ADR‑134: este mismo módulo la prueba —`pcc_eval_liftfc : DEUDA_evalLiftfc`, §11, y su forma desplegada `pcc_eval_liftfc_wit`— y C3 está cerrado desde el 2026‑09‑10: `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean`), sin hipótesis.)»
  - :32: «(✏️ 2026‑10‑14, ADR‑134: A5 está hecha —`pcc_eval_liftc_at`, `Meta/EvalLiftcPrf.lean` §7bis— y los cuatro tags, cerrados con C3.)»
- **3‑08** · :1262‑1265 · NOTA de cabecera de §12. Evidencia: `prf_hasWit_liftc_at` (LiftfcWitnessPrf:345) y `deuda_hasWitF_liftfc` (:652). Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — la deuda está SALDADA (`deuda_hasWitF_liftfc`, en `Meta/LiftfcWitnessPrf.lean`; ver el docstring de abajo) y la mitad TÉRMINO a nivel arbitrario existe: `prf_hasWit_liftc_at`, en el mismo módulo; lo que sigue describe el estado de antes, medido el 2026‑09‑10.»
- **3‑09** · :1331‑1333 · NOTA. Evidencia: SubstTreeReflect:533, dentro de `PrfH_tc_objAt` (:428). Texto: «(✏️ 2026‑10‑14, ADR‑134: ya lo consume: `PrfH_tc_objAt` (`Meta/SubstTreeReflect.lean`) usa `pcc_eval_liftfc_wit` en su caso `lift`, y C3 está cerrado: `pcc_lineWF_tracked`, en el mismo fichero.)»
- **3‑10** · :498‑499 y :928‑929 · NOTA. Evidencia: `casoAtomL_thm`/`casoEqL_thm` en §9.2, y :1247 `pcc_eval_liftfc_isFC1 := pcc_eval_liftfc_modulo_2 casoAtomL_thm casoEqL_thm`.
  - :498: «(✏️ 2026‑10‑14: se descarga en §9.2, `casoAtomL_thm`, con `DESCENSO_at_lista_imp`, la forma implicación de `pcc_eval_liftsc_at`.)»
  - :928: «(✏️ 2026‑10‑14: los dos se descargan en §9.2 —`casoAtomL_thm`, `casoEqL_thm`— y `pcc_eval_liftfc_isFC1` aplica este lema a ambos.)»
- **3‑11** · :756‑757 · NOTA. Evidencia: HilbertDeduction:54 («deuda B6b, saldada el 2026‑09‑11») y :76/:96. Texto: «(✏️ 2026‑10‑14, ADR‑134: B6b está saldada desde el 2026‑09‑11: `PrfH_mono` y `PrfH_w1`, en `Meta/HilbertDeduction.lean`; este núcleo se quedó escrito con las HI como hipótesis objeto.)»

**EvalNthcPrf**
- **3‑12** · :61‑63 · NOTA. Evidencia: `pcc_nthc_succ_code` (:121) y `pcc_eval_nthc` (:375), que usan D3BodyPrf:121/218 y PremsBdAllPrf:678/715. Texto: «(✏️ 2026‑10‑14, ADR‑134: hoy el módulo entrega las dos ecuaciones y la inducción: `pcc_nthc_succ_code` y la evaluación acotada `pcc_eval_nthc`, que consumen `D3BodyPrf` y `PremsBdAllPrf`.)»
- **3‑13** · :246‑249 y :265‑267 · CORREGIDO + «decía». También quedan emparejados los acentos graves. Evidencia: `prf_tc_cons'` era de CÓDIGO (`tcFn (cons a b) =eq consT …`) y se retiró con `ax_tc_cons` (`6f66e61`); `pcc_dot_cons` es interno (DotConsPrf:335) y el molde lo usa.
  - Título: «### El sustituto de `prf_tc_cons'` (retirado con `ax_tc_cons`) en esta capa», más la nota «(✏️ 2026‑10‑14: el título decía que era el sustituto de `pcc_dot_cons`, «antes `prf_tc_cons'`», resto de una sustitución mecánica: `pcc_dot_cons` es el transporte INTERNO que usa el molde.)»
  - Docstring: «Sustituye al viejo transporte por `prf_tc_cons'` (retirado con `ax_tc_cons`), que era de CÓDIGO; éste es INTERNO y se apoya en `pcc_dot_cons`. (✏️ 2026‑10‑14: decía que el transporte de CÓDIGO era `pcc_dot_cons`, «antes `prf_tc_cons'`»; `pcc_dot_cons` es interno.)»

**EvalSubstfcPrf**
- **3‑14** · :37‑38 · CORREGIDO. Evidencia: `bridge_isTC1` sólo existe en sondeos/EvalSubstfcPrf:7629 y HasWitFReal:7636; `isTC1` se declara una sola vez (Minimal/Axioms:1254). Texto: «(`bridge_isTC1` en el sondeo; en el build no hace falta: hay un solo `isTC1`, el de `Minimal/Axioms.lean`)».
- **3‑15** · :293, :501, :507, :1579 y :1584 · CORREGIDO, sin nota: `pcc_eval_substtc'`/`pcc_eval_substtsc'` pasan a `pcc_eval_substtc`/`pcc_eval_substtsc`. Evidencia: EvalSubsttcPrf:1251/1256, con la misma firma que las primadas del sondeo. Dejo :280, que habla del sondeo, donde la prima sí existe.
- **3‑16** · :1524‑1526 · CORREGIDO + «decía». Evidencia: la tabla da `Classical.choice,Quot.sound,propext`; la firma lleva `hws` y `hfc`; hay 0 `axiom` en el build. Texto: «Footprint: los tres de Lean; ningún `axiom` del proyecto, cero `sorry`, y sólo las dos guardas (`hws`, `hfc`): ninguno de los ocho `Caso*` queda como hipótesis. (✏️ 2026‑10‑14: decía «CERO axiomas de Lean, cero `sorry`, cero hipotesis».)»
- **3‑17** · :1614‑1617 · NOTA. Evidencia: SubstTreeReflect:471 (`pcc_eval_substfc_wit`) y :494/:621; sondeos/RosserReflexion.lean:131 (rc 0 en `tabla_adr129.txt`). Texto: «(✏️ 2026‑10‑14, ADR‑134: hoy sí hay consumo. C3, cerrado con `pcc_lineWF_tracked`, usa `pcc_eval_substfc_wit` en `PrfH_tc_objAt` y `pcc_congr_substfcT_arg2_code`, los dos en `Meta/SubstTreeReflect.lean`; y el sondeo `sondeos/RosserReflexion.lean` usa `pcc_eval_substfc_wit` (compila: rc 0 en `sondeos/pasadas/tabla_adr129.txt`, 2026‑10‑05).)»

**SubstfcWitnessPrf**
- **3‑18** · :401‑403 · NOTA. Evidencia: :402‑422; el mismo commit que escribió la frase (`e68c313`) borró la copia de EvalLiftcPrf (en `e68c313^` estaba en EvalLiftcPrf:311); EvalLiftcPrf compila en `build_1014b`. Texto: «(✏️ 2026‑10‑14, ADR‑134: es al revés desde esta misma promoción, `e68c313`: `nilOrCons*` y `prf_nil_or_cons*` se declaran AQUÍ y `Meta/EvalLiftcPrf.lean` ya no los declara —los recibe por el `export` de este módulo—; y `EvalLiftcPrf` compila, build del 2026‑10‑14.)»
- **3‑19** · :1487‑1489 · NOTA. Evidencia: NumCodeClosedPrf:92; `e68c313` lo movió desde BdAllIntroPrf; BdAllIntroPrf compila en `build_1014b`. Texto: «(✏️ 2026‑10‑14, ADR‑134: vive en `Meta/NumCodeClosedPrf.lean`, adonde bajó en esta misma promoción, `e68c313`; aquí no se reproduce, y `BdAllIntroPrf` compila, build del 2026‑10‑14.)»
- **3‑20** · :547‑549 · NOTA. Evidencia: `prf_in_nthc` se declara una sola vez en el build; la copia de sondeos/MergeTestigos.lean:63 sigue. Texto: «(✏️ 2026‑10‑14, ADR‑134: ya está promovido —este fichero es el módulo de producción— y en el build `prf_in_nthc` es una sola constante, la de aquí; la copia de `sondeos/MergeTestigos.lean` sigue fuera del build.)»

**LiftcCodePrf**
- **3‑21** · :29‑30 · NOTA. Evidencia: :34 («promovido… el 2026‑09‑02»); `git ls-files Probe` da 0. Texto: «(✏️ 2026‑10‑14, ADR‑134: ya no es una propuesta: es el módulo promovido el 2026‑09‑02, como dice el párrafo de abajo; `Probe/` no está versionado.)»
- **3‑22** · :66‑67 · NOTA. Evidencia: sólo queda `prf_congr_liftc` en NumCodeClosedPrf:57; el gemelo se borró en `c937b30` («B8b SALDADA»). Texto: «(✏️ 2026‑10‑14, ADR‑134: esa colisión ya no existe: el `prf_congr_liftc` gemelo de `SinWTs` se borró en B8b, `c937b30`, y hoy sólo queda el de `NumCodeClosedPrf`.)»
- **3‑23** · :235‑237 · NOTA. Evidencia: los puentes `rfl` de EvalLiftcPrf §0; sondeos/DescensoLiftc.lean:79 sigue redefiniendo. Texto: «(✏️ 2026‑10‑14, ADR‑134: B2 ya se promovió, `Meta/EvalLiftcPrf.lean`, y consume éstas —lo miden sus puentes `rfl` de §0—; el sondeo no se tocó y sigue redefiniéndolas, fuera del build.)»
- **3‑24** · :1436‑1437 · NOTA. Evidencia: la misma que 3‑11. Texto: «(✏️ 2026‑10‑14, ADR‑134: B6b está saldada desde el 2026‑09‑11: `PrfH_mono` y `PrfH_w1`, en `Meta/HilbertDeduction.lean`; estas cadenas se quedaron escritas en `PrfH`.)»
- **3‑25** · :45‑47 · NOTA (caso A, no error). Hoy hay cinco axiomas `ax_liftc*`/`ax_liftsc*` y cinco imágenes `pcc_*_code`. En `21c8a6b`, que escribió «cuatro», había cuatro imágenes; `pcc_liftc_var_lt_code` entró con `6c07958` (A5). Texto: «(✏️ 2026‑10‑14, ADR‑134: hoy son cinco imágenes dotadas, aquí y en «Lo que SI se promueve»: A5, `6c07958`, añadió `pcc_liftc_var_lt_code`, la de `ax_liftc_var_lt`.)»
- **3‑26** · CORREGIDO, sin nota; punteros pasados a símbolo.
  - Tabla :58‑61. Además del :53 de la lista, también estaban desplazados :54‑56 (hoy CodeWitnessPrf:80/84, EvalCarcNthcPrf:68, Sigma1AtomPrf:129).
  - :622 (Delta0ReflectPrf, hoy :244), :664 (CodeCtorKit, hoy :339), :769 («por el `export` de `EvalRunFnPrf`», hoy :165), :1280 («los dos usos de `PrfH_congr_targetLift`», hoy :1280/:1283) y :1306.

**LiftfcWitnessPrf**
- **3‑27** · :17 y :21‑22 · CORREGIDO + «decía». Evidencia: `prf_hasWitArgs_liftsc` no existe en ningún sitio; lo que hay es :360 `prf_hasWitArgs_liftsc_of (w v Y) : Prf (land (wfAll1 w) (argsIn w Y) ⇒ …)`.
  - :17: «prf_hasWitArgs_liftsc_of (w v Y) : Prf (wfAll1 w ∧ argsIn w Y ⇒ hasWitArgs (liftsc v Y))   -- vía la conjuntiva»
  - Nota: «(✏️ 2026‑10‑14: la segunda línea decía `prf_hasWitArgs_liftsc (v Y) : Prf (hasWitArgs Y ⇒ …)`, que no existe; la mitad de lista expuesta es `prf_hasWitArgs_liftsc_of`, con el testigo `w` explícito.)»

**CodeWitnessPrf**
- **3‑28** · :41‑43 · CORREGIDO + «decía». Evidencia: la fila de la tabla y el build de hoy dan `SinWTs.prf_isTermCodeE1_of_In` = `[propext, Quot.sound]`; hay 0 `axiom` en el build. Texto: «Cero `axiom` del proyecto, cero `sorry`; los de Lean, sí: `SinWTs.prf_isTermCodeE1_of_In` sale `[propext, Quot.sound]` (tabla de `check-footprints.bash`). (✏️ 2026‑10‑14: decía «Cero axiomas de Lean».)»
- **3‑29** · :53‑58 · CORREGIDO + «decía». Evidencia: el fichero sólo tiene `S_Clausura`/`SinWTs`, `S_Ens`/`ENS` y `S_HW`/`HW`, y así era ya en `7be9ee8`; el rótulo se copió tal cual de sondeos/HasWitFRealMin.lean:14; `CRIT_hasWit_lift` está en `ENS` (:1404). Texto: «Rotulo heredado de `sondeos/HasWitFRealMin.lean` (copia de `sondeos/SubstfcEx.lean` lineas 46-4111, segun aquel). Aqui hay tres secciones: `S_Clausura` (namespace `SinWTs`), `S_Ens` (`ENS`) y `S_HW` (`HW`). (✏️ 2026‑10‑14: decía «secciones S_Clausura, S_Descenso y S_Paso2 … Aportan `DescMutua.DESCENSO_hasWit`, `SinWTs.CRIT_hasWit_lift` y todo el KIT unario `Paso2.*`»; en este fichero nunca hubo `S_Descenso`, `S_Paso2`, `DescMutua` ni `Paso2`, y `CRIT_hasWit_lift` vive en `ENS`.)»
- **3‑30** · :1401‑1403 · NOTA. Evidencia: LiftfcWitnessPrf:638. Texto: «(✏️ 2026‑10‑14, ADR‑134: hoy existe, a nivel arbitrario: `prf_hasWitF_liftfc (v X) : Prf (hasWitF X ⇒ hasWitF (liftfc v X))`, en `Meta/LiftfcWitnessPrf.lean`.)»
- **3‑31** · :2046‑2048 · NOTA. Evidencia: `git ls-files Probe` da 0 y `.gitignore:30` ignora `Probe/`; el lema versionado está en sondeos/HasWitFRealMin.lean:2001. Texto: «(✏️ 2026‑10‑14, ADR‑134: `Probe/` no está versionado —lo ignora `.gitignore`—; la copia versionada del mismo lema está en `sondeos/HasWitFRealMin.lean`.)»
- **3‑32** · :2182‑2183 · NOTA. Evidencia: `git blame` da `03f9523` (2026‑09‑04). Texto: «(✏️ 2026‑10‑14: cifras medidas al escribir este bloque, el 2026‑09‑04, `03f9523`; no se han re‑medido.)»

### NUEVAS
- **N1** · `EvalLiftfcPrf.lean:1281` · CORREGIDO (puntero). Decía `Meta/SubstfcWitnessPrf.lean:1936`; `prf_hasWit_liftc` está hoy en :1937. Queda `(`Meta/SubstfcWitnessPrf.lean`)`.
- Los punteros LiftcCodePrf :54‑56 están dentro de 3‑26.

Vi y no toqué tres cosas:
- `EvalLiftcPrf.lean:922` conserva el nombre `prf_axiomsCodeT_eq` en texto viejo. Queda cubierto por la nota de 3‑05 y no lo reescribí.
- `EvalLiftcPrf.lean:62` dice «5 controles negativos (`example`)». Hay 5 `example`, pero sólo 3 son `fail_if_success`. No medí el estado histórico.
- `EvalLiftfcPrf.lean:497` atribuye el consumo a `pcc_eval_liftc_at`; el código usa `DESCENSO_at_imp`. Es impreciso, no falso.

### Ficheros tocados (`git diff --stat`) y delimitadores

| fichero | stat | `/-` antes→después | `-/` antes→después |
|---|---|---|---|
| `ROBINSON_PlusPlus/Meta/EvalArithPrf.lean` | 14 (+11 −3) | 50→50 | 50→50 |
| `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean` | 50 | 44→44 | 44→44 |
| `ROBINSON_PlusPlus/Meta/EvalLiftfcPrf.lean` | 29 | 70→70 | 70→70 |
| `ROBINSON_PlusPlus/Meta/EvalNthcPrf.lean` | 12 | 19→19 | 19→19 |
| `ROBINSON_PlusPlus/Meta/EvalSubstfcPrf.lean` | 24 | 81→81 | 81→81 |
| `ROBINSON_PlusPlus/Meta/SubstfcWitnessPrf.lean` | 13 | 104→104 | 104→104 |
| `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean` | 33 | 73→73 | 73→73 |
| `ROBINSON_PlusPlus/Meta/LiftfcWitnessPrf.lean` | 5 | 25→25 | 25→25 |
| `ROBINSON_PlusPlus/Meta/CodeWitnessPrf.lean` | 24 | 98→98 | 98→98 |

En total, 9 ficheros: +154 −50. El recuento de CR coincide con el número de líneas en los tres ficheros CRLF y es 0 en los seis LF. La línea base está en `scratchpad/suelo/comentarios/g3/base.txt`. Falta que el coordinador compile.

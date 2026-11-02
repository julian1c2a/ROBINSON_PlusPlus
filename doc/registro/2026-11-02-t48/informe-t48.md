# T48 · Los cuatro de «promover 4 y barrer», re‑medidos (2026‑11‑02)

**Last updated:** 2026-11-02 — lo que entregó el agente de T48 (ADR‑247), tal cual.

Triaje de `Probe/B3_planos_dedup_kit.lean`, `Probe/B3_planos_dedup.lean`, `Probe/VER_extra.lean` y
`Probe/CritRefl_anidado.lean` (más los hermanos `B3_planos_dedup_funcc3.lean` y `B3_planos_dedup_opens.lean`), contra
el build de `master` `4a0c00e`. Nada se ha tocado en RPP, en `Probe/` ni en FOL (comprobado al final: `git status`
limpio y los seis ficheros con el mismo md5 que su copia en `orig/MD5SUMS`).

## 0 · Veredicto

| fichero | compila hoy (MEDIDO) | qué aporta que el build no tenga | recomendación |
|---|---|---|---|
| `B3_planos_dedup_kit.lean` | ❌ 2 errores → 1 tras renombrar (de fondo) | sólo el genérico `pcc_congr_hole_code` | **PROMOVER el genérico, ADAPTADO**, como `sondeos/CongruenciaHueco.lean` (una sola fila para los dos B3) |
| `B3_planos_dedup.lean` | ❌ 14 → 9 tras renombrar (todos de fondo) | el MISMO genérico (idéntico al byte: md5 `2c3635c9…`, 15 líneas) | va en el mismo `CongruenciaHueco.lean`; el resto, **DESCARTAR** |
| `VER_extra.lean` | ✅ tal cual (3 s) | tres pares de teoremas con el mismo enunciado y dos nombres, vivos y sin registrar | **PROMOVER** como `sondeos/DuplicadosPorEnunciado.lean` (cabecera nueva, código intacto) |
| `CritRefl_anidado.lean` | ❌ 34 → 16 tras renombrar (de fondo) | nada: el build lo tiene, y más fuerte | **DESCARTAR** |
| `B3_planos_dedup_funcc3.lean` (hermano) | ❌ 4 → ✅ 0 tras renombrar | nada (el KIT TERNARIO está en `EvalArithPrf`) | **DESCARTAR** |
| `B3_planos_dedup_opens.lean` (hermano) | ❌ 6 → 2 tras renombrar (de fondo) | nada | **DESCARTAR** |

Los hermanos **no son variantes** de los cuatro: son los otros dos arneses de la misma auditoría (§2.1).

## 1 · Cómo se midió

* Clon compartido en `t48/rpp` (`git clone --shared`, `4a0c00e`); los ficheros, copiados a `t48/rpp/Probe/` (ignorado
  por el `.gitignore` del clon). Orden, desde la raíz del clon (`compila.bash`, uno a la vez, `timeout 900`):
  `LEAN_PATH='<FOL>\.lake\build\lib\lean;<RPP>\.lake\build\lib\lean;<toolchain v4.35.0>\lib\lean' LEAN_NUM_THREADS=2
  lean.exe -DautoImplicit=false -DrelaxedAutoImplicit=false <fichero>`. Los dos `-D` son los `leanOptions` del lakefile
  (los que pasa `lake lean` y usa `check-sondeos.bash`): sin ellos un nombre perdido en una firma se volvería variable.
  No se ejecutó `lake` (ni `lake lean`: podría reconstruir).
* El arnés se vio funcionar en los dos sentidos antes de medir: un fichero que importa `CodeCtorKit` compila (rc 0) y
  otro con un nombre inexistente y una variable suelta da rc 1 con 3 errores, uno de ellos la nota «autoImplicit option
  is set to false» (`salidas/humo*.{meta,out}`).
* «Renombre» = lo que se arregla cambiando un nombre o una ruta; «fondo» = la API cambió (otra firma). Las versiones
  renombradas están en `medidas/ren/`; cada salida, con su md5 y su orden, en `salidas/*.meta`.
* Cada control nuevo se vio fallar con un mutante (cuatro: `medidas/*_MUTANTE.lean`, `salidas/*-MUTANTE.*`).

## 2 · Fichero a fichero

### 2.1 · `B3_planos_dedup_kit.lean` y `B3_planos_dedup.lean` (y los dos hermanos)

**Qué son.** Los cuatro arneses del «ángulo (B)» de la auditoría de duplicación de `sondeos/SubstfcPlanos.lean`
(2026‑09‑04; ese sondeo está hoy archivado en `archivo/sondeos-2026-10`). Cada uno copia byte a byte la lista de
`import` de un módulo de DESTINO: lo que compila ahí cabe en ese módulo sin ciclo (ADR‑019).

| arnés | imports de | qué probaba |
|---|---|---|
| `B3_planos_dedup.lean` (1) | `Meta/LiftcCodePrf.lean` (25 módulos) | `prf_substtc_binK_at` ⊐ `prf_substtc_binT_at` (subsunción al revés); el genérico `pcc_congr_hole_code` y, de él, la «octava copia» `pcc_congr_substfcT_arg3_code`; el censo de las 34 declaraciones del sondeo |
| `B3_planos_dedup_kit.lean` (2) | `Meta/CodeCtorKit.lean` (2 módulos) | `binK` ⊐ `binT`; el genérico da el enunciado LITERAL de 5 de las 7 copias de entonces |
| `B3_planos_dedup_opens.lean` (3) | el barril y los `open` del sondeo | los cinco duplicados POR NOMBRE del sondeo son *drop‑in*; `binct` ⊐ seis constructores objeto |
| `B3_planos_dedup_funcc3.lean` (4) | `Meta/EvalArithPrf.lean` (4 módulos) | el KIT TERNARIO (9 declaraciones) cabe en `EvalArithPrf` |

Dependen sólo de `ROBINSON_PlusPlus.Meta.*`; cero axiomas nuevos, cero `sorry` (en su fecha).

**Compilación (MEDIDO).**

| fichero | original | tras renombrar | causas |
|---|---|---|---|
| `_kit` | rc 1, 2 errores | rc 1, 1 | renombre: `strCode "liftc"` (D7: `strCode` toma `List Char`; `sym!"liftc"`). Fondo: l.160, `PrfH_leibniz_apply` pide hoy `hasWitF Ac`, `hasWit X`, `hasWit Y` |
| `B3_planos_dedup` | rc 1, 14 | rc 1, 9 | renombre: cinco `strCode "…"`. Fondo: l.267 (la misma guarda); l.295, `pcc_congr_binT_2_code` tiene hoy tres auto‑parámetros `hw_auto` que no se rellenan con `A X Y` abstractos (6 errores); l.325 y l.331, `pcc_thm_inst4`/`pcc_axiom_inst4` piden cuatro `hasWit` |
| `_funcc3` | rc 1, 4 | **rc 0** | sólo `strCode "substfc"` (dos líneas; los otros dos errores, en cascada) |
| `_opens` | rc 1, 6 | rc 1, 2 | renombre: `strCode`, y `LiftcCodePrf.prf_substtc_termCode_closed` → `CodeCtorKit.prf_substtc_termCode_closed` (subió con `binK`). Fondo: `pcc_thm_inst4`/`pcc_axiom_inst4` |

La guarda de fondo es la de testigo de **ADR‑020 (2026‑09‑05), un día POSTERIOR a los arneses**: el genérico se midió
contra la API de antes y nunca contra la de después.

**¿Está ya en el build? (MEDIDO: `medidas/T48_YaEnElBuild.lean`, rc 0; cada `example` lleva el enunciado del arnés y se
cierra con la constante del build por su nombre completo; el mutante falla.)** Todo, salvo el genérico:

* El KIT TERNARIO (9) → `Meta/EvalArithPrf.lean` (l. 165‑210).
* `binK`, `binK_binT`, `prf_congr_binK`, `prf_substtc_binK_at` → `Meta/CodeCtorKit.lean` (l. 125‑136, `export` l. 412),
  con los tres `prf_substtc_termCode_*` (l. 110‑121).
* La subsunción al revés, **ejecutada**: `prf_substtc_binT_at` es corolario de una línea de `prf_substtc_binK_at`
  (`Meta/LiftcCodePrf.lean` l. 207‑213, «eran DOCE lineas de `refine`, y son una»); `prf_substtc_binT`, su instancia a
  nivel `zero` (`CodeCtorKit` l. 179‑187); `prf_substtc_funccT_at`, `binT_at 1`.
* `binct`, `binct_implc/_andc/_orc`, `AXBOT_BODY(_ok)`, `AXBIN_BODY`, `AXBIN_impl/_and/_or` → `Meta/SubstfcCodePrf.lean`
  (no en `Minimal/Axioms.lean`, como proponía el arnés).
* `pcc_congr_substfcT_arg3_code` → `Meta/SubstfcCodePrf.lean:85`, con su prueba propia de 26 líneas (la «octava copia»);
  `pcc_thm_inst4`/`pcc_axiom_inst4` → `Meta/MpCodePrf.lean:311/376`, con la guarda.
* NO están: `pcc_congr_hole_code` (grep en el árbol: sólo prosa; y compilado: «Unknown identifier» en `CodeCtorKit`,
  `salidas/humo-rojo.out`) y tres `rfl` triviales de `_opens` §3 (`binct_funcc/_atomc/_eqc`), que el propio arnés decía
  que «NO obliga[n] a bajar nada».

**El patrón, hoy (MEDIDO por `git grep "^theorem pcc_congr_"` y leyendo cada prueba):** 19 copias en 12 módulos
—exactamente la cifra del triaje—, 419 líneas en total (de `theorem` a la línea en blanco). Todas llevan ya la guarda:
15 en forma de implicación, 2 en forma de regla (`pcc_congr_succ_code`, `pcc_congr_predcT_code`, con `heq` como
hipótesis), y una con el hueco DOS veces (`pcc_congr_eqcT_diag_code_imp`). Cuatro van por `pcc_leibniz_apply(_imp)` en
vez de `PrfH_leibniz_apply`; dos pagan el `hasWitF` con `(by hw_auto)`.

**La adaptación (fondo, no renombre).** `promover/CongruenciaHueco.lean` (379 líneas):

* §1, el genérico con cuatro hipótesis de testigo (`hwFX`, `hwF0`, `hwX`, `hwY`) y `pcc_leibniz_apply_imp` en vez de
  `PrfH_leibniz_apply`: 20 líneas.
* §2, las **19** copias como corolarios con su firma LITERAL copiada (auto‑parámetros `hw_auto` incluidos) —199 líneas—
  y, para cada una, `@corolario = @original := rfl` (mismo tipo; por irrelevancia de pruebas basta).
* §3, controles negativos: el `rfl` no casa dos copias de contexto distinto (tres casos).
* **Resultado (MEDIDO):** rc 0, 0 errores, 0 avisos, ≈ 5 s; `[propext, Quot.sound]` en el genérico y en las cuatro
  muestras impresas. **Visto fallar** (`medidas/CongruenciaHueco_MUTANTE.lean`): con una hipótesis de más en la firma de
  `C_pcc_congr_unT_code` —sigue siendo demostrable— su `rfl` da «Type mismatch»; y un control sin su
  `fail_if_success`, también.
* **Destino (MEDIDO).** `medidas/CongruenciaHueco_destino.lean`, que importa SÓLO `Meta/EvalArithPrf.lean`, compila
  con el genérico y la copia de ese módulo (con su `rfl`): el genérico no necesita nada aguas abajo de `EvalArithPrf`.
  Y `medidas/dag.py` (sobre las líneas `import`, con un control positivo y uno negativo; `salidas/dag.txt`):
  `EvalArithPrf` está en la clausura de los 12; **`CodeCtorKit`, el destino que se probó en 2026‑09, NO** está en la de
  `EvalArithPrf`, `EvalCarcNthcPrf`, `EvalMulPrf` ni `LineWFTrackedPrf` (5 de las 19 copias).

**Recomendación.** PROMOVER `promover/CongruenciaHueco.lean` como `sondeos/CongruenciaHueco.lean`, REGISTRO. Los cuatro
arneses, DESCARTAR con esta razón (verificable): *«Arneses del test de destino de la auditoría B3 de `SubstfcPlanos`
(2026‑09‑04). Lo que proponían bajar está en el build —`binK` en `Meta/CodeCtorKit.lean`, la subsunción de
`prf_substtc_binT_at` hecha en `Meta/LiftcCodePrf.lean`, el KIT TERNARIO en `Meta/EvalArithPrf.lean`, `binct` y su
familia en `Meta/SubstfcCodePrf.lean`—, salvo el genérico, que sigue en `sondeos/CongruenciaHueco.lean`, adaptado a la
guarda de ADR‑020.»* Sustituir las 19 copias del build por corolarios (419 líneas por ≈ 219 en la forma de este sondeo,
MEDIDO sobre su texto, no sobre una refactorización) es otra decisión, del propietario; ojo si se hace: en
`EvalArithPrf`, `pcc_congr_succ_code` (l. 340) está ANTES de `pcc_leibniz_apply_imp` (l. 385).

**Fila para `sondeos/README.md`** (tabla «Qué hay, y qué demostró cada uno», arriba del todo; ADR‑NNN por poner; las
rutas de `Probe/` van SIN comillas invertidas, para que `[B]` no las lea como citas vivas):

```
| **`CongruenciaHueco.lean`** | 🔬 **¿subsume UN genérico las 19 congruencias internas `pcc_congr_*_code` del build?** (2026‑11‑02, ADR‑NNN; T48: el genérico `pcc_congr_hole_code` de Probe/B3_planos_dedup_kit.lean y Probe/B3_planos_dedup.lean, del 2026‑09‑04, que el triaje del 2026‑09‑11 mandó promover) | ✅ **SÍ**, compila (≈ 5 s; 379 líneas). El original no compila desde la guarda de testigo de ADR‑020, un día posterior: `PrfH_leibniz_apply` pide `hasWitF` del contexto y `hasWit` de los dos extremos. **Adaptado**: cuatro hipótesis de testigo, y `pcc_leibniz_apply_imp` en vez de `PrfH_leibniz_apply`; así sólo usa `Meta/EvalArithPrf.lean` y lo de arriba (compila importando sólo ese módulo), que está en la clausura de imports de los doce módulos con copia —`Meta/CodeCtorKit.lean`, el destino que se probó en 2026‑09, no: cuatro de los doce no lo importan—. Las 19 copias (12 módulos, 419 líneas) salen como corolarios con su enunciado LITERAL, auto‑parámetros `hw_auto` incluidos, y en las 19 el tipo del corolario es el de la copia del build (`rfl` entre las dos constantes); visto fallar con una hipótesis de más. `[propext, Quot.sound]`. No cambia el build: sustituir las copias sería una refactorización aparte. REGISTRO |
```

### 2.2 · `VER_extra.lean`

**Qué demuestra.** «Verificación adversarial de la tanda B2 (T2_higiene)», 2026‑09‑03, 58 líneas: tres pares de
teoremas del build con el MISMO enunciado y distinto nombre, por `rfl` entre las constantes (dos pruebas de la misma
proposición son iguales por irrelevancia, así que el `rfl` tipa sólo si los enunciados coinciden): `SinWTs.prf_shapeUn_str`
= `ENS.prf_shapeUn_str'`, `SinWTs.prf_shapeBin_str` = `ENS.prf_shapeBin_str'` (los cuatro en `Meta/CodeWitnessPrf.lean`,
l. 283, 289, 1555, 1562) y `SinWTs.prf_congr_lenc` (`CodeWitnessPrf` l. 97) = `RunFnBoundedPrf.prf_eq_congr_lenc` (l. 43).
Control negativo: Un contra Bin (y contra Nul) no tipa. Depende de `Meta/CodeWitnessPrf.lean` y
`Meta/RunFnBoundedPrf.lean`, sin barril.

**Compilación (MEDIDO):** rc 0 tal cual, 3 s, `[propext, Quot.sound]` en los tres. Los tres duplicados siguen vivos.

**¿En el build o en los documentos?** El build tiene los duplicados, no su registro: los nombres salen en la prosa
(`DECISIONS.md:1727`, `doc/REFERENCE-Incompleteness.md:508`), pero ningún documento versionado dice que son el mismo
enunciado (grep en `*.md`, `*.lean`, `*.tsv`, `*.txt`, `*.json`; tampoco en `doc/control/hallazgos.tsv`).
Lo que ya NO es cierto (MEDIDO, leyendo los `export` con un control positivo): la frase del HALLAZGO 1 «están LOS
CUATRO en su bloque `export`» — hoy ninguno de los cuatro está en un `export`; de los de `lenc`, sólo
`prf_eq_congr_lenc` (el de `RunFnBoundedPrf`). Registro del 2026‑10‑16, no re‑medido con los 32 titulares:
`ENS.prf_shapeUn_str'` y `ENS.prf_shapeBin_str'` estaban fuera del cono de los titulares
(`doc/registro/2026-10-16-cono/fuera-del-cono.txt:410‑411`).

**Recomendación.** PROMOVER `promover/DuplicadosPorEnunciado.lean` como `sondeos/DuplicadosPorEnunciado.lean`,
REGISTRO: el código es el de `VER_extra.lean` sin tocar una línea; sólo cambia la cabecera (nombre, procedencia y una
nota fechada que corrige la frase del `export`). Compila (rc 0, 4 s); su control negativo, visto fallar sin el
`fail_if_success`. Cuando alguien quite los duplicados dejará de compilar, que es su salida (a archivado).

**Fila para `sondeos/README.md`** (sin comillas invertidas en `fail_if_success`: es cita muerta de `[B]` en
`doc/control/b-deuda.tsv`, l. 492‑493):

```
| **`DuplicadosPorEnunciado.lean`** | 📏 **tres pares de teoremas del build con el MISMO enunciado y dos nombres** (2026‑09‑03, verificación adversarial de la tanda B2; promovido de Probe/VER_extra.lean el 2026‑11‑02, ADR‑NNN, T48) | ✅ compila sin tocar una línea (≈ 4 s; 65 líneas): `SinWTs.prf_shapeUn_str` = `ENS.prf_shapeUn_str'` y `SinWTs.prf_shapeBin_str` = `ENS.prf_shapeBin_str'` (los cuatro en `Meta/CodeWitnessPrf.lean`), y `SinWTs.prf_congr_lenc` = `RunFnBoundedPrf.prf_eq_congr_lenc`, por `rfl` entre las constantes, `[propext, Quot.sound]`; control negativo (Un contra Bin no tipa), visto fallar. Su frase «los cuatro, en su bloque `export`» ya no es cierta (nota fechada en la cabecera). Cuando se quite el duplicado dejará de compilar: es su salida. REGISTRO |
```

Y en la tabla de clasificación: REGISTRO (34) → (36), con «✏️ 2026‑11‑0X (ADR‑NNN, T48): `CongruenciaHueco` y
`DuplicadosPorEnunciado`, nuevos»; 46 sondeos → 48.

### 2.3 · `CritRefl_anidado.lean`

**Qué demuestra.** «VÍA 2 — el `∀` anidado, de frente»: el reflector de `isTC1` con el `bdAllCode` de `argsIn` DENTRO
del de `wfAll1`, con las dos vistas del hueco (`varc ⌜0⌝` fuera, `varc ⌜1⌝` dentro) y dos aplicaciones de
`pcc_bdAll_intro`. Importa el barril; copia piezas de `sondeos/A3IsFCBTracked.lean` y de
`ClausuraLiftSinWTs.lean` (archivado).

**Frente a `ReflectorForallAnidado.lean` (MEDIDO, `diff` contra `archivo/sondeos-2026-10`).** Es el MISMO fichero —las
1 095 primeras líneas iguales salvo dos notas fechadas que ADR‑134 añadió a la copia archivada—, y lo que añade es:
§13 **CRIT‑A** (l. 1097‑1222: instancia cerrada `S(0)`, con lista de argumentos `[⌜0⌝]`, para que el `∀` interno no sea
vacuo), §14 **CRIT‑B** (l. 1223‑1298: el antecedente rechaza los códigos de fórmula, tags 3‑6) y §15 **CRIT‑C**
(l. 1299‑1333: un `rfl` de que SU imagen punteada es un `forallc` dentro de otro); sustituye el bloque final de
`#print axioms`. El «control que no ejercía la rama que decía medir» era `pcc_isTC1_wz`, cuyo `∀` interno es vacuo; la
copia archivada ya lo dice en su §12 (l. 991‑992: «Su lista de argumentos es `nil`, o sea el `∀` interno es vacuo»).

**Compilación (MEDIDO):** rc 1, 34 errores. Con 17 líneas de renombre, 16. Renombres (18 errores): `prf_gnum_lt` →
`prf_numeral_lt` (retirado en ADR‑190), `liftTerm_numeralM` ambiguo entre `Minimal.Axioms` y `PremsOfDotPrf` (y dos
«unsolved goals» en cascada), `BoundedInPrf.PrfH_lt_subst2` → `ChainPrf.PrfH_lt_subst2` (cinco), `strCode "0"`/`"S"` →
`sym!` (ocho). Fondo (16): la guarda de testigo en `PrfH_eq_symm_code` (5), `PrfH_leibniz_apply` (5),
`PrfH_eq_trans_code` (2), `PrfH_bdEx_intro_open`, `pcc_thm_inst2`, y la NOVENA obligación de `pcc_bdAll_intro`,
`hwPsi : ∀ q, Prf (hasWitF (PsiF q))`, en sus dos usos (el sondeo contaba ocho). Arreglarlo es enhebrar testigos por
dieciséis sitios y probar `hasWitF` de un `PsiF` con un `bdAllCode` dentro: trabajo, no un renombre.

**¿Está en el build? Sí, y más fuerte (MEDIDO: `medidas/T48_CoberturaCrit.lean`, rc 0, sólo compone lemas del build):**

* El reflector, con `w` y `c` abstractos: `pcc_isTC1_tracked` y `pcc_wfAll1_tracked` (`Meta/HasWitTrackedPrf.lean`
  l. 906‑916; el `∀` anidado de `argsIn`, su §4).
* CRIT‑A, para TODO término real: `prf_mp (pcc_isTC1_tracked _ _) (prf_isTC1_tcodes t)` compila
  (`prf_isTC1_tcodes`, `Meta/CodeWitnessPrf.lean:1119`), `[propext, Quot.sound]`; su instancia en `σ(0)` también, y un
  `rfl` comprueba que la lista de argumentos de `⌜σ(0)⌝` es `[⌜0⌝]` (con su control negativo: la de `0` es vacía).
* CRIT‑B: `crit_isTermCodeE1_rejects` está en `Meta/CodeWitnessPrf.lean:318` (con `crit_num_ne`, `crit_tag_absurd`,
  `crit_isTermCodeB1_rejects`); sus cuatro instancias del sondeo (`atomc`, `eqc`, `implc`, `forallc`) compilan con él.
  Las definiciones del sondeo (`shapeUn`, `shapeBin`, `argsIn`, `isTermCodeE1`, `wfAll1`, `isTC1`) son, al carácter, las
  de `Minimal/Axioms.lean` l. 1115‑1142.
* CRIT‑C certificaba la imagen punteada DEL SONDEO (`wfAllB1Dot`), que no existe en el build; el del build es
  `wfAll1Dot` (`HasWitTrackedPrf` l. 511). Un certificado así para el del build sería trabajo nuevo, no una promoción.

**Recomendación.** DESCARTAR, con esta razón: *«Es `ReflectorForallAnidado.lean` (archivado, `archivo/sondeos-2026-10`)
más tres controles. No compila (18 errores de renombre y 16 de la guarda de testigo de ADR‑020, entre ellos la novena
obligación de `pcc_bdAll_intro`), y lo que medía está en el build y más fuerte: el reflector `pcc_isTC1_tracked`, el
rechazo `crit_isTermCodeE1_rejects` y la no vacuidad para todo término real, `prf_isTC1_tcodes` (compuestos en T48:
compila).»* Opcional, si se quiere dejar rastro en la fila archivada de `ReflectorForallAnidado.lean`: *«✏️ 2026‑11‑0X
(T48): la variante con lista de argumentos no vacía (CRIT‑A, en Probe/CritRefl_anidado.lean, descartado) la cubre hoy
el build para todo término real: `pcc_isTC1_tracked` con `prf_isTC1_tcodes`.»*

### 2.4 · Los hermanos

* `B3_planos_dedup_funcc3.lean`: tras `sym!` compila (rc 0, `[propext, Quot.sound]`), pero sus nueve declaraciones son
  las de `EvalArithPrf` l. 165‑210 (comprobado en `T48_YaEnElBuild.lean` (a)). DESCARTAR: *«Arnés 4 de la auditoría B3:
  el KIT TERNARIO que comprobaba que cabía en `EvalArithPrf` está en `EvalArithPrf`.»*
* `B3_planos_dedup_opens.lean`: 2 errores de fondo tras renombrar. DESCARTAR: *«Arnés 3: comprobaba que borrar cinco
  duplicados por nombre del sondeo `SubstfcPlanos` era drop‑in; el sondeo está archivado y los cinco viven en
  `CodeCtorKit` y `MpCodePrf`.»*

## 3 · `pcc_congr_hole_code` y la tabla de deuda de `[B]`

**MEDIDO: `pcc_congr_hole_code` NO está en `doc/control/b-deuda.tsv`** (939 líneas, `4a0c00e`; ni la cadena «hole»
salvo `substF_hole_hasWitF`). Salió de `B_DEUDA` en **ADR‑142** (DECISIONS.md:1108: «Viven en
`doc/historia/NEXT-STEPS-hasta-2026-10-14.md`: ax_tc_liftfc, pcc_congr_hole_code, …»), por exclusión: su única cita
con comillas invertidas está en `doc/historia/NEXT-STEPS-hasta-2026-10-14.md:1689`, fuera del universo de `[B]`; la de
`doc/AUDITORIA-SUELO-2026-10-12.md:847` va sin comillas, y `[B]` sólo lee lo que va entre comillas invertidas
(cabecera de `b-citas.awk`). La evidencia «check-doc-sync.bash:480» de T48 era la lista `B_DEUDA` en `99baa89`
(2026‑10‑12), hoy sustituida por la tabla; la copia congelada de aquella lista, `scripts/pruebas/b/bdeuda.txt:10`, aún
la nombra. INFERIDO (no ejecuté `[B]`: pide `lake`): con el sondeo promovido, una cita con comillas en una línea que
nombre `CongruenciaHueco.lean` la absuelve («si la declara un sondeo, que la línea nombre ese sondeo»).

## 4 · Censo de las citas a `Probe/` en los documentos versionados

Orden: `git ls-files '*.md' '*.lean'` (259 ficheros, sin `.lake/`) | `LC_ALL=C grep -o -n -E 'Probe/[A-Za-z0-9_.\-]*'`.
Tablas: `salidas/censo-probe-por-fichero.tsv` y `salidas/censo-probe-ocurrencias.txt`.

* **85 apariciones en 28 ficheros**: **23** citan un fichero concreto (`Probe/X.lean`) y **62** nombran el directorio
  («`Probe/` está en `.gitignore`», «promover 4 de `Probe/`»…).
* **Ninguna apunta a uno de los cuatro** (ni a los hermanos). Los cuatro se citan sólo por su nombre, sin el prefijo:
  `doc/AUDITORIA-SUELO-2026-10-12.md:847` (los cuatro) y `:849` (`CritRefl_anidado`), y
  `doc/historia/NEXT-STEPS-hasta-2026-10-14.md:1688` y `:1690` (los cuatro); fuera de md/lean, también en
  `doc/registro/2026-10-12-auditoria-suelo/candidatos.json`.
* Por fichero (citas a un fichero + menciones del directorio): `doc/historia/NEXT-STEPS-hasta-2026-10-14.md` 3+7;
  `doc/AUDITORIA-SUELO-2026-10-12.md` 0+6; `doc/REFERENCE-Incompleteness.md` 2+4; `PLAN-PRUEBAS.md` 1+5;
  `CHANGELOG.md` 1+4; `PLAN-SORTES.md` 4+1; `sondeos/PrfHMono.lean` 1+4; `sondeos/README.md` 3+2;
  `doc/historia/DECISIONS-001-130.md` 0+4; `DECISIONS.md` 0+3; `doc/AUDITORIA-2026-09-11.md` 0+3;
  `doc/registro/2026-10-12-t02-teoria/comentarios/correccion-grupo-3.md` 0+3; `NEXT-STEPS.md` 0+3;
  `sondeos/AcotarEsLaMismaObligacion.lean` 3+0; `doc/book/AUDITORIA-2026-09-10.md` 0+2;
  `ROBINSON_PlusPlus/Meta/CodeWitnessPrf.lean` 1+1; `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean` 0+2;
  `sondeos/ClausuraFormaEcuacional.lean` 2+0; y uno en cada uno de `AI-GUIDE.md`, `NAMING-CONVENTIONS.md`,
  `doc/AUDITORIA-FOL-2026-09-12.md` (1+0), `sondeos/A3IsFCBTracked.lean` (1+0),
  `ROBINSON_PlusPlus/Meta/{EvalLiftcPrf,HilbertDeduction,LineWFGuardPrf}.lean` y tres de
  `doc/registro/2026-10-12-t02-teoria/`.
* Los 17 destinos concretos: `ADV_novacuo` (3), `CritDesc_consumidor` (3), `Lift_acotar` (2), `PilotoParticion` (2), y
  uno cada uno `A3_directa`, `ClausuraSubstfc`, `CritLift_acotar`, `Fuerza`, `Magnitud`, `MC_enmienda`, `PilotoAislado`,
  `PilotoDiagonal`, `PuenteInNth`, `SinMap`, `Sortes`, `V4_census`, `VerifClausuraAdv`. De ellos, 15 existen hoy en
  `Probe/` (`Fuerza` y `Sortes`, no) y sólo 2 tienen copia versionada con el mismo nombre (`sondeos/PilotoAislado.lean`,
  idéntica; `sondeos/Magnitud.lean`, distinta).
* (Contexto, fuera del ámbito pedido: sobre TODOS los ficheros versionados, `json`/`tsv`/`txt` incluidos, hay 44 rutas
  `Probe/*.lean` distintas; T48 decía 42 el 2026‑10‑12, con otro ámbito que no he reconstruido.)

## 5 · Lo raro

1. `pcc_congr_hole_code` no está en `b-deuda.tsv` (§3): el encargo lo daba por cita muerta allí.
2. Los arneses B3 son del 2026‑09‑04 y la guarda de testigo (ADR‑020) del 2026‑09‑05: el genérico nunca se midió contra
   la API con guarda, y desde entonces las copias pasaron de 7 (+1) a 19.
3. El destino que se probó para el genérico (`CodeCtorKit`) ya no sirve para 5 de las 19 copias; `EvalArithPrf` sí.
4. La cabecera de `VER_extra` afirma algo hoy falso (los cuatro, en su `export`); corregido con nota fechada en la
   versión a promover.
5. **Antes de barrer `Probe/`**: el build mismo cita un fichero de `Probe/` como procedencia
   (`ROBINSON_PlusPlus/Meta/CodeWitnessPrf.lean:2047`, «`prf_wfAllF_of_list` es COPIA LITERAL de
   `Probe/ADV_novacuo.lean`»), y `sondeos/README.md:162` y `sondeos/PrfHMono.lean:12` citan
   `Probe/CritDesc_consumidor.lean`; 13 de los 17 ficheros citados no tienen copia versionada con su nombre (y la de
   `Magnitud` no es idéntica), así que el barrido borraría la única. No son de los cuatro, pero es la misma decisión.
6. `doc/book/scripts/simbolos.py:88` sigue metiendo `Probe` en su censo (T48 pide sacarlo al barrer).
7. `Probe/` tiene 334 `.lean` (331 arriba y 3 en `salvage/`), más `lib/` con dos `.olean` y dos `.err` vacíos: las
   335 entradas del directorio no son 335 `.lean`.
8. `fail_if_success` es cita muerta de `[B]` (`b-deuda.tsv` l. 492‑493): las filas propuestas no lo citan con comillas.
9. Numeración incoherente de los arneses B3 en sus cabeceras («arnés 2 de 3», «1 de 4», «3 de 3», «4 de 4»).
10. `CritRefl_anidado.lean` tiene finales de línea CRLF (los otros cinco, LF); `sed` de msys los pasa a LF en las copias
    renombradas (el `diff` real son 17 líneas). No afecta a la compilación.

## 6 · Lo que se entrega (en este directorio)

* `promover/CongruenciaHueco.lean` (md5 `80a64314…`) y `promover/DuplicadosPorEnunciado.lean` (md5 `02a6d3c6…`):
  las dos versiones que compilan y se proponen.
* `orig/`: los seis de `Probe/`, tal cual, con `MD5SUMS`.
* `medidas/`: las versiones renombradas (`ren/`), `T48_YaEnElBuild.lean`, `T48_CoberturaCrit.lean`,
  `CongruenciaHueco_destino.lean`, los cuatro mutantes, `dag.py` y `compila.bash`.
* `salidas/`: la salida de cada compilación (`*.out`) con su orden, md5, rc, segundos, errores y `sorry` (`*.meta`);
  `dag.txt`; el censo de `Probe/`.
* `rpp/`: el clon compartido (limpio para git; las pruebas, en su `Probe/`, que ignora).

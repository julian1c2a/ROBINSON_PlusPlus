# T18 · Las 19 filas «⬜ **sin redactar**» de `sondeos/README.md`, redactadas

**Last updated:** 2026-11-02 — lo que entregó el agente de T18 (ADR‑246), tal cual.

Fecha: 2026‑11‑02, sobre `master` = `4a0c00e` (Lean v4.35.0). Para cada fila va el texto que sustituye EXACTAMENTE a
«⬜ **sin redactar**». Lo que la celda ya tenía detrás («· ✏️ …», «· `prf_tc_form` fue retirado…») va al final, sin tocar.

Fuentes, por orden: el propio fichero (cabecera, títulos de sección, resumen final); para los cinco del árbol, una
compilación de hoy (`lean.exe` con los `leanOptions` del lakefile, sin `-o`); para los catorce archivados, su
`git show archivo/sondeos-2026-10:sondeos/X.lean` y una compilación de hoy (para el primer error); y, cuando la
cabecera no dice el resultado, la fila de la tabla principal o el mensaje del commit, CITADOS como tales.

⚠️ **Nueve de las diecinueve ya tienen fila con resultado en la tabla principal** («Qué hay, y qué demostró cada
uno», `sondeos/README.md:168-177`, escritas el 2026‑08‑17/23): `PilotoDiagonal` (l. 168), `S4` (169), `S3S5` (170),
`PilotoAislado` (171), `Magnitud` (172), `S1Audit` (173), `KitPayoff` (175), `TcFormPayoff` (176) y `CarcPayoff` (177).
Sus cabeceras van SIN negrita (`` | `X.lean` | ``) —son las nueve únicas filas sin negrita de esa tabla, medido—, y `[H]`
de `check-doc-sync.bash` sólo casa `` | **`X.lean`** | ``. INFERIDO: son los «nueve de los proyectados que no lo
estaban» de la nota del 2026‑09‑22, que eran filas de verdad. Sin redactar de verdad estaban DIEZ.
Abajo, para esas nueve, el texto es coherente con su fila vieja (comprobado contra el fichero y, en las tres del
árbol, contra la compilación de hoy) y la cita.

---

## Las cinco del árbol (tabla «⬜ Sondeos SIN REDACTAR», l. 228‑232)

### `ClausuraFormaEcuacional.lean` (l. 228)

✅ compila (4 s, 2026‑11‑02; once avisos de `if_true` obsoleto), y sus quince `#print axioms` dan `[propext, Quot.sound]`. Era el piloto de clausura de la vía (2) —¿se cierra el testigo de parseo bajo `substfc`?, con el tag 5 y `v t X wF` abstractos— y su cabecera da el **desenlace (b), demostrado**: `W' := wF` es absurdo (`identity_witness_absurd`); el testigo imagen está forzado a contener la imagen elemento a elemento, la de los parámetros desplazados y el sustituyendo entero (`forced_map_tag5`, `forced_map_tag6`, `forced_substituend`); el map sobre lista abstracta sale por `listInd`, gratis en la mitad de términos (`map_mem_tc`); la cláusula de forma hay que reescribirla como ecuación (`shapeImpl`, un fortalecimiento sin axiomas), y `Wtwo` cierra el paso unitario pero no es punto fijo (`forced_shift2`). REGISTRO

### `Div2Gen.lean` (l. 229)

✅ **SÍ, en una línea**: `prf_div2_double_all : Prf (∀. div2 (#0 · 2) = #0)` es `Prf.gen` sobre `prf_div2_double`; compila (5 s, 2026‑11‑02), `[propext, Quot.sound]` (el commit que lo trajo, `a1c6d4d`, 2026‑08‑19: el peldaño `div2` «no necesita inducción»). ⚠️ Su `#check` final ya no imprime lo que el docstring daba por hecho: `pcc_thm_inst` lleva hoy la guarda `⊢ᴴ hasWit (liftTerm 0 w)` (la vía C, ADR‑020), así que mete el teorema en `Prov` sólo para testigos con `hasWit`, no «en cualquier testigo». REGISTRO

### `Magnitud.lean` (l. 230)

✅ compila (8 s, 2026‑11‑02). Calcula en coma flotante, en escala logarítmica, el tamaño del valor de `formCode φ` con las ecuaciones de `cons` de ANTES de ADR‑113 (lo avisa su cabecera): `formCode ax_tc_succ` anida 3 873 `cons` y su log₂ desborda el `Float` (`inf`); el de `ax_tc_cons` es ≈ 8,66 × 10⁷⁸ y el de `ax_L0_cons_def`, ≈ 1,6 × 10¹¹ —lo que ya decía su fila de la tabla principal (l. 172)—. ⚠️ Su último `#eval` imprime «119 (y el ancla, el 142.º)»: el «142.º» está escrito a mano (la cuenta de ADR‑117) y, con 119 en `axiomsBase`, el ancla es hoy el 120.º. REGISTRO · ✏️ 2026‑10‑04 (ADR‑117): su `#eval` del número de axiomas pasa a `axiomsBase.length` —evaluar `axioms` construiría el numeral del ancla, que es astronómico, y no acabaría—

### `PilotoAislado.lean` (l. 231)

✅ compila (3 s, 2026‑11‑02). Re‑prueba por la ruta NUMERAL, importando sólo `SubstCodeOpenPrf` y `DerivCondPrf`, la invariancia `substtc_inv_termCode_listFormCodeM`, la de `formCode` y el caso general `substtc_inv_termCode_closed`, que quita la hipótesis `tcFn a = termCode a`; los cinco `#noExiste` certifican que `prf_tc_form`, `prf_tc_of_cons`, `prf_tc_cons`, `prf_tc_term` y `prf_tc_listFormCodeM` no están en el entorno, y los tres teoremas dan `[propext, Quot.sound]`. Lo mismo dice su fila de la tabla principal (l. 171). REGISTRO

### `S4.lean` (l. 232)

✅ compila (3 s, 2026‑11‑02): el primer paso del sondeo S4 —la evaluación provable de Cantor sobre numerales—, `prf_add_eq_zero_right : Prf (a + b = 0 ⇒ b = 0)`, por casos sobre `b` (`prf_zero_or_eq_succ_pred`), `[propext, Quot.sound]`. Su fila de la tabla principal (l. 169) dice que faltaba `prf_div2_numeral`; la cadena se terminó en el build (`prf_div2_numeral`, `prf_cons_eval`: la nota de ADR‑134 de su cabecera). REGISTRO

---

## Las catorce archivadas (tabla «🗄️ Archivados el 2026‑10‑16», l. 264‑313)

### `CarcPayoff.lean` (l. 264)

✅ Preguntaba si basta `pcc_dot_cons` para devolver `pcc_eval_carc`, cuyo cierre viejo usaba `prf_tc_cons'`. La cabecera no da el resultado, pero el fichero lo cierra con un único `pcc_rw` sobre `pcc_dot_cons`, y su fila de la tabla principal (l. 177) dice **«`pcc_eval_carc` RECUPERADO, mismo enunciado y mismo footprint»** (`68fa43c`, 2026‑08‑22). Hoy no compila: primer error (2026‑11‑02), l. 15, el literal `"carc"` es un `String` donde D7 pide `List Char` (`strCode "carc"`).

### `ChainNegPuente.lean` (l. 265)

🏁 Medía el puente de `DEUDA_chainNeg` —de una línea cuyo `lineWF` la teoría refuta a `axioms ⊢ ¬ chainOk nil ⟦l⟧`— y lo construye (`derives_chainOk_neg_of_line`, §1); su §3 se titula «🏁 `DEUDA_inNeg`, SALDADA» (`deuda_inNeg`: las cabezas de una cadena aceptada son los códigos de sus conclusiones). La cabecera no dice el coste ni el footprint; el commit que lo añadió (`4622af9`, 2026‑09‑11) dice que `NegVerifier` pasó de dos deudas a una. Era capa `⊢` con `FOL.MetaRules.raa` (ADR‑115), y hoy su primer error (2026‑11‑02) sale antes, en la l. 18: `unknown namespace ROBINSON_PlusPlus.Meta.CodeArith` (módulo retirado en ADR‑190).

### `ClausuraNoHaceFalta.lean` (l. 267)

✅ **No hace falta, salvo en dos sitios** (su «RESPUESTA MEDIDA»): la cadena sólo usa las conclusiones anteriores por MEMBRESÍA, y los reflectores de `mp`, `gen` y `thy` se instancian sin pedir forma a un `substfc` (§1–§2); sólo `ax_lineWF_ind` y `ax_lineWF_listInd` aplican `substfc` al RESULTADO de un `liftfc`, y ahí el valor anidado ya es un `formCode` (`prf_liftFormula_arith`), así que basta un conjunto extra en el codificador (§3–§4). Su §5 nombra el sitio profundo: bajo `∀`/`∃`, `substfc` cambia el sustituyendo por `liftc 0 s`, lo que pide la clausura de `isTermCode` bajo `liftc`. Hoy no compila: primer error (2026‑11‑02), l. 139, `ax_lineWF_q1` ya no es definicionalmente su forma de entonces (lleva la guarda `hasWitF`/`hasWit` de ADR‑020).

### `HasWitTcFn.lean` (l. 285)

✅ **SÍ, por inducción OBJETO** (`prf_nat_induction`): `prf_hasWit_tcFn (t) : Prf (hasWit (tcFn t))`, con la base sacada de `ax_tc_zero` y un paso que pidió una pieza que no existía, la monotonía del testigo (`prf_argsIn_mono`, `prf_wfAll1_cons`); ⬆️ subió el mismo día a `Meta/HasWitTcFnPrf.lean` (`bb0e483`, 2026‑09‑05). T18 (2026‑11‑02): con el renombre de `PrfH_lt_subst2` (3 sitios) quedan dos errores, y el primero pasa de la l. 177 a la l. 178, `Unknown identifier …BoundedInPrf.PrfH_lt_subst1` —su gemelo, movido a `ChainPrf` en el mismo dedup de ADR‑019—; renombrando también ése (2 sitios, fuera del encargo de T18) **compila entero** (5 s) y sus tres `#print axioms` dan `[propext, Quot.sound]`. No cita nada de la capa `⊢`, contra lo que dice la lista del 2026‑10‑02 de este README («lo retirado fallaría después»).

### `KitPayoff.lean` (l. 288)

✅ **NO es un muro** (su «RESULTADO»): `pcc_dot_nul`, `_un` y `_bin` salen por composición de `pcc_dot_cons`, sin inducción nueva (sólo código; un paso interno; dos anidados), con `pcc_dot_cons_symm` de por medio; el coste real está en `CodeTreeReflect`, la recursión `prf_tc_objAt` a mover dentro de `Prov` (hecho después, `pcc_tc_objAt`: nota de ADR‑134). Lo mismo dice su fila de la tabla principal (l. 175). Hoy no compila: primer error (2026‑11‑02), l. 77, `pcc_eq_symm_code_internal` pide ya las guardas `hasWit` de sus dos códigos (la vía C, ADR‑020).

### `MedirC_Carga.lean` (l. 290)

⛔ **El ángulo (B) no sirve: la guarda colgante implica `⊥`.** Medía arrastrar la guarda de `pcc_eval_substfc` como hipótesis por la cadena y descargarla al final, contra el chasis y el ensamblador de producción. Sus respuestas compiladas: el chasis no se toca (1a) y el ensamblador tampoco, pero no descarga nada y la guarda sube hasta D3 (2, 4); `hcond_absorbe_extra` la absorbe sólo con el axioma `q1` enmendado (3); y `M5_LA_GUARDA_COLGANTE_IMPLICA_BOT` (5): la D3 que saldría sería VACUA. Del 2026‑09‑01 (`d876e26`); hoy no compila: primer error (2026‑11‑02), l. 40, `ax_lineWF_q1` ya no es definicionalmente su forma de entonces (lleva la guarda de ADR‑020).

### `MedirC_Deriva.lean` (l. 291)

⛔ **NO, y está REFUTADA** (su cabecera): medía el ángulo (A) —¿sale la guarda `hasWitF (nthc t 2̄)` del propio antecedente `lineWF t`?— y construye una línea basura de tag 9 y `lenc` 4 que satisface `lineWF` con el `prf_lineWF_q1` de entonces y cuya casilla 2 es un código de variable: si la guarda saliera, `Prf ⊥` (`MEDIDA_A_REFUTADA_con_TODO_el_antecedente_de_hcond`; también la mitad de término, `MEDIDA_A_REFUTADA_mitad_TERMINO`). La causa: la condición del tag 9 era una sola ecuación de `carc` (`condQ1_es_UNA_ecuacion_atomica`). Del 2026‑09‑01 (`d876e26`); hoy no compila: primer error (2026‑11‑02), l. 45, `ax_lineWF_q1` ya no es definicionalmente su forma de entonces (lleva la guarda de ADR‑020).

### `MedirC_Enmienda.lean` (l. 292)

⚠️ **La enmienda de `q1` es escribible y el chasis la absorbe, pero es CIRCULAR tal cual** (su «RESUMEN DE LO MEDIDO»): tipa con `ENS.hasWit`/`ENS.hasWitF`, `hcond_absorbe_extra` aplica, no rompe la solidez y sobre líneas reales se paga; pero la guarda DISCRIMINA (`CRIT_hasWitF_rejects_varc`), no se descarga para código abstracto, y `prf_lineOk_q1`/`_q2` la usan con argumentos abstractos: enmendar `q1` rompe el chasis que consume la enmienda. Y `G` no cambia: `godelCN` no depende de `axioms` (medido sobre el `Environment`, con 141 axiomas y sobre `⊢`). Del 2026‑09‑01 (`d876e26`); hoy no compila: primer error (2026‑11‑02), l. 67, `ax_lineWF_q1` ya no es definicionalmente su forma de entonces. · ✏️ 2026‑10‑04 (ADR‑117): su `#eval axioms.length` pasa a `axiomsBase.length`; y sus dos `example` sobre `axioms` (`length = 141` por `decide`, y `axioms_eq`) ya no valen —son 142, y `axioms_eq` se retiró—: fallan detrás de su primer error, que no cambia

### `MedirF_Opaco.lean` (l. 294)

⛔ **El «Bloqueo 2» de `PLAN-NEGVERIFIER.md` estaba muerto** (su «RESUMEN DE LO MEDIDO»): `axiomsCodeT` no era opaco en ninguna dirección; `¬ In ⌜φ⌝ axiomsCodeT` salía con la hipótesis meta `¬ List.Mem φ axioms` (`neg_In_axiomsCodeT_of_notMem`), ya estaba en producción con `¬ Prf φ` (`neg_In_axiomsCodeT`), valía para cualquier término invariante por sustitución que se distinga uno a uno de los 141 axiomas (`neg_In_axiomsCodeT_gen`), basura incluida (`nil`), y cerraba el caso `thy` del módulo C. Del 2026‑09‑01 (`d876e26`); era capa `⊢`, y hoy su primer error (2026‑11‑02) es la l. 36, `unknown namespace ROBINSON_PlusPlus.Meta.CodeDistinct` (fuera del build en ADR‑161). · ✏️ 2026‑10‑04 (ADR‑117): su `#eval axioms.length` pasa a `axiomsBase.length`

### `MedirF_Replan.lean` (l. 295)

📏 Re‑medía `PLAN-NEGVERIFIER.md` (2026‑07‑14) contra el árbol del 2026‑09‑01. La cabecera no da el resultado, pero su bloque final, «RESUMEN DE CORRECCIONES AL PLAN», lista **catorce** —entre ellas, que el Bloqueo 2 («`axiomsCodeT` es OPACO») era falso, que `axioms` tenía 141 entradas y no ~35, que las copias de `numeral` eran tres y sus puentes ya estaban en el build, y que el plan subestimaba las líneas un 30–80 %—; y su §2 re‑verifica que el Bloqueo 1 (`canon_ne`) seguía en pie (`canon_ne_sigue_inconsistente`). Era capa `⊢`; hoy su primer error (2026‑11‑02) es la l. 15, `unknown namespace ROBINSON_PlusPlus.Meta.OmegaReflect` (retirado en ADR‑160). · ✏️ 2026‑10‑04 (ADR‑117): su `#eval` de `axioms.length` pasa a `axiomsBase.length`

### `PilotoDiagonal.lean` (l. 302)

✅ **El punto fijo de Gödel sobrevive con códigos NUMERALES.** Su cabecera sólo fija el método (asumir `codeN` y `hFN` como `axiom`) y el criterio (que `diag_arith_num` no lleve `tc_cons`); el resultado está en su fila de la tabla principal (l. 168, del 2026‑08‑17): `godelCN_fixedpoint` con el footprint del original menos `tc_cons`, y `provCode_transfer` por un paso de Leibniz. Lo rehizo con `hFN` demostrada `DescargaHFN`. Era capa `⊢`: hoy su primer error (2026‑11‑02) es la l. 25, `unknown namespace ROBINSON_PlusPlus.Meta.Induction` (ADR‑115).

### `S1Audit.lean` (l. 307)

🔬 La auditoría S1: `#print axioms` de los titulares de entonces, de D1, de la capa rastreada y de los sitios puente, con `prf_tc_cons`/`tc_cons` convertidos en `axiom` de Lean para que el footprint delate quién dependía de la lectura sintáctica de `tcFn`. La cabecera da el footprint «sano esperado», no el obtenido, y su fila de la tabla principal (l. 173) sólo dice que compilaba en la rama `sondeo/s1-sin-ax-tc-cons`; el resultado está en el mensaje del commit de esa rama (`4b3492f`, etiqueta `archivo/sondeo-s1-sin-ax-tc-cons-2026-08-16`): la única puerta del daño a Gödel I era el lema diagonal (`godelC'_fixedpoint` citaba `tc_cons`; D1 y las dos mitades de Gödel I, limpias). Hoy no compila: primer error (2026‑11‑02), l. 17, `Unknown constant …DiagonalTwo.goedel_first_real'`.

### `S3S5.lean` (l. 308)

✅ S3 preguntaba si `codeNat φ` se queda SIMBÓLICO al elaborar, y S5 de dónde sale la profundidad de `formCode`. La cabecera no da el resultado, que está en su fila de la tabla principal (l. 170): los seis teoremas elaboran al instante sin reducir `codeNat φ` (✏️ ADR‑117: el núcleo sí lo evaluaba con `simp only` sobre el ancla), y los puntos Unicode de los diez símbolos suman 19 068, frente a 45 con índices. Hoy no compila: primer error (2026‑11‑02), l. 27, «Ambiguous term» `consN` —el suyo contra el de `Minimal/Axioms.lean`—.

### `TcFormPayoff.lean` (l. 313)

✅ **NO es un muro** (su «RESULTADO»): el sustituto directo de `prf_tc_form` es una línea y net‑0, cambiando el código estático a `termCode (numeral (codeNat φ))`, pero el lado derecho no es negociable (`inDot` lo fija `D3DottedPrf`: es el objetivo de D3); la salida es que D1 dota `prf_formCode_numeral` y da el puente dentro de `Prov` (`pcc_to_formCode`/`_imp`): no tocar definiciones, convertir en la frontera. Lo mismo dice su fila de la tabla principal (l. 176). Hoy no compila: primer error (2026‑11‑02), l. 109, `pcc_rw` pide ya las guardas `hasWitF`/`hasWit` (la vía C, ADR‑020). · `prf_tc_form` fue retirado el 2026‑08‑18 (`6f66e61`)

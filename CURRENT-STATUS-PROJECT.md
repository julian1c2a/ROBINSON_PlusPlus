# Current Project Status — ROBINSON_PlusPlus

> ## ESTADO REAL — 2026-09-10c · **`master`** · 🏁 **VÍA C INTEGRADA** (ADR-020) · ✅ **ÁRBOL VERDE** · ✅ **CI VERDE**
>
> 🏁🏁🏁 **D3 ESTÁ EN UNA SOLA OBLIGACIÓN: `hbody`** (§3.58). `d3_prf_of_body_only` la cierra desde
> ahí, y **todo lo demás está probado** —el puente átomo↔forma acotada, la cota, el `∃` acotado, el
> cuerpo del `∀`, el empaquetado, los **dos** `PsiF`, `hmatch`, `hPinv`, `hPsiId` y `hwP`—, con
> footprint igual a la base sancionada.
>
> `hbody` se parte —por `chainOkBPsi_split`, que conecta los dos `PsiF` **por construcción**— en:
>
> `hbody` está **partido por `rfl`** en sus dos mitades (§3.59), con la **composición de los dos
> `substfc`** — el `PsiF` dotado es él mismo un `substfc`, y el resultado tiene **DOS huecos**.
>
> | mitad | estado | depende de |
> |---|---|---|
> | **(a)** reflexión de `lineWF` = `pcc_lineWF_tracked` | ⬜ **5 de 7** reflectores (`modulo_2`) | **`prf_hasWitF_liftfc`** (`ind` 18, `listInd` 20) |
> | **(b)** reflexión de `boundedPremsIn` | ⬜ núcleo probado, falta ensamblar | ⛔ **el análisis por tags de (a)** |
>
> ⛔⛔ **CORREGIDO (§3.59.2)**: aquí se dijo que (b) «no depende de C3» y era «ensamblaje». **Es
> falso.** Su cota lleva `premsOf` **dotado**, y `premsOf` no está definido por recursión sino por
> **21 axiomas, uno por TAG**, con pattern-matching sobre la forma de la línea ⇒ para un argumento
> abstracto **no hay nada que evaluar**. ⇒ **el orden correcto es (a) primero**.
>
> ⛔ Y **`prf_hasWitF_liftfc` es un FRENTE**, medido (§3.60): no existe ni la mitad TÉRMINO a nivel
> arbitrario, y el molde es una inducción de **2 088 líneas**. La deuda está **enunciada**
> (`DEUDA_hasWitF_liftfc`), con su guarda medida — sólo `hasWitF X`, el nivel **libre**.
>
> ### Cómo se llegó, en cuatro tramos (§3.55–§3.58)
>
> | tramo | de → a | la pieza que lo movió |
> |---|---|---|
> | §3.55 | sin medir → **2** | destino abierto y forma fijada por `rfl`; la cota **dentro de `Prov`**; `hPinv` genérico |
> | §3.56 | 2 → **3** ⚠️ | ⛔ el chasis **no era aplicable**: `hPl` era **FALSA** ⇒ el `PsiF` **dotado** |
> | §3.57 | 3 → **2** | `hPsiId`, con la **tercera variante** de la familia |
> | §3.58 | 2 → **1** | `hwP`, transportando el **testigo** por el puente de §3.56 |
>
> 🔑🔑🔑 **Las tres reglas del frente, y las tres son sobre la FORMA:**
> 1. **El destino fija la IMAGEN; el chasis fija la FORMA en que hay que escribirla.** Hacen falta
>    **los dos** cuerpos —el computable, que casa el destino por `rfl`, y el **dotado**, que es el
>    único natural— y por el puente entre ellos, **dentro de `Prov`**, han viajado ya **tres cosas**:
>    la forma (`hmatch`), la prueba (`hbdAll_of_dotted`) y el testigo (`hwP`).
> 2. **El ÍNDICE no es cosmético, y van tres veces.** La familia `substfc_inv_substCodeF` tiene
>    **tres** variantes y **no son intercambiables**: por debajo del hueco el testigo **deja de ser
>    libre**, y un salto de dos o más haría el enunciado **FALSO**.
> 3. ⚠️ **El contador de obligaciones NO mide el progreso**: §3.56 lo **subió** de 2 a 3 y fue el
>    paso más importante de los cuatro — lo que el «2» medía era una cadena que **no cerraba**.
>
> 🔧 **Y el instrumental mentía** (AI‑GUIDE §27.1): `check-sorry.bash` daba **101 falsos positivos**
> —menciones en prosa— donde hay **0** de verdad; `check-doc-sync.bash` daba verde con los cuatro
> controles `[A]` **vacíos**; y la **CI no
> había arrancado nunca** (YAML inválido). Arreglado el 2026‑09‑09, y lo primero que encontró
> fueron **siete documentos autoritativos** con la cifra de jobs obsoleta.
>
> 🏁 **`Build completed successfully (141 jobs)`.** La enmienda de los 7 esquemas está aplicada y
> **el árbol entero compila con ella**. La rama `via-c-adr020` (20 commits) se **integró en
> `master`** el 2026-09-07 con merge commit `7bc2c8a`, y el build se verificó verde **después** del
> merge, no sólo en la rama.
>
> 🏁 **LA VÍA C, COMPLETA** (§3.38–§3.40):
> * **`prf_hasWit_substtc` y `prf_hasWitF_substfc`** —las dos clausuras, con código y sustituyendo
>   ABSTRACTOS— en `Meta/SubstfcWitnessPrf.lean`, **net-0 puro**.
> * ✅ **① promoción** (sin ciclo de imports; ⛔ ADR-019 **tres veces** al promover).
> * ✅ **② `MpCodePrf`**: los 10 sitios cerrados; la mitad CÓDIGO se paga entera ahí.
> * ✅ **③ propagación**: los **29 módulos** bloqueados, cerrados.
>
> 🏁 **Y después del merge, dos cierres más el mismo día — los dos net-0** (§3.41):
> * **B3.2 · `Meta/EvalSubsttcPrf.lean`** — `pcc_eval_substtc` / `pcc_eval_substtsc` /
>   `pcc_eval_substtc_hasWit`, con `v`, `s`, `t` **ABSTRACTOS**. Era el **prerrequisito de B3.4**.
>   De 154 declaraciones del sondeo entraron **71**: promover fue sobre todo **borrar**.
> * **El chasis de `hGuard` · `Meta/LineWFGuardPrf.lean`**, **net-0 puro**. Mete en el build
>   `hcond_absorbe_extra` —el lema sobre el que se aceptó ADR-020, que vivía en **cinco copias
>   fuera del build**— y ⭐ `hcond_absorbe_cascade`, que **reduce la deuda de los 7 tags a DOS
>   lemas genéricos**, `DEUDA_hGuardT`/`DEUDA_hGuardF`, **enunciados y no postulados**.
>   ⚠️ Corrigió además la descripción de la enmienda: el conjunto extra es una **cascada** de 1–3
>   guardas anidadas a la derecha, no un par — comprobado con **siete `rfl`** contra
>   `Minimal/Axioms.lean` (§3.41.4).
>
> 🏁 ⭐ **2026-09-08 · B3.4 CERRADO: el muro de `substfc` está DENTRO DEL BUILD** (§3.42).
> `Meta/EvalSubstfcPrf.lean` — `pcc_eval_substfc` con `v`,`s`,`f` **abstractos**,
> `pcc_eval_substfc_wit` y el chasis genérico `pcc_eval_substfc_modulo_8`. Footprint = la base
> sancionada. De **806** declaraciones del sondeo entraron **90**: era la **acreción de cinco
> sondeos**, y `ENS` —el trabajo real— sólo dependía de **41** nombres de los otros cuatro
> namespaces, **31 ya en producción**.
> ⭐ Con esto **`hCarc` queda comprado** para C3: el antecedente de `pcc_eval_substfc_wit` es
> literalmente el conjunto extra que ADR-020 metió dentro del `⇔`.
>
> ▶ **2026-09-09b · `pcc_eval_liftfc`: la base, y una medición que REORDENA el plan** (§3.49).
> `Meta/EvalLiftfcPrf.lean` — `liftfcT` (⛔ **definición**, nunca axioma), `targetLiftfc`, los
> controles y la deuda **enunciada, no postulada**. Footprint = sólo los tres axiomas de Lean.
> ⚠️⚠️ **`pcc_eval_liftc` sólo vale a nivel `zero`**, y `ax_liftfc_forall`/`_ex` **suben el
> nivel** ⇒ **A5 no es una generalización opcional: es PRERREQUISITO** de `pcc_eval_liftfc`, y
> por tanto de los cuatro tags que faltan. Orden correcto: **A5 → chasis → los 4 tags**.
> ⚠️ Y es un frente de **escala B3.4**, no de una sesión.
>
> 🏁 **2026-09-09 · C3: TRES de los SIETE reflectores de sustitución, PROBADOS** (§3.48).
> `pcc_lineWF_tracked_q1_imp` (tag 9), `_q2_imp` (10), `_leibniz_imp` (13); net-0 puros.
> ⭐ **Y se ve por qué ADR-020 puso la guarda donde la puso**: las casillas guardadas son
> **exactamente los hijos del nodo `sub`** — la `witF` sobre el cuerpo del `substfc`, la `wit`
> sobre el sustituyendo. La forma de la enmienda, que parecía arbitraria, resulta ser la
> **aridad de los nodos `sub`** de cada árbol.
> ⚠️ Corrige §3.47.5: `PrfH_dotVN` **no** paga la guarda (es pura congruencia); la paga
> `PrfH_tc_objAt`, vía `pcc_eval_substfc_wit`.
> ⬜ Los otros **cuatro** esperan a `pcc_eval_liftfc`, y hasta que estén los siete
> `pcc_lineWF_tracked` **sigue siendo condicional**.
>
> ▶ **2026-09-08f · C3 ARRANCADO: el chasis del árbol con `substfc`** (§3.47).
> `Meta/SubstTreeReflect.lean` — `STree` con nodo `sub`; footprint = sólo los tres axiomas de
> Lean. ⭐ Los árboles de **q1, q2 y leibniz** declarados y **casados por `rfl` con los axiomas
> ENTEROS**, cascada de guardas incluida ⇒ el `∃ C` de §2.1 de `LineWFGuardPrf` queda resuelto
> para tres tags.
> ⚠️ Y un hueco del chasis, tapado: `hcond_absorbe_cascade` reflejaba cada conjunto por
> separado, y el núcleo estructural **no veía las guardas** — que es justo lo que
> `pcc_eval_substfc_wit` pide como antecedente OBJETO. `hcond_absorbe_1/2/3` se las dan.
> ⭐ **Medición que cuantifica el siguiente frente**: `pcc_eval_liftfc` bloquea **4 de los 7**
> reflectores (q3, qconf, ind, listInd); **tres son alcanzables hoy**.
>
> 🏁🏁 **2026-09-08e · C3-F CERRADO: `DEUDA_hGuardF` PROBADA** (§3.46).
> `pcc_hGuardF` + `hGuard_of_slots`: **la cascada de ADR-020 no tiene ninguna obligación
> abierta**. Footprint = la base sancionada, net-0 puro.
> ⭐ Todo el trabajo estaba en el **`∃∃`**: el `∃` EXTERIOR liga `wF` y el INTERIOR `wT`, luego
> los huecos se rellenan **en dos pasadas y a NIVELES DISTINTOS** ⇒ hubo que **abrir el nivel**
> de la keystone. 🔑 Cuando un `∃` se anida, lo que hay que generalizar no es el testigo: es el
> NIVEL.
> ⚠️ **Y lo que esto NO cierra**: C3 sigue abierto. `pcc_lineWF_tracked_modulo_7` pide un
> reflector por tag y hay **14** en el árbol, ninguno de los 7 de sustitución. Pero lo que les
> falta es ya **sólo la condición ESTRUCTURAL**, que es lo que B3.2/B3.4 compraron.
>
> 🏁 **2026-09-08d · C3-F, la mitad cara: `Meta/HasWitFTrackedPrf.lean`** (§3.45, 828 l.,
> net-0 puro). `pcc_wfAllF_trackedC` — `wfAllF` reflejado con los DOS testigos abstractos y la
> cota ya dotada — sobre `pcc_isFormCodeE2_trackedC`, el recorrido de las OCHO cláusulas.
> ⭐ **La regla de §3.44 aplicada ANTES de construir**: siete `example … := rfl` casando la
> imagen con la que `substCodeF` produce. Acertaron todos a la primera.
> ⭐ Y confirmó que lo genérico de C3-T lo era de verdad: `pcc_shape_tree` en el árbol,
> `shapeFCun`/`shapeFCbin` en el tag, `wfAll1DotAtC` **literalmente el mismo término**.
> ⬜ Queda `isFC1` (trivial), el `∃∃` y la fontanería `condD` — todos con la máquina escrita.
>
> 🏁🏁 **2026-09-08c · C3-T CERRADO: `DEUDA_hGuardT` PROBADA** (§3.44).
> `pcc_hGuardT (i n t) (hin : i < n) : DEUDA_hGuardT i n t` en `Meta/HasWitTrackedPrf.lean`,
> footprint = la base sancionada, **net-0 puro**. Con `hGuard_of_deudaF`, la cascada de ADR-020
> queda a la espera de **UNA sola** deuda: `DEUDA_hGuardF`.
> ⚠️ **La corrección que costó el frente entero, y que conviene no repetir**:
> `condD C t = substfc 0 ṫ (formCode C)` **NO admite elegir imagen** — la impone `formCode`, y
> `formCode (shapeUn X k)` es la **ecuación posicional**, no la conjunción de accesores
> (`shapeDot`) que §5 había elegido. Equivalentes en la teoría objeto, **códigos distintos**.
> ⭐ Y la corrección salió **gratis en teoría objeto**: `pcc_tc_objAt` + `PrfH_dotVN` de
> `Meta/CodeTreeReflect.lean` ya reflejaban esa ecuación por inducción sobre el árbol, desde el
> frente de los 14 tags estructurales. `pcc_shape_tree` sólo las compone — y es genérica, luego
> C3-F la hereda.
> ⚠️ **La cota de casilla `i < n` no es un artefacto**: el puente `(nthc t ı̇)˙ → nthcT ṫ ı̄` es
> `pcc_eval_nthc` y la exige. Las cuatro casillas `wit` reales la cumplen (`decide`).
>
> ✅✅ **LA LÍNEA ROJA DE ADR-020, COMPROBADA Y CON RAZÓN ESTRUCTURAL**: `d3_prf_of_chainOkDot` y
> `pcc_lineWF_tracked_modulo_7` **conservan su firma exacta**. La guarda va DENTRO del `⇔` OBJETO,
> así que al reflector le llega como conjunto objeto extraído de `lineWF t`, **no** como hipótesis
> Lean — y por tanto no puede aparecer en su firma. Era el argumento que sostenía la vía; ahora es
> una comprobación.
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.51.
>
> **Build 141 jobs · 0 sorrys · Lean v4.31.0** ✅ **VERDE** (2026‑09‑10e).
>
> 🏁🏁🏁 **C3 CERRADO: `pcc_lineWF_tracked` es INCONDICIONAL** (§3.62). Los **21 tags** cableados.
> La cadena, en cinco pasos: `prf_hasWitF_liftfc` (§3.61, `Meta/LiftfcWitnessPrf.lean`, net‑0 puro)
> ⇒ `ind` (18) y `listInd` (20) con el nodo **`tcm`** de `STree` ⇒ **los SIETE** reflectores de
> sustitución ⇒ ⭐ `pcc_tag_vacuous`, que **paga** el `hOther` que §11/§11bis habían declarado
> «vacuo pero más honesto como hipótesis» ⇒ **`hbody`(a) de D3, incondicional**
> (`Meta/D3BodyPrf.lean`).
> ⭐⭐ **Y `premsOf` SÍ se evalúa** (§3.63, `Meta/ListEtaPrf.lean` + `Meta/PremsOfTagPrf.lean`): la
> obstrucción de §3.59.2 («21 axiomas con *pattern‑matching*, nada que evaluar sobre un argumento
> abstracto») le faltaba una frase — *mientras no se sepa la **LONGITUD***, que sale del propio
> bicondicional del tag. Las **21 ramas**, a nivel objeto, en 417 líneas.
> 🏁🏁🏁🏁 **2026‑09‑10g · D3 PROBADA — `axiom d3` RETIRADO** (§3.67).
> `d3_prf_real (φ) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))`. La **tercera condición de
> derivabilidad** de Hilbert‑Bernays‑Löb es un **teorema**, `GodelTwo.d3` pasa de `axiom` a
> `theorem` ⇒ **la cadena D1/D2/D3 no postula ninguna de las tres**, y `goedel_second'` ya no
> depende de `d3`. **6 `axiom` de Lean** (eran 7).
> ⭐ **La QUINTA variante de `substfc_inv_*`** —nivel actuante **igual** al hueco bajo— es la **más
> barata de la familia**: el testigo **no aparece** en el resultado, luego no hace falta la
> hipótesis `u ≐ varc v̄` que la cuarta sí pedía. ⚠️ Van **cinco veces** que el índice no es
> cosmético; el inventario completo está en §3.67.3.
> ⚠️ **Tres trampas de FORMA nuevas** (§3.67.2): una hipótesis que **no viajaba** por el genérico;
> `rfl` desplegando `strCode` **carácter a carácter** hasta agotar los heartbeats; y el Leibniz que
> **captura** la variable si no se protege el hueco con `liftTerm`.
>
> 🏁🏁 **2026‑09‑10f · B1 y B2 CERRADAS, y B3 en 8 de 9** (§3.64–§3.66).
> **B1** (`Meta/PremsOfDotPrf.lean`): `pcc_eval_premsOf` — `premsOf` reflejado **dentro de `Prov`**
> con `t` abstracto, las 21 ramas. **B2** (`Meta/D3BodyPrf.lean` §2–§3): la **cota** cruzada, con B1
> en el eslabón que faltaba; ⚠️ los dos eslabones intermedios son **condicionales** ⇒ hizo falta
> `PrfH_pcc_rw`. **B3** (`Meta/PremsBdAllPrf.lean`): el chasis interior con sus **ocho**
> administrativas, más `substfc_id_substCodeF2` (la **cuarta** variante de la familia) y la
> naturalidad de `substCodeF2` en sus dos testigos.
> ⭐⭐ **Y ADR‑021 se AFINA** (§3.66.1): lo que rompe la naturalidad del `PsiF` **no es «ser un
> `substCodeF`»**, es que **el PARÁMETRO VIAJE DENTRO DE LA FÓRMULA**. Enunciada así predice los
> dos casos —el exterior, donde `hPl` era falsa, y el interior, donde es cierta—.
> ⬜ **D3 queda en UNA obligación con nombre**: `DEUDA_premsBody`, la novena del chasis interior,
> con la ruta medida (la única fricción es la **MONEDA de §3.55.2 por cuarta vez**, y sus dos
> piezas ya existen).
>
> 🔑🔑 **Las dos lecciones de método del día, y son recíprocas la una de la otra:**
> 1. ⚠️ **Una obligación declarada VACUA sin pagarla sigue contando como ABIERTA** aguas abajo
>    (§3.62.3). Ésta se arrastró como parámetro dos módulos y tres sesiones; pagarla costó veinte
>    líneas.
> 2. ⚠️ **Medir un frente por el TAMAÑO del molde sobreestima** (§3.61.3): el molde incluye lo que ya
>    está comprado. La medida útil se lee de su bloque `export`, no de su `wc -l`.
>
> 🏁🏁 **`pcc_eval_liftfc` PROBADO** (§3.53): sin hipótesis, con `v` y `X` abstractos y sólo
> `hasWitF X` de guarda, net‑0.
> 🏁 **D3: destino fijado, puente de la cota, `∃` acotado, cuerpo del `∀`, empaquetado, `PsiF`
> exterior, `hmatch`, `hPinv`, `hPsiId` y `hwP`: probados** (§3.55–§3.58).
> 🧹 **Dedup ADR‑019 de SEIS familias** (§3.52).
> ⛔ **Trampa del día, tres veces**: `substfc`/`carc`/`lenc`… son símbolos OBJETO y **no reducen**.
> **127 módulos activos** (Minimal 11 + Meta 105 + Full 11) **+ 0 en `cuarentena/` + 60 en `sondeos/`.**
> **6 `axiom` de Lean · 141 axiomas objeto** en `axioms` — ⚠️ la enmienda **sustituye 7 de los 141**,
> no añade ninguno: las listas no cambian de longitud y el inventario de Lean sigue en 7.
>
> 🏁 **`∀t. hasWit (tcFn t)` PROBADO** y en producción (`Meta/HasWitTcFnPrf.lean`), footprint
> `[propext, Classical.choice, Quot.sound]` — **net-0 puro**.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

**Last updated:** 2026-09-10d — **`hbody` PARTIDO** (§3.59) y ⛔ corregida la dependencia de (b); la deuda del testigo de `liftfc`, enunciada y medida (§3.60). Antes: **D3 EN UNA SOLA OBLIGACIÓN** (§3.58, `hwP` probado); antes **§3.57** (`hPsiId`) y **§3.56** (el `PsiF` del chasis) y la reparación del instrumental (§27.1). Antes: **B3 en curso**: `SubstfcPlanos` cerrado (2 descensos + `SubstfcCodePrf`, 4 muertas retiradas) y la escalera `psi` subida, que cazó un duplicado invisible a todo censo (§3.35)
**Author**: Julián Calderón Almendros

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total modules | **110 activos** (Minimal/ 11 + Meta/ 88 + Full/ 11) + barrel `Meta.lean` · **+0 en `cuarentena/`** (fuera del build) · **+57 en `sondeos/`** |
| Modules sin sorry | 110 / 110 ✅ |
| Sorry reales (total) | **0** 🎉 |
| Declaraciones `axiom` de Lean | **7** (tras F7a): 3 esquemas de inducción `Full/`, TFA `Block8`, 2 anclas de codificación, `d3`. Inventario en **`AXIOMS.md`**. Ninguna es un `sorry` (ADR-010) |
| Meta-reglas FOL (ω) | 6 en **`FOL/MetaRules.lean`** (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`, `dne`) — re-export desde `Minimal.Axioms` |
| Meta-axiomas matemáticos | Tras F7a: `ax_p_tfa` (Block8); `ax_induction`/`ax_mod2_alternation`/`ax_list_induction` (Full); **`ax_axiomsCodeT_eq`** (⊢, `Minimal/Axioms:1376`) / **`prf_axiomsCodeT_eq`** (Prf, `Representability2Prf:104`) — anclas de codificación; `d3` (GodelTwo, único gödeliano vivo). ⚠️ `ax_inAxC`/`prf_inAxC` **ya no son axiomas**: son teoremas derivados de las anclas. Los 7 postulados legacy (`Dem`/`dem_iff_provable`/`provFormula`/`provFormula_repr`/`diagonal_lemma` + `D2`/`D3`) **retirados**. `qconf`/`Full.ax_induction` integrados como reglas del verificador. Inventario completo en **`AXIOMS.md`** |
| Axiomas matemáticos | **34** en `Minimal/`; en `Full/` **ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3** son **teoremas** + **TFA completo** (`tfa_numeral`) |
| Gödel | **Gödel I — sólo `⊬G`**: `goedel_first_numeral (hcon : ConsistentOmega) : ¬ Prf godelCN` (`Meta/DiagonalNumeral.lean`), sobre el punto fijo real `godelCN_fixedpoint`. Footprint = la base sancionada **menos `tc_cons`**. ⚠️ **La mitad `⊬¬G` (indecidibilidad) NO está cerrada**: `goedel_first_undecidable_numeral` toma `Reflects` como **hipótesis META explícita**; para descargarla falta **`NegVerifier`** (`PLAN-NEGVERIFIER.md`). *No revertir F7a — fue un arreglo de solidez.* — **D1** `repr_pos'_prf` ✅ y **D2** `d2_prf` ✅ reales sobre el cálculo finitario `Prf`. **Gödel II**: `goedel_second'` montado, **módulo `axiom d3`**. **D3 está FUERA de la cadena activa** (la capa rastreada está en `cuarentena/`): se recupera repatriando las raíces que quedan (7 a 2026-08-23), y el habilitador (`pcc_dot_cons`, escalera a.2) ya está ✅. Ver `NEXT-STEPS.md` |
| Build status | ✅ Passing (**141 jobs**, **127 módulos**, 0 errores, **0 warnings**, **0 sorry** — verificado con el `check-sorry.bash` reparado —, 7 `axiom` de Lean, Lean v4.31.0, 2026-09-09) |
| Promoción a `Meta/` (rama B) | ⏳ **B0–B2 hechas; B3 EN CURSO.** 🆕 **B3 (2026‑09‑04)**: de `SubstfcPlanos` salieron DOS DESCENSOS —`binK` a `CodeCtorKit` y el KIT TERNARIO a `EvalArithPrf`, que retira **74 copias a mano** de `sondeos/`— y el módulo **`SubstfcCodePrf`** (17 de 39; 4 retiradas por MUERTAS). Quedan `EvalSubsttc`, `SubstfcEx` y `EvalSubstfcPrf`. 🆕 **B2 (2026‑09‑04)**: `Meta/EvalLiftcPrf.lean` — **el DESCENSO**, que pone **`pcc_eval_liftc`** en producción y descarga el `hLift` de `Paso2CasoForall`. De 198 declaraciones del sondeo se promovieron **31**. 🔑 Destapó el **CICLO DE IMPORTS** (**ADR‑019**): cuando el sondeo subsume a producción hay que **bajar el general**, no subir el corolario. Seis piezas genéricas subieron aguas arriba (`PSI_inst` estaba copiado a mano en **siete** sondeos). Detalle en [§3.34](doc/REFERENCE-Incompleteness.md) |
| Verdad de los docstrings (rama G) | 🆕 ⚠️ **El libro se escribe leyendo del árbol, y el compilador NO verifica la prosa.** Auditoría en curso, 5 categorías con método propio cada una. Casos ya confirmados: `CodeWitnessPrf:78‑82` promete un `DescMutua` **inexistente**; `refl_isTermCodeE1_imp` se anuncia «EL RESULTADO CENTRAL» con **cero usos**. Ver `NEXT-STEPS.md` rama G |
| `NegVerifier` (módulo A) | ✅ **Decodificador COMPLETO** (§43): `CodeDecode` (biyección `decodeForm` + inyectividad) + `ChainDecode` (`decodeChain_prf`). **Módulo B** (`LineWFCases`, 21 tags) ✅. ⚠️ `canon_ne` es FALSO (reintroduciría la inconsistencia, `sondeos/CanonNeRefuta.lean`), pero ✅ **su sustituto YA ESTÁ EN PRODUCCIÓN** (2026‑09‑01): `Meta/CodeNatInjPrf.lean` (`codeNat_ne`/`codeNatTerm_ne`). ⛔ Y el otro bloqueo que el plan documentaba (`axiomsCodeT` opaco) **es FALSO desde julio** (§3.32.3). Estimación revisada: **~800‑1 300 líneas / 3,5‑5 sesiones** |
| D3 / plan 12‑A | 🏁🏁 **D3 EN UNA SOLA OBLIGACIÓN: `hbody`** (2026‑09‑10, §3.55–§3.58). `d3_prf_of_body_only (φ) (hbody)` cierra D3; todo lo demás está **probado** en `Meta/D3ChainDotPrf.lean` (978 l.), con footprint igual a la base sancionada. ⚠️ **Lo que costó el frente no fue el tamaño, fue la FORMA**: `pcc_bdAll_intro` **no era aplicable** —su obligación de naturalidad `hPl` es **FALSA** para el cuerpo que casa el destino, certificado por dos `rfl`—, así que hacen falta **DOS** cuerpos: `chainOkBPsi` (`substCodeF`, computa y casa el destino por `rfl`) y **`chainOkBPsiDot`** (símbolos objeto, único natural), puenteados **dentro de `Prov`** por `prf_substfc_arith_open`. ⭐⭐ Por ese puente han viajado **tres cosas**: la FORMA (`hmatch`), la PRUEBA (`hbdAll_of_dotted`) y el TESTIGO (`hwP`). ➕ `hPsiId` pidió la **tercera variante** de `substfc_inv_substCodeF` —nivel actuante **por debajo** del código, donde el testigo **deja de ser libre**— y `hwP` salió en **cuatro líneas**. ▶ De `hbody`, la mitad **(a)** (`pcc_lineWF_tracked`, ⬜ **5 de 7**) es **lo único de D3 aguas abajo de C3** —desbloqueo: `prf_hasWitF_liftfc`—; la mitad **(b)** (reflexión de `boundedPremsIn`) tiene el núcleo probado sobre argumentos **abstractos** y **no depende de C3**: es ensamblaje. Detalle en [§3.55–§3.58](doc/REFERENCE-Incompleteness.md) |
| Limpieza F7 | **F7a ✅ HECHA (2026-07-09)**: retirados los 7 postulados legacy (14→7 `axiom`); `Meta/Incompleteness.lean` eliminado + 5 postulados de `Meta/Provability.lean`. Cadena real verificada intacta (`#print axioms`). **F7b bloqueada** (`GodelTwo.d3` es portante; espera a D3 real) |
| Lean version | v4.31.0 |
| Naming convention | Mathlib-style (see `NAMING-CONVENTIONS.md`) |

> **Nota**: Todos los módulos compilan sin errores. Las **6** meta-reglas ω (que viven en
> `FOL/MetaRules.lean`, no aquí) y los meta-axiomas matemáticos son `axiom` intencionales, no
> provables — **no** son `sorry`s (ADR-010).

---

## Status by Module

| Module | Sorry | Status |
|--------|------:|--------|
| `Minimal/Axioms.lean` | 0 | ✅ Complete — lenguaje + **141 axiomas objeto** + esquemas del verificador + capa Δ₀. Contiene **1** `axiom` de Lean (`ax_axiomsCodeT_eq`); las 6 meta-reglas ω se movieron a `FOL/MetaRules.lean`. ⚠️ `ax_tc_cons` sigue como `def` en `:827` pero **fuera de las listas** — definición muerta |
| `Minimal/Theorems/Block1.lean` | 0 | ✅ Complete |
| `Minimal/Theorems/Block2.lean` | 0 | ✅ Complete |
| `Minimal/Theorems/Block3.lean` | 0 | ✅ Complete (verboso: enumera div2/mod2 por numeral, sin inducción) |
| `Minimal/Theorems/Block4.lean` | 0 | ✅ Complete |
| `Minimal/Theorems/Block4_C5.lean` | 0 | ✅ Complete — `lemma_C5`, `lemma_C5_unique`, `cantor_bounds` |
| `Minimal/Theorems/Block4_C6_C7.lean` | 0 | ✅ `add_left_cancel`, `mod2_of_even`, `proj1`/`proj2` (defs), `proj_is_cantor`, `cantor_uniqueness`, `cantor_surjectivity` |
| `Minimal/Theorems/Block5.lean` | 0 | ✅ `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c`, `pair_inj`, `is_cantor_pair` (mod2_of_even movido a Block4_C6_C7 el 2026-06-03) |
| `Minimal/Theorems/Block6.lean` | 0 | ✅ Todos probados (`concat_assoc` e `in_concat_iff` vía ax_C3/ax_L3 nuevos) |
| `Minimal/Theorems/Block7.lean` | 0 | ✅ `IsFunction`, `Functional`, `teo_F1`, `teo_F2`, `teo_F3` (Bloque VII spec) |
| `Minimal/Theorems/Block8.lean` | 0 | ✅ `Dvd`, `IsPrime`, `IsFactorization`, `ax_p_tfa` (TFA), pow/prod_pairs + **10 teoremas** (álgebra de `Dvd`, corolarios TFA) — Bloque VIII Fase 17 completa |
| `Meta/Godel.lean` | 0 | ✅ Nivel B Gödelización: `Sym`, `gNat`, `numeral`, `G`, `encode` (`⌜·⌝`), `encode_injective` (Teo G1) |
| `Meta/Provability.lean` | 0 | ✅ Nivel C (núcleo real): `formCode`+inyectividad, `IsFormula`, `Provable` (+`provable_formCode_iff`). Capa legacy (`Dem`/`diagonal_lemma`/`goedelSentence`/…) retirada en F7a |
| `Meta/NumListPrf.lean` | 0 | ✅ 12‑A/1a: `prf_lenc_nil/cons`, `prf_nthc_zero/succ` |
| `Meta/NatArithPrf.lean` | 0 | ✅ 12‑A/1b: toolkit de `<` en `Prf` (`prf_nat_induction`, `prf_add_zero_left`, `prf_lt_iff`, `prf_succ_lt_succ_of_lt`, `prf_not_lt_zero`, …) |
| `Meta/BoundedInPrf.lean` | 0 | ✅ 12‑A/1b: **`prf_In_iff_boundedIn`** + `prf_zero_or_eq_succ_pred` |
| `Meta/RunFnBoundedPrf.lean` | 0 | ✅ 12‑A/2 (`In`): `prf_runFn_nil_cons` (map de `carc`), `prf_nthc_runFn`, **`prf_In_runFn_iff`** |
| `Meta/ChainOkBoundedPrf.lean` | 0 | ✅ 12‑A/2 (`chainOk`): `prf_premOk_cons_iff`, `prf_allIn_iff_boundedAllIn`, **`prf_chainOk_iff_chainOkB`** |
| `Meta/CodeDecode.lean` | 0 | ✅ `NegVerifier` A.1 (§43): `decodeNat`/`decodeChars`/`decodeStr`/`decodeTerm`/`decodeForm` + round‑trips + **inyectividad** ⟹ `decodeForm` es una **biyección** |
| `Meta/LineWFCases.lean` | 0 | ✅ `NegVerifier` B (§44): `tagArity`/`tagConcl`/`tagPrems` + `prf_lineWF_tag`/`prf_premsOf_tag` + dirección negativa (`derives_lineWF_neg_*`). `tagConcl` cubre **19, no 21** (`thy` va por `In`; `mp` es incondicional) |
| `Meta/LineWFDerives.lean` | 0 | ✅ Des‑duplicación: los 42 `lineWF_*`/`premsOf_*` de `⊢` son `prf_to_derives` de sus gemelos `prf_*` (antes: probados dos veces) |
| `Meta/ChainDecode.lean` | 0 | ✅ `NegVerifier` A.2 (§43): `decodeRule`/`decodeLine`/`decodeChain`, `DecidableEq Term`/`Formula` + `findIdx`, secciones `thy`/`mp`/`gen`, ensamblado **`decodeChain_prf`** (cadena aceptada ⟹ `Prf`) |
| `Meta/NatOrderPrf.lean` | 0 | ✅ Orden `≤` en `Prf`: transitividades, sustitución, `prf_add_assoc`/`prf_add_comm`. ⚠️ Asoc./conm. de `+` son **axiomas objeto** (ax6/ax7), no se prueban por inducción |
| `Meta/NatMulPrf.lean` | 0 | ✅ Producto en `Prf` (leyes = ax8–ax12), monotonía, **cancelación** `prf_lt_of_mul_lt_mul_right`, tricotomía, `div2`/`mod2` (ax17/ax21) |
| `Meta/CantorMonoPrf.lean` | 0 | ✅ **`prf_cantor_mono_left/right`** — sub‑código < código, en 13 pasos troceados. Aquí vive `abbrev cpOf` |
| `Meta/Div2ParityPrf.lean` | 0 | ✅ **`prf_div2_numeral`** (cadena L1–L5, forma OBJETO, net‑0) + **paridad de Cantor**: `prf_mod2_consec`, `prf_mod2_cpOf`, **`prf_cons_double`** (el puente de la fase C de `pcc_dot_cons`) |
| `Meta/CodeNumeralPrf.lean` | 0 | ✅ **LA REPARACIÓN**: `triN`/`consN` (números triangulares ⇒ **sin división**), `codeNat`, **`prf_formCode_numeral`** por meta‑recursión |
| `Meta/DiagonalNumeral.lean` | 0 | ✅ Lema diagonal por la **vía NUMERAL**: `hFN`, `godelCN`, `godelCN_fixedpoint`, `provCode_transfer`, **`goedel_first_numeral`** (Gödel I), `goedel_first_undecidable_numeral` |
| `Meta/StrongInductionPrf.lean` | 0 | ✅ `prf_strong_induction` (inducción fuerte en `Prf`) + `prf_le_of_lt_succ` |
| `Meta/EvalMulPrf.lean` | 0 | ✅ Escalera (a.2) peldaño 2: **`pcc_eval_mul`** + `pcc_congr_addcT1_code_imp`, `pcc_eq_subst2_code_imp` |
| `Meta/DotConsPrf.lean` | 0 | ✅ Escalera (a.2) peldaño 4: **`pcc_dot_cons`** — `⊢ Prov(⌜cons(ḣ,ṫ) = (cons h t)˙⌝)`, argumentos abstractos. Herramientas nuevas `pcc_rw`/`pcc_rw_div2` |
| `Full/Induction.lean` | 0 | 🔄 Inducción general object-level: `ax_induction`, composición generalizada, **ax6/7/10/11/12/18/19** derivados + lemas de orden |
| `Full/Mod2.lean` | 0 | ✅ Opción C.2 (2026-06-11): `ax_mod2_alternation` + **ax21 (mod2_range) y ax24 (mod2_of_even) derivados como teoremas** |
| `Full/Lists.lean` | 0 | ✅ Listas (2026-06-11): meta-axioma `ax_list_induction` + **ax_C3 (concat_assoc) y ax_L3 (in_concat) derivados como teoremas** |
| **Total** | **0** | 🎉 |

*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending

---

## Recent Achievements

- **2026-08-22 — ✅ La ESCALERA (a.2) COMPLETA: `pcc_dot_cons`** (`Meta/DotConsPrf.lean`, nuevo).
  `⊢ Prov(⌜ cons(ḣ,ṫ) = (cons h t)˙ ⌝)` para `h`, `t` **abstractos**; footprint
  `[propext, choice, Quot.sound, prf_axiomsCodeT_eq]`. **Sin inducción nueva**: `cons` no tiene
  ecuaciones recursivas propias (`ax_L0_cons_def` lo define por `div2 (cantor_poly h (σt))`), así que
  fue **ensamblaje** en tres fases — (A) la instancia codificada **computa por `rfl`**, (B) el
  polinomio se evalúa dentro de `Prov` en 5 pasos, (C) el `div2` se cancela vía `pcc_thm_inst` con
  `prf_cons_double` de puente. Dos herramientas reutilizables: `pcc_rw` y `pcc_rw_div2`.
  **Rédito verificado** (`sondeos/CarcPayoff.lean`): `pcc_eval_carc` vuelve con el mismo enunciado y
  footprint, sustituyendo `prf_tc_cons'` por un único `pcc_rw`. Build **97 jobs**.
  *Las dos lecciones:* (1) todo teorema **OBJETO** se «dota» gratis con `prf_congr_tcFn`, sin entrar
  en `Prov`; (2) `substfc` sustituye **todas** las ocurrencias del hueco ⇒ un solo
  `pcc_leibniz_apply` cubre las repeticiones del polinomio (5 pasos, no 15).

- **2026-08-18/19 — LA REPARACIÓN: `ax_tc_cons` retirado, códigos como NUMERALES** (ADR‑012/013).
  La teoría objeto probaba ⊥ (verificado en compilador). Cuatro reparaciones descartadas con
  evidencia; la que funciona es escribir `⌈φ⌉` como `numeral (codeNat φ)`. **Coste: −1 axioma,
  ninguno nuevo.** Módulos nuevos: `Div2ParityPrf`, `CodeNumeralPrf`, `DiagonalNumeral`,
  `NatOrderPrf`, `NatMulPrf`, `CantorMonoPrf`, `StrongInductionPrf`. 31 módulos a cuarentena (hoy 21,
  tras refundar el keystone `Sigma1CorePrf`, que devolvió 10 de golpe).
  ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.

- **2026-07-09c — 12‑A fase 3: puente D3→forma acotada + átomo `=eq` rastreado**:
  **`Meta/Sigma1BoundedPrf.lean`** (NUEVO): **`d3_prf_of_reflect_bounded`** — como la fase 1/2 dio los
  `⇔` (`prf_In_iff_boundedIn`, `prf_chainOk_iff_chainOkB`) y `pcc_imp` sube implicaciones a
  `provCodeC'`, D3 se reduce a reflejar la forma **Δ₀ acotada** `boundedIn`/`chainOkB`.
  **`Meta/Sigma1AtomPrf.lean`** (NUEVO): toolkit RASTREADO del átomo `=eq` (`eqCodeFn` + congruencia +
  transporte + `prf_provCodeC'_eq_of_tracked`), espejo del de `In`. **Hallazgo confirmado en código:**
  la reflexión de `=eq` para términos abstractos es imposible **libre de muro** (Tarski: `termCode`
  sin congruencia object) → se rastrea con `tcFn` (que sí la tiene) y el puente `tcFn t =eq termCode t`
  lo descarga la inducción de fase 5 (numerales, `prf_tc_numeral`). `#print axioms` limpios. Plan
  restante en `GODEL-D3-TRACKED-DESIGN.md` §15.4. Build **76 jobs**, 0 sorrys, v4.31.0.

- **2026-07-09 — F7a: retirada la capa Gödel legacy (14 → 7 `axiom`)**:
  Auditado con `#print axioms` que la cadena real (`goedel_first_real'`, `d2_prf`, `goedel_second'`)
  no cita ninguno de los 7 postulados legacy. **Eliminado** el módulo `Meta/Incompleteness.lean`
  (Gödel I/II vía D2/D3 postulados) y retirados los 5 postulados de `Meta/Provability.lean`
  (`Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma` + `goedelSentence`/
  `goedelSentence_fixedpoint`); se conserva el núcleo real de codificación (`formCode`/`IsFormula`/
  `Provable`). Nuevo **`AXIOMS.md`** (registro autoritativo de los 7 axiomas restantes + las 6
  meta-reglas ω de FOL). Cadena real verificada intacta. **F7b** (retirar `d3`) sigue bloqueada
  hasta D3 real. Build verde (**74 jobs**), 0 sorrys, v4.31.0.

- **2026-07-08 — 12‑A FASES 1b y 2 COMPLETAS: el verificador ya es Δ₀ y sin acumulador**:
  Cerrado el **único punto de diseño del plan 12‑A que no estaba verificado en código**.
  **`Meta/NatArithPrf.lean`** (NUEVO): toolkit aritmético de `<` en `Prf` — hallazgo de escala,
  `lt a b := ∃k. a+σk=b` y `add` recurre por la derecha ⇒ **`0+n=n` NO es teorema de Q** y hay que
  reconstruirlo con `Prf.ind`. **`Meta/BoundedInPrf.lean`** (NUEVO): **`prf_In_iff_boundedIn`**
  (`In x L ⇔ ∃i<lenc L. nthc L i =eq x`) + `prf_zero_or_eq_succ_pred` (case-split de índice sin `∃`).
  **`Meta/RunFnBoundedPrf.lean`** (NUEVO): *corrección al diseño §12.3 —* **no hace falta β‑función**:
  `runFn nil p` no es recursión con acumulador, es el ***map* de `carc` sobre `p`**
  (`prf_runFn_nil_cons`, vía `prf_runFn_weaken`) ⇒ **`prf_In_runFn_iff`**, acotado por `lenc p`.
  **`Meta/ChainOkBoundedPrf.lean`** (NUEVO): (a) `prf_allIn_iff_boundedAllIn`, (b)
  `prf_in_concat_singleton_iff`, (0) `boundedCarcLt` (cota arbitraria), (c)
  `prf_boundedCarcLt_cons_succ_iff`, (d) **`prf_chainOk_iff_chainOkB`** — *el acumulador desaparece*:
  `chainOk c p ⇔ ∀i<lenc p. (lineWF (nthc p i) ∧ ∀j<lenc (premsOf …). (In … c ∨ ∃k<i. carc (nthc p k) =eq …))`,
  la formulación Δ₀ de libro. Inducción de listas con acumulador **`∀c` interno**, HI instanciada en
  `c ++ [carc line]`; el paso `cons` se apoya en el lema puntual `prf_premOk_cons_iff` (fusiona (b)+(c)).
  Todos `#print axioms` = `[propext, choice, Quot.sound]`. Nuevo `ESCALANDO_EL_PROYECTO.md` (enlace con
  DeepArith sobre el kernel FOL⁼ común). Build verde (**75 jobs**), 0 sorrys, v4.31.0.
  Siguiente: fases 3‑5 (`num` + evaluación provable + Δ₀‑completitud atómica → inducción estructural
  → `d3_prf` → `goedel_second_prf`).

- **2026-07-05c/d — D3: investigación de atajos (§11–§12) + arranque Σ₁‑completitud estándar (12‑A fase 1a)**:
  Investigación rigurosa: **no hay atajo para D3** (atajo por teorema de deducción imposible — D1
  exige `Prf` cerrado, D1‑con‑contexto es falsa = esa brecha es D3; enfoque `tcFn` descartado —
  `tcFn L =eq termCode L` stuck para `L` abstracta). Hallazgo central: **codificar el testigo ≡
  representar el verificador** sobre números (Δ₀), pero el verificador es estructural sobre listas.
  Decidida la **Opción 12‑A (capa numérica Δ₀ del verificador)**. **Fase 1a hecha**: `lenc`/`nthc`
  (longitud/índice de lista‑código) — defs + 4 axiomas en `Minimal/Axioms` (extensión conservadora,
  `axioms_eq` rfl preservado, **build entero verde: verificador/D1 intactos**) + ecuaciones `Prf`
  (`Meta/NumListPrf.lean`). Además `Meta/TrackedCorePrf.lean` extendido con `atom2CodeFn` (infra de
  códigos). Diseño completo en `GODEL-D3-TRACKED-DESIGN.md` §11–§12. Build verde (**71 jobs**),
  0 sorrys, v4.31.0. Siguiente: fase 1b (caracterización acotada de `In`).

- **2026-07-05b — Gödel II / Opción A: A‑F3 `pcc_exIntro_code` + verificación concreta RIESGO‑1**:
  `Meta/ExIntroCodePrf.lean` cierra la **A‑F3** (∃‑intro de la regla Q2 al nivel de código con
  testigo‑código arbitrario cerrado; `#print axioms` = estándar). `Meta/Sigma1TrackedPrf.lean`
  (NUEVO) verifica el ∃‑intro rastreado para testigos **concretos** (`pcc_exIntro_code_bridge`/
  `_objList`). **Hallazgo:** el testigo **abstracto** no lo cubre esta pieza — `tcFn #0` no es
  cerrado y todo combinador base produce `termCode` meta (transporte a `tcFn` stuck para lista
  abstracta) → `hI_tracked` abstracto requiere la **Opción A de raíz** (`provFormulaC'ₜ`/D1ₜ).
  Limpieza F7 (retirar `GodelTwo.d3` legacy) sigue BLOQUEADA hasta `goedel_second_prf` real.
  Build verde (**69 jobs**), 0 sorrys, Lean v4.31.0.

- **2026-06-11 — `Full/Lists.lean`: ax_C3 y ax_L3 derivados (inducción estructural)**: nuevo módulo (330 líneas) con **meta-axioma `ax_list_induction`** (estilo `imp_intro`/`gen`, parametrizado por `φ : Term → Formula`, conclusión sobre todos los Terms). Helpers de congruencia (`eq_congr_cons_right_full`, `eq_congr_concat_left/right`, `eq_subst_in`) + helper local `iff_intro`. **`concat_assoc_thm : ⊢ ax_C3_concat_assoc`** y **`in_concat_thm : ⊢ ax_L3_in_concat`** derivados por inducción estructural sobre L. Cobertura del fragmento aritmético + listas de Minimal en Full: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅. Build verde (29 jobs). Pendientes: Ax-P (TFA, inducción fuerte), Gödel Nivel D.

- **2026-06-11 — `Intermediate/` ELIMINADO + `Full/Mod2.lean` (Opción C.2)**: borrado el módulo prototipo `Intermediate/Induction.lean` y el directorio (decisión 2026-06-11: el sistema con Φ finito es caso particular de Full, mantener un nivel separado era burocracia conceptual). Nuevo módulo `Full/Mod2.lean` (290 líneas) con `ax_mod2_alternation : ∀n, mod2(σn)+mod2(n)=1` y derivación de **ax21 (mod2_range) y ax24 (mod2_of_even) como teoremas**. Auditoría 2026-06-11 (en `MINIMAL-AXIOMS.md §3.2`) documenta el hallazgo: `ax16+ax17` dejan `mod2` subdeterminado (modelos no estándar con mod2≥2 cumplen ambos), por eso `ax21` no es derivable sin axioma extra. Conservativo respecto a Minimal. Build verde (28 jobs).

- **2026-06-07 — `Full/Induction.lean`: ax19 (tricotomía del orden) derivado**: `lt_trichotomy_ax`/`lt_trichotomy_thm : axioms ⊢ ax19_lt_trichotomy`, por inducción object-level sobre `a` con `∀b` interno y `or_elim` 3-vías. Nuevos lemas de orden auxiliares: `zero_lt_succ`, `zero_or_succ_ax` (`∀n. n=0 ∨ ∃k. n=σk`), `lt_succ_cases` (`a<b → σa<b ∨ σa=b`) y `lt_intro`. Con ax18, el **fragmento de orden de PA⁻ queda derivado de la inducción**. Build verde (28 jobs, 0 sorrys/warnings).

- **2026-06-07 — `Full/Induction.lean`: inducción general object-level + axiomas derivados**: inducción general como **axioma object-level** (`ax_induction`), codificación lift-aware de `φ(σn)` y **composición De Bruijn generalizada** (`substFormula_succ_lift_gen` + `step_reduce`, que admite fórmulas no-ecuacionales). Derivados como **teoremas** (sin usar el axioma respectivo): **ax6** (add_comm), **ax7** (add_assoc), **ax10** (mul_comm), **ax11** (mul_assoc), **ax12** (mul_distrib) — algebraicos ecuacionales — y **ax18** (lt_irrefl) — primer no-ecuacional. + lemas de orden auxiliares (`lt_succ_self`, `not_lt_zero`, `lt_succ_of_lt`). Build verde (28 jobs).

- **2026-06-07 — `Intermediate/Induction.lean`: prototipo de inducción** (luego eliminado 2026-06-11): meta-axioma `peano_induction` (forma híbrida) + derivación de `zero_add`, `succ_add`, `add_comm` (= ax6). Hallazgo confirmado: la inducción general (Full) es de menor fricción técnica que la restringida a Φ → el trabajo continúa en `Full/`. Tras el prototipo, el módulo se elimina como conceptualmente redundante (caso finito de Full).

- **2026-06-06 — `Meta/Provability.lean` (Nivel C Gödelización) AÑADIDO**: codificación estructural de Gödel de la sintaxis FOL (`formCode`/`termCode`/`strCode`) con **inyectividad demostrada** (consistency-free, vía `injection`); `IsFormula`, `Provable` + teorema `provable_formCode_iff`; `Dem` + Teo Meta `dem_iff_provable`; lema del punto fijo `diagonal_lemma`; sentencia de Gödel `goedelSentence` + `goedelSentence_fixedpoint`. 5 meta-axiomas nuevos (Dem, dem_iff_provable, provFormula, provFormula_repr, diagonal_lemma) para las propiedades profundas (Nivel D). Barrel `Meta.lean` creado. Build verde, 0 sorrys.

- **2026-06-06 — `Meta/Godel.lean` (Nivel B Gödelización) AÑADIDO**: nuevo módulo `ROBINSON_PlusPlus.Meta.Godel` con Def 27 (`Sym`, `gNat`+`gNat_injective`, `numeral`+`numeral_injective`, `G`+`G_injective`), Def 28 (`encode`/`⌜·⌝`), y Teo G1 (`encode_injective`, meta-inyectividad consistency-free vía `injection`; + versiones object-level `encode_cons_inj`/`encode_cons_neq_nil` vía Block6). No añade axiomas matemáticos. Build verde a la primera. Ver `GODEL-STATUS.md`.

- **2026-06-06 — Block8 +10 teoremas**: álgebra de `Dvd` (`dvd_trans`, `dvd_mul_right/left`, `dvd_mul_of_dvd_left/right`, `dvd_add`) y corolarios del TFA (`factorization_exists/unique`, `lt_zero_one`, `factorization_one_eq_nil`). Euclides/multiplicatividad fuera de scope (requieren `prod_pairs_concat` → inducción).

- **2026-06-06 — Linter `unusedSimpArgs` a `false` global + warning FOL cerrado**: los 12 módulos pasan a `set_option linter.unusedSimpArgs false`. Cerrado el último warning externo `FOL/Theorems/Eq.lean:130` (commit FOL `9888c58`). Build global con 0 warnings.

- **2026-06-06 — Bloque VIII extendido (Fase 17 completa)**: `Axioms.lean` +`pow`/`prod_pairs` y 4 axiomas (sistema 30→34); `Block8.lean` +`IsFactorization` (Def 26) + meta-axioma `ax_p_tfa` (TFA). Limpieza de warnings previa 411→0.

- **2026-06-03 — Block8 (BLOQUE VIII Fase 17 parcial — Primos) AÑADIDO**: `Dvd` (divisibilidad), `IsPrime` (Def 25), lemas básicos. Pendientes documentados en header: Def 26 `IsFactorization` (necesita `pow`/`prod_list`), Ax-P (TFA), Fases 18-19 (Gödelización → módulo `Meta/` futuro). Build verde, 0 sorrys.

- **2026-06-03 — Block7 (BLOQUE VII Funciones Discretas) AÑADIDO**: nuevo módulo con `IsFunction`/`Functional` (meta-predicados Lean) y los 3 teoremas F1 (`IsFunction nil`), F2 (evaluación única `IsFunction F ∧ In ⟨x,y⟩ F ∧ In ⟨x,y'⟩ F → y=y'`), F3 (bicondicional `IsFunction ⟺ Functional`). Compiló a la primera, 0 sorrys. Cierra el alcance Cantor + Pares + Listas + Funciones declarado en `TuplasFuncionesYListas.md`.

- **2026-06-03 — `ax27_add_left_cancel` ELIMINADO**: derivable en PA⁻ sin inducción (tricotomía + monotonía + irreflexividad). Reescrito `add_left_cancel` (Block4_C6_C7) con prueba PA⁻; refactorizado `succ_le_of_lt` (Block2) para usar truco `ax13 + ax3 + ax18` (deriva `lt a a` y contradice). Sistema reducido **31 → 30 axiomas matemáticos**.

- **2026-06-03 — Build verde restaurado tras `537fd68`**: el commit del 2026-06-02 introdujo `proj_is_cantor` en `Block4_C6_C7` usando `mod2_of_even` (Block5), creando dependencia circular. Solución: mover `mod2_of_even` a `Block4_C6_C7` (justo antes de `proj_is_cantor`). Ningún cambio de prueba, solo de ubicación. **Recuento canónico rectificado: 31 axiomas** (los docs previos decían "30" por un error histórico de conteo; el sistema siempre tuvo 33 antes de eliminar ax22/ax23/ax28).

- **2026-06-02 — `ax22`/`ax23` ELIMINADOS** (commit `537fd68`, Claude Code Pro / Copilot Pro): `proj1`/`proj2` ya no son símbolos opacos del lenguaje sino `def proj1 (c) := x_of_c c` y `def proj2 (c) := y_of_c c` en `Block4_C6_C7`. El contenido de ax22 se demuestra constructivamente como teorema `proj_is_cantor`. `ax23` (`cantor_proj_uniq`) nunca se usó en código (la unicidad real estaba probada como `cantor_uniqueness`). `Block5` refactorizado para usar `proj_is_cantor` en lugar de `spec h_ax22`.

- **2026-06-02 — `ax28_mul_two_cancel` ELIMINADO**: la spec `TuplasFuncionesYListas.md §Teo 2.11` ya proporcionaba la prueba sin inducción (tricotomía + irreflexividad + monotonía estricta de *2). Reprobado `teo_2_11` directamente en Block1 (con nuevos helpers `mul_two_succ_ne_zero` y `mul_two_lt_mono`). Refactorizados `cantor_injective_c` (Block4) y `cantor_uniqueness` (Block4_C6_C7) para usar `teo_2_11` real.

- **2026-06-02 — REFERENCE.md proyectado**: reescritura completa, sustituyendo la versión severamente stale (todos los módulos marcados 🔄 In progress, fechado 2026-05-12). Ahora refleja 9/9 módulos ✅ Complete, 30 axiomas, lista de exports por módulo con signatura Lean + descripción matemática + dependencias.

- **2026-05-27 — 🎉 PROYECTO A 0 SORRYS REALES**: Cerrados los 2 últimos pendientes (`concat_assoc` e `in_concat_iff`) postulando `ax_C3_concat_assoc` y `ax_L3_in_concat` en Axioms.lean. Ambos son teoremas en sistemas con inducción; en Minimal se postulan (mismo patrón que ax21/ax24/ax27/ax28). Los 5 `axiom imp_intro/gen/raa/or_elim/ex_elim` son meta-reglas de FOL, no `sorry`. Build verde, WARN_sorry=0.

- **2026-05-27 — Block6 5/7 (sólo quedan los inductivos)**: Probados `cons_neq_nil` (vía ax_L0 + `is_cantor_pair` + teo_2_9 + ax9/ax5 + ax2), `cons_inj` (vía ax_L0 + `pair_inj` + ax3), `in_cons_self_nil` y `in_cons_nil_imp_eq` (vía ax_L2 triple-spec + ax_L1 para el caso falso), y `concat_singletons` (vía ax_C1 + ax_C2 + helper `eq_congr_cons_right`). Quedan `concat_assoc` y `in_concat_iff`: no derivables en Minimal sin inducción sobre L. Patrón del proyecto: postular como axiomas (candidatos a `ax_C3_concat_assoc` y `ax_L3_in_concat_iff`).

- **2026-05-27 — Block5 COMPLETO (0 sorrys)**: Probados `mod2_of_even` (vía ax24), `proj1_pair_eq_x`, `proj2_pair_eq_y` (vía `cantor_uniqueness` + ax22 + lema clave `is_cantor_pair`), `pair_proj_eq_c` (vía `cantor_injective_c` + ax22 + `is_cantor_pair`), y `pair_inj` (vía `cantor_uniqueness` tras `eq_congr_mul_left` para transportar al mismo `c = pair x y`). Lema clave nuevo `is_cantor_pair (x y) : mul two (pair x y) =eq cantor_poly x y` derivado de `cantor_poly_is_even` + `mod2_of_even` + ax17 + ax4 + `mul_comm'`.

- **2026-05-27 — Block4_C6_C7 COMPLETO (0 sorrys)**: `cantor_surjectivity` cerrado. Construcción: `w` desde `lemma_C5`, `k` desde `parity_lemma w` (`w(w+1)=2k`), `y := sub c k` con `k ≤ c` (de `2k ≤ 2c` y `ax28`/`le_of_mul_le_mul_left`), `x := sub w y` con `y ≤ w` (tricotomía + contradicción usando `expand_succ_succ` y `h_w_hi`). Verificación de `is_cantor` por cadena ecuacional `(x+y)(x+y+1) = w(w+1) = 2k`, luego `2k + 2y = 2c` vía `ax29_sub_witness` + `ax12_mul_distrib`. Sentencia ajustada a `liftTerm 0 (liftTerm 0 c)` bajo ∃∃; cierre con `ex_intro x; ex_intro y; simp + FOL.substTerm_liftTerm/liftLift`.

- **2026-05-27 — Infraestructura de resta añadida**: `sub_sym`, `def sub (a b)`, `ax29_sub_witness : ∀ a b, b ≤ a → b + (a − b) = a`. Permite cerrar `cantor_surjectivity` sin postular axiomas adicionales del estilo `sub_zero`/`sub_succ` (la unicidad determinada por el axioma testigo basta).

- **2026-05-27 — Block4_C5 completo (0 sorrys)**: Demostrados `sq_2w_plus_1`, `w_w1_le_2c_iff_sq_2w1_le_8c1`, `mono_w_w1`, `h_sq_2w1_le_sq_s`, `h_existence_part2` (este último por contradicción reusando el iff). Sentencia de `lemma_C5` corregida a `liftTerm 0 c` (era bare `c`, mal-formada en De Bruijn) y cerrada con `ex_intro w`. Eliminado `h_uniqueness` (código muerto: la meta es `∃` no `∃!`). Exportados además `lemma_C5_unique` y `cantor_bounds`.

- **2026-05-27 — Block4_C6_C7: `cantor_uniqueness` ✅**: Probado vía `cantor_bounds` + `lemma_C5_unique` + `add_left_cancel` + ax28. Helper local `add_comm_c`.

- **2026-05-27 — Conflicto de merge en FOL resuelto**: `FOL/Theorems/Eq.lean` tenía marcadores `<<<<<<<`/`=======`/`>>>>>>>` sin resolver entre dos `mutual` blocks (`substTerm_liftTerm_succ` HEAD vs `substTerm_lift_comm` incoming). Conservados ambos. También arreglados errores menores en `FOL/Theorems/Quantifiers.lean` (sintaxis `<;> [tac; tac]` → `<;> first | tac | tac`).

- **Block1–Block4 completados** (2026-05): Los cuatro bloques base (aritmética, raíz cuadrada, div2/mod2, auxiliares Cantor) están completamente probados sin sorrys.

- **Block4_C6_C7.lean — `add_left_cancel`** (2026-05-11): Demostrado el teorema de cancelación por la izquierda. Lema A privado (`lift_01_eq_00`) para triple `spec` sobre axiomas `forall_3`.

---

## Pending Work

**`Minimal/`, `Full/` y `Meta/` (Niveles A–D) completos.** Gödel I es REAL y sin postulados; D1 y D2
son teoremas reales. **Lo único vivo es D3** (Σ₁‑completitud provable del verificador), en
construcción por el plan **12‑A** (`GODEL-D3-TRACKED-DESIGN.md` §12–§14):

| Fase 12‑A | Contenido | Estado |
|-----------|-----------|--------|
| 1a | `lenc`/`nthc` + ecuaciones `Prf` | ✅ |
| 1b | toolkit `<` en `Prf` → `prf_In_iff_boundedIn` | ✅ |
| 2 | `prf_In_runFn_iff` + `prf_chainOk_iff_chainOkB` (verificador Δ₀, sin acumulador) | ✅ |
| 3 puente | `d3_prf_of_reflect_bounded` (D3 ⇐ reflejar `boundedIn`/`chainOkB`) | ✅ |
| 3 átomo `=eq` | `Sigma1AtomPrf`: `eqCodeFn` + `prf_provCodeC'_eq_of_tracked` (rastreado) | ✅ |
| 3‑4 resto | reflexividad libre de muro, átomos `<`/`lineWF`, cuantificadores acotados | ⏳ |
| 5 | inducción estructural sobre `boundedIn`/`chainOkB` → `d3_prf` → `goedel_second_prf` | ⏳ |

*Nota honesta:* 12‑A ≈ portar la Σ₁‑completitud provable de IΣ₁ — trabajo de varias sesiones, pero ya
no queda ningún punto del plan sin verificar en código. **Alternativa siempre disponible**: consolidar
Gödel II **módulo el axioma D3** (`goedel_second'`), estado ya publicable.

Trabajo de limpieza: **F7a ✅ HECHA** (2026-07-09; 14→7 `axiom`, `Meta/Incompleteness.lean`
eliminado + 5 postulados de `Provability`). **F7b** (`GodelTwo.d3`) espera a D3 real (12‑A fase 5).

---

## Architecture

```text
ROBINSON_PlusPlus/
├── Minimal/
│   ├── Axioms.lean          # 34 axiomas + pow/prod_pairs + carc/cdrc + lenc/nthc + 5 meta-reglas FOL
│   └── Theorems/
│       ├── Block1.lean      # Aritmética básica, constantes, orden ✅
│       ├── Block2.lean      # Raíz cuadrada, cotas, unicidad ✅
│       ├── Block3.lean      # div2, mod2 ✅
│       ├── Block4.lean      # Lemas auxiliares de Cantor ✅
│       ├── Block4_C5.lean   # Lema C5: ∃!w, w(w+1)≤2c<(w+1)(w+2) ✅
│       ├── Block4_C6_C7.lean# add_left_cancel, proj1/2, proj_is_cantor, mod2_of_even ✅
│       ├── Block5.lean      # Pares: proj1/2_pair, pair_proj, pair_inj, is_cantor_pair ✅
│       ├── Block6.lean      # Listas: cons_neq_nil, cons_inj, concat_assoc, in_concat ✅
│       ├── Block7.lean      # Funciones: IsFunction, Functional, F1/F2/F3 ✅
│       └── Block8.lean      # Primos+factorización: Dvd, IsPrime, IsFactorization, Ax-P TFA, +10 teoremas ✅
├── Meta.lean                # Barrel de Meta/ (40 módulos)
├── Meta/                    # Nivel B + Nivel C (núcleo real) + Nivel D REAL (40 módulos)
│   ├── Godel.lean           # Nivel B: G, ⌜·⌝, Teo G1 (encode_injective) ✅
│   ├── Provability.lean     # Nivel C núcleo real: formCode+iny., IsFormula, Provable ✅ (legacy retirada F7a)
│   ├── Hilbert.lean … CheckArith.lean         # cálculo finitario Prf + verificador (19 reglas)
│   ├── Representability.lean … Diagonal.lean  # D1 + punto fijo + goedel_first_real
│   ├── ProofChain.lean … DiagonalTwo.lean     # verificador estructural runFn/chainOk + Gödel I real'
│   ├── HilbertDeduction.lean … DerivCondPrf.lean  # PrfH + deducción + D1/D2 finitarias reales
│   ├── ReflectionPrf.lean … Sigma1TrackedPrf.lean # D3 reducida + reflexión Σ₁ (tcFn: descartado)
│   ├── NumListPrf.lean      # 12‑A/1a: ecuaciones Prf de lenc/nthc ✅
│   ├── NatArithPrf.lean     # 12‑A/1b: toolkit aritmético de `<` en Prf ✅
│   ├── BoundedInPrf.lean    # 12‑A/1b: prf_In_iff_boundedIn ✅
│   ├── RunFnBoundedPrf.lean # 12‑A/2: prf_In_runFn_iff (runFn nil = map de carc) ✅
│   ├── ChainOkBoundedPrf.lean # 12‑A/2: prf_chainOk_iff_chainOkB (sin acumulador) ✅
│   ├── Sigma1BoundedPrf.lean # 12‑A/3 puente: d3_prf_of_reflect_bounded ✅
│   ├── Sigma1AtomPrf.lean   # 12‑A/3 núcleo: átomo =eq rastreado (eqCodeFn) 🔄
│   └── GodelTwo.lean        # Gödel II núcleo: goedel_second' (D2 real + `axiom d3`) 🔶
└── Full/                    # Eje 4: inducción general object-level + TFA (11 módulos)
    ├── Induction.lean       # ax6/7/10/11/12/18/19 derivados ✅
    ├── Mod2.lean            # ax_mod2_alternation + ax21/24 derivados ✅
    ├── Lists.lean           # ax_list_induction + ax_C3/L3 derivados ✅
    └── … Numerals / Bounded / Divisibility / Division / PrimeFactor / Primality / Factorization (tfa_numeral) ✅
```

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-07-09c — Build ✅ (76 jobs), 0 errores, 0 sorrys, 0 warnings, 62 módulos, Lean v4.31.0. F7a: 14 → 7 axiomas (AXIOMS.md). 12‑A fases 1a/1b/2 ✅ + fase 3 en curso (puente + átomo `=eq`).*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

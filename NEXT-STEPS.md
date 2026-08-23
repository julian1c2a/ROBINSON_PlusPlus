# Next Steps — ROBINSON_PlusPlus

---

## ▶ PUNTO DE REANUDACIÓN (leer PRIMERO)

**Estado 2026‑08‑23 · `master` limpio y verde · Lean v4.31.0**
**108 jobs · 94 módulos activos (Minimal 11 + Meta 72 + Full 11) + 10 en `cuarentena/` · 10 `sondeos/`**
**7 `axiom` de Lean · 0 errores · 0 warnings · 0 sorrys** (las 4 coincidencias de `sorry` son
comentarios).

> ## ✅ LA INCONSISTENCIA CONOCIDA ESTÁ REPARADA
>
> `ax_tc_cons` **RETIRADO** de `axioms`. Era la ecuación que obligaba a `tcFn` a recurrir a la vez
> sobre estructura NUMERAL y sobre estructura de CÓDIGO — imposible, porque en ℕ el mismo valor es
> ambas cosas (`cons 0 nil = 2 = σσ0`). El lema diagonal está reconstruido por la **vía NUMERAL**
> (`Meta/DiagonalNumeral.lean`).
>
> ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### Lo que hay, verificado con `#print axioms`
>
> | | |
> |---|---|
> | **`goedel_first_numeral`** | `ConsistentOmega → ¬Prf godelCN` — **Gödel I** |
> | `goedel_first_undecidable_numeral` | `… → Reflects godelCN → ⊬G ∧ ⊬¬G` |
> | `goedel_first_undecidable_omega` | lo mismo desde ω‑consistencia (`OmegaReflect`) |
> | `repr_pos'_prf` | **D1**, intacta |
> | `prf_formCode_numeral` | `formCode φ =eq numeral (codeNat φ)`, net‑0 |
> | `prf_div2_numeral`, `prf_cons_eval` | la cadena aritmética, net‑0 |
>
> Footprint de Gödel I: `[propext, choice, Quot.sound, dne, gen, imp_intro, ax_induction,
> ax_list_induction, ax_axiomsCodeT_eq]` — la base sancionada de siempre, **menos `tc_cons`**.

> ## ✅✅ LA ESCALERA (a.2) ESTÁ **COMPLETA — 4 de 4**
>
> `pcc_dot_cons` **HECHO** (`Meta/DotConsPrf.lean`, 2026‑08‑22), footprint
> `[propext, choice, Quot.sound, prf_axiomsCodeT_eq]` — la base sancionada, **sin `tc_cons`**:
>
> ```lean
> pcc_dot_cons (h t : Term) :
>     Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (tcFn (cons h t))))
> ```
>
> o sea `⊢ Prov(⌜ cons(ḣ,ṫ) = (cons h t)˙ ⌝)` — el `prf_cons_eval` **internalizado y para argumentos
> ABSTRACTOS**.
>
> | peldaño | estado | dónde |
> |---|---|---|
> | `Prov(⌈ ẋ + ỳ = (x+y)˙ ⌉)` | ✅ | `Meta/EvalArithPrf.lean` — `pcc_eval_add`, por `prf_nat_induction`, ~440 líneas |
> | `Prov(⌈ ẋ · ỳ = (x·y)˙ ⌉)` | ✅ | `Meta/EvalMulPrf.lean` — `pcc_eval_mul`. **Consume `pcc_eval_add`** en el paso |
> | `div2` | ✅ **atajo, sin inducción** | `prf_div2_double_all` (`Prf.gen` sobre `prf_div2_double`) + `pcc_thm_inst` |
> | `Prov(⌈ cons(ḣ,ṫ) = (cons h t)˙ ⌉)` | ✅ | `Meta/DotConsPrf.lean` — ensamblaje en 3 fases, **sin inducción nueva** |
>
> ### Cómo salió (y por qué fue barato)
>
> `cons` **no tiene ecuaciones recursivas propias**: `ax_L0_cons_def` lo define como
> `div2 (cantor_poly h (σt))`, o sea puro `+`, `·` y `div2`, los tres ya internalizados. Así que el
> peldaño es **ensamblaje**, no inducción. Tres fases, todas verdes a la primera:
>
> * **(A)** `substCodeF` **computa por `rfl`** sobre el cuerpo de `ax_L0_cons_def`, igual que sobre
>   `ax5`/`ax9` (`prf_substfc_arith_open`). Era la pregunta arriesgada; salió que sí.
> * **(B)** el polinomio se evalúa dentro de `Prov` en **cinco pasos**, alternando reescrituras
>   internas (`pcc_rw`) con reescrituras **de código**, que son gratis (`succcT (tcFn x) = tcFn (σx)`
>   es `prf_tc_succ'`, y `tcFn` es congruente ⇒ todo teorema OBJETO se «dota» sin coste).
> * **(C)** el `div2` se cancela contra `prf_div2_double` vía `pcc_thm_inst`; el puente con el
>   polinomio es **`prf_cons_double`** (`Div2ParityPrf`), que es objeto y se dota con `prf_congr_tcFn`.
>
> 🔑 **La idea que abarató (B):** el polinomio `(x+y)·σ(x+y)+2y` menciona `x+y` **dos veces**.
> Reescribir por posiciones exigiría congruencias a cada profundidad — pero `substfc` sustituye
> **todas** las ocurrencias del hueco a la vez, así que **un solo** `pcc_leibniz_apply` con el
> contexto `Ac := C[v₀]` cierra ambas. De ahí que (B) sean 5 pasos y no 15. `pcc_rw` empaqueta el
> patrón y es reutilizable para cualquier evaluación futura dentro de `Prov`.
>
> ### ▶▶ DÓNDE SE RETOMA: **repatriar la cuarentena** — el rédito ya está VERIFICADO
>
> **`sondeos/CarcPayoff.lean`: `pcc_eval_carc` YA VUELVE**, con el mismo enunciado y el mismo
> footprint. El viejo (`cuarentena/EvalListPrf.lean:130`) cerraba con `prf_tc_cons'` — el puente que
> murió con la reparación — y la sustitución es **un único `pcc_rw` con `pcc_dot_cons`**; los pasos
> 1‑3 (instancia de `ax_carc` + los dos `substfc` computados) quedan **intactos**.
>
> #### ⚠️ Corrección de la auditoría 2026‑08‑22: son **8 raíces**, no 6
>
> El recuento anterior buscaba sólo `prf_tc_cons` y se dejó fuera **`CodeTreeReflect`** y
> **`LineWFEfqPrf`**, que usan la **otra** sub‑familia: `prf_tc_nul`/`prf_tc_un`/`prf_tc_bin`, los
> constructores del KIT. Grafo recalculado por máquina en `cuarentena/README.md`.
>
> Y **`EvalListPrf` no es sólo el keystone: es la BASE.** No tiene ninguna dependencia dentro de la
> cuarentena, los **otros 20 dependen de él**, y es donde se **define** `prf_tc_cons'` (`:48`) — el
> origen literal de la contaminación. **Nada vuelve antes que él.**
>
> #### 📋 PLAN EJECUTABLE — orden de repatriación
>
> | # | paso | qué hay que hacer | estado |
> |--:|---|---|---|
> | **1** | **`EvalListPrf`** | los 3 usos de `prf_tc_cons'` → `pcc_rw_dot_cons_un` | ✅ **HECHO 2026‑08‑23** |
> | **2** | **`EvalNthcPrf`** → `EvalCarcNthcPrf` | necesitó **`pcc_rw_imp`** (la forma implicación de `pcc_rw`) | ✅ **HECHO 2026‑08‑23** |
> | **3** | **`D3InDotPrf`** | familia `prf_tc_form`, por **conversión en la frontera** | ✅ **HECHO 2026‑08‑23** — arrastró `BdAllIntroPrf`. **D3 vuelve a estar reducida a UN SOLO lema** |
> | **4** | **KIT**: `CodeCtorKit` (4) → `CodeTreeReflect` (2) → `LineWFEfqPrf` (1) | ✅ **MEDIDO** (`sondeos/KitPayoff.lean`): los 3 sustitutos ya están escritos y compilados. El coste está en mudar `prf_tc_objAt` dentro de `Prov` | ▶ **el siguiente** |
> | **5** | `LineWFTrackedPrf` (8) | `prf_tc_cons'` + `prf_tc_eqc`. `prf_tc_eqc` es un `binT 4` ⇒ debería caer con el KIT | ⏳ |
> | **6** | `InAxiomsCodePrf` (2) | medido: el más fiddly de los tres (hipótesis muerta + hueco en cabeza de `cons`) | ⏳ |
> | **3bis** | **KIT: `pcc_dot_nul`/`_un`/`_bin`** | ⚠️ **medir primero.** Desbloquea `CodeCtorKit` (12 usos), `CodeTreeReflect`, `LineWFEfqPrf` | ⏳ **sondeo pendiente** |
> | **4** | `LineWFTrackedPrf` + los 14 tags | 6 usos (`prf_tc_cons'` + `prf_tc_eqc`); caen `LineWFSchemaPrf`, `LineWFPropPrf`, `LineWFMpPrf`, `LineWFThyPrf`, `LineWFAssemblePrf`, `BdAllIntroPrf` | ⏳ |
> | **6** | **D3** → **Gödel II** → **F7b** (7→6 `axiom`) | `D3DottedPrf` **ya ha vuelto** (paso 1) y `d3_prf_of_dotted_atoms` es **net‑0** | ⏳ |
>
> ### 📏 MEDICIÓN del KIT (2026‑08‑23) — **la última familia, y tampoco es un muro**
>
> `sondeos/KitPayoff.lean`, cuatro declaraciones compiladas. **La hipótesis era correcta**: los tres
> sustitutos salen **por composición de `pcc_dot_cons`, sin inducción nueva**.
>
> | | cómo sale |
> |---|---|
> | `pcc_dot_nul` | **sólo reescrituras de CÓDIGO** — las hojas (`prf_tc_numeral`, `prf_tc_zero`) **nunca murieron** |
> | `pcc_dot_un` | código → **1 paso interno** (`pcc_rw`) → código |
> | `pcc_dot_bin` | código → **2 pasos internos anidados** → código |
>
> Los tres con footprint sancionado.
>
> 🔑 **Hizo falta `pcc_dot_cons_symm`**, que sale de `pcc_eq_symm_code_internal` — y **ésa volvió con
> `BdAllIntroPrf` en el paso 3**. Los pasos componen: hacerlos en orden de cascada dejó la
> herramienta a mano justo cuando hacía falta.
>
> #### ⚠️ Dónde está el coste real: NO en el KIT, sino en `CodeTreeReflect`
>
> ```lean
> prf_tc_objAt (t) : ∀ T : CTree, Prf (tcFn (T.objAt t) =eq T.dotV t)
> ```
>
> Es **recursión estructural sobre `CTree`** que produce una igualdad **de código**. Con sustitutos
> internos, la recursión entera se muda **dentro de `Prov`**. **Todas las piezas existen y están
> activas**: `pcc_eq_trans_code` (`EvalArithPrf`) y las congruencias internas del KIT
> (`pcc_congr_unT_code`, `pcc_congr_binT_1/2_code`), que **sobreviven intactas** y ya están en forma
> implicación. ⇒ conversión **mecánica pero voluminosa**.
>
> ### ✅ PASO 3 EJECUTADO (2026‑08‑23) — `D3InDotPrf`, y **D3 vuelve a estar reducida a un solo lema**
>
> ```lean
> d3_prf_of_chainOkDot (φ) : Prf (chainOk nil #0 ⇒ provFromCode chainOkDot)
>                          → Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))
> ```
>
> Ese consecuente **es D3**. Footprint sancionado (`prf_axiomsCodeT_eq`), sobre la teoría
> **reparada**. Arrastró `BdAllIntroPrf` (§40, `pcc_bdAll_intro`) sin tocar una línea.
>
> **La estrategia de frontera funcionó tal cual se midió.** Los tres usos de `prf_tc_form` se
> repartían así:
>
> * **dos** estaban en `substtc_inv_termCode_formCode`, cuyo enunciado **no cambia**: bastó una
>   prueba nueva por `substCodeT_closed` — `formCode φ` es **cerrado**, así que la invariancia
>   `substtc` no necesita pasar por `tcFn` en absoluto. *Lección: mirar si el lema realmente
>   necesitaba el puente, o sólo lo usaba de atajo.*
> * **uno** era el genuino, dentro de `pcc_bddCarcDot_reflect`. Ahí el transporte de código sólo
>   llega a `termCode (numeral (codeNat φ))`, y la frontera se cruza **dentro de `Prov`** con
>   `pcc_to_formCode_imp`. **Ningún enunciado público cambió**, y `D3DottedPrf` encajó sin tocarse.
>
> ### 📏 MEDICIÓN de `InAxiomsCodePrf` (2026‑08‑23) — más caro de lo que parecía
>
> Sus 2 usos **no** son como el de `D3InDotPrf`:
>
> * `prf_tc_listFormCodeM` usa **también `prf_tc_of_cons`** (muerto) ⇒ es meta‑recursión sobre lista,
>   el mismo patrón que `prf_tc_form` mismo. Se resolvería con `prf_objList_numeral`
>   (`Sigma1CorePrf:218`, ya existe y es genérico) + `liftTerm_listFormCodeM` (existe,
>   `Minimal/Axioms:654`).
> * ⚠️ **`pcc_in_head_swap` toma la ecuación muerta COMO HIPÓTESIS** (`haform : Prf (tcFn a =eq
>   termCode a)`), y la conversión hay que meterla **dentro de un código `cons`** — el objetivo es
>   `inFormCodeFn yc (termCode (cons a t))`, con el hueco en la **cabeza**. Más fiddly que el de
>   `D3InDotPrf`.
>
> Su buena noticia: `substtc_inv_termCode_listFormCodeM` (el consumidor principal) es **invariancia
> de un código cerrado**, o sea el caso barato — `substCodeT_closed`, igual que en el paso 3.
>
> ### 📏 MEDICIÓN de `prf_tc_form` (2026‑08‑23) — la tercera familia **no es un muro**
>
> `sondeos/TcFormPayoff.lean`, cuatro declaraciones compiladas. Dos hallazgos:
>
> **1. El sustituto directo es UNA LÍNEA y net‑0.**
>
> ```lean
> prf_tc_form_numeral (φ) : Prf (tcFn (formCode φ) =eq termCode (numeral (codeNat φ)))
>   := prf_eq_trans (prf_congr_tcFn (prf_formCode_numeral φ)) (prf_tc_numeral (codeNat φ))
> ```
>
> Es la vía numeral aplicada a la estructura CONCRETA de `φ` — justo el «nivel 1» que
> `PLAN-FRENTE-A.md` predijo que la reparación cubría. Las hojas de la vieja meta‑recursión
> (`prf_tc_numeral`, `prf_tc_zero`) **nunca murieron**; sólo el paso `prf_tc_of_cons`.
>
> **2. ⚠️ Pero el lado derecho NO es negociable, y esto es lo importante.**
>
> `inDot φ` está fijado por **`D3DottedPrf`** —que ya está **activo y es net‑0**— como
> `substfc 0 (tcFn #0) (formCode (In (formCode φ) (runFn nil #0)))`. Ese código lleva
> `termCode (formCode φ)`, **no** `termCode (numeral (codeNat φ))`, y **es el objetivo de D3**:
> sale de la definición de `provCodeC'`. Cambiarlo no sería «refundar un enunciado» — sería
> **cambiar el teorema**.
>
> **La salida, y es elegante:** los dos códigos son los de dos términos objeto **provablemente
> iguales** (`prf_formCode_numeral`), y **D1 dota cualquier teorema `Prf`**. Así que el puente entre
> las dos formas sale **dentro de `Prov`**, gratis:
>
> ```lean
> repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ))
>   : Prf (provFromCode (eqc ⌜numeral (codeNat φ)⌝ ⌜formCode φ⌝))
> ```
>
> …que es **exactamente** el `heq` que `pcc_rw`/`pcc_rw_imp` piden (verificado: `provCodeC' (a =eq b)`
> unifica con `provFromCode (eqc ⌜a⌝ ⌜b⌝)`). De ahí salen `pcc_to_formCode` y `pcc_to_formCode_imp`.
>
> **⇒ ESTRATEGIA: no tocar las definiciones, convertir en la FRONTERA.** Probar por dentro en forma
> NUMERAL (donde `prf_tc_form_numeral` funciona) y aplicar `pcc_to_formCode_imp` al final. Así los
> enunciados públicos de `D3InDotPrf` —`inDot`, `bddCarcDotAt`, `hI_dot`, `d3_prf_of_chainOkDot`—
> quedan **intactos**, y `D3DottedPrf` sigue encajando sin tocarse.
>
> **Radio de impacto medido:** `D3InDotPrf` = 3 usos de `prf_tc_form` + 8 menciones de
> `termCode (formCode φ)` (de las cuales **1 definición** y **2 enunciados**, el resto cuerpos de
> prueba). `InAxiomsCodePrf` = 2 usos y **0** menciones ⇒ mucho más barato, pero depende de
> `D3InDotPrf`, así que va detrás.
>
> ### ✅ PASO 2 EJECUTADO (2026‑08‑23) — `pcc_rw_imp`, y la tercera familia a la vista
>
> `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta. **No valía el molde del paso 1**, y por tres razones
> que conviene recordar para los que quedan:
>
> 1. Los sitios viven dentro de **`PrfH`** (con contexto de hipótesis) ⇒ un `Prf → Prf` no encaja.
>    Hizo falta **`pcc_rw_imp`**, la forma implicación de `pcc_rw` (`Meta/DotConsPrf.lean`, **net‑0**):
>    `Prov(⌜G X⌝) ⇒ Prov(⌜G Y⌝)`, que entra en `PrfH` con `PrfH.mp` + `prf_to_prfH`. Se monta con
>    `pcc_leibniz_code` + `pcc_mp_code_apply` + `pcc_mp_code_open`, las tres ya existentes.
> 2. `nthcT` es **binario** y el hueco va en el primer argumento ⇒ molde propio,
>    `pcc_rw_dot_cons_nthc`.
> 3. El `cons` era **una de tres ranuras** que la prueba reescribía a la vez. Las otras dos van por
>    `prf_tc_zero`/`prf_tc_succ'`, que **siguen vivos** ⇒ hay que **separarlas**: primero las sanas a
>    nivel de código, y sólo el `cons` por dentro de `Prov`.
>
> ⚠️ **Efecto colateral a vigilar:** importar `DotConsPrf` arrastra `NatOrderPrf`, y aparecieron
> **ambigüedades de nombre** (`PrfH_lt_subst1`/`_subst2` existen en `NatOrderPrf` y en
> `BoundedInPrf`). Se resuelven cualificando (`BoundedInPrf.PrfH_lt_subst2`). Esperar más de esto
> según se repatríen módulos.
>
> ### ✅ PASO 1 EJECUTADO (2026‑08‑23) — 7 módulos recuperados, cuarentena 21 → 10
>
> `EvalListPrf` repatriado. El trabajo real fueron **3 sitios**, no 6: el recuento anterior incluía la
> definición, el `export` y los docstrings. Y los tres tenían **la misma forma**, así que se cerraron
> con **un solo molde**:
>
> ```lean
> pcc_rw_dot_cons_un (F : Term → Term) (hFs …) (hFc …) (R : Term) (hR …) (h t : Term)
>     (hbase : Prf (provFromCode (eqCodeFn (F (consT (tcFn h) (tcFn t))) R))) :
>     Prf (provFromCode (eqCodeFn (F (tcFn (cons h t))) R))
> ```
>
> Es `pcc_rw` con contexto `G s := ⌜F s = R⌝` y `pcc_dot_cons h t`. Instanciado en `carcT`/`cdrcT`/
> `lencT`. **Compiló a la primera.** Todo net‑0 salvo `prf_axiomsCodeT_eq`, y los enunciados de
> `pcc_eval_carc`/`_cdrc`/`_lenc` son **idénticos** a los de la versión en cuarentena.
>
> Dos limpiezas que hicieron falta y no estaban en el plan:
> * **`prf_tc_cons'` se BORRA**, no se reescribe: su cuerpo era `prf_tc_cons`, que **ya no existe**.
> * **4 declaraciones duplicadas** con `DotConsPrf` (`consT`, `prf_congr_consT`, `prf_substtc_consT`,
>   `substtc_inv_consT`) — se borran y se importan.
>
> **La cascada fue el rédito grande.** Al volver `EvalListPrf` quedaron libres, sin tocar una línea:
> `EvalLtPrf`, `EvalRunFnPrf`, `EvalBoundedPrf`, `Delta0ReflectPrf`, `PropCodePrf` y **`D3DottedPrf`**.
> Los seis compilan tal cual.
>
> 🎯 **`D3DottedPrf` es el que importa**: contiene `d3_prf_of_dotted_atoms` — la **reducción de D3** —
> y vuelve **net‑0** (`[propext, choice, Quot.sound]`). También vuelve `PropCodePrf` (§39, la lógica
> interna completa incl. `pcc_ind_code`, net‑0).
>
> ### Estado de la cuarentena: **10 módulos**, 5 raíces
>
> Raíces (**5**, tras los pasos 1‑3): `LineWFTrackedPrf` (8) · `CodeCtorKit` (4) ·
> `CodeTreeReflect` (2) · `InAxiomsCodePrf` (2) · `LineWFEfqPrf` (1).
> No‑raíz (5, caen solos): `LineWFAssemblePrf`, `LineWFMpPrf`, `LineWFPropPrf`, `LineWFSchemaPrf`,
> `LineWFThyPrf`. Grafo en `cuarentena/README.md`.
>
> ✅ **Las TRES sub‑familias están MEDIDAS, y ninguna es un muro:** `prf_tc_cons'` (resuelta,
> `pcc_dot_cons`), `prf_tc_form` (resuelta, conversión en la frontera) y el **KIT** (medido,
> `sondeos/KitPayoff.lean` — los sustitutos ya están escritos).

> ### ⚠️ TRAMPAS METODOLÓGICAS — caras, no repetir
>
> 0. **Los documentos de estado se actualizan por su BANNER y no por su CUERPO.** (auditoría
>    2026‑08‑22) `CURRENT-STATUS-PROJECT.md` tenía un banner correcto y una tabla que decía «113 jobs,
>    99 módulos»; `DECISIONS.md` ADR‑007 llevaba **un mes** diciendo «no implementado — no existe
>    todavía `doc/`» sobre un directorio que existe con 5 nodos. **Al auditar, leer el cuerpo.**
> 0bis. **Al contar por familia de símbolos, contar la familia ENTERA.** El recuento de raíces de la
>    cuarentena buscó `prf_tc_cons` y se dejó dos raíces que usan `prf_tc_nul`/`un`/`bin`. 6 → 8.
> 1. **La alcanzabilidad por `import` da FALSOS NEGATIVOS.** Me hizo afirmar en falso que Gödel I
>    estaba limpio. Un **crawler de dependencias tampoco vale**: Lean 4.31 da `value? = NONE` para
>    teoremas importados, o sea sólo recorre tipos. **La técnica buena**: convertir el puente
>    sospechoso en **`axiom` de Lean** y leer `#print axioms`. Meter siempre un **control positivo**.
> 2. **No lanzar sondeos contra un árbol que cambia.** El workflow S2 corrió mientras una rama tenía
>    `ax_tc_cons` retirado y dos diseños leyeron el árbol mutado.
> 3. **`lake build` puede dar VERDE sin construir lo que crees.** La `lean_lib` sólo construye lo
>    **alcanzable desde el módulo raíz**: mover ficheros a `Meta/` sin añadir el `import` en
>    `Meta.lean` los deja fuera del build. **Señal de alarma: el número de jobs no cambia.**
> 4. **Filtrar comentarios de bloque** al buscar usos de un identificador: contar menciones en
>    documentación infló una cuarentena de 31 a 72 módulos.

> ### ⏸️ Otros frentes, sin cambios
>
> **`repr_neg` / `NegVerifier` para `⊬¬G`** — independiente, `PLAN-NEGVERIFIER.md`.
> ⚠️ NO recuperar F7a (ver [[project-godel-first-complete]]).
> **`prf_strong_induction`** al 90 % (rama B); `Meta/StrongInductionPrf.lean:156‑178`.
> **El LIBRO**: ver `PLAN-LIBRO.md`, Parte IV reescrita con el episodio de hoy.

> ### 🎯 FOTO DE REANUDACIÓN (2026‑07‑20)
>
> **⚠️ FOOTPRINT CAMBIÓ (`25d255b`):** nuevo `axiom prf_axiomsCodeT_eq : Prf (axiomsCodeT =eq
> listFormCodeM axioms)` (espejo `Prf` del `ax_axiomsCodeT_eq` de `⊢`) ⇒ **`prf_inAxC` es ahora
> TEOREMA** (derivado; net‑0 axiomas). **D1 `repr_pos'_prf` cita ahora `prf_axiomsCodeT_eq`** (antes
> `prf_inAxC`); `d2_prf` limpio; `goedel_second'` sigue citando sólo `d3`. Cadena real intacta.
>
> **DÓNDE ESTAMOS:** B.3c = `pcc_lineWF_tracked (t) : Prf (lineWF t ⇒ provFromCode (lineWFCodeFn
> (tcFn t)))` (reflexión punteada de `lineWF`, 21 tags, que consume `hC_dot` → D3). Módulo A +
> B.1/B.2/B.3a/B.3b **cerrados**.
> - **✅ `eqrefl` (tag 12) CERRADO** — PLAN (A) esquema estricto (`Meta/LineWFTrackedPrf.lean`):
>   `ax_lineWF_eqrefl` ahora `lineWF #0 ⇔ ((lenc #0 = 3̇) ∧ (carc #0 = eqc …))`; la cláusula `lenc`
>   fuerza las cotas de sub‑índice (hueco real cerrado). ⇒ `pcc_lineWF_tracked_eqrefl_imp (t)` SIN
>   hipótesis de cota. Accesor concreto conserva enunciado (`prf_iff_drop_left_conj`).
> - **✅ `In`‑REFLECT de `axiomsCodeT` CERRADO** (`Meta/InAxiomsCodePrf.lean`) — era el nudo
>   `NegVerifier` (8‑11 sesiones); NO bloqueado por Tarski (código rastreado `carcT(tcFn·)`):
>   `pcc_in_head_swap`+`pcc_in_tail_tracked`+**`pcc_In_lfc_tracked`** (recursión sobre lista de
>   axiomas ABSTRACTA)+**`pcc_In_axiomsCodeT_tracked`** (`In y axiomsCodeT ⇒ Prov(⌜In yc axiomsCodeT~⌝)`,
>   `yc` rastreado invariante + `hbr : Prov(yc = tcFn y)`).
>
> **▶ MAÑANA — cerrar `thy`** (mecánico, espejo de `eqrefl`; todas las piezas duras hechas):
> instanciar `pcc_In_axiomsCodeT_tracked` con `yc = carcT(tcFn t)`, `y = carc t`, `hbr` de
> `pcc_eval_carc` (+ probar `carcT(tcFn t)` `substtc`‑invariante); strict schema `thy` (`lenc = 2`,
> forma explícita en `Minimal/Axioms.lean:1010`); backbone; `pcc_lineWF_tracked_thy`.
> **Después:** `mp` (tag 16, explícita, incondicional) + 17 tags `=eq` (clones de `eqrefl`, conviene
> helper genérico) + `or_elim` ×21 (`prf_lineWF_inv`). Detalle en el bloque «🔖 SIGUIENTE PASO
> CONCRETO» más abajo.

**Histórico (2026‑07‑14) · 85 módulos · 7 `axiom` de Lean (`AXIOMS.md`):**

> ### 🔖 ÚLTIMO AVANCE (2026‑07‑14): **MÓDULO A (decodificador) — MITAD DE FÓRMULAS CERRADA** ✅
>
> `Meta/CodeDecode.lean` (nuevo, ~330 líneas, todo `[propext, choice, Quot.sound]`):
> **`decodeForm` es una BIYECCIÓN verificada** entre códigos de fórmula y fórmulas.
>
> | | round‑trip (`decode (code v) = some v`) | **inyectividad** (`decode c = some v → c = code v`) |
> |:--|:--|:--|
> | `decodeNat` | ✅ `decodeNat_numeralM` | ✅ `decodeNat_inj` |
> | `decodeChars` / `decodeStr` | ✅ `decodeChars_charsCodeM` / `decodeStr_strCodeM` | ✅ `decodeChars_inj` / `decodeStr_inj` |
> | `decodeTerm` / `decodeTerms` (mutuos) | ✅ `decodeTerm_termCodeM` / `decodeTerms_termsCodeM` | ✅ `decodeTerm_inj` / `decodeTerms_inj` |
> | `decodeForm` (9 tags) | ✅ `decodeForm_formCodeM` | ✅ **`decodeForm_inj`** ← *la «dirección crítica» del plan* |
>
> **▶ MÓDULO A COMPLETO — `Meta/CodeDecode.lean` + `Meta/ChainDecode.lean`.**
> Fórmulas (A.1) = biyección; cadenas (A.2) = `peelArgs`, `decodeRule`/`decodeLine`/`decodeChain`,
> `DecidableEq Term`/`Formula` + `findIdx` (con corrección), retract de los 18 tags limpios, sección de
> `thy`/`mp`/`gen`, y el **ENSAMBLADO**:
> ```lean
> decodeChain_checkProof : decodeChain t = some rs → ∃ L, checkProof rs = some L   -- SOLIDEZ
> decodeChain_prf : decodeChain t = some rs → (∀ L, checkProof rs = some L → φ ∈ L) → Prf φ
> ```
> Lo que el módulo E consume es la **solidez** (cadena decodificada ⟹ derivación válida ⟹ `Prf` vía
> `derivation_to_prf`), NO el retract sintáctico `proofCode' rs = t` (que `peelArgs` no da para códigos
> con «cola basura»). Clave: `decodeLine` verifica `stepConcl acc r = some f`.
>
> **⚠️ HALLAZGO que corrigió el plan:** `lineJustif` es **lossy** para `thy`/`mp`/`gen` (descarta los
> índices) ⇒ el round‑trip `decodeChain (proofCode' rs) = some rs` (*retract*) es **FALSO**. Detalle
> en `PLAN-NEGVERIFIER.md` §4 y en la cabecera de `ChainDecode.lean`.
>
> **▶ MÓDULO B EN CURSO (§44, `Meta/LineWFCases.lean`)** — la tabla de los 21 tags.
> **HECHO:** `tagArity`/`tagConcl`/`tagPrems` + envoltorios `prf_lineWF_tag`/`prf_premsOf_tag`; la
> **dirección negativa** (`derives_lineWF_neg_of_tag`, y `derives_lineWF_neg_thy_of_not_prf` que ya
> **refuta** una línea `thy` de conclusión indemostrable); y la **des‑duplicación** del nivel `⊢`
> (`Meta/LineWFDerives.lean`: los 42 `lineWF_*`/`premsOf_*` que `ProofChain` probaba **por segunda vez**
> pasan a ser `prf_to_derives` de sus gemelos; `ProofChain` 870→540; D1/D2 con axiomas intactos).
>
> ⚠️ **`tagConcl` cubre 19, NO 21**: `thy` (15) va por `In … axiomsCodeT` (no es ecuación) y `mp` (16)
> es **INCONDICIONAL** ⟹ **`mp` no se puede refutar por `lineWF`**, sólo por `premsOf`/`boundedPremsIn`.
> **NO es el mismo corte que en el módulo A** (allí los raros eran `thy`/`mp`/`gen`; aquí `gen` SÍ es
> estructural).
>
> ### 🔖 SIGUIENTE PASO CONCRETO: **`substfcT`/`liftfcT` rastreados** → los 7 tags que faltan
>
> **B.3c va por 14 de 21 tags.** ✅ Cerrados: `eqrefl`(12) `thy`(15) `mp`(16) `efq`(8) `gen`(17)
> y los 9 proposicionales `p1 p2 c1 c2 c3 j1 j2 j3 p3`.
>
> **Las tres piezas genéricas que lo hicieron posible** (leer en este orden si se retoma):
> 1. **CHASIS** — `Meta/LineWFSchemaPrf.lean`. `pcc_lineWF_tracked_of_schema` es el ensamblaje
>    final; factoriza `schema_bwd`, `schema_backbone`, los punteados de tag/longitud (genéricos en
>    `k`/`n`), los puentes `pcc_{carc,nthc}D_bridge` y las cotas desde la longitud canónica.
> 2. **KIT** — `Meta/CodeCtorKit.lean`. `nulT`/`unT`/`binT` parametrizados por **tag y aridad**:
>    todos los constructores de código (`botc`=2, `eqc`=4, `implc`=5, `forallc`=6, `andc`=7,
>    `orc`=8, `exc`=9) son el mismo `cons`‑árbol. Incluye la congruencia **dentro de `Prov`**.
>    (`eqcT` de `LineWFTrackedPrf` es hoy `binT 4`.)
> 3. **ÁRBOL** — `Meta/CodeTreeReflect.lean`. `CTree` reifica los RHS y `PrfH_dotVN` prueba la
>    reflexión **por inducción, una sola vez**. Con esto **cada tag son TRES declaraciones**
>    (literal del árbol + un `rfl` + una llamada). Ver `Meta/LineWFPropPrf.lean` como plantilla.
>
> **▶ LO QUE FALTA — 7 tags: `q1`(9) `q2`(10) `q3`(11) `leibniz`(13) `ind`(18) `qconf`(19)
> `listInd`(20).** ⚠️ **NO son más de lo mismo.** Sus RHS llevan `substfc`/`liftfc` **dentro** del
> árbol, y ésas **no son constructores de código** (no son `cons`‑árboles) sino **funciones OBJETO**,
> del mismo tipo que `carc`/`nthc`. Verificado (2026‑07‑21) que **no existe** su contrapartida
> rastreada: no hay `substfcT`/`liftfcT`, ni `prf_tc_substfc`, ni `prf_substtc_substfc`. Los dos
> únicos lemas `Prf` con `substfc` en el mundo rastreado (`prf_substfc_ltCodeFn_varc0`,
> `prf_substfc_exBodyc`) son sobre la sustitución **externa** del código punteado — otra cosa.
>
> ⚠️ **NO confundir con `substCodeT`/`substCodeF`** (`Meta/SubstCodeOpenPrf.lean`), que **sí**
> existen pero son funciones **META** (recursión Lean sobre `Term`/`Formula`: «código de `t` con la
> variable `v` rellena por el código `w`»). No sirven aquí: en los 7 tags los argumentos de
> `substfc` son **términos objeto abstractos** (accesores `nthc #0 i` sobre la línea abstracta), que
> una función meta no puede recorrer. Lo que falta es el constructor **objeto** rastreado.
> (Comprobado 2026‑07‑22; la similitud de nombres es una trampa real.)
>
> ### ⛔ CORRECCIÓN (2026‑07‑22): el plan de abajo era ERRÓNEO EN SU FORMA — **no ejecutarlo**
>
> Se planificó «construir `substfcT`/`liftfcT` con su ecuación `tc`». **Esa ecuación no puede
> existir.** Diagnóstico verificado:
>
> * `tcFn` está axiomatizado **sólo** sobre `zero`/`succ`/`cons` (`ax_tc_zero`, `ax_tc_succ`,
>   `ax_tc_cons`) — los tres **CONSTRUCTORES** de códigos. La ley `tcFn (cons a b) =eq
>   consT (tcFn a) (tcFn b)` vale **porque `cons` es un constructor**: el código del valor de una
>   aplicación de constructor ES el constructor‑código aplicado a los códigos.
> * `substfc`/`liftfc` **no son constructores**, son funciones DEFINIDAS. Un axioma análogo
>   `ax_tc_substfc : tcFn (substfc v t f) = substfcT (tcFn v) (tcFn t) (tcFn f)` sería **FALSO**:
>   iguala el código de un **valor** (izquierda) con el código de una **expresión** (derecha).
>   ⚠️ Añadirlo rompería la solidez — es justo el tipo de error de [[feedback-verifier-soundness]].
> * No hay ni habrá `prf_tc_carc`/`prf_tc_nthc` tampoco (comprobado): los accesores rastreados
>   **no van por `tc`**, van por **EVALUACIÓN PROVABLE** (`pcc_eval_carc`, `pcc_eval_nthc`, …), que
>   internaliza con `pcc_thm_inst` la ecuación objeto que computa la función.
>
> **Lo que realmente hace falta es `pcc_eval_substfc` / `pcc_eval_liftfc`**, y eso es mucho más caro
> que un kit: `pcc_eval_carc` funciona porque `carc` tiene UNA ecuación definitoria instanciable en
> un patrón `cons` explícito; `substfc` se define por **recursión sobre los 8 constructores de
> fórmula, con binders**, y en los 7 tags se aplica a un código **ABSTRACTO** (`nthc #0 2`) ⟹ su
> evaluación provable exige **inducción interna sobre códigos de fórmula dentro de `Prov`**.
> Pertenece a la familia de `pcc_eval_runFn`/`pcc_bdAll_intro` («la bestia» del §18), no a la del kit.
> Todos los `prf_substfc_*` existentes (`_and`, `_atom`, `_eq`, `_impl`, `_forall`, …) computan
> `substfc` **sólo sobre constructores de código explícitos**; ninguno sobre un código abstracto.
>
> ### 🔬 INVESTIGACIÓN 2026‑07‑22 — ② DESCARTADA, y ① tiene una obstrucción MÁS PROFUNDA
>
> **② (reformular los 7 esquemas) — DESCARTADA, no ahorra nada.** La reflexión de una ecuación
> lateral va por `pcc_eq_tracked (t u) : (t =eq u) ⇒ Prov(⌜ṫ = u̇⌝)`, que devuelve **ambos lados como
> `tcFn ·`** (código del VALOR). Sacar `substfc` a una condición lateral
> (`nthc #0 4 = substfc 0 (nthc #0 3) (nthc #0 2)`) da `Prov(… = tcFn (substfc …))`, y el código
> objetivo sigue necesitando `substfcT …` (código de la EXPRESIÓN, porque `formCode` es sintáctica).
> El hueco es **el mismo** `pcc_eval_substfc`: ② sólo lo cambia de sitio.
> Y **eliminar** la condición para que el árbol quede puro es **INSÓLIDO**: `q1` podría concluir
> `∀x.φ ⇒ ψ` con `ψ` arbitraria — el fallo exacto de `ax_lineWF_gen` ([[feedback-verifier-soundness]]).
>
> **① necesita inducción sobre códigos — pero ES DERIVABLE, sin axioma nuevo.**
>
> ⛔ **CORRECCIÓN (misma sesión):** primero se afirmó aquí que «`cons` es un símbolo abstracto ⟹ los
> códigos no son números con medida». **ERROR.** `cons_sym` es opaco como símbolo, **pero
> `ax_L0_cons_def` lo ancla a la aritmética**: `cons h t = pair h (succ t)` con
> `pair = cantor_func` (emparejamiento de Cantor, `Minimal/Axioms.lean:122`). ⟹ **los códigos SÍ
> son números**, existe medida, y la inducción fuerte sobre el numeral se deriva de `ax_induction`
> (que ya existe en `Full/`). **NO hace falta (1b) ni ningún axioma nuevo: net‑0.**
> * La inducción de listas (`ax_list_induction`) sí es insuficiente por sí sola: su paso es
>   `∀h t. φ t → φ (cons h t)` — induce sobre el **espinazo**, sin IH sobre la cabeza `h`, y
>   `substfc` recurre en las **cabezas**. Por eso hay que ir por la vía aritmética.
> * La única inducción de listas disponible (`ax_list_induction` / `prf_list_induction`) tiene paso
>   **`∀h t. φ t → φ (cons h t)`**: induce sobre el **ESPINAZO (la cola)**, con la cabeza `h`
>   universalmente cuantificada y **sin hipótesis de inducción sobre `h`**.
> * Pero `substfc v t f` **recurre en las CABEZAS**: `⟨5,a,b⟩` es `cons 5̇ (cons a (cons b nil))` y
>   las subfórmulas `a`, `b` son cabezas. La inducción de espinazo **no da IH sobre ellas**.
>
> ⟹ **RUTA (1a), sin axiomas nuevos:** (i) probar la monotonía del emparejamiento de Cantor
> (`h ≤ pair h (succ t)`, `t < pair h (succ t)`) ⟹ **sub‑código < código**, apoyándose en lo que ya
> hay en `Minimal/Theorems/Block5.lean` (`is_cantor_pair`, `cantor_uniqueness`, `cantor_poly`);
> (ii) derivar **inducción fuerte** del `ax_induction` ordinario (truco estándar: inducir sobre
> `∀y ≤ x. φ(y)`, usando el aparato acotado ya existente); (iii) con eso, `pcc_eval_substfc` /
> `pcc_eval_liftfc` por inducción sobre el código. ⚠️ (i) es trabajo real (aritmética de Cantor en
> Q++), pero es **teoría de números, no metamatemática**, y no toca la solidez del verificador.
>
> **Nota foundacional (respuesta a «¿esto exige inducción?»): SÍ, y es lo esperado.** Gödel II no es
> alcanzable sobre Q sola — es un resultado clásico: Q **no** satisface D2/D3 (la Σ₁‑completitud
> *provable* requiere inducción; hace falta IΣ₁/EA). La cadena real de este proyecto **ya vive en
> `Full`**: `#print axioms goedel_second'` y `goedel_first_real'` citan **`Full.ax_induction` y
> `Full.ax_list_induction`**. Nótese el reparto fino, verificado: **D1 (`repr_pos'_prf`) y D2
> (`d2_prf`) NO usan inducción** — son limpios; la inducción entra en el punto fijo/Gödel I y en D3.
> Encaja con la teoría: D1 es Σ₁‑completitud *externa* (cómputo finito); D3 es la *provable*.
> ⟹ **No hay que replantear nada**: `Minimal` es la teoría OBJETO que se aritmetiza, `Full` es donde
> vive la prueba. Lo único que cambia es que conviene **decirlo explícitamente** en `AXIOMS.md`.
>
> **Opciones a decidir antes de seguir** (ninguna ejecutada):
> ### 📏 COSTE DE (1a), MEDIDO (2026‑07‑23) — tiene un PRERREQUISITO grande
>
> Al arrancar (1a) se mide el gap real. La cadena es
> `Cantor monótono` → `sub‑código < código` → `inducción fuerte` → `pcc_eval_substfc`.
> El eslabón 1 necesita aritmética de **`mul`/`le`/transitividad**, y ahí está el problema:
>
> * **A nivel `⊢` (Derives) SÍ existe**: `Minimal/Theorems/Block3‑5` tienen ~24 teoremas
>   (`le_mul_left`, `le_mul_right`, `le_trans`, `lt_le_trans`, `le_self_add`,
>   `le_add_const_of_le`, `le_of_mul_le_mul_left`, `is_cantor_pair`, `cantor_uniqueness`, …).
> * **A nivel `Prf` NO está portado**: `Meta/NatArithPrf.lean` sólo tiene lo básico de `lt`
>   (`prf_lt_iff`, `prf_lt_intro`, `prf_zero_lt_succ`, `prf_succ_lt_succ_of_lt`,
>   `prf_not_lt_zero`, `prf_nat_induction`, `prf_succ_inj`, `prf_zero_or_succ`).
>   **Cero teoremas de `mul`, cero de `le`.**
> * ⚠️ **No hay puente `⊢ → Prf`** (`Derives` tiene la ω‑regla; sólo existe `prf_to_derives`).
>   Los ~24 hay que **re‑probarlos** en `Prf`, como se hizo con `Meta/ArithPrf.lean`. Es
>   mecánico (esas pruebas no usan la ω‑regla) pero es **volumen real**.
> * `le` no es primitivo: `le a b := lt a b ∨ a =eq b` (`Axioms.lean:145`) ⟹ cada lema de `le`
>   arrastra manejo de disyunción interna.
>
> **Descomposición de (1a) en entregables independientes:**
> | # | entregable | depende de |
> |---|---|---|
> | i‑a | `Meta/NatOrderPrf.lean`: `le` en `Prf` (refl, trans, `lt_le_trans`, `le_self_add`, …) | — |
> | i‑b | `Meta/NatMulPrf.lean`: `mul` en `Prf` (`le_mul_left/right`, distributividad) | i‑a |
> | i‑c | `prf_cantor_mono`: `h < cons h t` y `t < cons h t` vía `2·pair = (x+y)(x+y+1)+2y` | i‑b |
>
> ⚠️ **REVISIÓN de i‑c (2026‑07‑23): NO es un porte, es DESARROLLO ORIGINAL.** Comprobado que el
> orden sobre `pair` **no existe tampoco a nivel `⊢`**: `Block5` tiene `is_cantor_pair`,
> `proj1/proj2_pair_eq`, `pair_proj_eq_c`, `pair_inj` — todo **ecuacional**, ninguna desigualdad.
> Hay que construir la cadena entera. Bosquejo verificado a mano (no formalizado):
> con `s = h + σt`, `2·cons h t = s·σs + 2σt`; de `prf_lt_add_succ` sale `h < s`, luego `s ≥ σh`,
> luego `s·σs ≥ (h+1)(h+2) ≥ 2h+2 > 2h`; y de `2·x > 2·h` se concluye `x > h` por **cancelación
> multiplicativa** (`le_of_mul_le_mul_left`, que existe en `⊢` y **habría que portar**).
> Piezas que faltan para eso: monotonía multiplicativa (`x ≤ y ⟹ x·c ≤ y·c`), cancelación, y
> `cantor_poly_is_even` (para pasar de `2·div2(n) + mod2(n) = n` a la igualdad exacta).
> Estimación: **~10‑15 lemas** de aritmética, todos de riesgo bajo pero volumen real.
> | ii | `prf_strong_induction` desde `prf_nat_induction` (inducir sobre `∀y ≤ x. φ(y)`) | i‑a |
>
> ✅ **i‑a, i‑b, i‑c HECHOS** (2026‑07‑23). `prf_cantor_mono_left/right` cerrados, **net‑0 axiomas**,
> footprint `[propext, choice, Quot.sound]`. No hicieron falta `ax11`/`ax12`/`ax24` ni
> `cantor_poly_is_even`: basta `mod2 ≤ 1` y tratar `2·σt` como opaco.
>
> 🔎 **HALLAZGO sobre ii (2026‑07‑23): existe un PLANO COMPLETO.**
> `ROBINSON_PlusPlus/Full/StrongInduction.lean` ya tiene la inducción fuerte **entera** a nivel `⊢`
> (`strong_induction`, línea 173), con toda la maquinaria De Bruijn resuelta. **Es importable desde
> `Meta/`** (verificado: `import ROBINSON_PlusPlus.Full.StrongInduction` compila y
> `ROBINSON_PlusPlus.Full.substFormula_liftFormula` queda accesible).
> * **Reutilizable tal cual**: `substFormula_liftFormula (φ c s) : substFormula c s (liftFormula c φ) = φ`
>   — es un lema **de nivel Lean**, independiente del cálculo. Era la pieza De Bruijn crítica.
> * **Hay que re‑declarar** (son `private`): `PSI` (línea 145) y `psi_at` (149). Son definiciones
>   triviales, pero copiarlas exige abrir el fichero.
> * **Hay que re‑probar en `Prf`**: el ensamblaje (usa `induction_object`/`gen`/`imp_intro` de
>   `Derives`; en `Prf` van `prf_nat_induction`/`Prf.gen`/`prf_deduction`) y `lt_succ_split`
>   (línea 92) — aunque para éste ya está **`prf_le_of_lt_succ`** (ii.1, hecho), que es su forma `≤`.
> * ⚠️ **Pregunta de diseño ABIERTA, resolver antes de portar**: el `strong_induction` de `Full` usa
>   una formulación **META** (`∀ n : Term, (∀ m : Term, axioms ⊢ lt m n → …) → …`), mucho más barata
>   que la objeto. **No está verificado que esa forma sirva para (iii)**: en `pcc_eval_substfc` los
>   sub‑códigos son `carc c`/`nthc c i` sobre un `c` ABSTRACTO, y habría que disponer de
>   `Prf (lt (nthc c i) c)` — que **no** es lo que da `prf_cantor_mono` (éste da
>   `lt h (cons h t)`, con el código ya presentado como `cons`). Puede hacer falta un puente
>   `lineWF`/`ax_lineWF_cons` → forma `cons`, o bien la formulación objeto. **Sondear (iii) con un
>   caso mínimo ANTES de portar (ii)**, para no portar la forma equivocada.
> | iii | `pcc_eval_substfc` / `pcc_eval_liftfc` por inducción sobre el código | i‑c, ii |
>
> 🔬 **EXPLORACIÓN DE (2) — 2026‑07‑24, 2º workflow (11 agentes). VEREDICTO: (2) NO EXISTE.**
>
> Se probaron **4 rutas predicate‑free independientes**. Tres fallan de plano (backbone
> alternativo, disyunción derivada, evitar‑substfc). La cuarta («substfc simbólico») se declaró
> **viable con sólo 2 axiomas** (`ax_tc_substfc`, `ax_tc_liftfc`) presentados como «misma categoría
> que `ax_tc_cons`, verdaderos, sin coste de solidez» — pero la **refutación adversarial la tumbó
> 3/3, con «axioma oculto» marcado por los 3**, y el agente de imposibilidad concluye `True`.
>
> **⚠️ FALSO POSITIVO ATRAPADO — y verificado a mano contra el código (linchpin de solidez).**
> `ax_tc_substfc : tcFn (substfc v s f) =eq substfcT (tcFn v)(tcFn s)(tcFn f)` **NO es de la
> categoría de `ax_tc_cons`: hace la teoría INCONSISTENTE.** Derivación:
> 1. `ax_substfc_impl` (axioma YA existente, `Axioms.lean:506`): `substfc v s (implc a b) =eq
>    implc (substfc v s a)(substfc v s b)` — la teoría **interpreta** `substfc`, no es opaco.
> 2. `tcFn` respeta `=eq` (congruencia Leibniz, `PrfH_congr_tcFn`) ⟹
>    `tcFn (substfc v s (implc a b)) =eq tcFn (implc …)`.
> 3. LHS por `ax_tc_substfc` = `substfcT …` = `funcc ⌜"substfc"⌝ …`, cabeza `⟨1, ⌜"substfc"⌝, …⟩`.
> 4. RHS por `ax_tc_cons` (`implc` ES un `cons`, `Axioms.lean:827`) = `⟨1, ⌜cons_sym="::"⌝, …⟩`.
> 5. ⟹ la teoría prueba `⟨1,⌜"substfc"⌝,…⟩ =eq ⟨1,⌜"::"⌝,…⟩`, y `cons_ne_head`/`formCode_ne`
>    (aritmética negativa de códigos, YA existe) prueba su **negación** ⟹ **`⊥`**.
> Un `Prov` inconsistente probaría `Prov(⌜⊥⌝)` y **aniquila toda la construcción de Gödel**.
> El error del agente: tratar `substfc` como símbolo **opaco** ignorando que `ax_substfc_*` ya lo
> **interpreta** como productor de `cons`‑árboles. **Esto VINDICA la decisión de `15dccda`**
> (abandonar `substfcT`): era correcta.
>
> **CONCLUSIÓN FIRME: no hay ruta sin axioma objeto de buena‑formación** para el target actual.
> Evidencia convergente: 3 rutas fallan, la 4ª es inconsistente (refutada 3/3), imposibilidad
> `True`, y derivación manual contra el código.
>
> **⛔ PUERTA (a) CERRADA (2026‑07‑25, sondeo de 8 agentes) — IMPOSIBILIDAD ESTRUCTURAL.**
> Reformular los 7 esquemas para ELIMINAR `substfc` del árbol reflejado, net‑0 y sólido, **no
> existe**. Dicotomía exhaustiva (dos bisagras verificadas a mano: `Rule.q1` toma término
> ARBITRARIO en `Hilbert.lean:93`; `substFormula` es recursión sobre los 8 constructores): la
> solidez ata `carc` a la instancia correcta, que **contiene `A[t]`**; o queda LIGADA (función /
> ecuación / premsOf / átomo relacional `subst`) ⟹ muro `CTree` (axiomas), o queda LIBRE ⟹ insólido
> (bug `ax_lineWF_gen`). Las 3 propuestas (premsOf, fVarización, átomo relacional) colapsan al mismo
> núcleo. La fVarización además rompe completitud (D1/Gödel I). Detalle en [[project-substfc-wall]].
>
> **⟹ SÓLO QUEDAN (1) y (3), deliverables DISTINTOS. Recomendación: (3) `repr_neg` AHORA (net‑0,
> avanza `⊬¬G`); (1) `isFormCode` después, como paso consciente para Gödel II. Nunca (a).**
>
> **DOS matices honestos que el agente de imposibilidad dejó abiertos (NO explorados):**
> * **Reformular el TARGET de los 7 esquemas** para que `substfc` **no aparezca** en la
>   reconstrucción (que nunca haya que evaluarlo). Es opción‑(1)‑adyacente (toca esquemas, requiere
>   sanción) pero podría ser más barato que los predicados. Distinto de la «② reformular» ya
>   descartada, que sólo movía el `substfc` de sitio; aquí sería **eliminarlo** del árbol.
> * El **mínimo axiomático de (1) es < 12**: las 16 ecuaciones `ax_substfc_*`/`ax_liftfc_*`/
>   `ax_substtc_*` ya existen (0 nuevas), la inducción fuerte se **deriva** (0 nueva); lo
>   genuinamente nuevo es **el predicado de buena‑formación + su inversión estructural**.
>   Mismo coste de solidez (amplía `Prov`), pero menos superficie que la estimación inicial.
>
> ---
>
> 🚨 **SONDEO DE (iii) — 2026‑07‑23, workflow de 11 agentes. DOS RESULTADOS NEGATIVOS.**
>
> **(A) La vía «extender `CTree`» está MUERTA, y se sabe exactamente por qué.**
> Añadir constructores `substF`/`liftF` a `CTree` es *necesario* (sin ellos no se declaran los 7
> árboles) y cierra **6 de las 7** inducciones de `Meta/CodeTreeReflect.lean` gratis. Pero rompe en
> la séptima, `PrfH_dotVN`, de forma **irreparable**: la obligación `prf_tc_objAt` pide
> `Prf (tcFn (substfc v A B) =eq substfcT v̇ Ȧ Ḃ)` — **el axioma PROHIBIDO y FALSO**. En el modelo
> estándar el izquierdo es un `cons`‑árbol (`⟨1,⌜"::"⌝,…⟩`) y el derecho es `⟨1,⌜"substfc"⌝,…⟩`, y
> `"substfc" ≠ "::"`. Los dos extremos (`dotV` opaco, `dotN` forzado por el esquema, que escribe
> literalmente `substfc`) no dejan **ninguna** libertad de diseño, y el hueco entre ellos **es**
> `pcc_eval_substfc`. Razón de fondo: `CTree` describe la **sintaxis de la expresión**, pero
> `substfc` recurre sobre el **valor** de su 3er argumento, que en los 7 tags es una **hoja**
> (`nthc t k`, caja negra para el árbol).
>
> **(B) La vía «inducción fuerte» funciona, pero NO es net‑0: exige ≥12 AXIOMAS OBJETO nuevos.**
> Hacen falta predicados de buena formación `isTermCode`/`isTermsCode`/`isFormCode` con sus
> cláusulas de generación e inversión. El revisor de solidez lo marca **grave** y con razón:
> llamar a eso «net‑0 axiomas de Lean» sería un **re‑encuadre que oculta el resultado**, porque
> amplían `axioms` y **por tanto amplían `Prov`** — es decir, cambian la teoría cuya demostrabilidad
> se aritmetiza, justo lo que `AXIOMS.md` obliga a sancionar.
>
> **`metaBasta = false`, confirmado por AMBOS diseñadores con tres razones independientes:**
> (1) el análisis por los 8 constructores es una **disyunción OBJETO**, y toda rama vive bajo
> `PrfH Γ`; la HI meta de `Full.strong_induction` exige premisa **cerrada** ⟹ inaplicable.
> (2) los casos con binder cambian los parámetros (`substfc v s (forallc a) = forallc (substfc (σv)
> (liftc 0 s) a)`), así que la HI debe estar **∀‑cuantificada en `v` y `s` a nivel objeto**.
> (3) `Full/StrongInduction` está sobre `Derives`; sirve de **guion**, no de teorema importable.
> ⟹ **(ii) hay que portarlo en forma OBJETO**, no meta. Parar antes de portarlo fue correcto.
>
> **Falsas alarmas ya resueltas** (los otros dos «graves»): `prf_lt_succ_self` y `prf_lt_subst2`
> fuera del cierre de imports — ya cubiertos por `prf_lt_succ_self_cm`/`prf_lt_subst2_cm` y por la
> copia local de `NatOrderPrf.lean:177`.
>
> **DECISIÓN PENDIENTE DEL USUARIO** (ninguna opción ejecutada):
> 1. **Sancionar los predicados de buena formación** (≥12 axiomas objeto) y seguir por (B).
>    Requiere análisis de conservatividad propio y entrada en `AXIOMS.md`.
> 2. **Buscar una vía sin predicados**: ¿puede la inducción fuerte sobre el **número** prescindir
>    de `isFormCode`, decidiendo la forma del código por otros medios? (El módulo A ya tiene
>    `decodeForm`, pero es **meta**, no objeto.) **No explorado.**
> 3. **Reordenar el frente**: dejar B.3c en 14/21 y atacar `repr_neg` u otra pieza.

> | iv | 2 constructores en `CTree` + los 7 tags | iii |
>
> **Estimación honesta: varias sesiones.** i‑a/i‑b son un porte tedioso pero de riesgo bajo;
> iii es el riesgo real (es «la bestia», familia `pcc_bdAll_intro`).
>
> **Alternativa a considerar antes de empezar (③):** el `or_elim` ×21 y `hC_dot` **no** están
> bloqueados por esto en su estructura — sólo faltarían 7 de las 21 ramas. Podría montarse el
> ensamblaje completo dejando los 7 como hipótesis explícitas, comprobando que TODO lo demás
> encaja, y volver a (1a) sabiendo que es lo único que queda. Reduce el riesgo de construir
> i‑a…iii y descubrir después un problema aguas abajo.
>
> 1. **RUTA ELEGIDA — (1a) aritmética, net‑0 axiomas:** monotonía de Cantor ⟹ sub‑código < código ⟹
>    inducción fuerte desde `ax_induction` ⟹ `pcc_eval_substfc`/`_liftfc` ⟹ los 7 tags.
> 2. ~~Reformular los 7 esquemas~~ — **DESCARTADA** (no ahorra; la variante que sí ahorraría es insólida).
> 2b. ~~Axioma de inducción estructural~~ — **INNECESARIA** (la vía aritmética es net‑0).
> 3. **Reordenar el frente**: dejar B.3c al 14/21 y atacar antes otra pieza (p. ej. el `or_elim` ×21
>    sobre los 14 cerrados, o el frente ① `repr_neg`), volviendo aquí con más maquinaria.
>
> <details><summary>Plan original (ERRÓNEO, conservado como registro)</summary>
>
> construir `substfcT`/`liftfcT` con (a) su ecuación `tc` (`prf_tc_substfc`), (b) su distribución
> de `substtc`, (c) su congruencia interna en `Prov`; luego **añadir dos constructores a `CTree`**
> (`sub c a b` / `lift c a`) extendiendo las 6 pruebas por inducción de `CodeTreeReflect`. Hecho
> eso, los 7 caen tan baratos como los 14.
> </details>
>
> **Después de los 21:** el **`or_elim` ×21** (`prf_lineWF_inv` da la disyunción de tags) para
> ensamblar `pcc_lineWF_tracked` → `hC_dot` → `d3_prf` → `goedel_second_prf` → **F7b** (7→6 `axiom`).
>
> #### Trampas ya diagnosticadas en este frente (NO volver a tropezar)
> * `numeralM k` y `Godel.numeral k` **NO son defeq** para `k` variable (`numeralM_eq` va por
>   inducción). Con literales reducen — por eso no aparece hasta que algo se hace genérico en `k`.
> * `substFormula 0 #0 C ≠ C` para `C` ABIERTA: `substFormula` **decrementa** los índices
>   superiores. Por eso el chasis toma `hC` como hipótesis explícita (cada tag la da con `rfl`).
> * **`≤` resuelve al orden OBJETO** (sobre `Term`) con `Minimal.Axioms` abierto, y el error es
>   opaco (*«type expected, got (n : Nat)»*). Escribir `Nat.le … n`. Además `Nat.le` crudo **no
>   tiene instancia `Decidable`** ⇒ descargar cotas con `Nat.le_refl`, no con `decide`.
> * `substTerm_numeralM`/`liftTerm_numeralM` **ya existen** en `Minimal/Axioms.lean`: no
>   redefinirlos (hace el nombre ambiguo en los módulos cliente).
> * `set` (Mathlib) **no está disponible**: usar `let`.
>
> #### Nota de solidez registrada
> Los 21 esquemas están hoy en **forma ESTRICTA uniforme** (cláusula canónica `lenc = ṅ`, con `ṅ` =
> máx índice + 1, derivada del propio esquema — no elegida). **Net‑0 axiomas: siguen 7.** Los 21
> `prf_lineWF_<tag>` conservan su enunciado exacto (`prf_iff_drop_left_conj`), así que D1/D2 no
> cambian. Con `mp` estricto **se revisa el hallazgo B.2**: una línea `mp` de forma incorrecta
> (longitud ≠ 3) **sí** es refutable por `lineWF`; las premisas siguen exigiendo `premsOf`.
> `NegVerifier` gana una vía de refutación, no la pierde.
>
> <details><summary>Histórico: el plan original de B.3c (21 casos a mano) — superado</summary>
>
> ### 🔖 SIGUIENTE PASO CONCRETO: **B.3c — `pcc_lineWF_tracked`** (el átomo `lineWF` punteado)
> **B.3a/B.3b HECHO**: nivel `⊢` des‑duplicado (`Meta/LineWFDerives.lean`) y los **19 `ax_lineWF`
> estructurales reformulados a ACCESORES** (net‑0 axiomas; los 21 `prf_lineWF_<tag>` conservan
> enunciado; D1/D2 intactos). Con eso `lineWF` ya es **reflejable sobre líneas abstractas**.
>
> **B.3c** = `pcc_lineWF_tracked (t) : Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t)))` — la
> reflexión punteada que `hC_dot` consume. Plan (diseño §16), **21 casos** de reflexión codificada:
> 1. `prf_lineWF_inv t` da `⋁_{k} (lineTag t =eq k̇)` → `PrfH_or_elim` de 21 ramas.
> 2. En la rama `k`: el bicondicional‑accesor `prf_lineWF_<k>` reduce `lineWF t` a `carc t =eq expr_k`.
> 3. Reflejar ese `=eq` con **`pcc_eq_tracked`** (libre de muro).
> 4. **Transportar de vuelta** reflejando `ax_lineWF_<k>` a nivel de código (patrón
>    `PropCodePrf.pcc_p1_code`/`pcc_ind_code`) + `pcc_thm_inst`/`pcc_mp_code`. **Paso 4 = el corazón
>    denso** («subproyecto de 21 casos de tag»).
> **ARRANCAR por `eqrefl` (tag 12)**: su producción libre de muro `prf_provFromCode_eqCodeFn_refl` ya
> existe. Cerrar ese caso valida el patrón del paso 4 y mide el coste real por tag antes del batch.
>
> **▶ ARRANQUE DE `eqrefl` HECHO (2026‑07‑14):** enunciado fijado
> (`pcc_lineWF_tracked (t) : Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t)))`, typechequea); los
> **pasos 1–5 validados** (inversión + bicondicional‑accesor + reflejar el `=eq` con `pcc_eq_tracked`
> compila). **Aislado el PASO 6** (la pieza densa que falta), con enunciado EXACTO:
> ```lean
> -- transporte codificado del bicondicional ax_lineWF_eqrefl:
> provFromCode (eqCodeFn (tcFn (carc t)) (tcFn (eqc (nthc t 2̇) (nthc t 2̇))))
>   ⇒ provFromCode (lineWFCodeFn (tcFn t))
> ```
> Construirlo: reflejar el axioma `ax_lineWF_eqrefl` a nivel de código (vía `thy`), instanciarlo en
> `tcFn t` (`pcc_thm_inst`), descargar la hipótesis del tag codificada, obtener el bicondicional
> codificado y aplicar `iff.mpr` codificado. Es **común a los 21 casos** (sólo cambia el axioma y la
> `expr_k`). ⚠️ Nota De Bruijn: hará falta la forma **accesor‑abstracta** del bicondicional
> (instanciar `ax_lineWF_<k>` en `t` SIN reconstruir a forma explícita), distinta de la
> `prf_lineWF_<k>` que B.3b dejó (ésa reconstruye la forma explícita).
>
> **▶ PASO 6 DESRIESGADO (2026‑07‑14):** reflejar `ax_lineWF_eqrefl` con `pcc_thm_inst` (testigo
> `tcFn t`) produce el bicondicional codificado con forma
> `provFromCode (substfc zero (tcFn t) (formCode <cuerpo accesor>))` — **la MISMA forma que
> `hI_dot`/`bddCarcDot` ya dominan** (`inDotAt φ p = substfc zero (tcFn p) (formCode …)`). Y la
> maquinaria de tracking de accesores **existe**: `pcc_eval_carc_nthc` evalúa `carc(nthc …)` rastreado
> (`D3InDotPrf` la usa para el `∃i<lenc p. carc(nthc p i)=⌜φ⌝`). **⟹ el paso 6 NO está bloqueado por
> puentes inexistentes** (el riesgo que se temía); es **composición densa** de: `pcc_thm_inst` (el
> bicondicional codificado) → distribuir `substfc` sobre `implc`/`iff` (`substCodeF`) → `pcc_mp_code_open`
> (MP interno) → antecedente del tag por `pcc_eq_tracked`+`pcc_eval_*` → `iff.mpr` codificado con el `=eq`
> del paso 5. **Es un caso de sesión dedicada, no de minutos.** Arrancar componiendo estas piezas para
> `eqrefl`; una vez cerrado, los otros 20 casos son el mismo esqueleto cambiando axioma y `expr_k`.
>
> **▶ COLUMNA VERTEBRAL DEL PASO 6 CONSTRUIDA (2026‑07‑14, compila limpio, `[propext,choice,Quot.sound,prf_inAxC]`).**
> Confirma la plantilla `pcc_bddDot_imp_inDot`. Código de referencia (para eqrefl; probar en un módulo
> tras `MpCodePrf`+`ArithPrf`+`Sigma1AtomPrf`):
> ```lean
> abbrev TAG : Formula := nthc (.var 0) (succ zero) =eq numeralM 12
> abbrev EQ  : Formula := carc (.var 0) =eq eqc (nthc (.var 0) (numeralM 2)) (nthc (.var 0) (numeralM 2))
> abbrev LWF : Formula := lineWF (.var 0)
> abbrev TAG_dot (t) : Term := substfc zero (tcFn t) (formCode TAG)   -- idem EQ_dot, LWF_dot
> -- hbwd: ∀.(TAG ⇒ (EQ ⇒ LWF)) — dirección ⇐ del bicondicional, currificada bajo el tag:
> --   Prf.gen; prf_spec del axioma ax_lineWF_eqrefl (accesor) en .var 0; prf_deduction×2;
> --   iff.mpr interno con c3 (Prf₀.c3) + MP.  [COMPILA]
> -- paso6_backbone: Prf (provFromCode (implc (TAG_dot t) (implc (EQ_dot t) (LWF_dot t)))):
> --   pcc_thm_inst (TAG⇒(EQ⇒LWF)) hbwd (tcFn t)  →  prf_substfc_impl ×2 (distribuye substfc)
> --   →  prf_provCode_congr.  [COMPILA]
> ```
> **▶ MATERIALIZADA + EVALUACIÓN DE LOS PUNTEADOS (2026‑07‑20, `Meta/LineWFTrackedPrf.lean`, 100 jobs).**
> La columna vertebral **ya no vive sólo en este documento**: los 3 commits anteriores de B.3c tocaron
> *sólo* `NEXT-STEPS.md` (el probe era gitignored), así que se materializó en módulo fuente y la
> verifica el build. Contiene: `tagEqrefl`/`eqEqrefl`/`lwfVar` (+`ax_lineWF_eqrefl_eq`, rfl),
> **`prf_lineWF_eqrefl_bwd`** (`[propext,choice,Quot.sound]`), `tagDot`/`eqDot`/`lwfDot` y
> **`paso6_backbone`** (`[propext,choice,Quot.sound,prf_inAxC]`).
> **Y avanza (a)** con la mitad *estructural*: los códigos punteados **EVALUADOS** a forma rastreada
> — `prf_tagDot_eq` (`substfc 0 (tcFn t) ⌜nthc #0 1 = 12̇⌝ = ⌜nthc(ṫ,1̇) = 12̇⌝`) y `prf_eqDot_eq`
> (idem con el `eqc` anidado) — que es justo la forma que consumen `pcc_eval_nthc`/`pcc_eval_carc_nthc`.
> Piezas nuevas reutilizables por los otros 20 tags: `substtc_inv_termCode_of_tc` (generaliza
> `substtc_inv_termCode_formCode` a cualquier `a` rastreado) y la familia **`eqcT`**
> (`eqc a b` es un `cons`‑árbol, no un `.func` ⇒ necesita constructor object propio, con
> `prf_congr_eqcT`/`prf_substtc_eqcT`).
>
> **▶ (a‑bis) + (b) HECHOS (2026‑07‑20, `Meta/LineWFTrackedPrf.lean`, 100 jobs,
> `[propext,choice,Quot.sound,prf_inAxC]`).**
> **(a‑bis) — PRODUCCIÓN de los punteados vía evaluación provable** (NO `pcc_eq_tracked` directo):
> `pcc_tagDot` (bajo `1 < lenc t` y la igualdad de tag ⇒ `Prov(TAG_dot t)`, con `pcc_eval_nthc` +
> `PrfH_congr_tcFn` + `prf_tc_numeral`) y `pcc_eqDot` (bajo `lineWF t` + `2 < lenc t` + la condición
> estructural ⇒ `Prov(EQ_dot t)`, encadenando `pcc_eval_carc` [línea es `cons` vía `prf_lineWF_cons`]
> + `pcc_eval_nthc` + `prf_tc_eqc` + la congruencia diagonal `pcc_congr_eqcT_diag_code_imp`). Piezas
> nuevas: `prf_tc_eqc` (`tcFn(eqc a b) = eqcT(tcFn a)(tcFn b)`), `pcc_congr_eqcT_diag_code_imp`
> (Leibniz interno con **dos** huecos `⌜v₀⌝`, que es lo que pide `eqrefl`: `t ≐ t`).
> **(b) — MP interno ×2**: `pcc_lineWF_tracked_eqrefl (t) (hlw)(htag)(hb1)(hb2)(heq)
> : Prf (provFromCode (lineWFCodeFn (tcFn t)))` — de `paso6_backbone` + los dos punteados, vía
> `pcc_mp_code_apply`×2, cerrando con `prf_lwfDot_eq` (`lwfDot t =eq lineWFCodeFn (tcFn t)`). **Es el
> caso `eqrefl` de `pcc_lineWF_tracked` completo salvo las hipótesis** (tag, cotas, condición).
>
> **▶ PLAN (A) — ESQUEMA ESTRICTO — HECHO PARA `eqrefl` (2026‑07‑20). CIERRA EL HUECO DE LAS COTAS.**
> Sancionado (A): `ax_lineWF_eqrefl` (en `Minimal/Axioms.lean`) ahora tiene RHS estricto
> `lineWF #0 ⇔ ((lenc #0 = 3̇) ∧ (carc #0 = eqc (nthc #0 2)(nthc #0 2)))`. La cláusula canónica
> `lenc = 3̇` **fuerza las cotas** `1 < lenc t`, `2 < lenc t`, que antes eran un hueco irresoluble.
> - **Núcleo intacto**: `axioms_eq` sigue `rfl`; **cadena real sin cambios** — D1 `repr_pos'_prf`
>   `[propext,choice,Quot.sound,prf_inAxC]`, D2 `d2_prf` `[…,Quot.sound]`, `goedel_second'` cita sólo
>   `d3`. El accesor concreto `prf_lineWF_eqrefl` **conserva su enunciado** (helper genérico
>   `prf_iff_drop_left_conj` descarga el conjunto `lenc=3` en la línea concreta) ⇒ D1/B.2/B.3b no
>   cambian de enunciado. Único módulo reescrito: `Meta/LineWFTrackedPrf.lean`.
> - **Backbone a 3 partes**: `paso6_backbone` = `Prov(⌜TAG_dot ⇒ ((LENC_dot ∧ EQ_dot) ⇒ LWF_dot)⌝)`.
>   Nuevo punteado `LENC_dot` producido con **`pcc_eval_lenc`** (incondicional) + reescritura del valor
>   por `lenc t = 3̇`; ensamblado con `∧`‑intro interno (`PrfH_and_intro_code`).
> - **`pcc_lineWF_tracked_eqrefl_imp (t) : Prf (lineWF t ⇒ ((nthc t 1 = 12̇) ⇒ provFromCode
>   (lineWFCodeFn (tcFn t))))` — SIN HIPÓTESIS DE COTA.** El accesor estricto (dirección `⇒`) da el RHS
>   entero; el 1.er conjunto `lenc t = 3̇` ⇒ cotas (`prf_lt_numeralM`+`PrfH_lt_subst2`), el 2.º ⇒ `heq`.
>   `[propext,choice,Quot.sound,prf_inAxC]`.
>
> **▶ CASO `thy` — In‑REFLECT ARRANCADO (2026‑07‑20, `Meta/InAxiomsCodePrf.lean`).**
> Investigado a fondo: `thy` (tag 15) NO es un clon de `eqrefl` — usa la forma EXPLÍCITA + condición
> **`In (carc) axiomsCodeT`** (membresía). Su reflexión = **Σ₁‑completitud positiva de la pertenencia
> a axiomas** = groundwork de `NegVerifier`. **Hallazgo clave: NO está bloqueada por Tarski** — el
> destino usa `carcT (tcFn t)` (código RASTREADO, evaluable con `pcc_eval_carc`), no `termCode
> (carc t)` (stuck). En el disyunto cabeza `carc t = f̄` (f axioma concreto), la cadena
> `carcT(tcFn t)→tcFn(carc t)→tcFn(f̄)→termCode(f̄)` deja el argumento concreto ⇒ pertenencia libre.
> **Entregado (libre de muro):** `pcc_inAxiomsCodeT_concrete (f∈axioms) : Prf (provCodeC'(In ⌜f⌝
> axiomsCodeT))` — el *payload* del caso cabeza (`repr_pos'_prf` de `prf_inAxC`).
> **▶ In‑REFLECT de `axiomsCodeT` CERRADO (2026‑07‑20) — el nudo `NegVerifier` (8‑11 sesiones) hecho.**
> `Meta/InAxiomsCodePrf.lean`, `[…,prf_axiomsCodeT_eq]`, 101 jobs en su momento. La Σ₁‑completitud rastreada de la
> pertenencia a axiomas, **sin muro de Tarski** (código rastreado `carcT (tcFn ·)`):
> - `pcc_in_tail_tracked` (cola, reflejo del In‑cons vía `pcc_thm_inst`) + `pcc_in_head_swap`
>   (cabeza: `pcc_in_head` libre + swap `termCode a → yc` por Leibniz DENTRO de `Prov`, cadena
>   `yc=tcFn y=tcFn a=termCode a` sólo con códigos `tcFn`).
> - **`pcc_In_lfc_tracked`** — recursión sobre la lista de axiomas ABSTRACTA (sin materializar):
>   `In y (listFormCodeM L) ⇒ Prov(⌜In yc (listFormCodeM L)~⌝)`.
> - **`pcc_In_axiomsCodeT_tracked`** — reflexión sobre `axiomsCodeT` opaco, componiendo la recursión
>   con el anclaje `prf_axiomsCodeT_eq` en LOS DOS lados (object `In y axiomsCodeT → In y
>   (listFormCodeM axioms)`; código dentro de `Prov` por Leibniz reflejada del anclaje).
> **Refactor de footprint (net‑0):** nuevo `axiom prf_axiomsCodeT_eq : Prf (axiomsCodeT =eq
> listFormCodeM axioms)` (espejo `Prf` del `ax_axiomsCodeT_eq` de `⊢`) ⇒ `prf_inAxC` pasa a TEOREMA.
> D1 cita ahora `prf_axiomsCodeT_eq` (antes `prf_inAxC`); `goedel_second'` sigue citando sólo `d3`.
>
> **FALTA sólo el ENSAMBLAJE de `thy`** (mecánico, espejo de `eqrefl`): instanciar
> `pcc_In_axiomsCodeT_tracked` con `yc = carcT (tcFn t)`, `y = carc t`, `hbr` de `pcc_eval_carc`
> (+ `carcT(tcFn t)` invariante); strict schema `thy` (`lenc = 2`); backbone; `pcc_lineWF_tracked_thy`.
>
> **FALTA de (c):** (1) **`thy`**: cerrar la recursión `pcc_In_lfc_tracked` (arriba) → strict schema
> `lenc=2` → reflector. (2) **`mp`** (tag 16, forma explícita, `lineWF` incondicional). (3) los **17
> tags `=eq`** — clones de `eqrefl` (helper genérico: `lenc = len_k`, la mayoría=3, p2/j3/leibniz=4/5).
> (4) El **`or_elim` ×21** (`prf_lineWF_inv` da los tags; cada rama su `pcc_lineWF_tracked_<k>_imp`).
>
> **(histórico) (c) PARCIAL (2026‑07‑20): reflector POR RAMA con `heq` descargada.**
> `pcc_lineWF_tracked_eqrefl_imp (t) (hb1)(hb2)
> : Prf (lineWF t ⇒ ((nthc t 1 = 12̇) ⇒ provFromCode (lineWFCodeFn (tcFn t))))` — instancia el
> accesor `ax_lineWF_eqrefl` en `t` y **deriva** la condición estructural (`heq`) por `iff.mp`
> (`Prf₀.c2`) desde `lineWF t` + el tag; ya **no** la pide como hipótesis. Es el reflector que el
> `or_elim` ×21 invocará en el disyunto `eqrefl`. `[propext,choice,Quot.sound,prf_inAxC]`.
>
> **FALTA de (c):**
> 1. **⚠️ LAS COTAS `1 < lenc t` / `2 < lenc t` — HUECO REAL, decisión de diseño.** NO son derivables
>    de `lineWF t` + tag con la axiomática actual: `nthc` no tiene ecuación fuera de rango (no hay
>    `nthc_oob`), y `ax_lineWF_eqrefl` es un `⇔` que no fuerza la longitud de la línea. Opciones:
>    (A) **reforzar el esquema** eqrefl para que `lineWF` de una línea eqrefl **exija** la estructura
>        canónica de 3 elementos `cons concl (cons 12̇ (cons arg nil))` (toca axiomática ⇒ sanción);
>    (B) enunciar `pcc_lineWF_tracked` sólo sobre **líneas canónicas** y que `hC_dot` provea la
>        canonicidad; (C) añadir `ax_nthc_oob` (`i ≥ lenc t ⇒ nthc t i = 0`) para que
>        `nthc t 1 = 12̇ ≠ 0` fuerce `1 < lenc t` (toca axiomática ⇒ sanción). La forma **explícita**
>        de B.3b (`lineWF_eqrefl : lineWF (cons concl (cons 12̇ (cons t nil))) ⇔ …`, longitud 3) ya
>        da las cotas gratis — pista de que (A)/(B) son el camino natural.
> 2. Los **otros 20 tags**: replicar `pcc_lineWF_tracked_eqrefl_imp` cambiando axioma/`expr_k`.
> 3. El **`or_elim` ×21** (`prf_lineWF_inv` da la disyunción; cada rama invoca su reflector).
>
> **(referencia histórica de la capa densa)** (a‑bis) *producir* `Prov(TAG_dot t)` y `Prov(EQ_dot t)` aplicando
> = `Prov(⌜carc t =eq eqc(nthc t 2)(nthc t 2)⌝)` vía **evaluación provable** (`pcc_eval_nthc` /
> `pcc_eval_carc_nthc`, que operan DENTRO de `Prov` bajo cota `i<lenc`; de `lineWF t` sale la cota y la
> estructura de `t`); (b) dos `pcc_mp_code_open` (MP interno con TAG_dot y EQ_dot) → `provFromCode (LWF_dot t)`;
> (c) envolver con la inversión `prf_lineWF_inv` (`PrfH_or_elim` ×21) para el teorema completo. ⚠️ El
> encaje forma‑`substfc`/forma‑`tcFn` NO va por `pcc_eq_tracked` directo (sería Tarski) sino por la
> evaluación provable — que es justo lo que `pcc_eval_*` resuelve.
> Después C, D, E (`VerifierSound`, riesgo ALTO — sondeo antes; `decodeChain_prf` es la pieza que E
> ensambla) y F.
> exige sondeo antes de codificar; `decodeChain_prf` es la pieza que E ensambla) y F.
>
> **⚠️ DOS TRAMPAS YA DIAGNOSTICADAS — no re‑descubrirlas** (documentadas dentro de `CodeDecode.lean`):
> 1. **Kernel + `DecidableEq String`.** `split` / `rw` / `simp` **manuales** sobre un `if s == sym`
>    fabrican un cast `congrFun'` que **el núcleo RECHAZA** (`application type mismatch`). Se sortea
>    con **inducción funcional** (`fun_induction`, o `foo.induct` para las mutuas — que sí existe,
>    con `motive_2` explícito), que genera los casos **ya reducidos**; y con **`unfold … at h`**
>    (limpio) en vez de `simp only [decodeX] at h` (frágil).
> 2. **`Char.ofNat` CLAMPA.** Sin guard, `decodeChars` **no es inyectiva** (un numeral fuera del rango
>    Unicode decodifica a un char cuyo `toNat` ya no vuelve). Hubo que añadir el guard
>    `(Char.ofNat code).toNat == code`; el round‑trip lo cumple gratis por `Char.ofNat_toNat`.

> </details>

---

## 🎯 LO QUE QUEDA (3 tareas, por orden de valor)

> Nada de esto es una incógnita: de las tres se sabe **exactamente** cómo se hace. Lo que queda es
> volumen, no diseño.

### ① ⊬¬G — **HECHO** ✅ · descargar `Reflects` es lo que queda (y NO por donde se creía)

**Ya está (`Meta/DiagonalTwo.lean`, HEAD `c9c4607`), sin ningún postulado gödeliano:**

```lean
abbrev Reflects (G) : Prop := (axioms ⊢ provCodeC' G) → Prf G     -- hipótesis META, EXPLÍCITA
theorem goedel_first_unrefutable_real' (hcon) (hfp) (hrefl) : ¬ Prf (neg G)
theorem goedel_first_undecidable_real'  (hcon) (hrefl) : ¬ Prf godelC' ∧ ¬ Prf (neg godelC')
```

`#print axioms` = `[propext, choice, Quot.sound, FOL.MetaRules.{dne,gen,imp_intro},
Full.ax_induction, Full.ax_list_induction, ax_inAxC]` — **cero postulados gödelianos**.

> ⛔ **HALLAZGO: `repr_neg` NO se sigue de `ConsistentOmega`. Está CERRADO POR GÖDEL.**
> La reflexión **no puede derivarse dentro de la teoría**: haría falta `⊢ ¬provCodeC' φ` para `φ`
> indemostrable, y con **`φ = ⊥`** eso es **literalmente `Con(T)`** — indemostrable por **Gödel II**.
> (Con `φ = G` tampoco: por el punto fijo `⊢ ¬provCodeC' G ⟺ ⊢ G`, y `⊬G`.) Además la ω‑regla `gen`
> cuantifica sobre **todo `Term`** (no sólo numerales), así que tampoco se aplica desde hechos sobre
> testigos concretos: para una variable libre `x`, `⊢ ¬A(x)` **es** la universal — circular.
> **Por eso `Reflects` se deja como hipótesis META explícita** (como la ω‑consistencia clásica, y como
> `goedel_second'` hace con las suyas) en vez de esconderla en un postulado. Y por eso el plan que
> `CodeDistinct.lean` tenía escrito (probar `⊢ ¬provCodeC φ` «con el esquema de inducción, Fase 5»)
> **era imposible** — ya corregido en el módulo.

**LO QUE QUEDA de ①** — ✅ **la REDUCCIÓN ya está hecha** (`Meta/OmegaReflect.lean`, HEAD `f53dd4e`):

```lean
def OmegaConsistent : Prop := …   -- ω-consistencia CLÁSICA, hipótesis META explícita
def NegVerifier    : Prop := ∀ φ, ¬ Prf φ → ∀ l, StdChain l → axioms ⊢ neg (Verifies φ (objList l))
theorem reflects_of_omega (hω : OmegaConsistent) (hneg : NegVerifier) (φ) : Reflects φ
theorem goedel_first_undecidable_omega (hcon) (hω) (hneg) : ¬ Prf godelC' ∧ ¬ Prf (neg godelC')
```

**Valor:** la reflexión deja de ser un enunciado **bloqueado por Gödel** y pasa a ser **`NegVerifier`,
un enunciado Δ₀ concreto**, más una hipótesis clásica y **visible**. `OmegaConsistent` **no** es
`ConsistentOmega`: es estrictamente más fuerte, es lo que Gödel exige, y es creíble (toda teoría
**sólida** la cumple).

**Falta sólo `NegVerifier`** — es un **proyecto real** (magnitud ~D1, varios módulos).

> 📄 **PLAN DETALLADO Y EJECUTABLE: [`PLAN-NEGVERIFIER.md`](PLAN-NEGVERIFIER.md)** — arquitectura de
> 6 módulos, orden de ejecución, estimaciones, criterios de aceptación y **trampas conocidas**.
> Incluye **dos hallazgos que hay que atender ANTES de codificar**:
> * ⚠️ **`StdChain` debe ser CANÓNICO, no «cerrado»** (`add zero zero =eq zero` es demostrable ⇒ la
>   igualdad de términos cerrados NO es refutable). Fix bloqueante en `Meta/OmegaReflect.lean`.
> * 🔬 **SONDEO DE SOLIDEZ obligatorio** antes del módulo E: los esquemas `ax_lineWF_<tag>`
>   cuantifican sobre códigos **arbitrarios**; hay que descartar que el verificador objeto acepte
>   cadenas basura que «prueben» `⌜φ⌝` sin `Prf φ`. Si las aceptara, sería un **bug de solidez del
>   proyecto**, no del plan.
>
> ✅ **SONDEO EJECUTADO (2026‑07‑14) — veredicto en `PLAN-NEGVERIFIER.md` (§🔬):**
> **(A)** el verificador es **SÓLIDO** — los 21 tags están ligados (20 por ⇔, `mp` por `premsOf`),
> `thy` sólo inyecta axiomas reales, y la realidad hereditaria (rigidez+inyectividad de `formCode`)
> cierra el argumento. **No hay bug; el módulo E es viable.**
> **(B) HALLAZGO que BLOQUEA `NegVerifier`:** `axiomsCodeT` es un átomo **OPACO** con sólo
> dirección positiva (`ax_inAxC`) ⇒ **no se puede refutar `In v0 axiomsCodeT`** ⇒ el módulo D no
> puede refutar líneas `thy` basura ⇒ **`NegVerifier` NO es demostrable con `axiomsCodeT` opaco**.
> **No es insoldez** — es que la teoría no “sabe” que `axiomsCodeT` = sus axiomas (fue concreto y
> se retiró en `7ae7b7b` por rendimiento). **(C)** el fix de `StdChain` que planeé («canónico») es
> **falso** (`cons` es una pareja de Cantor, `ax_L0_cons_def`).
> **⟹ NUEVO PASO BLOQUEANTE 0.5 (requiere SANCIÓN):** concretar `axiomsCodeT` — recomendado un
> ancla negativa `ax_notInAxC` (dual de `ax_inAxC`). Ver `PLAN-NEGVERIFIER.md` §🔬.

Estado de sus piezas:

| Pieza | Estado |
|:--|:--|
| `prf_iff_derivation : Prf φ ↔ ∃ rs, Derivation rs φ` | ✅ existe |
| `chainOk_track` / `runFn_track` (**positiva**: `checkAux` ok ⟹ `⊢ chainOk`) | ✅ existe (núcleo de D1) |
| **Solidez estructural del verificador** (cadena válida ⟹ `Prf`) | ❌ **NO existe — pieza CRÍTICA** (módulo E) |
| `In` **negativo** (`⌜φ⌝ ∉ L` ⟹ `⊢ ¬ In ⌜φ⌝ L`) | ❌ no existe (módulo D; base: `formCode_ne` ✅) |
| **Decodificador de FÓRMULAS** `Term → Option Formula` (inverso de `formCodeM`) | ✅ **HECHO** (`Meta/CodeDecode.lean`) — round‑trip **e inyectividad** (`decodeForm_inj`) |
| **Decodificador de CADENAS** `Term → Option (List Rule)` (inverso de `proofCode'`) | ⏳ **← EMPEZAR AQUÍ** (resto del módulo A) |
| `neg_In_axiomsCodeT` (`⊬φ` ⟹ `⊢ ¬ In ⌜φ⌝ axiomsCodeT`) | ✅ **HECHO** (`Meta/AxiomListCode.lean`, paso 0.5) |
| `StdChain` = «con forma de código» (`IsCodeShaped`) | ✅ **HECHO** (`Meta/OmegaReflect.lean`, paso 1) |

**Dificultad de fondo:** `NegVerifier` cuantifica sobre **cualquier** list‑term cerrado, y **la mayoría
NO están en la imagen de `proofCode'`** (son basura). Para cada uno hay que: **decodificarlo**; si no
decodifica, **refutar `chainOk` estructuralmente** — lo que exige la **inversión de los 21 tags**
(`ax_lineWF_inv` + distinción de códigos). Si decodifica, correr `checkAux`: si falla, refutar; si pasa
y `⌜φ⌝` está entre las conclusiones, entonces `Prf φ` (`derivation_to_prf`) — contra la hipótesis.

> 🔗 **SINERGIA con ②:** la refutación estructural de los **21 tags** es la **misma maquinaria** que la
> reflexión del átomo `lineWF` que necesita `hC_dot` (tarea ②), en dirección negativa. Conviene
> construirlas juntas.

### ② Átomo `lineWF` dotado — **SUBPROYECTO** (el bloque grande de `hC_dot`)

Reflejar `lineWF X` punteado exige recorrer los **21 casos de tag**: `prf_lineWF_inv` da la disyunción
`tagDisj`; en **cada** caso hay que (a) reflejar su **ecuación estructural** (`pcc_eq_tracked` +
evaluaciones de los constructores de código) y (b) aplicar el **bicondicional codificado**
`ax_lineWF_<tag>` vía `pcc_thm_inst`. Varios cientos de líneas, mecánico pero largo.

**Faltan además** (misma tarea): evaluaciones provables de **`premsOf`** (y de `lenc`/`nthc` sobre él),
y los **cómputos `substCodeF`** de `chainOkB`/`lineOkB`/`boundedPremsIn` (patrón `substCodeT_closed`).

### ③ Componer `hC_dot` → `d3_prf` → `goedel_second_prf` → **F7b** (7→6 `axiom`)

**D3 ya está reducida a UN SOLO lema:** `d3_prf_of_chainOkDot (φ) (hC)`. Todo lo demás está hecho.

```text
chainOkB c p  = ∀i<lenc p. lineOkB c p i                       ← ✅ pcc_bdAll_intro  (§40)
lineOkB c p i = lineWF (nthc p i)  ∧  boundedPremsIn …          ← ② arriba   ✅ pcc_reflect_and
boundedPremsIn = ∀j<lenc L. ( In (nthc L j) nil ∨ ∃k<i. carc (nthc p k) = nthc L j )
                  ✅ pcc_bdAll_intro   ✅ ex-falso   ✅ pcc_reflect_or   ✅ pcc_bdEx_intro_open
                                                        y el átomo: ✅ pcc_eq_tracked +
                                                        pcc_eval_carc_nthc + pcc_eval_nthc
```

Falta también **codificar el ⇐** (`chainOkB nil p ⇒ chainOk nil p`, de `prf_chainOk_iff_chainOkB`):
patrón Step A, barato. **Estimación honesta de ②+③: 2‑4 sesiones.**

---

**Para arrancar una sesión nueva, leer en este orden:**

1. **`MEMORY.md`** (índice de memoria; carga los `project_*.md` / `feedback_*.md`) — estado global y hallazgos.
2. **Este `NEXT-STEPS.md`** (bloque de reanudación + "Last updated") — qué está hecho y qué sigue.
3. **`GODEL-D3-TRACKED-DESIGN.md` §12–§14** — plan 12‑A por fases, veredicto del sondeo de la fase 2 (§13) y **§14.4 lecciones De Bruijn acumuladas** (leer SIEMPRE antes de escribir `PrfH`).
4. **`doc/REFERENCE-Incompleteness.md` §3.18–§3.20** (nodo temático del árbol REFERENCE) — proyección completa de la capa Δ₀ (`NumListPrf`, `NatArithPrf`, `BoundedInPrf`, `RunFnBoundedPrf`, `ChainOkBoundedPrf`) + evaluación provable + ruta B dotada (`D3InDotPrf`).
5. **`PLAN-NEGVERIFIER.md`** — plan detallado de la tarea ① (solidez estructural del verificador +
   decodificador + inversión de los 21 tags). **Leerlo antes de tocar `NegVerifier`.**
6. **`ESCALANDO_EL_PROYECTO.md`** — enlace con el proyecto hermano DeepArith sobre el kernel FOL⁼ común.

> ⚠️ **AUDITORÍA 2026-07-13 (`repasa_y_proyecta`) — HALLAZGO DE SOLIDEZ.** La mitad **`⊬¬G`** de Gödel I
> (indecidibilidad) **NO está en la cadena real**: se probó en la capa LEGACY (`Meta/Incompleteness.lean`)
> y se retiró en **F7a** (`f03eacf`). **NO recuperar F7a** — fue un *arreglo de solidez*: la prueba legacy
> descansaba en `provFormula_repr`, postulado como bicondicional, cuya dirección `.mp`
> (`⊢Prov⌜φ⌝ → ⊢φ`, representabilidad **negativa**) **no se sigue de la consistencia simple** — y el
> teorema se enunciaba bajo `Consistent`, afirmando **más de lo que Gödel permite** (por eso existe
> Rosser). Era un **postulado falso en general**, misma familia que `subst_lift_cancel_formula` y
> `ax_lineWF_gen`.
>
> **TAREA ABIERTA (independiente de D3):** construir **`repr_neg : ConsistentOmega → Prf (provCodeC' φ)
> → Prf φ`** (no existe). Con ella + el punto fijo real (`godelC'_fixedpoint`) + `dne`, el argumento de
> ~8 líneas se porta y se recupera la indecidibilidad **con la hipótesis honesta**. Groundwork en
> `Meta/CodeDistinct.lean`. Ver `GODEL-STATUS.md`.

---

## 📜 REGISTRO CRONOLÓGICO (§15–§40) — cómo se llegó aquí

> **El estado ACTUAL y lo que queda están ARRIBA** (93 jobs, 79 módulos). Lo que sigue es el histórico
> de hitos, en orden de construcción; las cifras de cada entrada son las **de su momento**, no las de hoy.

- ✅ **Gödel I REAL** sin postulados (`goedel_first_real'`); **D1** (`repr_pos'_prf`) y **D2** (`d2_prf`) reales; `d3_prf_of_sigma1` (D3 reducida a `hC`/`hI`).
- ✅ **12‑A fases 1a/1b/2**: el verificador (`chainOk c p` y `In · (runFn nil p)`) está **expresado en la capa numérica Δ₀ y sin acumulador**. Era el único punto del plan sin verificar en código; ya no queda ninguno.
- 🔄 **Fase 3 ARRANCADA** (`Meta/Sigma1BoundedPrf.lean`, §15 del diseño): **puente `d3_prf_of_reflect_bounded`** — D3 reducida (vía `pcc_imp` + los `⇔` de fase 1/2) a reflejar la forma **Δ₀ acotada** `boundedIn`/`chainOkB` (`prf_hI_of_reflect_boundedIn`, `prf_hC_of_reflect_chainOkB`). La obstrucción de Tarski queda reubicada en el **átomo** `nthc L i =eq x`, que resuelven las ecuaciones de variable de `substfc`.
- ✅ **Fase 3 núcleo — átomo `=eq` CERRADO, LIBRE DE MURO** (`Meta/Sigma1AtomPrf.lean`, §15.3‑§15.4 del diseño). Clave: el verificador comprueba `lineWF` **estructuralmente** (`lineWF ⟨concl,12,t⟩ ⇔ concl =eq eqc t t`, y `eqc = eqCodeFn`), así que la **línea‑axioma EQREFL** `⟨eqCodeFn c c, 12, c⟩` es válida por **pura reflexividad** para `c` arbitrario, sin `termCode`. De ahí: **`prf_provFromCode_eqCodeFn_refl (c)`** (reflexividad libre de muro, testigo de una línea) y **`pcc_eq_tracked (t u) : Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))`** (libre de muro, vía congruencia de `tcFn` + Leibniz object). Los tres `#print axioms = [propext, choice, Quot.sound]` — **desaparece hasta `prf_inAxC`**. El muro de Tarski queda confinado al último paso (`pcc_eq_of_tc_bridge`: puente `tcFn t =eq termCode t`, descargable con numerales en fase 5).
- ✅ **`atom1CodeFn` + `lineWFCodeFn`** (constructores de código de átomos unarios + transporte), `Meta/Sigma1AtomPrf.lean`.
- ✅ **OBSTRUCCIÓN §16 RESUELTA (sancionada):** `lineWF`/`premsOf` no estaban determinados (21 bicondicionales indexados por etiqueta, sin inversión). Añadido **`ax_lineWF_inv`** a `Minimal/Axioms.lean` (`lineTag`/`tagDisj` + el axioma, al final de `axioms` **y** `codingAxioms`) + cierre `Prf` **`prf_lineWF_inv`**. Verificado tras tocar el núcleo: `axioms_eq` sigue `rfl`, la cadena real **no cambia** (`goedel_second'` sólo `d3`), y los **7 `axiom` de Lean no cambian** (es un `def ax_*` de la teoría objeto).
- ✅ **SEGUNDA OBSTRUCCIÓN §17 RESUELTA: `pcc_exIntro_code'` (`hw` era innecesaria).** Pieza clave: **`liftTerm_substfc_open`** (`liftTerm c (substfc zero w Ac) = substfc zero (liftTerm c w) Ac`, con `Ac` cerrado) — el lift **atraviesa** y queda sobre el testigo. Así el contexto tras `prf_ex_elim_imp` es idéntico con `w' := liftTerm 0 w` y el ensamblaje `p ++ [q2line, mpline]` pasa **verbatim** (`prf_lineOk_q2` admite cualquier testigo). `[propext, choice, Quot.sound]`. El viejo `pcc_exIntro_code` se conserva como **corolario** (retrocompatible). **Verificado:** `pcc_exIntro_code' Ac (tcFn #0) hAc` typechequea — testigo **abierto** y **rastreado**.
- 📌 **De RIESGO‑1 cae exactamente la mitad (a)** — `tcFn #0` no cerrado ⇒ `hw` falla — **disuelta**. La mitad **(b)**, el transporte `tcFn L =eq termCode L` (Tarski genuino), **sigue viva pero confinada** al último paso (§15.4), descargable con numerales (`prf_tc_numeral`) en la inducción de fase 5. Sin sobre‑afirmar.
- 📌 **§18 (sondeo verificado): la reflexión de `<` NO es un ladrillo pequeño.** `=eq` está cerrado (§15.4) y el `∃`‑intro admite testigo abierto (§17.2), **pero no encajan**: `pcc_eq_tracked` produce el código con `tcFn` del **término entero** (= numeral del *valor* `a+σk`), mientras el cuerpo del `∃` de `ax13` necesita el código del **término simbólico** `ȧ + σj̇`. Son códigos distintos. `tcFn` (= `num`) sólo tiene 3 ecuaciones (`zero`/`succ`/`cons`) y **no debe** computar sobre `add`. El puente es **`⊢ Prov(⌜ȧ + σk̇ = (a+σk)˙⌝)`**: la **evaluación provable**, que se prueba por inducción interna. Es «la bestia» de §11.3.
- ✅ **Ladrillo entregado hacia ella:** **`liftFormula_provFromCode_open (k c) : liftFormula k (provFromCode c) = provFromCode (↑c)`** (`Meta/TrackedCorePrf.lean`) — generaliza la clausura a **códigos abiertos**. La necesita el **∀‑elim de código** (`prf_lineWF_q1` es estructural, como la línea Q2), donde el código abierto cae en el **consecuente** — al revés que en `pcc_exIntro_code'`. Imprescindible para **instanciar axiomas codificados** (p. ej. `ax13`) en la prueba interna.
- ✅ **§19 — SISTEMA DE PRUEBA INTERNO A NIVEL DE CÓDIGO (andamiaje de la evaluación provable), COMPLETO.** Las cuatro reglas, todas con **testigo abierto** donde procede: **`pcc_exIntro_code'`** (∃‑intro Q2, `ExIntroCodePrf`), **`pcc_forallElim_code'`** (∀‑elim Q1, `ForallElimCodePrf` — NUEVO; `prf_lineWF_q1` es estructural como Q2; la asimetría es que el código abierto cae en el CONSECUENTE, de ahí `liftFormula_provFromCode_open`), **`pcc_mp_code`** (MP, `MpCodePrf` — NUEVO; porte de `d2_prf` a códigos cerrados arbitrarios), y **`pcc_axiom_inst`** (instanciación de axiomas codificados). Los tres primeros `[propext, choice, Quot.sound]`; el cuarto `+ prf_inAxC`. **Verificado:** `pcc_ax4_inst (tcFn #0)` typechequea — `ax4` codificado instanciado en un testigo **abierto**.
- 📌 **El caso `σ` de la evaluación provable es GRATIS**: `prf_tc_succ` (`ax_tc_succ`) ya da `tcFn (succ x) =eq succc (tcFn x)`.
- ✅ **§20 — PRIMER PASO REAL DE LA EVALUACIÓN PROVABLE** (`Meta/SubstCodeOpenPrf.lean`): **`prf_substfc_arith_open (v w f) : substfc ⌜v⌝ w ⌜f⌝ =eq substCodeF v w f`** — aritmetización de la sustitución con **testigo‑código ARBITRARIO** (antes sólo `termCode s`, con `s` meta; pero `tcFn a` no es `termCode` de nada meta: ese era el único hueco). Salió barato porque `termCode s` viajaba **opaco** por las pruebas originales, pasándose tal cual a `prf_substtc_var_eq/gt/lt`, que son genéricas en `s`. Contenido: funciones meta `substCodeT`/`substCodeTs`/`substCodeF` (bajo binder el testigo se **levanta**, `liftc zero w`), los lemas `prf_substtc_arith_open`/`prf_substtsc_arith_open`/`prf_substfc_arith_open`, y el chequeo de cordura `substCodeT_termCode` (recupera `prf_substTerm_arith`). Todos `[propext, choice, Quot.sound]`.
- ✅ **Payoff verificado:** `substCodeF 0 w (add #0 zero =eq #0) = ⟨4, addcT w ⌜0⌝, w⟩` por **`rfl`** (la función meta computa), y de `pcc_ax4_inst (tcFn a)` + `prf_substfc_arith_open` sale **`Prov(⌜ȧ + 0 = ȧ⌝)`**. Confirmación De Bruijn: `prf_substfc_forall` levanta el testigo bajo el binder ⇒ era **obligatorio** que el ∀‑elim de código admitiera testigos abiertos (§19.1).
- ✅ **§21 — BASE DE `+` CERRADA** (`Meta/EvalArithPrf.lean`, 80 jobs): **`pcc_eval_add_zero (a) : Prf (provFromCode (evalAddCode a zero))`**, o sea `⊢ Prov(⌜ȧ + 0̇ = (a+0)˙⌝)` — **primera aritmética real demostrada DENTRO de `Prov`**. Piezas: `addcT` (código del término `x+y`) + `addcT_termCode` (rfl) + `prf_congr_addcT`; `evalAddCode a b := eqCodeFn (addcT (tcFn a) (tcFn b)) (tcFn (add a b))`; `pcc_ax4_computed` (instancia de `ax4` codificado YA computada). Encaje: `pcc_ax4_inst` (§19.3) → `prf_substfc_arith_open` (§20) → `prf_provCode_congr` con `prf_tc_zero` y `prf_congr_tcFn` sobre `prf_add_zero_t`. `[propext, choice, Quot.sound, prf_inAxC]` (el `prf_inAxC` entra por `repr_pos'`; es uno de los 7 legítimos). **La asimetría clave:** el lado izquierdo del código es el **término simbólico**, el derecho el **numeral del valor**; sólo coinciden porque la teoría prueba `add a 0 =eq a` y `tcFn` tiene congruencia.
- ✅ **§22 — `pcc_axiom_inst2` HECHO** (`MpCodePrf`): instancia axiomas `forall_2` codificados con **dos testigos abiertos**. Requirió **`pcc_forallElim_code_open`** (`ForallElimCodePrf`): **`hAc` también era innecesaria** — tras `prf_substfc_forall` el cuerpo de la 2ª eliminación es `substfc (σ0) (liftc 0 w1) ⌜phi⌝`, que **contiene `w1`** y no es cerrado. Mismo patrón que §17 (arrastrar los lifts). Piezas: `liftTerm_forallc_open`, `liftTerm_substfc_open2`. `pcc_forallElim_code'` queda como corolario. **Verificado:** `pcc_ax5_inst (tcFn a) (tcFn b)` typechequea. `[propext, choice, Quot.sound]` (+`prf_inAxC` en las instancias).
- ⛔ **HUECO del paso inductivo de `+` (§22.3, sondeo verificado):** para USAR `pcc_ax5_inst` hay que computar el **doble** `substfc`. El **interno** sí (`prf_substfc_arith_open 1 ...` → `substCodeF 1 (liftc 0 w1) phi`); el **externo** actúa sobre `substCodeF ...`, que **no es `formCode` de nada meta** ⇒ `prf_substfc_arith_open` no aplica. Faltan **(A)** «el código de un numeral es CERRADO» (`prf_liftc_tcFn`/`prf_substtc_tcFn`: no hay axioma, pero **es derivable por inducción interna** con `ax_tc_zero`/`ax_tc_succ` — el hecho estándar «`num a` es cerrado») y **(B)** la composición `substfc 0 w2 (substCodeF 1 w1 phi) =eq substCodeF2 w1 w2 phi` (inducción estructural en `phi`, usando (A)).
- ✅ **§23 — (A) EL CÓDIGO DE UN NUMERAL ES CERRADO** (`Meta/NumCodeClosedPrf.lean`): **`prf_liftc_tcFn (a) : liftc zero (tcFn a) =eq tcFn a`** y **`prf_substtc_tcFn (W a) : substtc zero W (tcFn a) =eq tcFn a`**. **Primera inducción interna del proyecto** (`prf_nat_induction`): base `tcFn 0 = ⌜0⌝` (código concreto), paso `tcFn (σx) = succc (tcFn x)` atravesando `funcc`. `[propext, choice, Quot.sound]` — **sin `prf_inAxC`** (no pasa por `repr_pos'`). Infra: `prf_congr_liftc`, `prf_congr_substtc3`, `prf_congr_funcc2` (+ versiones `PrfH`).
- ✅ **§24 — (B) LA INSTANCIA DE `ax5`, COMPUTADA**: **`pcc_ax5_computed (a b) : ⊢ Prov(⌜ȧ + σḃ = σ(ȧ + ḃ)⌝)`**. **No necesitaba la inducción general** sobre fórmulas que preveía §22.3(B): el cuerpo de `ax5` es concreto y `substCodeF 1 W₁ (cuerpo)` computa **por `rfl`**; basta computar el `substfc` externo con (A). Infra: `succcT`, `prf_tc_succ'`, `prf_congr_succcT`, `prf_substtc_funcc1/2`, `prf_substtc_succcT/addcT/varc0`.
- ✅ **§25 — `pcc_thm_inst` + LEIBNIZ CODIFICADO LIBRE DE MURO.** `pcc_thm_inst (φ) (h : Prf (∀φ)) (w)` y `pcc_thm_inst2` internalizan **cualquier teorema universal** (no sólo axiomas); `pcc_axiom_inst`/`inst2` pasan a ser corolarios. **Hallazgo:** `prf_lineWF_leibniz` es **estructural** (`lineWF ⟨concl,13,A,t₁,t₂⟩ ⇔ concl =eq implc (eqc t₁ t₂) (implc (substfc 0 t₁ A) (substfc 0 t₂ A))`), sin premisas y con códigos **arbitrarios** — como EQREFL y Q1/Q2. Luego **`pcc_leibniz_code (Ac t₁ t₂)`** se demuestra con un testigo de **una sola línea**, `[propext, choice, Quot.sound]` **sin `prf_inAxC`**. Verificado con códigos abiertos. **Consecuencia:** la lógica ecuacional interna sale de `pcc_leibniz_code` + `pcc_mp_code`, sin teoremas codificados ni `∀`-elim triple.
- ✅ **§26 — `pcc_mp_code_open` + LÓGICA ECUACIONAL INTERNA.** `hAc`/`hBc` eran el **cuarto** artefacto de clausura (`hw` §17, `hAc` §22): se arrastran los lifts (`liftFormula_provFromCode_open` + `liftTerm_implc_open`); tras los dos `∃`-elim los códigos quedan **doblemente lifteados** y el ensamblaje pasa verbatim. `pcc_mp_code` queda como corolario. Con `pcc_leibniz_code` + `pcc_mp_code_open`: **`pcc_leibniz_apply`**, **`pcc_eq_trans_code`** (Leibniz con `Ac := (X = v₀)`) y **`pcc_congr_succ_code`** (Leibniz con `Ac := (σX = σv₀)`, base = reflexividad codificada libre de muro). Todos `[propext, choice, Quot.sound]`. **Restricción real:** el código fijo `X` debe ser `substtc`-invariante; lo descargan `substtc_inv_tcFn` (= (A)), `substtc_inv_succcT`, `substtc_inv_addcT`.
- ✅ **§28 — EVALUACIÓN PROVABLE DE LISTAS.** `pcc_eval_carc`/`pcc_eval_cdrc` (sin inducción, axiomas `forall_2`) y `pcc_eval_lenc` (inducción `prf_list_induction`). Constructores `carcT`/`cdrcT`/`lencT`/`consT`. `nthc`/`runFn` pertenecen a la fase estructural.
- 🛠️ **FIX DE SOLIDEZ (2026‑07‑12, commit `99183a7`):** `ax_lineWF_gen` era **incondicional** ⇒ el verificador concluía cualquier fórmula desde una premisa en `checked` ⇒ **`Prov` era total** (testigo sin `sorry` a `Prf (provFromCode ⊥)`). Corregido a bicondicional `concl =eq forallc body`. Exploit muerto; cadena real intacta (mismos axiomas). Ver `feedback-verifier-soundness`.
- ✅ **§32 — CASOS COMPOSICIONALES `∧`/`∨`.** Líneas J1/J2 libres de muro (`pcc_j1_code`/`pcc_j2_code`, `pcc_or_introL/R_code`); combinadores `pcc_reflect_and`/`pcc_reflect_or` (agnósticos del código, suben las reflexiones de las partes). `[propext, choice, Quot.sound]`.
- ✅ **§32 — GEN interno (`pcc_gen_code`) + ladrillo aritmético (`prf_lt_succ_split`).**
- 🧭 **DECISIÓN (B) confirmada:** reformular el target sobre la forma **punteada** (dot-notation, `tcFn`), que es la formulación canónica para fórmulas abiertas. **Keystone validado**: `formCode(provCodeC' φ) = exc(formCode(bodyF φ))`, luego `pcc_exIntro_code_open (formCode bodyF)(tcFn #0)` conecta la reflexión punteada del cuerpo con `provCodeC'(provCodeC' φ)`. El dotado reutiliza `substCodeF` (`substfc 0 (tcFn #0)`).
- ⏳ **SIGUIENTE (ladrillos de B):** (1) `d3_prf_of_dotted` (∃-elim + `pcc_and_intro_code` + `pcc_exIntro_code_open`); (2) **hC_dot/hI_dot** — reflexión punteada de `chainOk`/`In`, cuyo 2º arg `runFn nil p` compuesto exige la **evaluación provable de `runFn`** (la pieza dura); (3) `∀i<b`-intro (ley de sucesor acotada codificada con `prf_lt_succ_split`+`pcc_gen_code` + base + inducción); (4) `d3_prf` → `goedel_second_prf` → F7b.
- ✅ **§33‑§37 — `d3_prf_of_dotted` + evaluación provable estructural** (`D3DottedPrf`, `EvalRunFnPrf`, `EvalNthcPrf`, `LineWFConsPrf`, `EvalCarcNthcPrf`). Keystone `formCode(provCodeC' φ)=exc(formCode(bodyF φ))` → `d3_prf_of_dotted_atoms` reduce D3 a las reflexiones punteadas de `chainOk`/`In`. Evaluación provable de `runFn`/`nthc`/`carc∘nthc`: **`pcc_eval_nthc`** (inducción acotada), **`pcc_eval_carc_nthc`** (`chainOk nil p ⇒ i<lenc p ⇒ Prov(⌜carc(nthc(ṗ,ı̇))=(carc(nthc p i))˙⌝)`). Sancionado **`ax_lineWF_cons`** (companion de `ax_lineWF_inv`; una línea `lineWF` es un `cons`; refuerza `lineWF`, cadena real intacta) → `prf_line_is_cons`.
- ✅ **§38 — `hI_dot` COMPLETO: D3 REDUCIDA A `hC_dot` SOLO** (`D3InDotPrf`, HEAD `eb48a1b`; commits `f4f095b`/`262e18e`/`c12172e`/`05fe7c3`/`eb48a1b`). El átomo `In` está cerrado: **`d3_prf_of_chainOkDot (φ) (hC) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))`** — D3 depende ya de **un único** lema, la reflexión punteada de `chainOk`. Ladrillos: `substCodeT_closed`, `pcc_bdEx_intro_open`, Step A `pcc_bddDot_imp_inDot`, Step B puente `prf_bddCarcDot_eq`, y el **NÚCLEO** `pcc_bddCarcDot_reflect` (`chainOk nil p ⇒ boundedCarcIn ⌜φ⌝ p ⇒ Prov(⌜bddCarcDotAt φ p⌝)`). **Tres hallazgos del núcleo:** (1) el `PrfH_ex_elim` **liftea `p`** ⇒ hubo que **generalizar todo lo dotado sobre `p` arbitrario** (el `formCode` codifica siempre el *esquema* con `#0`; sólo varía el testigo `tcFn p`, así que `substCodeF` no cambia); (2) la **COTA exigió SIMETRÍA INTERNA** (no existía) — `pcc_lt_tracked` da `tcFn (lenc ↑p)` pero el código dotado pide `lencT`, y **sólo son iguales dentro de `Prov`** (es `pcc_eval_lenc`), en dirección contraria a Leibniz ⇒ **`PrfH_eq_symm_code`** + `prf_substfc_ltCodeFn_snd`; (3) el **CUERPO NO la necesita** (la hipótesis del `∃` es una igualdad *objeto* ⇒ basta congruencia objeto + `PrfH_provCode_congr` sobre `pcc_eval_carc_nthc`, que consume `chainOk`). Piezas nuevas: `PrfH_eq_symm_code`, `PrfH_and_intro_code`, `PrfH_bdEx_intro_open`, `liftTerm_tcFn`, `substtc_inv_liftc_tcFn`, `substtc_inv_termCode_formCode`, `prf_substfc_ltCodeFn_snd`, `liftTerm_inDotAt`/`liftTerm_bddCarcDotAt`. `hbody_of_atoms`/`d3_prf_of_dotted_atoms` reestructurados (`hI` recibe también `chainOk`). Build **91 jobs**, 0 sorrys; `[propext, choice, Quot.sound, prf_inAxC]`; cadena real intacta.
- ✅ **§39 — LÓGICA PROPOSICIONAL e INDUCCIÓN *internas* a nivel de código** (`Meta/PropCodePrf.lean`). Hallazgo: las líneas‑axioma `p1`/`p2`/`j3`/`efq` **y la de INDUCCIÓN (`ind`, tag 18)** son TODAS **estructurales** (bicondicional `lineWF` con códigos **arbitrarios** y `premsOf = nil`, como EQREFL/Q1/Q2/LEIBNIZ) ⇒ cada una cuesta un testigo de **una sola línea** (`pcc_axline`) y sale **libre de muro**. Con **P1+P2+MP** el cálculo implicacional interno es completo (`pcc_weaken_code`, `pcc_imp_trans_code`, `pcc_or_elim_imp_code`): **`Prov` dispone YA de lógica completa** (MP, `∀`‑elim, `∃`‑intro, gen, Leibniz, `∧`, `∨` intro **y elim**, ex‑falso, **inducción**). `pcc_ind_code` es el desbloqueo de `hC_dot`.
- ✅ **§40 — `pcc_bdAll_intro`: la INTRODUCCIÓN del `∀` acotado** (`Meta/BdAllIntroPrf.lean`, HEAD `6dba12e`, 93 jobs). Es el keystone que §30 dejó pendiente (`pcc_bdAll_elim` existía; la intro NO) y que bloqueaba `hC_dot`. **Lo que costó:** (1) **NO se induce sobre el testigo** (`Ac[x] ⇒ Ac[σx]` es FALSO) sino sobre la **COTA**, a nivel objeto, con guarda `b < σbnd` — la guarda da `b < bnd` y de ahí `hbody` entrega el `Prov(⌜φ(ḃ)⌝)` que el paso necesita; la **disyunción finita de casos** (Hájek‑Pudlák) **NO sirve** porque `lenc p` con `p` abstracto **no es un numeral concreto**; (2) `pcc_gen_code` toma el body **abierto** ⇒ se induce sobre el **CUERPO ABIERTO** y se aplica `gen` **una vez al final** (evita el *round‑trip* `∀`‑elim); (3) el split se **voltea en el objeto** (`prf_lt_succ_split'` da `b = i`), porque la simetría interna exige el 1er arg `substtc`‑invariante y `⌜v₀⌝` no lo es; (4) **obstrucción `hPsiId`**: `substfc` **DECREMENTA** las variables superiores, así que `substfc 0 ⌜v₀⌝ Psi` sólo es la identidad si la única code‑var de `Psi` es `⌜v₀⌝`; (5) **obstrucción De Bruijn del ensamblaje**: el binder de la inducción **desplaza** las libres ⇒ dentro del `gen` hace falta `hbody` en **`↑p`**, no en `p` — resuelto **parametrizando sobre `p`** (`CF`/`bndF`/`PsiF` como funciones + conmutación del lift), mismo patrón que el `∃`‑elim de `hI_dot`.
- ⏳ **SIGUIENTE — `hC_dot`: el cuerpo `lineOkB`** (composite GRANDE, 2‑4 sesiones; **toda la maquinaria existe ya**). `chainOkB c p = ∀i<lenc p. lineOkB c p i` con `lineOkB = lineWF (nthc p i) ∧ ∀j<lenc L. (In (nthc L j) nil ∨ ∃k<i. carc (nthc p k) = nthc L j)`. Descomposición: **∀i** y **∀j (anidado)** = `pcc_bdAll_intro` ✅ (dos veces); **∧** = `pcc_reflect_and` ✅; **∨** = `pcc_reflect_or` ✅; **∃k** = `pcc_bdEx_intro_open` ✅ (de `hI_dot`); `In x nil` es **refutable** ⇒ el disyunto izquierdo sale por **ex falso** (barato); el átomo `carc (nthc p k) = nthc L j` = `pcc_eq_tracked` + `pcc_eval_carc_nthc` + `pcc_eval_nthc` ✅. **⚠ El átomo `lineWF` es un SUBPROYECTO**: reflejarlo dotado exige recorrer los **21 casos de tag** (`prf_lineWF_inv` da la disyunción `tagDisj`; en cada caso hay que reflejar su ecuación estructural y aplicar el **bicondicional codificado** `ax_lineWF_<tag>` vía `pcc_thm_inst`) — varios cientos de líneas. Faltan además las evaluaciones de `premsOf` (y `lenc`/`nthc` sobre él) y los cómputos `substCodeF` de `chainOkB`/`lineOkB`/`boundedPremsIn` (patrón `substCodeT_closed`). Luego `d3_prf := d3_prf_of_chainOkDot φ hC_dot` → `goedel_second_prf` → **F7b retira `axiom d3` (7→6)**.
- ✅ **§31 — COMPLETITUD-Δ₀ PROVABLE (arranque): reflexión de los átomos desde hipótesis.** Desbloqueo: `pcc_eval_add` demuestra `addcT(ȧ)(ḃ) =eq tcFn(a+b)` para `a,b` **abstractos** (puente símbolo↔valor sobre `+`). **`pcc_exIntro_code_open`** (∃-intro sin `hAc`, arrastrando el lift — keystone), **`pcc_lt_intro_open`**, y las DOS reflexiones atómicas Δ₀: **`pcc_eq_tracked`** (`=`, ya existía) y **`pcc_lt_tracked`** (`<`, NUEVO) — ambas `⊢ (átomo) ⇒ provFromCode(código tracked)` para términos arbitrarios.
- ⏳ **SIGUIENTE:** (1) casos composicionales `∧`/`∨` (con C libres de muro §30) e `impl`/`¬`; (2) el **`∀i<b`** necesita **inducción acotada interna** sobre la cota (el punto duro que queda); (3) ensamblar `boundedIn`/`chainOkB` → `hbI`/`hbC` (quizá reformulando el target sobre `tcFn`) → `d3_prf` → `goedel_second_prf`.
- ✅ **§30 — CUANTIFICADORES ACOTADOS a nivel de código.** `and` interno **libre de muro** (líneas C1/C2/C3 estructurales): `pcc_c1_code`/`_c2`/`_c3` + `pcc_and_intro_code`/`_elim_left`/`_elim_right`. **`pcc_bdEx_intro`** (`∃i<B`-intro = `∧`-intro + `∃`-intro) y **`pcc_bdAll_elim`** (`∀i<B`-elim = `∀`-elim + MP interno), con `bdExCode`/`bdAllCode`. Todos `[propext, choice, Quot.sound]` — **sin `prf_inAxC`**.
- ⏳ **SIGUIENTE (fase estructural, la última):** (1) `hbI` = reflexión de `boundedIn` (`∃i<lenc L. nthc L i=x`) vía `pcc_bdEx_intro` + `pcc_lt_intro` + evaluación de `nthc`; (2) la **INTRODUCCIÓN del `∀` acotado** para `hbC` (reflexión de `chainOkB`) requiere **inducción acotada interna** sobre la cota; (3) `d3_prf_of_reflect_bounded (hbC) (hbI)` → `d3_prf` → `goedel_second_prf`; F7b retira `axiom d3`.
- ✅ **§29 — REFLEXIÓN DEL ÁTOMO `<`** (`= ∃ + =eq + evaluación provable`). `pcc_lt_intro (a b K) (ha hb) (h : Prov(⌜ȧ+σK=ḃ⌝)) : Prov(⌜ȧ<ḃ⌝)`. `ltBwd` = dirección `⇐` de `ax13` como teorema object cerrado; `pcc_ltBwd_computed` lo codifica en **tracked** (`pcc_thm_inst2` + `prf_substfc_arith_open`, sin muro). El `substfc` externo baja bajo el `∃`-binder (nivel 1) ⇒ nuevos `prf_substtc_tcFn_*_at` (invariancia de `tcFn a` bajo `substtc` a nivel arbitrario). Ensamblaje: `prf_substfc_exBodyc` + `pcc_exIntro_code'` + `pcc_mp_code_apply`.
- ⏳ **SIGUIENTE:** (1) **cuantificadores acotados** a nivel de código (`boundedIn`/`boundedCarcLt`/`boundedAllIn` usan `∃i<b`/`∀i<b`) — única zona aún no sondeada; (2) inducción estructural sobre la forma acotada → `hbI`/`hbC` → `d3_prf_of_reflect_bounded` → `d3_prf` → `goedel_second_prf`.
- ✅ **§27 — EVALUACIÓN PROVABLE DE `+` COMPLETA.** `pcc_eval_add (a b) : Prf (provFromCode (evalAddCode a b))` para `a`,`b` **arbitrarios**. Piezas: formas implicación de los combinadores (`pcc_leibniz_apply_imp`, `pcc_eq_trans_code_imp`, `pcc_congr_succ_code_imp`), el paso `pcc_eval_add_succ_imp` (congruencia interna de `σ` sobre la HI + transitividad interna con (B) + transporte de códigos), y la inducción object `prf_eval_add_all` (`prf_nat_induction`). Transparencia del código: `substTerm_evalAddCode`/`liftTerm_evalAddCode`/`substFormula_evalAddPred`/`step_evalAddPred` + nuevos `substTerm_numeral`/`substTerm_strCode`. **Truco De Bruijn:** `liftTerm 1 (liftTerm 0 a)` se cancela vía `← FOL.liftTerm_comm_zero a 0` y luego `FOL.substTerm_liftTerm`.
- ⏳ **SIGUIENTE:** (1) misma receta para `lenc`/`nthc`/`carc`/`runFn` sobre numerales; (2) `<` (= `∃` + `=eq` + evaluación provable, §18); (3) **cuantificadores acotados** a nivel de código — única zona aún no sondeada; (4) inducción estructural → `hbI`/`hbC` → `d3_prf_of_reflect_bounded` → `d3_prf` → `goedel_second_prf`.
- 📌 (plan previo §25.4): `pcc_mp_code_open` Para aplicar `pcc_leibniz_code` hace falta `pcc_mp_code` dos veces, pero éste exige **códigos cerrados** (`hAc`/`hBc`) y los nuestros contienen `tcFn #0`. **Cuarta vez** que una hipótesis de clausura estorba (`hw` §17, `hAc` §22): se arregla **arrastrando los lifts** con `liftFormula_provFromCode_open`. Luego: `pcc_eq_trans_code`/`pcc_congr_succ_code` → paso inductivo de `+` → evaluación provable de `+` COMPLETA → `lenc`/`nthc`/`carc`/`runFn` → `<` → cuantificadores acotados → inducción estructural → `hbI`/`hbC` → `d3_prf`.
- 📌 (plan previo §24.3) — el paso inductivo de `+` pide LÓGICA ECUACIONAL INTERNA sobre códigos:** normalizando los códigos, el objetivo es `Prov(⌜ȧ + σḃ = σ((a+b)˙)⌝)`, y tenemos (B) `Prov(⌜ȧ + σḃ = σ(ȧ + ḃ)⌝)` y la HI `Prov(⌜ȧ + ḃ = (a+b)˙⌝)`. Faltan **`pcc_congr_succ_code (X Y) : Prov(⌜X=Y⌝) → Prov(⌜σX=σY⌝)`** y **`pcc_eq_trans_code (X Y Z)`**. **Derivables sin obstrucción:** la teoría objeto demuestra sus clausuras universales (teoremas), `repr_pos'_prf` da sus códigos, y se instancian en códigos **abiertos** con `pcc_forallElim_code_open` + `pcc_mp_code`. Ladrillo auxiliar: **`pcc_thm_inst`** (instanciar un **teorema** codificado, no sólo un axioma). Orden: (1) `pcc_thm_inst`; (2) `pcc_congr_succ_code`/`pcc_eq_trans_code`; (3) paso inductivo → evaluación provable de `+` COMPLETA; (4) `lenc`/`nthc`/`carc`/`runFn` → `<` → cuantificadores acotados → inducción estructural → `hbI`/`hbC` → `d3_prf`.
- 📌 (plan previo §22.4): (1) **(A)**; (2) **(B)** composición; (3) paso inductivo de `+`; (4) misma receta para `lenc`/`nthc`/`carc`/`runFn`; luego `<`, cuantificadores acotados, inducción estructural → `hbI`/`hbC` → `d3_prf` → `goedel_second_prf`.
- 📌 (plan previo §21.3): (1) **`pcc_axiom_inst2`** para axiomas `forall_2` como `ax5` (`pcc_forallElim_code'` ×2 + `prf_substfc_forall`); (3) **paso inductivo de `+`** (inducción interna sobre el 2º sumando: `⊢ ∀b. Prov(⌜ȧ + ḃ = (a+b)˙⌝)`, con `prf_nat_induction` y lifts vía `liftFormula_provFromCode_open`); luego `lenc`/`nthc`/`carc`/`runFn` → reflexión de `<` → cuantificadores acotados → inducción estructural → `hbI`/`hbC` → `d3_prf` → `goedel_second_prf`. **Sin obstrucción conocida.**
- ⚠ **Nota honesta:** 12‑A ≈ portar la Σ₁‑completitud provable de IΣ₁; es trabajo de varias sesiones. **Alternativa siempre disponible:** consolidar Gödel II *módulo el axioma D3* (`goedel_second'`) — estado ya publicable.
- 🧹 **F7a ✅ HECHA** (2026‑07‑09): 14→7 `axiom`; `Meta/Incompleteness.lean` eliminado + 5 postulados de `Provability` retirados; registro en `AXIOMS.md`. **F7b** (`GodelTwo.d3`) bloqueada hasta D3 real.

> **HISTÓRICO (contexto de cómo se llegó aquí).** Lo que sigue en este bloque documenta el camino descartado (`tcFn`/Opción A) y el diagnóstico que llevó a 12‑A. Se conserva porque explica *por qué* la vía actual es ineludible; **no es la tarea abierta**.

**⚠ HALLAZGO (muro del testigo abstracto):** el puente cierra sólo para testigos **cerrados** (`tcFn p` cerrado sii `p` lo es → `hw` de `pcc_exIntro_code` se descarga). Para el testigo **abstracto** (`p = #0` tras `prf_ex_elim_imp`), `tcFn #0` NO es cerrado (`hw` falla) y, además, todo combinador base (`pcc_in_*`/`pcc_imp`/D1) produce códigos vía `termCode` **meta**; transportar a `tcFn` exige `tcFn L =eq termCode L`, **meta‑stuck para `L` abstracta**. **Conclusión: `hI_tracked` abstracto requiere la Opción A DE RAÍZ** (redefinir `provFormulaC'ₜ`/`provCodeC'ₜ` con `tcFn`/`substfc` desde el cuerpo Σ₁ + re‑derivar D1ₜ `repr_pos'_prfₜ`), no un lema incremental. Ver `GODEL-D3-TRACKED-DESIGN.md` §4.2.

**Próxima acción concreta (Opción A de raíz — plan detallado en `GODEL-D3-TRACKED-DESIGN.md` §10):**

0. ✅ **HECHO** (commit `fac8668`) `Meta/TrackedCorePrf.lean`: **`liftFormula_provFromCode`** (clausura genérica de `provFromCode c` para código cerrado arbitrario).
1. ✅ **HECHO** (commit `7fb9052`) **constructores `tcFn`‑based**: `atom2CodeFn` (generaliza `inFormCodeFn` a átomos‑2) + puente `formCode` + `inFormCodeFn_eq_atom2` + congruencia + clausura + transporte + `chainOkCodeFn`/`allInCodeFn`. §10.4 pasos 1‑2.
2. ⚠️ **`tcFn` (Opción A §10) DESCARTADO para el paso abstracto** (investigación §11, 2026‑07‑05c): el sondeo del caso cabeza de `hI_tracked` muestra que el consecuente `provFromCode(atom2CodeFn (tcFn·)(tcFn·))` sólo se identifica con el teorema real si `tcFn L =eq termCode L`, **stuck para `L` abstracta** (`tcFn` no tiene ecuación de variable). Además se verificó que **NO hay atajo por teorema de deducción** (D1 `repr_pos'` exige `Prf` CERRADO; D1‑con‑contexto es FALSA — esa brecha ES D3). Los constructores `atom2CodeFn` (`7fb9052`) siguen válidos como infraestructura.
3. ⏳ **VÍA GENUINA — Σ₁‑completitud provable estándar, diseño de codificación resuelto (§12)**: la vía testigo‑lista naíf **también se descartó** (§12.2: el paso cola mezcla testigos `tcFn rest` vs `tcFn (cons line rest)` → `pcc_imp` no aplica). **Hallazgo central (§12.1): la codificación del testigo ≡ la representación del verificador** — la Σ₁‑completitud estándar exige `δ` Δ₀‑sobre‑NÚMEROS (∃/∀ acotados), pero el verificador es estructural sobre listas (`carc`/`cdrc`, sin `len`/`nth`). **Recomendación §12.4 = Opción 12‑A (β‑función / capa numérica Δ₀ del verificador)**: grande pero segura (construcción de libro). Plan por fases §12.4:
   - **1a ✅ HECHO (commit `3eaffd8`)**: `lenc`/`nthc` (long./índice de lista‑código) — defs + 4 axiomas en `Minimal/Axioms` (extensión conservadora; `axioms_eq` rfl preservado; build entero verde, verificador/D1 intactos) + ecuaciones `Prf` (`Meta/NumListPrf.lean`: `prf_lenc_nil/cons`, `prf_nthc_zero/succ`).
   - **1b ⏳ EN CURSO** (más grande de lo estimado — es la puerta a reconstruir aritmética en `Prf`): la caracterización acotada `In x L ⇔ ∃ i < lenc L. nthc L i =eq x` necesita **primero un toolkit aritmético de `<` en `Prf`**, porque `<` = `∃k. a+σk=b` (`ax13`) y `add` recurre por la derecha, así que `0+n=n` NO es teorema de Q (necesita `Prf.ind`). **✅ TOOLKIT `<` COMPLETO** (`Meta/NatArithPrf.lean`, commits `2d7c17c`/`80bb08b`/`5e2ce47`/`d655e3c`; **todos `[propext, choice, Quot.sound]`**): `prf_nat_induction` (eliminador de inducción natural, envuelve `Prf.ind`); `norm11` (norm De Bruijn de 1 binder); `prf_add_zero_left` (`0+n=n`), `prf_add_succ_left` (`σm+n=σ(m+n)`); `prf_lt_iff` (`lt a b ⇔ ∃k. a+σk=b`); `PrfH_lt_intro`/`prf_lt_intro`; `prf_succ_ne_zero`, `prf_succ_inj`; `prf_zero_lt_succ`, **`prf_succ_lt_succ_of_lt`**, **`prf_lt_of_succ_lt_succ`**, **`prf_not_lt_zero`**; `PrfH_eq_congr_succ`.
     **Lección De Bruijn (clave, reusar):** para eliminar un `∃` de una HIPÓTESIS usar **`prf_ex_elim_imp`** (lift simple, casa con el `↑a`/`↑b` que ya trae el cuerpo del `∃`), **NO `PrfH_ex_elim`** (liftea además el contexto → doble lift). Y al desplegar `ax13_lt_def` hay que incluir **`add`** en el simp‑set o el cuerpo del `∃` no reduce.
   - **1b ✅ COMPLETA (commit `154fbc3`, `Meta/BoundedInPrf.lean`; `#print axioms` = `[propext, choice, Quot.sound]`):** **`prf_In_iff_boundedIn (x L) : Prf (In x L ⇔ ∃ i < lenc L. nthc L i =eq x)`**. Piezas: `boundedIn`; `liftFormula_boundedIn_gen`/`substFormula_boundedIn` (empujan lift/subst a través de `boundedIn` — imprescindibles: la inducción de listas mete DOS binders y `boundedIn` contiene un `∃`); helpers `prf_boundedIn_head/tail/nil/cons`; congruencias `prf_lt_subst2`/`PrfH_lt_subst1`/`PrfH_eq_congr_nthc2`/`PrfH_eq_congr_pred`; **`prf_zero_or_eq_succ_pred`** (`n=0 ∨ n=σ(pred n)`) y **`prf_zero_or_succ`** (`NatArithPrf`); las dos inducciones + el `⇔`.
     **TRUCOS clave (reusar):** (1) los `∃`‑elim van en **lemas `Prf` autónomos** (`prf_ex_elim_imp`, lift simple) y se aplican con `PrfH.mp` dentro de la inducción — nunca `PrfH_ex_elim` (liftea el contexto → doble lift). (2) Para partir por casos un índice dentro de un contexto `PrfH` **sin `∃`**, usar el **predecesor** (`prf_zero_or_eq_succ_pred`): el testigo del caso `i=σ(pred i)` es directamente `pred i`.
   - **FASE 2 — RIESGO CERRADO ✅ (sondeo 2026‑07‑08, commit `4685366`, `Meta/RunFnBoundedPrf.lean`, §13 del diseño):** **NO hace falta β‑función.** `runFn nil p` **no es recursión con acumulador: es el *map* de `carc` sobre `p`** — probado: `prf_runFn_nil_cons : runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest)` y `prf_lenc_runFn : lenc (runFn nil p) =eq lenc p` (cadena `prf_runFn_cons`→`prf_concat_nil_eq`→**`prf_runFn_weaken`** (saca el acumulador fuera)→`prf_concat_cons_eq`; axiomas limpios). ⇒ el acumulador nunca hay que construirlo: `In x (runFn nil p)` queda acotado por `lenc p`, y en `chainOk` el acumulador solo se usa vía `In y (·)`, que se reescribe como `∃ k < i. carc (nthc p k) =eq y`. Es la formulación Δ₀ clásica «prueba = sucesión de líneas justificadas por líneas anteriores». **Corrección a §12.3: llamarlo «β‑función» era pesimista; la capa `lenc`/`nthc` de la fase 1 basta.**
   - **FASE 2 — lado `In` ✅ CERRADO** (`Meta/RunFnBoundedPrf.lean`, commits `4685366`/`ffbcdb9`/`05cc4ab`; todos `[propext, choice, Quot.sound]`): `prf_runFn_nil_cons`, `prf_lenc_runFn`, **`prf_nthc_runFn`** (`i < lenc p ⇒ nthc (runFn nil p) i =eq carc (nthc p i)`; patrón `∀i` interno + `qconf` + `PrfH_spec`, como `prf_runFn_concat`) y el **payoff**: **`prf_In_runFn_iff : In y (runFn nil p) ⇔ ∃ i < lenc p. carc (nthc p i) =eq y`** — cota `lenc p`, acotado sobre `p` directamente.
   - **EN CURSO — FASE 2, lado `chainOk`** (plan preciso en `GODEL-D3-TRACKED-DESIGN.md` **§14.2‑14.3**; sin obstrucción vista): objetivo `chainOk c p ⇔ chainOkB c p` con `chainOkB c p := ∀ i < lenc p. (lineWF (nthc p i) ∧ ∀ j < lenc (premsOf (nthc p i)). (In (nthc (premsOf (nthc p i)) j) c ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j))` — **el acumulador se elimina generalizando en `c`**. Sub‑lemas: (a) `allIn c L ⇔ ∀ j < lenc L. In (nthc L j) c`; (b) `In y (concat c [x]) ⇔ In y c ∨ y =eq x`; (c) split del `∃k<σj`; (d) la inducción principal con **`∀c` interno**. **Dependencias: (a), (b) y (c) son mutuamente independientes; sólo (d) depende de las tres.**
     - **✅ (b) HECHA** (`Meta/ChainOkBoundedPrf.lean`): `prf_in_concat_iff` (cierre de `ax_L3_in_concat`), `prf_in_cons_nil_iff` (`In y [x] ⇔ y =eq x`) y **`prf_in_concat_singleton_iff : In y (concat c [x]) ⇔ In y c ∨ y =eq x`** — el paso que absorbe la conclusión de la línea actual en el acumulador.
     - **✅ (0) HECHA** (refactor compartido; no bloqueaba a nadie, pero (c) y (d) lo necesitan): **`boundedCarcLt y p b`** = `∃k<b. carc (nthc p k) =eq y` con **cota arbitraria** (`boundedCarcIn y p = boundedCarcLt y p (lenc p)`, `rfl`) + `liftFormula_boundedCarcLt`. Necesario porque en `chainOk` la cota es el índice de la línea (`σj`, `i`), no `lenc p`.
     - **✅ (c) HECHA** (`Meta/ChainOkBoundedPrf.lean`): **`prf_boundedCarcLt_cons_succ_iff : (∃k<σj. carc (nthc (cons line rest) k) =eq y) ⇔ (carc line =eq y ∨ ∃k<j. carc (nthc rest k) =eq y)`**, con las dos reintroducciones `prf_boundedCarcLt_cons_of_head` (testigo `0`) y `prf_boundedCarcLt_cons_of_tail` (reindexa `k ↦ σk`). Todos `[propext, choice, Quot.sound]`.
     - **✅ (a) HECHA** (`Meta/ChainOkBoundedPrf.lean`): **`prf_allIn_iff_boundedAllIn : allIn c L ⇔ boundedAllIn c L`** con `boundedAllIn c L := ∀ j < lenc L. In (nthc L j) c`. Reparto: todo el manejo del `∀j` se **confina en cuatro lemas `Prf` autónomos** (`prf_boundedAllIn_nil`, `_cons_head` = instancia `j=0`, `_cons_tail` = reindexa `j ↦ σj`, `_cons` = reintroducción con case-split de `j`), y las dos inducciones de lista (`prf_boundedAllIn_of_allIn` / `prf_allIn_of_boundedAllIn`) quedan triviales. Piezas nuevas: `PrfH_eq_subst_in1` (congruencia de `In` en el **elemento**), `liftFormula_boundedAllIn_gen`/`substFormula_boundedAllIn`, `liftFormula_allIn`/`substFormula_allIn` (rfl). Todos `[propext, choice, Quot.sound]`.
     - **✅ (d) HECHA** (`Meta/ChainOkBoundedPrf.lean`): **`prf_chainOk_iff_chainOkB (c p) : Prf (chainOk c p ⇔ chainOkB c p)`**. Inducción de listas sobre `p` con el acumulador **`∀c` interno** (`chainBPred`), instanciando la HI en `c ++ [carc line]`. Escalones: (1) `prf_boundedCarcLt_zero` + **`prf_premOk_cons_iff`** (el lema puntual que fusiona (b) y (c): `In y c ∨ ∃k<σi. carc (nthc (line::rest) k) =eq y ⇔ In y (c++[carc line]) ∨ ∃k<i. carc (nthc rest k) =eq y`) + defs `boundedPremsIn`/`lineOkB`/`chainOkB` + clausuras De Bruijn + `prf_chainOkB_nil`; (2) las dos mitades del paso `cons` — `prf_lineOkB_zero_iff` (`i=0` ⇒ es `lineOk c line`, vía (a) + `prf_boundedPremsIn_zero_iff`) y `prf_lineOkB_cons_succ_iff` (`i=σi'`, vía `prf_boundedPremsIn_cons_succ_iff` + Leibniz `PrfH_congr_lineOkBAt`); (3) `prf_chainOkB_cons_iff` (espejo exacto de `ax_chainOk_cons`) + la inducción. Todos `[propext, choice, Quot.sound]`.
   - **✅ FASE 2 COMPLETA.** `chainOk`/`In (runFn nil p)` ya tienen forma Δ₀ sobre índices: `chainOkB c p := ∀ i < lenc p. (lineWF (nthc p i) ∧ ∀ j < lenc (premsOf (nthc p i)). (In (nthc (premsOf (nthc p i)) j) c ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j))`. **El acumulador ha desaparecido.**
     **Lecciones De Bruijn acumuladas (§14.4, REUSAR):** `∃`‑elim de una HIPÓTESIS → lema `Prf` autónomo con **`prf_ex_elim_imp`** (nunca `PrfH_ex_elim`, liftea el contexto). `∀`‑intro como CONSECUENTE → **`Prf.qconf`** (nunca `PrfH.gen`). `∀`‑elim de una hipótesis → `PrfH_spec`. Case‑split de un índice bajo `PrfH` sin `∃` → `prf_zero_or_eq_succ_pred` (testigo `pred i`). Empujar lift/subst a través de un predicado con `∃`/`∀` interno necesita lema propio (NO es defeq; los iguala `FOL.liftTerm_comm_zero`). En un `have`, `PrfH _ (…)` no infiere Γ → nombrar el contexto con `let`.
   - **Fases 3‑5:** `num` (numeral‑de) + provable eval + Δ₀‑completitud atómica (aquí entran las ecuaciones de variable de `substfc`); inducción estructural → `⊢ ∀p (δ → Prov ⌜δ(ṗ)⌝)`; ∃‑intro (`pcc_exIntro_code`) → `d3_prf` → `goedel_second_prf`. NOTA: 12‑A ≈ portar la Σ₁‑completitud provable de IΣ₁ (multi‑sesión). **Enlace estratégico:** ver `ESCALANDO_EL_PROYECTO.md` (este toolkit sirve también a DeepArith sobre el kernel FOL⁼ común).
4. **Alternativa honesta siempre disponible (§11.4):** consolidar Gödel II **módulo el axioma D3** (`GodelTwo.goedel_second'`) — estado ya excelente/publicable (Gödel I real + D1/D2 reales). D3 es notoriamente la pieza más dura de Gödel II.
5. **Limpieza F7 — auditoría 2026‑07‑08 la parte en dos:**
   - **F7a ✅ VIABLE AHORA** (verificado con `#print axioms`): `goedel_second'` NO cita `diagonal_lemma`/`provFormula_repr`/`Dem`/`Incompleteness.D2`/`Incompleteness.D3`. Esos 7 postulados solo los usa la **capa legacy** (`Provability.goedelSentence` + teoremas legacy de `Incompleteness.lean`); las menciones en `Necessitation`/`Diagonal`/`HilbertSeq` son solo docstrings. Retirarlos (junto con los teoremas legacy) **no toca la cadena real** y bajaría de 14 a 7 `axiom` de Lean.
   - **F7b ⛔ BLOQUEADA:** `GodelTwo.d3` sí es portante (`goedel_second'` lo cita). Espera al D3 real.

> **Estado real de la cadena (auditado 2026‑07‑08 con `#print axioms`):** D1 `repr_pos'_prf` = estándar + `prf_inAxC`; **D2 `d2_prf` = estándar, cero postulados**; `d3_prf_of_sigma1` = estándar + `prf_inAxC`; **Gödel I real** `goedel_first_real'` = estándar + ω‑reglas + `ax_induction`/`ax_list_induction`/`ax_inAxC` (ningún postulado gödeliano); **Gödel II** `goedel_second'` = estándar + ω‑reglas + `ax_list_induction` + **`d3`** (único postulado gödeliano). Los 4 axiomas `lenc`/`nthc` añadidos a `Minimal.axioms` son `def ax_*` de teoría object (extensión definicional conservadora), NO `axiom` de Lean.

<!-- -->

> **Nota De Bruijn (reusar en `hI/hC_tracked`):** colapso de lift con DOS ubicaciones OPUESTAS. (1) Contexto post‑`prf_ex_elim_imp`: `liftTerm 0 (substfc zero w Ac)` sin subst externa → colapsar con `simp only [liftTerm_substfc …]` PREVIO al `simp` grande, MIENTRAS `zero` es literal. (2) Target post‑`PrfH_ex_intro`: `liftTerm 0 (exc Ac)` se cancela con la subst externa `substTerm 0 r (·)` (`FOL.substTerm_liftTerm`) → NO pre‑colapsar. (`substTerm v s (.var v) = s` sin lift, FOL.lean:82.)

**Recordatorios de build (ver `feedback_*`):** compilar SIEMPRE desde RPP bajo v4.31.0 (nunca `cd FOL && lake build`); un build "Replayed" de caché puede ocultar errores en ediciones sin commitear.

---

**Last updated:** 2026-07-08 (61 módulos, 75 jobs, Lean v4.31.0, 0 sorrys) — **12‑A FASES 1b y 2 COMPLETAS: el verificador ya es Δ₀ y sin acumulador.** Cuatro módulos nuevos: `Meta/NatArithPrf.lean` (toolkit de `<` en `Prf`; `0+n=n` **no** es teorema de Q → `Prf.ind`), `Meta/BoundedInPrf.lean` (**`prf_In_iff_boundedIn`**), `Meta/RunFnBoundedPrf.lean` (**`prf_In_runFn_iff`**; hallazgo: `runFn nil p` es el *map* de `carc` ⇒ **no hace falta β‑función**, corrige el pesimismo de §12.3) y `Meta/ChainOkBoundedPrf.lean` (**`prf_chainOk_iff_chainOkB`**: *el acumulador desaparece*, inducción con `∀c` interno + lema puntual `prf_premOk_cons_iff`). Todos `#print axioms` = `[propext, choice, Quot.sound]`. Ya **no queda ningún punto del plan 12‑A sin verificar en código**. Siguiente: fases 3‑5 → `d3_prf` → `goedel_second_prf`. — (previo 2026-07-05, ~54 módulos, 67 jobs) **Opción A: predicado de demostrabilidad con TESTIGO RASTREADO (hacia D3/Gödel II)**. Tras caracterizar rigurosamente el muro (`hI`/`hC` genéricos son indemostrables: el código absorbe el testigo `#0` como `varc 0`, reflejando una fórmula con variable libre que no es teorema), se adoptó **Opción A** (rastreo uniforme vía `tcFn`/`substfc`, patrón `diag_arith`). Diseño completo en **`GODEL-D3-TRACKED-DESIGN.md`** (diagnóstico, opciones A/B, fases, riesgos). Hecho: **A‑F1** (`prf_tc_objList`/`prf_tc_objList_formCode`: `tcFn=termCode` sobre la forma de la lista de conclusiones) + **A‑F2** (**`prf_provCodeC'_of_tracked_witness`**: la reflexión rastreada con testigo-código = `provCodeC'` real; mecanismo central). También `pcc_in_runFn_objList` (= `hI` para testigos **concretos**) + tracking `runFn→objList`. **Próximo (A‑F3/F4, piezas grandes tipo `d2_prf`)**: `pcc_exIntro_code` (∃-intro a nivel de código para testigo-código arbitrario — **verificar primero** que el verificador acepta líneas-axioma Q2 con testigo arbitrario) + `hI_tracked`/`hC_tracked` por inducción object (consecuente `substfc 0 (tcFn p)` rastrea `p`) → `d3_prf` → `goedel_second_prf`.

**Last updated:** 2026-06-28b (~52 módulos, 65 jobs) — **Infraestructura de reflexión Σ₁ (núcleo duro de D3)**. `Meta/Sigma1Prf.lean` (NUEVO): combinador clave **`pcc_imp {A B} (h : Prf (A ⇒ B)) : Prf (provCodeC' A ⇒ provCodeC' B)`** (D2 `d2_prf` + D1 `repr_pos'_prf`) + `pcc_imp2` + combinadores `pcc_in_head/tail/head_eq/nil`, `pcc_chainOk_nil/cons`, `pcc_allIn_nil/cons`. Con ellos, `hI`/`hC` se reducen a **(1) reflexión de igualdad** `Prf ((x=eq y) ⇒ provCodeC'(x=eq y))` (obstrucción Tarski: los `▸`/Leibniz fallan porque `formCode(x=eq y)` absorbe la forma sintáctica de `y`, no su valor → necesita sustitución formalizada `substfc`) **y (2) cierre inductivo** sobre el código con seguimiento aritmético `tcFn`/`substfc` (la "bestia", Fase 5). CORRECCIÓN: la inducción object directa sobre `L` NO sirve (el código absorbe `#0` como numerales). **Próximo**: **reflexión de igualdad con `substfc`** (`substFormula_arith`/`prf_substTerm_arith` en SubstArith/ArithPrf) → `hI`/`hC` → `d3_prf` → punto fijo/necesitación en `Prf` → `goedel_second_prf`. — (hito previo) **D3 finitaria REDUCIDA: `d3_prf_of_sigma1` (Punto 6, paso 9)**. `Meta/ReflectionPrf.lean` (NUEVO), porte de `Reflection.lean` ω → `Prf`: combinadores `PrfH_pcc_mp`/`pcc_prf`/`pcc_andIntro`/`pcc_exIntro` (vía `d2_prf`+`repr_pos'_prf`) + **`d3_prf_of_sigma1 (φ) (hC) (hI) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))`** que reduce D3 a la **Σ₁-completitud provable del verificador** (hipótesis `hC`/`hI`), aislando el núcleo duro. `#print axioms` = `[propext, choice, Quot.sound, prf_inAxC]`. `Meta/ReflectionPrf.lean` (NUEVO), porte de `Reflection.lean` ω → `Prf`: combinadores `PrfH_pcc_mp`/`pcc_prf`/`pcc_andIntro`/`pcc_exIntro` (vía `d2_prf`+`repr_pos'_prf`) + **`d3_prf_of_sigma1 (φ) (hC) (hI) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))`** que reduce D3 a la **Σ₁-completitud provable del verificador** (hipótesis `hC : ∀p, Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))`, `hI : ∀x L, Prf (In x L ⇒ provCodeC'(In x L))`), aislando el núcleo duro. `#print axioms` = `[propext, choice, Quot.sound, prf_inAxC]`, sin postulados gödelianos. (Fix: `lean-toolchain` de la copia de trabajo estaba a v4.31.0 — rompía `simpa` de `Representability` al recompilar; restaurado al commiteado v4.29.1.) **Próximo (núcleo duro de D3)**: **`hI`** (el más tratable: inducción de listas sobre `L` — `nil` por explosión, `cons` por or-elim + `repr_pos'_prf` de `in_cons_head`/`in_cons_tail`) → **`hC`** (más difícil: `chainOk` = `lineOk`/`allIn`/`runFn`, construir código de prueba objeto por inducción sobre el testigo) → **`d3_prf := d3_prf_of_sigma1 φ hC hI`** → punto fijo + necesitación en `Prf` → **`goedel_second_prf : ConsistentH → ¬ Prf Con'`**. — (hito previo) **D2 FINITARIA REAL: `d2_prf` (Punto 6, paso 9)**. `Meta/DerivCondPrf.lean` (NUEVO): **`d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))`** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, sin postulados de derivabilidad). Tres piezas: **capa de clausura** (`liftTerm_numeral`/`charsCode`/`strCode`/`termCode`/`formCode` + `liftFormula_provCodeC'`: los códigos son cerrados — prerequisito porque `prf_ex_elim_imp` no da acceso meta al testigo); **`∃` en `PrfH`** (`PrfH_ex_intro`/`PrfH_ex_elim` vía `q2`/`q3` en `HilbertDeduction`, para testigos anidados `p=#1`,`q=#0`); **ensamblaje** `r=p++q++[mp]` con los lemas de cadena del paso 8. Helpers nuevos en `ChainPrf`: `prf_In_mono_right_imp`, `PrfH_allIn_subst2`, `PrfH_in_cons_head`. `Meta/DerivCondPrf.lean` (NUEVO): **`d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))`** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, sin postulados de derivabilidad). Tres piezas: **capa de clausura** (`liftTerm_numeral`/`charsCode`/`strCode`/`termCode`/`formCode` + `liftFormula_provCodeC'`: los códigos son cerrados — prerequisito porque `prf_ex_elim_imp` no da acceso meta al testigo); **`∃` en `PrfH`** (`PrfH_ex_intro`/`PrfH_ex_elim` vía `q2`/`q3` en `HilbertDeduction`, para testigos anidados `p=#1`,`q=#0`); **ensamblaje** `r=p++q++[mp]` con los lemas de cadena del paso 8. Helpers nuevos en `ChainPrf`: `prf_In_mono_right_imp`, `PrfH_allIn_subst2`, `PrfH_in_cons_head`. **Próximo (resto Punto 6)**: **`d3_prf`** (Σ₁-completitud provable — el más difícil; espejo de la D3 ω si existe, o `Reflection.lean`) → punto fijo + necesitación en `Prf` → **`goedel_second_prf : ConsistentH → ¬ Prf Con'`**. Limpieza opcional: retirar la vía legacy postulada (`Incompleteness.D2/D3`, `diagonal_lemma`, `GodelTwo.d3`). — (hito previo) **PASO 8 COMPLETO: los 10 lemas de cadena en `Prf`** (`runFn_concat`/`chainOk_concat`/`chainOk_mono`/`runFn_weaken`/`In_mono`/`In_mono_right`/`concat_assoc`/`allIn_mono`/`lineOk_mono`/`concat_nil_right`), frontera `∀c` resuelta de raíz vía `norm32`/`norm_s`/confinación-`qconf`. — (hito previo) **Lemas de cadena en `Prf`: eliminador + `prf_concat_nil_right` (paso 8, patrón validado)**. `Meta/ChainPrf.lean`: `prf_list_induction` + helpers `PrfH` (`PrfH_leibniz_subst`/`PrfH_eq_trans`/`PrfH_congr_cons_tail`) + primer lema de cadena `prf_concat_nil_right` (valida `base`+`step` vía `prf_deduction`; `#print axioms` = estándar). — (hito previo) **regla `listInd` integrada (paso 7 parte 2 COMPLETO)**. Vertical slice completo (`Prf.listInd`/`Rule.listInd` + doble aritmetización + `prf_listInd_concl_code` + cascada `vpf_run`/`chainOk_track`/`prf_chainOk_track` + `HilbertDeduction`); `repr_pos'_prf` honesto (`[propext, choice, Quot.sound, prf_inAxC]`). `Prf` tiene ahora inducción de listas. **Próximo (paso 8)**: port de lemas de cadena a `Prf` (`runFn_concat`, `chainOk_concat`, `In_mono`, `In_mono_right`, `concat_nil_right`, `runFn_weaken`, `chainOk_mono`) instanciando `listInductionFormula` con cada propiedad + `prf_deduction` para el paso → luego `d2_prf`/`d3_prf`/`goedel_second_prf : ConsistentH → ¬ Prf Con'`. — (hito previo) **`listInd_concl_code` (paso 7 parte 2, núcleo)**. `Meta/ListInductionArith.lean`: reconstrucción del código de `listInductionFormula A` desde ⌜A⌝ + `congr_liftfc_arg2` (más complejo que `ind`: `cons #1 #0` con variables libres). **Próximo (resto paso 7 parte 2)**: slice verificador `Prf.listInd`/`Rule.listInd` (stepConcl/ruleCode tag 20/prf_to_derivation + doble aritmetización legacy+runFn + versión Prf `prf_listInd_concl_code` + cascada lineJustif/lineCode/vpf_run/chainOk_track/prf_chainOk_track) → port lemas de cadena a Prf → `d2_prf`/`d3_prf`/`goedel_second_prf`. — (hito previo) **`list_induction_derives` (paso 7 parte 1)**. `listInductionFormula Φ` + `list_induction_derives : axioms ⊢ listInductionFormula Φ` en `Hilbert.lean` (vía `ax_list_induction`+ω-gen; antecedente del paso `subst_lift_same`, consecuente Barendregt `subst_subst_comm_succ`+`subst_subst_lift_gen`; `C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`). **Próximo (paso 7 parte 2)**: slice `Prf.listInd`/`Rule.listInd` (verificador: stepConcl/ruleCode/prf_to_derivation + doble aritmetización legacy+runFn + `listInd_concl_code` con `termCode (cons #1 #0)` — variables libres, más complejo que `ind`) → port lemas de cadena a Prf → `d2_prf`/`d3_prf`/`goedel_second_prf`. — (hito previo) **lema de Barendregt → paso 7a COMPLETO**. `subst_subst_comm_succ` (+ versiones término) en `FOL/Theorems/Eq.lean`; con `subst_subst_lift_gen`+`subst_lift_same` se verifica end-to-end la identidad del consecuente de la inducción de listas objeto (`C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`, antecedente `liftFormula 1 Φ`). **Próximo (paso 7)**: definir `listInductionFormula Φ` + probar `list_induction_derives : axioms ⊢ listInductionFormula Φ` (vía `ax_list_induction`+ω-gen+identidad consecuente) → slice `Prf.listInd`/`Rule.listInd` (tipo `qconf`) → port de lemas de cadena (`runFn_concat`/`chainOk_concat`/`In_mono`…) → `d2_prf`/`d3_prf`/`goedel_second_prf`. **Próximo (paso 7a→7)**: una composición subst–subst a nivel fórmula → formular `listInductionFormula Φ` + `list_induction_derives` (vía `ax_list_induction`+ω-gen) → slice `Prf.listInd`/`Rule.listInd` → port de lemas de cadena → `d2_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **SOLIDEZ: eliminado un `axiom` FALSO de FOL (`subst_lift_cancel_formula`)**. El axioma De Bruijn general era falso (verificado) y todo el Nivel D lo citaba; ahora es teorema en su forma restringida verdadera `substFormula v (#v) (liftFormula (v+1) f) = f` (demostrado por inducción + helper de término mutuo). `confinement_derives` queda en `[propext, Classical.choice, Quot.sound]`. **Próximo (paso 7, retomado)**: formular `listInductionFormula` (esquema objeto de inducción de listas) con el `subst_lift_cancel_formula` ya fiable → `Prf.listInd`/`Rule.listInd` (slice tipo `qconf`) → port de lemas de cadena → `d2_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **teorema de deducción finitario para `Prf`** (`Meta/HilbertDeduction.lean`). Nuevo `Meta/HilbertDeduction.lean`: cálculo con contexto `PrfH` (espejo finitario de `Prf`, `gen` de contexto-lift + `hyp`) + teorema de deducción (caso `gen` cerrado vía `qconf`) + `PrfH []↔Prf`. Exporta `prf_deduction : PrfH [A] B → Prf (A ⇒ B)` y `prf_ex_elim_imp : PrfH [A] (↑C) → Prf (∃A ⇒ C)` (eliminación del ∃ = `provCodeC'_elim` finitario). `#print axioms` = estándar. **Próximo (paso 7)**: regla/esquema de **inducción de listas en `Prf`** (slice análogo a `qconf`) → port de lemas de cadena (`runFn_concat`/`chainOk_concat`/`In_mono`...) → `d2_prf` → `d3_prf` → `goedel_second_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **regla `qconf` (confinamiento ∀) integrada en el verificador**. Slice completo (tipo `ind`, sin postulados): `Prf.qconf`/`Rule.qconf` + ambas aritmetizaciones (legacy `validProofFn` y `runFn`) + casos en `vpf_run`/`chainOk_track`/`prf_chainOk_track`. `prf_iff_derivation` sigue total; `repr_pos'_prf` honesto (`[propext, choice, Quot.sound, prf_inAxC]`); `provCodeC'` rastrea `IΣ₁ + confinamiento ∀`. **Próximo (paso 6)**: teorema de deducción finitario para `Prf` (caso `gen` vía `qconf`) → regla de inducción de listas en `Prf` (slice análogo) → port de lemas de cadena (`runFn_concat`...) → `d2_prf` → `d3_prf` → `goedel_second_prf : ConsistentH → ¬ Prf Con'`. Build verde (**59 jobs**), 0 sorrys. — (hito previo) **confinamiento ∀ (`confinement_derives`)**. Arrancando `d2_prf` se topó el **muro del confinamiento ∀**: el teorema de deducción de `Prf` (Hilbert finitario) lo necesita en su caso `gen`, pero `Prf₀`/`Prf` están **congelados** por la completitud del verificador (`prf_iff_derivation`, base de `repr_pos'_prf`) — no se le puede añadir confinamiento como axioma sin romperla, y derivarlo por dualidad clásica es circular. Solución de libro (sin postulados): **`confinement_derives : axioms ⊢ ((∀(↑P ⇒ C)) ⇒ (P ⇒ ∀C))`** probado directamente en `Derives` (deducción natural), que justificará el esquema `Prf.qconf`/regla del verificador. Plan multi-fase: regla `qconf` (slice tipo `ind`: verificador + aritmetización) → regla de inducción de listas → teorema de deducción finitario → port de lemas de cadena (`runFn_concat`/`chainOk_concat`/`In_mono`...) → `d2_prf` → `d3_prf` → **`goedel_second_prf : ConsistentH → ¬ Prf Con'`**. Build verde (**59 jobs**), 0 sorrys. — (hito previo) **`repr_pos'_prf` COMPLETO (D1 re-nivelada a `Prf`)**. Toda la representabilidad positiva sube al cálculo finitario `Prf` (necesario para Gödel II real: `provCodeC'` rastrea `Prf`, `¬⊢Con'` es falso): **`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`** (`#print axioms` = estándar + único meta-axioma `prf_inAxC`, espejo del `repr_pos'` ⊢-level). Dos módulos nuevos: `Meta/ArithPrf.lean` (porte finitario de toda la aritmetización, ~50 lemas; hallazgo: `numeral_lt` es finitario —∃-intro vía `q2`— por lo que toda la aritmética de códigos sube a Prf) y `Meta/Representability2Prf.lean` (tracking `prf_runFn_track`/`prf_chainOk_track` 19 casos + `provCodeC'_intro_prf` + ensamblaje). En `Meta/ReprPrf.lean`: 32 esquemas `lineWF`/`premsOf` portados. **Próximo (cadena Gödel II en Prf)**: `d2_prf` (añadir regla de inducción de listas en `Prf`, como se hizo con `ind`) → punto fijo + necesitación en Prf → `goedel_second_prf` (`ConsistentH → ¬ Prf Con'`) → **D3 real**. Ver [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

**(2026-06-19, 35 módulos, 49 jobs)** — **GÖDEL NIVEL D REAL — PRIMER TEOREMA DE GÖDEL REAL SIN POSTULADOS**. Cadena completa sobre el cálculo de Hilbert finitario `Prf`: verificador `validProofFn` sólido (18 reglas, `thy` vía `coreAxioms`) → `repr_pos`/**D1** (`Necessitation`) → **lema diagonal real** (`Diagonal`: `tc_arith` código-del-código → `diag_arith` → `godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`) → **`goedel_first_real : ConsistentOmega → ¬ Prf G`**. Además aritmética negativa de códigos `formCode_ne` (`CodeDistinct`). `#print axioms` de los resultados = solo ω-reglas ambiente; ningún `diagonal_lemma`/`provFormula`/D2/D3.

**(2026-06-12)** — **TFA COMPLETO CERRADO** (existencia object ∧ unicidad ℕ, sobre numerales, autocontenido sin Mathlib/Peano): `tfa_numeral` (`Full/Factorization.lean`). Unicidad ℕ vía Euclides (`Full/PrimeFactor.lean`: `euclid`, `factorization_perm_unique`). Capa de teoría de números completa sobre la representabilidad: `Primality` (`isPrime_numeral`), `Division` (`division_numeral`), `PrimeFactor` (ℕ pura: factor primo, factorización, **Euclides + unicidad**), `Factorization` (`tfa_exists_numeral`, `tfa_numeral`). Cimientos: `Numerals` (homomorfismo `+,·,^,<,≠`), `Bounded` (`le_numeral_split`), `Divisibility` (`numeral_dvd`, `divisor_le`), F1 `StrongInduction`. Reencuadre **numerales + representabilidad** (Gödel-aware) disuelve los Muros 1/2. Fragmento aritmético + listas de Minimal en Full: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅. Sistema con **34 axiomas matemáticos** en Minimal + meta-axiomas, **24 módulos** (Minimal/ 11 + Meta×2 + Full ×11), 0 sorrys, 0 warnings (37 jobs). **Próximo**: Gödel Nivel D (Meta/Incompleteness) sobre esta base; o consolidar.

---

## Situación actual

Build: ✅ `lake build` exit 0. **0 sorrys reales** y **0 warnings RPP** en los 11 módulos. Los 5 `axiom` de `Axioms.lean` (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) son meta-reglas de FOL; `ax_p_tfa` en `Block8.lean` es un meta-axioma adicional (TFA). Ninguno es `:= sorry`.

El sistema `Minimal/` cumple su objetivo declarado en [PLANNING.md](PLANNING.md): **34 axiomas matemáticos sin esquema de inducción son suficientes para construir la función de Cantor, las tuplas con proyecciones, las listas con concatenación y pertenencia, las funciones discretas, los primos y la factorización prima** (TFA vía Ax-P).

---

## Eje 1 — Consolidar `Minimal/` ✅ CERRADO (2026-06-06)

Todos los hitos completados:

- [x] **Bloque VII — Funciones discretas**: `Block7.lean` con `IsFunction`, `Functional`, F1/F2/F3 (2026-06-03).
- [x] **Bloque VIII — Primos**: `Block8.lean` con `Dvd`, `IsPrime`, lemas básicos (2026-06-03).
- [x] **Bloque VIII extendido — Factorización**: `pow`, `prod_pairs`, `IsFactorization`, `Ax-P` (TFA). Sistema 30 → **34 axiomas matemáticos** (2026-06-06). Auditoría profunda en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4-3.5.
- [x] **Limpieza warnings global**: 411 → 0 warnings RPP, linter `unusedSimpArgs true` global (2026-06-06).
- [x] **Diagnóstico frente Gödel (Nivel A)**: `Minimal/` satisface las hipótesis de Gödel I; relación con TFA y EFA/I∆₀+Exp analizada en [GODEL-STATUS.md](GODEL-STATUS.md) y [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §5.5.

**Estado de auditoría de axiomas no-induction-bound** (resuelto):

| Axioma | Estado | Comentario |
| --- | --- | --- |
| `ax21_mod2_range` | postulado | requiere inducción (irreducible — analizado en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.2) |
| `ax24_mod2_of_even` | postulado | requiere inducción sobre `k` (auditado 2026-06-03, irreducible) |
| `ax_C3_concat_assoc` | postulado | requiere inducción sobre `L` (irreducible) |
| `ax_L3_in_concat` | postulado | requiere inducción sobre `L` (irreducible) |
| `ax_pow_zero`, `ax_pow_succ` | postulados | definicionales puros (recursión primitiva base — [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4.1) |
| `ax_prodp_nil`, `ax_prodp_cons` | postulados | definicionales puros sobre listas (§3.4.2) |
| `ax_p_tfa` (TFA) | meta-axioma | requiere inducción fuerte; pasa a teorema en `Full/` |
| ~~`ax20`, `ax22`, `ax23`, `ax27`, `ax28`~~ | **ELIMINADOS** | derivables sin inducción o redundantes (ver CHANGELOG) |

**Pendientes menores** (no bloquean cierre):

- ✅ ~~Arreglar warning externo `FOL/Theorems/Eq.lean:130`~~ — **RESUELTO 2026-06-06** (eliminado el simp arg `hne` no usado en `substTerm_liftLift`; commit `9888c58` en el repo FOL). Build global con **0 warnings** (incl. FOL externo).
- ✅ ~~Más teoremas sobre `IsFactorization`/`Dvd` usando `ax_p_tfa`~~ — **HECHO 2026-06-06**: +10 teoremas en Block8 (álgebra de `Dvd`: `dvd_trans`, `dvd_mul_right/left`, `dvd_mul_of_dvd_left/right`, `dvd_add`; corolarios TFA: `factorization_exists/unique`, `lt_zero_one`, `factorization_one_eq_nil`). Lema de Euclides y multiplicatividad **fuera de scope** (requieren `prod_pairs_concat` → inducción).

---

## Eje 2 — Módulo `Meta/` (Niveles B y C ✅ 2026-06-06; próximo Nivel D)

**Objetivo**: implementar Fases 18-19 del spec (`TuplasFuncionesYListas.md §BLOQUE VIII`) — Gödelización y autorreferencia. Diagnóstico completo y arquitectura en [GODEL-STATUS.md](GODEL-STATUS.md).

**Decisión 2026-06-06**: `Meta/` arranca **al cerrar `Minimal/`**, no después de `Intermediate/`. Justificación: los niveles B-C (codificación + Dem) no requieren inducción, sólo meta-codificación. El nivel D (teoremas de incompletitud demostrados internamente) sí requiere `Intermediate/` o `Full/`.

### 2.1. Nivel B — `Meta/Godel.lean` (primer hito) ✅ COMPLETADO 2026-06-06

- [x] **Asignación de Gödel** `G : símbolos → ℕ` (Def 27 spec). `inductive Sym` (12 símbolos) + `gNat` (tabla ∀→2, ∃→3, =→10, …, m→111) + `gNat_injective`; `numeral`+`numeral_injective`; `G := numeral ∘ gNat` + `G_injective`.
- [x] **Corner brackets** `⌜·⌝ : List Sym → Term` (Def 28): `encode [] = nil`, `encode (s::S) = cons (G s) (encode S)`; notación scoped `⌜·⌝`.
- [x] **Teorema G1** (inyectividad): `encode_injective` (meta-inyectividad consistency-free, vía `injection` + inducción estructural) + versiones object-level `encode_cons_inj` (usa `cons_inj`, Block6) y `encode_cons_neq_nil`. Ver `GODEL-STATUS.md` §2 sobre la elección meta vs objeto.

**No introduce nuevos axiomas matemáticos** sobre `Minimal/`. Aprovecha `pow` + TFA para codificación primorial alternativa (ver [GODEL-STATUS.md](GODEL-STATUS.md) §3.1).

### 2.2. Nivel C — `Meta/Provability.lean` (segundo hito) ✅ COMPLETADO 2026-06-06

- [x] **Codificación estructural** de Gödel: `formCode : Formula → Term` (+ `termCode`/`termsCode`/`strCode`/`charsCode`), con **inyectividad demostrada** (`formCode_injective`, `termCode_injective`, … vía `injection`, consistency-free).
- [x] Predicado `IsFormula(x)` (Def 29): `∃ φ, x = formCode φ`. + `Provable x` y el teorema real `provable_formCode_iff` (`Provable ⌜φ⌝ ↔ axioms ⊢ φ`).
- [x] Predicado `Dem(d, x)` (Def 30) — **meta-axioma** (codifica árboles de derivación, requiere Nivel D). + **Teo Meta** `dem_iff_provable` (`axioms ⊢ φ ↔ ∃ d, Dem d ⌜φ⌝`), meta-axioma.
- [x] **Lema del punto fijo** (`diagonal_lemma`): `∀ φ, ∃ ψ, ⊢ ψ ⇔ φ[⌜ψ⌝]` — meta-axioma.
- [x] **Sentencia de Gödel** `goedelSentence` := punto fijo de `¬provFormula`; `goedelSentence_fixedpoint` (`⊢ G_Min ⇔ ¬Prov(⌜G_Min⌝)`) demostrado a partir de `diagonal_lemma`. `provFormula`/`provFormula_repr` postulados.

**Meta-axiomas nuevos (5)**: `Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma`. Justificados: la aritmetización de demostraciones y la diagonalización requieren inducción → pasarán a teoremas en el **Nivel D** (`Intermediate/`/`Full/`). Lo demostrado sin postular: toda la codificación + inyectividad + `provable_formCode_iff`.

### 2.3. Nivel D — `Meta/Incompleteness.lean` (requiere `Intermediate/` o `Full/`)

- [ ] **Gödel I**: `Minimal ⊬ G_Min` y `Minimal ⊬ ¬G_Min` (asumiendo consistencia).
- [ ] **Gödel II**: `Minimal ⊬ Con(Minimal)`.

Esto se queda para más adelante; la formalización requiere inducción sobre la complejidad sintáctica de las demostraciones.

---

## ~~Eje 3 — Sistema `Intermediate/`~~ ❌ ELIMINADO (2026-06-11)

**Decisión 2026-06-11**: `Intermediate/` se elimina por **redundancia conceptual**. El sistema con esquema de inducción restringido a Φ finito **es el caso particular** de `Full/` (cualquier instancia inductiva concreta que necesitemos se obtiene postulando sólo la φ pertinente en `Full/`, sin necesidad de un sistema separado). El prototipo `Intermediate/Induction.lean` confirmó que la inducción general no añade fricción técnica sobre la restringida — por lo tanto no hay coste por colapsar los dos niveles.

Todo lo que iba a desarrollarse en `Intermediate/` (derivar ax6, ax7, ax10-12, ax18, ax19, ax21, ax24, ax_C3, ax_L3 como teoremas) **se desarrolla directamente en `Full/`**. Resultados actuales en Full: ax6, ax7, ax10, ax11, ax12, ax18, ax19, **ax21, ax24** ✅ (ver Eje 4).

`Intermediate/Induction.lean` y el directorio `Intermediate/` quedan **borrados** del repositorio.

---

## Eje 4 — Sistema `Full/` (EN CURSO — arranque object-level 2026-06-07)

> **✅ `Full/Induction.lean` + `Full/Mod2.lean` + `Full/Lists.lean` (2026-06-07 + 2026-06-11)** — Inducción general como **axioma object-level** (`ax_induction : ⊢ inductionFormula φ`), con codificación **lift-aware** de `φ(σn)`. Composición De Bruijn generalizada (`substFormula_succ_lift_gen` + `step_reduce`). **Derivados como teoremas en forma object-level pura**: ax6 (`add_comm_thm`), ax7 (`add_assoc_ax`), ax10/11/12 (mul algebraicos), ax18 (`lt_irrefl_thm`), ax19 (`lt_trichotomy_thm`), y — **2026-06-11 vía Opción C.2** con axioma extra `ax_mod2_alternation : ∀n, mod2(σn)+mod2(n)=1` — `mod2_range_thm : ⊢ ax21_mod2_range` y `mod2_of_even_thm : ⊢ ax24_mod2_of_even`, y — **2026-06-11 vía meta-axioma `ax_list_induction`** (inducción estructural sobre listas, estilo `imp_intro`/`gen` parametrizado por `φ : Term → Formula`) — `concat_assoc_thm : ⊢ ax_C3_concat_assoc` y `in_concat_thm : ⊢ ax_L3_in_concat`. Lemas auxiliares: `mod2_zero_aux`, `a_plus_one_eq_one`, `eq_congr_mod2`, `eq_congr_cons_right_full`, `eq_congr_concat_left/right`, `eq_subst_in`, `iff_intro` (helper local). **`Intermediate/` eliminado** (caso finito de Full). **Estado**: fragmento aritmético + listas de Minimal totalmente cubierto en Full salvo Ax-P (TFA) y los testigos `ax21`/`ax24`/`ax_C3`/`ax_L3` que ya son teoremas. Siguiente: **Ax-P (TFA, inducción fuerte)**, Gödel Nivel D.

**Objetivo (PLANNING §6.3)**: Axiomas de Peano puros + **esquema de inducción general** sobre todas las fórmulas del lenguaje. Todos los axiomas postulados en `Minimal/` (ax21, ax24, ax_C3, ax_L3) y el meta-axioma `ax_p_tfa` (TFA) se vuelven teoremas. Habilita el **Nivel D** del frente Gödel: Gödel I y II demostrados internamente.

### 4.1. Roadmap de Ax-P / TFA — reencuadre **numerales + representabilidad** (2026-06-11)

**Obstrucción foundational detectada** al intentar F2 meta-nivel: en FOL=, (Muro 1) los existenciales object no dan testigos meta — `ex_elim` sólo concluye `axioms ⊢ C`; y (Muro 2) las disyunciones object (tricotomía) no se eliminan a conclusión meta. Por eso `strong_induction_meta` con case-split **no funciona**, y derivar el `ax_p_tfa` *meta* de Block8 con testigos usables es **equivalente a la maquinaria de representabilidad de Gödel** (no hay atajo).

**Decisión (Opción A, Gödel-aware)**: como Gödel Nivel D necesita representabilidad de todos modos, se construye esa capa una vez y TFA cae como corolario. Se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con **cómputo meta en ℕ + transferencia** vía homomorfismo. Disuelve los dos muros (lo decisional/constructivo ocurre en ℕ). Reutiliza Peano como cómputo meta.

**Capa de representabilidad (cimientos) — HECHO 2026-06-11**:

- [x] **F1 — Inducción fuerte object** (`Full/StrongInduction.lean`): `strong_induction` derivada de `ax_induction` sin axioma nuevo + `substFormula_liftFormula` + `lt_succ_split`.
- [x] **Numerales** (`Full/Numerals.lean`): `numeral : ℕ → Term` + homomorfismo `numeral_add/mul/pow`, orden `numeral_lt`, separación `numeral_ne`. El puente meta↔object.
- [x] **Cuantificación acotada** (`Full/Bounded.lean`): `le_numeral_split` — `d ≤ numeral n` ⇒ casos finitos `d = numeral i`. Convierte ∀ acotado en análisis finito.
- [x] **Divisibilidad** (`Full/Divisibility.lean`): `numeral_dvd` (meta ∣ → object Dvd) + `divisor_le` (divisor de positivo es ≤).

**Capa de teoría de números — HECHO 2026-06-12**:

- [x] **Primalidad representada** (`Full/Primality.lean`): `isPrime_numeral` — `p` primo (meta, hipótesis `2≤p` + divisores triviales, sin Mathlib) ⇒ `IsPrime (numeral p)`. Vía `divisor_le` + `le_numeral_split` + split anidado sobre el cofactor.
- [x] **División con resto** (`Full/Division.lean`): `division_numeral` — `numeral n = numeral(n/d)·numeral d + numeral(n%d)`, `numeral(n%d) < numeral d`. Trivial vía homomorfismo (cómputo `n/d`, `n%d` en ℕ).
- [x] **Factor primo + factorización META** (`Full/PrimeFactor.lean`, ℕ pura sin Mathlib): `exists_prime_factor` (∀ n≥2, ∃ factor primo) + `primeFactorList` (∀ n≥1, ∃ lista plana de primos con producto n), por inducción fuerte (`Nat.strongRecOn`).
- [x] **TFA-existencia transferida** (`Full/Factorization.lean`): `toTerm` (encoding lista de pares `(numeral p, 1)`), `prod_pairs_toTerm` (`⊢ prod_pairs (toTerm ps) =eq numeral (natProd ps)`), y **`tfa_exists_numeral`** — `∀ n≥1, ∃ ps, (∀p∈ps, IsPrimeNat p) ∧ ⊢ prod_pairs (toTerm ps) =eq numeral n`. Autocontenido (sin Peano).

**UNICIDAD + TFA completo — HECHO 2026-06-12**:

- [x] **Unicidad ℕ** (`Full/PrimeFactor.lean`): `euclid` (lema de Euclides vía `Nat.Coprime.dvd_of_dvd_mul_left` de core), `euclid_list`, `prime_dvd_prime_eq`, `natProd_erase`, `count_unique` (misma multiplicidad de cada primo) y **`factorization_perm_unique`** (dos factorizaciones del mismo `n` son permutaciones). Todo ℕ puro, sin Mathlib.
- [x] **TFA completo** (`Full/Factorization.lean`): **`tfa_numeral`** — `∀ n≥1, ∃ ps, (∀p∈ps, IsPrimeNat p) ∧ (⊢ prod_pairs (toTerm ps) =eq numeral n) ∧ (∀ qs factorización de n → ps.Perm qs)`. Existencia object + unicidad ℕ. La unicidad usa hipótesis meta `natProd qs = n` (evita reflejar igualdad de numerales, que necesitaría `Con(axioms)`).

> **`ax_p_tfa` de Block8** (membership object + testigo único object) queda como la forma **idealizada**: no admite discharge constructivo por el Muro 1 (object→meta). `tfa_numeral` es la realización constructiva equivalente para todos los usos reales (numerales/códigos).

### 4.2. Restantes tras TFA

- [x] **Nivel D Gödel — Gödel I (mitad esencial)** (`Meta/Incompleteness.lean`, 2026-06-12): `goedel_first_unprovable` (`Consistent → ⊬ G`), `goedel_first_true`, `incompleteness`. Derivado de D1 + diagonalización del Nivel C.
- [x] **Gödel II** (`goedel_second`, 2026-06-12): `Consistent → ⊬ Con` (`Con := ¬Prov(⌜⊥⌝)`). **Postulando D2/D3**; lema crucial `con_imp_goedelSentence : ⊢ Con⇒G`.
- [ ] ⚠️ **Gödel I completo — REVERTIDO por la auditoría 2026-07-13.** Se marcó ✅ el 2026-06-13
      (`goedel_first_unrefutable`, `goedel_first_undecidable`: `⊬¬G`, luego `⊬G ∧ ⊬¬G`, G indecidible),
      **pero en la capa LEGACY**, apoyándose en el postulado **falso en general** `provFormula_repr`
      (su dirección `.mp` es la representabilidad **negativa**, que NO se sigue de la consistencia
      simple — y el teorema se enunciaba bajo `Consistent`). **F7a lo retiró, y con razón: era un
      arreglo de solidez.** Hoy la cadena real da **sólo `⊬G`**.
      **Sigue vigente el diagnóstico**: el obstáculo es el **intuicionismo** del FOL, no la
      ω‑consistencia; Rosser habría sido peor. **Pendiente:** construir `repr_neg` (tarea ① del bloque
      «LO QUE QUEDA») y re‑derivarlo con la hipótesis honesta.
- [ ] **Cadena de embeddings**: `FOL⁼ ⊂ Minimal ⊂ Full`.
- [x] **[Deuda menor]** Refactor meta-axiomas FOL → ✅ HECHO 2026-06-12 (`FOL/MetaRules.lean`).

---

## Eje 4.3 — Gödel Nivel D REAL: aritmetización de D1–D3 (EN CURSO, 2026-06-13)

**Motivación**: D1/D2/D3 estaban **postulados** (meta-axiomas opacos). El `provFormula_repr` bicondicional era además imposible por Tarski (rastrea verdad en ℕ). Decisión (Opción A): **aritmetización total** — `demFormula` será una `Formula` Σ₁ concreta con `Dem d x → ⊢ᴴ demFormula[⌜d⌝,⌜x⌝]` demostrada. Plan completo y descomposición en [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

**Reencuadre clave**: el `axioms ⊢` del proyecto usa la **ω-regla** `gen` (premisas infinitas) → no es r.e. → no aritmetizable. Por eso Gödel se aplica a un **cálculo de Hilbert finitario `⊢ᴴ` nuevo, en paralelo**; el ω-sistema queda intacto.

- [x] **Fase 0** (`Meta/Hilbert.lean`): `Prf₀` (Hilbert intuicionista) + `Prf` (clásico). Puentes `prf0_to_derives`/`prf_to_derives : Prf φ → axioms ⊢ φ` usando **solo constructores de `Derives`**; `dne` aparece en **un único punto** (esquema P3), verificado por `#print axioms` (diferencia exacta entre ambos puentes = `{dne}`). `consistentH_of_omega`: la consistencia se hereda.
- [x] **Fase 1** (`Meta/HilbertSeq.lean`): `Rule` (líneas anotadas, evita invertir la sustitución) + verificador decidible `checkProof` + `Derivation`. **Solidez** `derivation_to_prf` + **completitud** `prf_to_derivation` (con `checkAux_append`/`checkAux_shift` para combinar subpruebas) ⟹ `prf_iff_derivation : Prf φ ↔ ∃ rs, Derivation rs φ`. Coding `ruleCode`/`rulesCode` → `Term`, `Dem` **concreto**, `dem_tracks : (∃d, Dem d ⌜φ⌝) ↔ Prf φ` (reemplaza `Dem`/`dem_iff_provable` postulados; solo axiomas estándar de Lean).
- [x] **Fase 2.1** (`Meta/CodeArith.lean`): `numeral_bridge` (Meta.Godel.numeral = Full.numeral) + `gnum_ne`/`gnum_lt`/`gnum_add`/`gnum_mul`/`gnum_refl` (aritmética de códigos re-expuesta de `Full.Numerals`).
- [x] **Fase 2.2 nivel término** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): funciones object `varc`/`funcc`/`substtc`/`substtsc` y sus ecuaciones recursivas **integradas en `Minimal.axioms`** (re-derivadas como teoremas vía `ax`+`spec`; `forall_4` requirió el lema de triple lift `substTerm_liftLiftLift`). `substTerm_arith`/`substTerms_arith` (cómputo `⊢ substtc ⌜v⌝ ⌜s⌝ ⌜t⌝ = ⌜substTerm v s t⌝`) por inducción meta mutua. **`#print axioms substTerm_arith` = solo axiomas estándar de Lean** (0 postulados nuevos).
- [x] **Fase 2.2 nivel fórmula** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): `liftc`/`liftsc` (lift aritmetizado) + `substfc` con los 8 constructores de código de fórmula (`botc`..`exc`); 13 ecuaciones recursivas más en `Minimal.axioms` (re-derivadas como teoremas). `liftTerm_arith` + `substFormula_arith` (binders ∀/∃ con `succ`-nivel y `liftc zero`-substituyendo, vía congruencias de `cons` y `congr_substfc_arg2`). `#print axioms substFormula_arith` = solo Lean estándar.
- [x] **Fase 2.3** (`Meta/StepArith.lean`): reconocimiento de instancias de axioma — `q1/q2/leibniz_concl_code` (esquemas de sustitución vía `substFormula_arith`); los proposicionales son definicionales.
- [x] **Fase 2.4** (`Meta/CheckArith.lean` + `Minimal/Axioms`): `numeralM`, extractores `carc`/`cdrc`; **`validProofFn`** + `forall_5` + 17 ecuaciones del verificador (params directos; MP/Gen condicionados por `In`) + 17 step lemmas `vpf_*` + lema 4-lift `substTerm_liftLiftLiftLift`; **`provFormulaC`** (demostrabilidad Σ₁) + `provCodeC`. **Pendiente regla `thy`**: nudo de capas (`formCode`/Meta vs `Minimal.axioms`); plan `formCode` a nivel Minimal vía `numeralM`.
- [x] **Fase 2.4-thy + soundness de `thy`** (`Minimal/Axioms` + `Meta/CheckArith`): verificador completo (18 reglas). `thy` recorre `coreAxioms` y es condicional a `In c axiomsCodeT` (`provCodeC` fiel). `formCodeM` + clausura De Bruijn estructural (numerales gigantes de símbolos Unicode).
- [x] **Fase 2.5** (`Meta/Representability.lean`): representabilidad positiva `repr_pos : Prf φ → axioms ⊢ provCodeC φ` (encoder object a medida `proofCode`/`lineCode` + inducción de seguimiento `vpf_run`). `#print axioms` = estándar.
- [x] **Fase 3 (D1)** (`Meta/Necessitation.lean`): `d1`/`necessitation` (= `repr_pos`) + Gödel I modular `goedel_first_unprovable_real`.
- [x] **Lema diagonal real** (`Meta/Diagonal.lean`): `tcFn`/`tc_arith` + `diag_arith` + **`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`** + **`goedel_first_real : ConsistentOmega → ¬ Prf G`** (sin postulados gödelianos).
- [x] **Fase 2.6 cimiento** (`Meta/CodeDistinct.lean`): aritmética negativa de códigos `formCode_ne` + familia.
- [x] **Fase 5 — regla `ind` INTEGRADA** (`Meta/Induction.lean` + stack): `ind_concl_code` + `Prf.ind`/`Rule.ind`/**`ax_vpf_ind`** sólida + `vpf_ind` + caso ind de `vpf_run`. **Verificador: 19 reglas.** `provCodeC` rastrea **IΣ₁**. `repr_pos`/`vpf_ind` `#print axioms` = estándar; `goedel_first_real` cita además `Full.ax_induction` (honesto: Prf modela IΣ₁).
- **D2/D3 → Gödel II real — rediseño honesto del verificador (EN CURSO, 2026-06-21)**.
  Hallazgo: `validProofFn` (opaca/condicional) sirve para la dirección positiva pero
  **bloquea** la inducción sobre testigos de prueba arbitrarios que D2/D3 exigen. Nuevo
  verificador estructural `runFn` (líneas `cons ⌜concl⌝ justif`, reduce vía `carc`).
  - [x] **R1** (`Meta/ProofChain.lean`): `runFn` + ecuaciones + **compositividad**
    `runFn c (p++s) =eq runFn (runFn c p) s` (inducción con acumulador ∀-object).
  - [x] **R2**: predicados `allIn`/`lineWF`/`premsOf`/`lineOk`/`chainOk` + ecuaciones +
    **monotonía** `In_mono`/`allIn_mono`/`lineOk_mono` (para línea arbitraria).
  - [x] **R3**: `concat_nil_right`, `In_mono_right`, **debilitamiento** `runFn c p =eq c++runFn nil p`,
    **composición** `chainOk c (p++s) ⇔ chainOk c p ∧ chainOk (runFn c p) s`, `chainOk_mono`.
  - [x] **R4 — D1 = `repr_pos'`** (`Meta/Representability2.lean`): `Prf φ → ⊢ provCodeC' φ`.
    Encoder `proofCode'` + `runFn_track` (rule-agnóstico) + `chainOk_track` (19-casos) +
    validez de las 19 reglas (`lineWF`/`premsOf`, fieles). `#print axioms` = solo estándar.
  - [x] **R5 — D2** (`Meta/DerivCond.lean`): `⊢ provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B)`
    (`r = p++q++[mp]`, vía `chainOk_concat`/`chainOk_mono`/`runFn_concat`/`runFn_weaken`).
  - [x] **Gödel II — núcleo lógico** (`Meta/GodelTwo.lean`): `con_imp_godel'`/`goedel_second'`
    vía **D2 real** + **D3 postulado** (`axiom d3`) + hipótesis explícitas honestas
    (`fp_bwd` punto fijo, `nec1` necesitación, `hgi` ⊬G ω). Mejora sobre legacy (postulaba D2 y D3).
  - **Camino a Gödel II 100% real** (descubierto al analizar D3):
    - [x] **Refactor `Prf.thy → axioms`** ✅ (2026-06-21): `Prf₀.thy` recorre todo `axioms`
      (core++coding); la teoría razona sobre su propia maquinaria (como IΣ₁). Ancla gigante
      `ax_axiomsCodeT` ELIMINADA, `axiomsCodeT` opaco, nuevo meta-axioma
      `ax_inAxC (a ∈ axioms) : ⊢ In (formCodeM a) axiomsCodeT` (sin término gigante ni
      auto-referencia; sonda validó el lift en un paso). Fixes thy en
      `Hilbert`/`HilbertSeq`/`Representability`/`Representability2`. Build 55 jobs.
    - [x] **Punto fijo real para `provCodeC'`** ✅ (`Meta/DiagonalTwo.lean`): `godelC'`/`godelC'_fixedpoint`
      (`⊢ G' ⇔ ¬provCodeC' G'`, sin postulados) + `goedel_first_real'` (Gödel I real estructural).
    - **HALLAZGO de niveles (2026-06-22)**: Gödel II requiere RE-NIVELAR la cadena HBL a `Prf`
      (no ⊢): `provCodeC'` rastrea la demostrabilidad finitaria `Prf`; `¬⊢G'`/`¬⊢Con'` son FALSOS
      (el ω-sistema es sólido y los prueba). Gödel II correcto = `ConsistentH → ¬ Prf Con'`, vía
      `con_imp` a nivel **Prf**, que necesita:
      - [ ] `repr_pos'_prf : Prf φ → Prf (provCodeC' φ)` (re-derivar `repr_pos'`/`chainOk_track` en `Prf`;
        el refactor `Prf.thy → axioms` lo habilitó).
      - [ ] `d2_prf`, punto fijo en `Prf` (`Prf (G' ⇔ ¬provCodeC' G')`).
      - [ ] `con_imp_prf : Prf (Con' ⇒ G')` → `goedel_second_prf : ConsistentH → ¬ Prf Con'` (D3 postulado a nivel Prf).
      - [ ] **D3 real** (Σ₁-completitud provable, núcleo).
    - [ ] **R6 — D3 real** (Σ₁-completitud provable): `⊢ ∀q. (R(q) ⇒ Prov(⌜R(q)⌝))` por inducción
      OBJECT sobre `q` (internaliza `repr_pos'`/`chainOk_track`) + ∃-intro interno + ex_elim.
      La pieza más grande del proyecto. (NOTA: `d3_of_sigma1` en `Reflection.lean` fue descomposición
      errónea —ex_elim sobre witness opaco—; superada por este plan.)
  - [ ] **R7**: replicar `con_imp_goedelSentence`/`goedel_second` con `provCodeC'`/`godelC` → **Gödel II real** (`⊬ Con`).
- [ ] **⊬¬G real** (reflexión / ω-soundness) + representabilidad **negativa** plena.

> **Integración ✅ (2026-06-13)**: las ecuaciones recursivas de las funciones de coding están ahora en `Minimal.axioms` (extensión definicional conservadora), por lo que `⊢ᴴ` también las tiene (vía `Prf.thy`). Ya no hay `axiom` local en `SubstArith`.

---

## Eje 5 — Más allá (muy largo plazo)

Sobre la base consolidada `Full/`:

1. **Teorías de conjuntos constructivas** (CZF de Aczel) usando listas y funciones como cimiento.
2. **Cardinalidad y números enteros/racionales**.
3. **Análisis constructivo elemental** (sucesiones, límites).

---

## Problemas técnicos recurrentes (referencia)

Heredados del trabajo en `Minimal/`. Útiles para `Intermediate/` y `Full/`.

| Problema | Síntoma | Solución |
| --- | --- | --- |
| `Block2.Γ` vs `Block4_C5.Γ` | `apply` falla con unificación | Usar `exact` (igualdad definitional) |
| `eq_trans` no-estándar | cadena `a=b, b=c` falla | Usar `FOL.derive_eq_trans` |
| `substTerm` bajo binder no reducido | `simp` deja `substTerm 0 t s` | añadir `FOL.substTerm_liftTerm`, `FOL.substTerm_liftLift` al simp set |
| `and_elim_*` ambiguo | error de elaboración | usar `Axioms.and_elim_left/right` |
| `Γ ⊢ t ≤ t'` parsing | `(Γ ⊢ t) ≤ t'` | paréntesis: `Γ ⊢ (t ≤ t')` |
| Implicación bajo `=eq` | `⇒` parsea más fuerte que `=eq` | paréntesis: `(A ⇒ (B =eq C))` |
| Triple `spec` (`forall_3`) | doble lift no se cancela | añadir `← lift_01_eq_00` o `FOL.substTerm_liftLift` |
| Caché de `lake build` | "Replayed" oculta cambios sin compilar | `lake clean && lake build` cuando hay dudas |

---

**Author**: Julián Calderón Almendros

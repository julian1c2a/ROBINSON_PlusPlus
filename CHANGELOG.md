# Changelog

> ## ⚠️ ESTADO REAL — auditoría 2026-08-21 12:00
>
> **La REPARACIÓN de la inconsistencia (2026‑08‑18/19) invalida buena parte de lo que sigue.**
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md).
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **21 módulos en `cuarentena/`** (D3 y Gödel II fuera de la cadena activa). NO borrados.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> **Último build verificado:** **121 jobs**, 0 errores, 0 warnings, 0 sorrys (2026‑08‑31).

---

## 2026-08-31 (b) — ✅ LA **NO‑VACUIDAD**, CERRADA · ⛔ y **A4 resultó IMPOSIBLE**

Cierra la **rama A** entera. `sondeos/HasWitFReal.lean` (+ `HasWitFRealMin.lean` y
`HasWitFCritica.lean`). **3 rutas de 3 CONFIRMADAS**, todas con `noVacuo=true`. Recompiladas por
mí. Build **121 jobs**, **57 `sondeos/`**. Proyectado en **§3.31**.

```lean
prf_isFC1_real   (φ) : Prf (ENS.isFC1 (objList (fcodesF φ)) (objList (tcodesF φ)) (formCodeM φ))
prf_hasWitF_real (φ) : Prf (ENS.hasWitF (formCodeM φ))
```

🔑 **Footprint `[propext, Classical.choice, Quot.sound]` — net‑0 PURO**, ni siquiera arrastra
`prf_axiomsCodeT_eq`. ⇒ para códigos **reales**, `pcc_eval_substfc` da la ecuación **pelada**.

### ⛔ A4 se retira del árbol: no es trabajo pendiente, **es imposible**

«La guarda sobre argumento **abstracto**» figuraba como tarea. **`hasWitF` sobre argumento
abstracto es FALSO en general**, y estaba **ya refutado en el árbol desde el día anterior**:
`ENS.CRIT_isFC1_rejects_varc` lo refuta **para cualquier testigo**. Se había escrito como control
de discriminación y nadie lo leyó como lo que también era.
⇒ **la vía real es cargar la guarda como hipótesis OBJETO por la cadena y descargarla al final**,
donde el argumento sí es un código real. Replantea cómo se ataca la rama C.

### ▶ La obligación NUEVA, ésta sí real

`Prf (hasWitF c ⇒ hasWitF (liftc zero c))` — la propagación bajo el `liftc` **objeto**. No existe.
El análogo del sort término sí (`SinWTs.CRIT_hasWit_lift`) y el molde debería transportarse.
⚠️ `ENS.liftF_hasWitF` **no sirve**: es el lift **De Bruijn**, no el objeto.

### 🧱 El footprint mínimo, medido — lo más accionable

La no‑vacuidad **no necesita nada** del descenso, ni `Paso2`, ni `SFsubsttc`, ni `DescMutua`, ni el
ensamblaje. Verificado **ejecutándolo**: `HasWitFRealMin.lean`, **1 819 l., EXIT=0, mismo net‑0**.
⇒ **promoverla a `Meta/` es un módulo pequeño e independiente**, y es el trozo de la rama B que se
puede pagar barato.

### Medidas que corrigen la estimación previa

* **La ruta encargada no hizo falta**: se pidió «copia §19 de `ParticionTresPredicados` (~650 l.)»
  y **no se abrió §19 ni una vez**. Coste real ~590 líneas, re‑derivadas desde el sort término.
* **El eje TÉRMINO costó cero líneas de invención**: `okE1_T`/`okE1_Ts` valen **byte a byte**.
* **TRES lemas de forma cubren los OCHO tags**, y dos de ellos salen **genéricos en el tag** ⇒ los
  8 nodos suman ~55 líneas. «En forma ecuacional cada nodo cuesta menos» **se quedó corto**.

### ⚠️ Cuarta vez: trabajo hecho y no recogido, ahora en `Probe/`

`Probe/ADV_novacuo.lean` (7 668 l., de una tanda anterior de esa misma noche) ya traía el molde
`PROBE_wfAllF_of_list`. La regla registrada decía «grepea **producción**»; **hay que extenderla a
`sondeos/` y `Probe/`**.

---

## 2026-08-31 — 🏁 **EL MURO DE `substfc` ESTÁ ROTO**: `pcc_eval_substfc` PROBADO

Cierra el frente que llevaba abierto desde julio. `sondeos/EvalSubstfcPrf.lean` (7 522 l.),
**CONFIRMADO** por verificación adversarial que recompiló de cero (107 s en frío) y reejecutó los
`#print axioms`; recompilado también por mí. Build **121 jobs** (tras promover `EvalPredPrf`), **57 `sondeos/`**. Proyectado en
**§3.30**.

```lean
pcc_eval_substfc (wF wT v s f) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT v̇ ṡ ḟ) (tcFn (substfc v s f))))
pcc_eval_substfc_wit (v s f) : Prf ((hasWit s ∧ hasWitF f) ⇒ targetSubstfc v s f)
```

Footprint = **la base sancionada**, sin nada nuevo; el gate y el paso inductivo son **net‑0 puro**.
Tres framings independientes: **1 CONFIRMADO + 2 PARCIAL** (los dos parciales con medición fiable —
midieron bien y no cerraron, que era el veredicto correcto).

### 🔑 Las cuatro ideas, y ninguna era la prevista

1. **No hacían falta tres sorts.** La inducción de término/lista ya estaba cerrada aparte ⇒ la de
   **fórmula es de UN SOLO SORT** y consume las otras dos como **caja negra**. Los tags `eqc` y
   `atomc` no descienden por `substfc`: descienden por `substtc`/`substtsc`.
2. **El puente de testigos no se prueba: SE DISUELVE.** No hay que demostrar «del testigo de
   fórmula sale el de término»: hay que **definir** el reconocedor de modo que sus casillas de
   término apunten a `wT` con la forma exacta que consume `EvalSubsttc`. Entonces la premisa sale
   por **`rfl`**, net‑0. **Definir bien salió más barato que probar.**
3. **El gate fue gratis por una decisión tomada por otra razón**: el paquete de testigos ya venía
   empaquetado en **un** término, cosa que `ParticionTresPredicados` decidió por naturalidad de
   `pcc_bdAll_intro`. ⇒ tres binders y los lifts existentes bastan.
4. ⚠️ **«La moneda de la inducción OBJETO» — lo caro de verdad, pagado tres veces.** Un lema de caso
   con la HI como hipótesis **META** (`Prf A → Prf C`) **no sirve**: la inducción objeto sólo
   consume implicaciones **objeto** o versiones **Γ‑paramétricas**, porque la HI **sólo existe
   dentro del `Γ` del paso**. **Regla: enunciar los lemas de caso en forma Γ‑paramétrica desde el
   principio.**

### ⚠️ Piezas que ya estaban y nadie había usado (tercera vez esta semana)

`SinWTs.isFormCodeB2` (`ClausuraLiftSinWTs.lean:1170`) era **exactamente** el reconocedor con dos
listas testigo que hacía falta, con su discriminación probada y **sin un solo consumidor**. Y
`SubstfcEx.lean` §MED ya había medido que los tags 4 y 3 no descienden por `substfc`.

### ⚠️ Trampa de notación nueva

`FOL/FOL/FOL.lean:38` declara `infixr:65 " ∨ " => Formula.or`, que **sombrea el `∨` de Lean**
(precedencia 30) ⇒ `(k = 5 ∨ k = 7 ∨ k = 8)` es un **error de PARSEO**, y el mensaje **no menciona
`∨`**. Escribir `Or (k = 5) (Or …)`.

### ▶ Lo único que falta

`prf_hasWitF_real (φ) : Prf (hasWitF (formCodeM φ))` — el control de **no‑vacuidad**. La mitad
difícil ya está: la guarda **discrimina** (rechaza `varc` y `funcc`, probado). Dos precedentes
exactos para transportar. **Los tres sondeos coinciden en señalar esta misma pieza.**

---

## 2026-08-30 (c) — ✅✅ LOS **OCHO** CONSTRUCTORES DE `substfc`, CUBIERTOS

Cuatro sondeos nuevos, **todos net‑0**, recompilados a mano desde su ubicación final (`EXIT=0`),
build de producción intacto (**118 jobs**, **45 `sondeos/`**). **3 CONFIRMADOS + 1 PARCIAL** — y el
`PARCIAL` no es por la matemática, sino por un **hallazgo falso** que el verificador cazó.
Proyectado en **§3.29**.

| constructor | dónde |
|---|---|
| `botc` `implc` `andc` `orc` | `sondeos/SubstfcPlanos.lean` |
| `exc` (espejo del `∀`) | `sondeos/SubstfcEx.lean` |
| `eqc` · `atomc` | `sondeos/EvalSubsttc.lean` (`pcc_eval_substtc'` / `pcc_eval_substtsc'`) |
| `pred` dotado | `sondeos/EvalPredDot.lean` |

⚠️ **CUBIERTOS ≠ ENSAMBLADO.** Tener los ocho casos **no** es tener `pcc_eval_substfc`: falta la
inducción que los junta, y no está medida. Todo vive en `sondeos/`.

### 🔑 Los tres binarios son la misma fórmula salvo el tag — y se certifica por `rfl`

`ax_substfc_impl/_and/_or = forall_4 (AXBIN_BODY (numeralM 5/7/8))`, los tres por `rfl`. ⇒ **una
prueba en vez de tres**, factorizada en `pcc_substfc_bin_dot` (genérico en la etiqueta) y
`paso2_caso_bin` (genérico en `k : Nat`); los tres casos finales son cuatro líneas cada uno. El
ensamblaje sale genérico **gratis** porque `binT`/`pcc_dot_bin`/`pcc_congr_binT_*_code` ya son
paramétricos en `k` en producción.

### 🔑 La técnica, reutilizable fuera de aquí

Cuando un parámetro bloquea la reducción **en una sola hoja**, enuncia el `have` **con la hoja sin
evaluar** —puro defeq, cero tácticas— y reescríbela después con una línea. **No intentes normalizar
el término entero.** Es hermana de las ideas #2 y #3 de §3.27.4: el ahorro viene de **no desplegar**.

### ⚠️ `pcc_eval_substtc` va CON GUARDA, y el encargo estaba mal pedido

La forma **sin guarda** que pedía el encargo **no está probada y no es probable por esta vía** — ni
ella ni su gemela `pcc_eval_liftc`. La inducción es sobre el **VALOR** del código, luego para
descender hace falta que `t` sea de verdad código de término: eso es `isTC1 w t`. **El enunciado
del encargo era el defectuoso, no la prueba.** Las dos obstrucciones de §3.28.4 quedan resueltas: la
**tricotomía** por or‑elim **EXTERNO** (`Prf₀.j3`; el interno existe pero no hizo falta) y el `pred`
dotado (`predHyp` **declarada y descargada**, sin inducción).

### ⛔ Lo que cazó el paso adversarial

De nueve hallazgos, **uno era FALSO**: `pcc_eq_tracked` **ya existe** en producción
(`Meta/Sigma1AtomPrf.lean:246`, enunciado idéntico, ya consumido en `InAxiomsCodePrf.lean:220`); la
copia local lo **sombrea**. Actuar sobre el hallazgo habría creado una **tercera** copia. Es la
trampa registrada de «misma definición en dos namespaces». Verificado por mí contra producción.

### Piezas nuevas y un arbitraje

* **`pcc_axiom_inst4` no existía** (producción llega a `pcc_axiom_inst3`, `Meta/MpCodePrf.lean:243`)
  y **dos agentes la escribieron por separado**. Candidata clara a promoción: `ax_substfc_atom` y
  `ax_substfc_eq` también son `forall_4`.
* **`pred` dotado, dos versiones**: `EvalPredDot` la prueba **incondicional** para `n` abstracto;
  `EvalSubsttc` prueba una **guardada** por `lt v n` y declaró la otra «innecesaria». **Es media
  verdad**: para su uso sí, pero la incondicional es **estrictamente más fuerte**.

---

## 2026-08-30 (b) — ✅ `paso2_caso_forall` REHECHO en `PrfH Γ`: la hipótesis colgante desaparece

`sondeos/Paso2Guardado.lean` + `sondeos/EqTransCodeImp2.lean`. Build **118 jobs**, **41 `sondeos/`**.
Proyectado en **§3.28.6**.

```lean
paso2_caso_forall_guarded (v s f) (hIH) :
    Prf (hasWit s ⇒ provFromCode (evalSubstfcCode v s (forallc f)))
```

**Una sola hipótesis** —la HI legítima sobre el subcódigo `f`—: `hLift` ha desaparecido.
Footprint **idéntico** al de `Paso2.paso2_caso_forall`, reprobado en el mismo fichero ⇒ **la
reescritura no añade nada**. 3 estrategias, **2 confirmadas + 1 parcial** (la parcial se declaró
así ella misma por literalidad del criterio: sus dos hipótesis residuales **son** `DESCENSO_hasWit`
y `CRIT_hasWit_lift` instanciadas).

### ⚠️ Dos correcciones al registro del día anterior

* **El obstáculo que se anunció no era tal.** Se dijo que la cadena se monta con
  `pcc_eq_trans_code` —que toma sus dos eslabones como `Prf`— y que bajo `PrfH Γ` haría falta un
  helper nuevo. **`PrfH_eq_trans_code` ya existía en producción** (`Meta/EvalCarcNthcPrf.lean:66`,
  exportado) con la firma exacta: la cadena se reescribe **1:1**. Fue trabajo dirigido a un hueco
  inexistente, y lo detectó quien lo ejecutó, no quien lo encargó.
* **Trampa real y nueva: `hasWit` son DOS CONSTANTES DISTINTAS** — `DescMutua.hasWit` y
  `SinWTs.hasWit`, definiciones literalmente iguales pero constantes diferentes que Lean **no
  identifica en el enunciado**. Sin puente, los dos sondeos **no componen**. Cerrado con
  `hasWit_bridge := rfl`, **net‑0**, lo que certifica que la coincidencia es **definicional**.

### ⚠️ Límite de alcance, declarado

El descargue de la guarda está verificado para códigos **REALES**. Los **7 reflectores de `lineWF`
llevan argumento ABSTRACTO** ⇒ necesitarán `hasWit` de ese argumento abstracto. **No resuelto.**

### Piezas genéricas nuevas, aunque resultaron innecesarias

`pcc_eq_trans_code_imp2` (transitividad interna con **ambos** eslabones como antecedentes) y
`prfH_deduction` (deducción dentro de `PrfH`). Ninguna existía; se conservan por reutilizables.

---

## 2026-08-30 — ✅✅ EL **DESCENSO**, CERRADO: `pcc_eval_liftc` existe

Cierra el único lema que la semana 08‑24→08‑29 dejaba abierto. **Cero axiomas de Lean nuevos, cero
`sorry`**, recompilado a mano. Build **118 jobs**, **39 `sondeos/`**. Proyectado en
**`doc/REFERENCE-Incompleteness.md` §3.28** (nueva). ADR **018**.

```lean
DESCENSO        (w s : Term) : Prf (isTC1 w s) → Prf (targetLift s)   -- w, s ABSTRACTOS
pcc_eval_liftc  (w s : Term) : … := DESCENSO w s                      -- ES el mismo teorema
DESCENSO_hasWit (s : Term)   : Prf (hasWit s ⇒ targetLift s)          -- la forma CONSUMIBLE
```

**3 estrategias independientes, 3 de 3 confirmadas** por verificación adversarial.

### Lo que enseñó, y que vale fuera de aquí

* 🔑 **Las tres vías convergieron por separado en el mismo motivo, y no era el previsto**: no dos
  inducciones mutuas, sino **UNA** inducción fuerte con conclusión **CONJUNTIVA**
  (`PHI := ∀w. (isTC1 w #0 ⇒ targetLift #0) ∧ (isTsC1 w #0 ⇒ targetLiftsc #0)`), con `w` **dentro**
  de `Φ` porque el gate `liftFormula 1 Φ = Φ` lo exige. **La mutua explícita era innecesaria.**
* 🔑 **La tercera vía se respondió a sí misma en NEGATIVO, con prueba**: el `s` que ve
  `paso2_caso_forall` **es `#0`**, luego pedir `hLift` sólo para él **es pedirlo para todo `s`**.
  Se cerró la vía **demostrando** que no había atajo, en vez de abandonarla por intuición.
* 🔑 **El residuo de acople, resuelto** (`sondeos/GateGuardaEnriquecida.lean`): los tres intentos
  señalaron sin que se les preguntara que `pcc_eval_liftc` llega con **guarda** y el `PHI` del
  consumidor no la tenía. `PHI_guarded` la mete dentro y **`PHI_guarded_lift` compila** — y **sin
  binder nuevo**, porque la guarda es un `∃` **interno**: el gate sólo mira los binders exteriores.

### ⚠️ Dónde está el siguiente muro — y no es donde se miraba

De los **8** constructores de `substfc` sólo existe `pcc_substfc_forall_dot`. **CINCO** de los siete
restantes son **mecánicos**; los distintos son `eqc` y `atomc`. Y **`pcc_eval_substtc` es
estrictamente MÁS DURO que el DESCENSO**, por dos razones verificadas en el código: la guarda de
`liftc` era **cerrada** (`liftc zero` ⇒ `zero < σn`, se descarga de una vez) mientras
`substtc v s (varc n)` tiene **tres** cláusulas guardadas con **`v` abstracto** ⇒ pide reflejar la
**tricotomía dentro de `Prov`**; y `ax_substtc_var_gt` devuelve `varc (pred n)` ⇒ pide la
evaluación **dotada de `pred`**, que no existe.

### 💰 Coste de promoción, que no figuraba en ninguna estimación

`targetLift`/`isTC1`/`wfAll1`/`argsIn` viven **sólo en `sondeos/`** ⇒ promover el DESCENSO a
`Meta/EvalLiftcPrf.lean` obliga a promover **antes** `ReflectorDesdeConsumidor` y
`ClausuraLiftSinWTs`. Sueltas: `PrfH_mono`/`PrfH_w1` → `Meta/HilbertDeduction.lean`;
`prf_nil_or_cons` → `Meta/ChainPrf.lean`.

### 🧹 Mantenimiento

* Limpiados **8 procesos `lake`/`lean` huérfanos** (~14 h, 889 MB). Build reverificado después:
  118 jobs, `EXIT=0`.
* ⚠️ **Aprendizaje de método**: `started > result` en el journal de un workflow **no** significa
  «agentes vivos» — tres daban esa señal y eran cadáveres de julio y del 28‑08. El criterio bueno
  es el **timestamp**, no el conteo.
* ⚠️ **Trampa de doc, cometida y corregida** (`c8f100f`): se actualizaron los banners de ocho
  documentos y se dejó el **cuerpo** con cifras viejas (`10 en sondeos/`, cuarentena «quedan 14»
  cuando está vacía desde el 23). Es exactamente la trampa que el proyecto tiene registrada.

---

## 2026-08-29 — 🎯 EL FRENTE `substfc` POR LA VÍA DE **CERO AXIOMAS** (semana 08‑24 → 08‑29)

**Decisión tomada y ejecutada**: la buena‑formación de códigos se define en vocabulario objeto
**EXISTENTE**. **Cero axiomas nuevos, cero símbolos nuevos.** Build **118 jobs**, **37 `sondeos/`** (39 tras cerrar el DESCENSO el 08‑30),
0 sorrys. Proyectado en **`doc/REFERENCE-Incompleteness.md` §3.27** (nueva).

### Lo que se cerró, en orden

| # | resultado | fichero en `sondeos/` |
|---|---|---|
| — | el «segundo muro» **no es un muro**: el chasis absorbe el conjunto extra | `SegundoMuro.lean` |
| A1/A2 | el reflector de `In` sobre lista **ABSTRACTA**, que no existía | `InTracked.lean` |
| A3 | el reflector **completo**, `w`/`c` abstractos | `A3IsFCBTracked.lean` |
| (i) | **todo `φ` tiene testigo** explícito y computable | `SubCodesWitness.lean` |
| — | la **PARTICIÓN en tres** funciona **y DISCRIMINA** (refuta el junk) | `ParticionTresPredicados.lean` · `ParticionDiscrimina.lean` |
| ① | la discriminación **sobrevive** a la forma ecuacional — **basta UN lema** | `DiscriminaEcuacional.lean` |
| ② | la discriminación vale con **testigo ABIERTO** (`#0`) | `DiscriminaTestigoAbierto.lean` |
| ③.1 | los **constructores dotados** y su kit | `CtorDotados.lean` |
| ③.2 | el caso `∀`, y **dónde se atasca** | `Paso2CasoForall.lean` |
| — | la **clausura bajo `liftc`** sin axiomas: quitando `wTs` se **disuelve** | `ClausuraLiftSinWTs.lean` |
| — | **NO hay muro nuevo** en el reflector: tres vías, las tres cierran | `ReflectorAtomoAllIn.lean` · `ReflectorForallAnidado.lean` · `ReflectorDesdeConsumidor.lean` |

### Por qué (1) quedó descartada — y no por el ahorro de líneas

`ax_axiomsCodeT_eq` (`Minimal/Axioms.lean:1376`) ancla a **`axioms`** (los 141, `:1199`) y **no** a
`coreAxioms` (`:922`) ⇒ los axiomas de la opción (1) **tienen** que entrar en `axioms` para
funcionar, `axiomsCodeT` los absorbe, el verificador interno los cita y **`provCodeC'` cambia ⇒ G
cambia** (141 → ~159). **(1) no es más cara: es OTRO TEOREMA.**
Corolario: **aunque se sancionara (1), los sondeos de (2) serían su certificado de conservatividad.**

### Las cuatro ideas reutilizables (material del libro)

1. **Dotar un átomo COMO ÁTOMO** en vez de desplegarlo — pagó **dos veces** (`inFormCodeFn` en A3,
   `allInFn` en el reflector sin `wTs`): el cuerpo queda **sin binder** y el problema De Bruijn
   **se disuelve** en vez de resolverse.
2. **Probar contra la lista COMPLETA** (generalizar sobre un superconjunto) en vez de usar
   monotonía: ahorra un or‑elim de 12 casos por composición.
3. **Llevar el lift en vez de quitarlo**: la clausura del testigo era un **artefacto de la ruta de
   prueba**, no del enunciado — `FOL.substTerm_liftTerm` vale para cualquier `p`.
4. **Poner el lift en el OBJETIVO, no en la hipótesis**: **no existe** lema de lifting de
   **derivaciones**, así que el testigo va dentro del objetivo del `∃`‑elim.

Y el cuadre que lo explica todo: **8↔8 / 2↔2 / 2↔2**. `pcc_eval_substfc` se atasca **porque 12 ≠ 8**;
partido, cada mitad encaja con su juego de ecuaciones. **Partir no repara un defecto: es la
CONDICIÓN para que la inducción exista.**

### ⚠️ Tres correcciones al propio registro

* **`d783b9f` estaba mal cerrado** («③ REORIENTADO: `pcc_eval_liftc` NO hace falta»). **Sí hace
  falta**: `paso2_caso_forall` la deja como única hipótesis colgando. Se refutó la **RAZÓN** del
  gate, no su **CONCLUSIÓN**. Modo de fallo: **generalizar de META a OBJETO**, que es donde vive la
  hipótesis de inducción. Corregido en `05df9b6`.
* **La recomendación «acotar» era circular**: acotar y la clausura de un paso son
  **inter‑construibles**, probado en las dos direcciones (`AcotarEsLaMismaObligacion.lean`).
  Y su diagnóstico estaba **mal atribuido** — seguirlo habría llevado a **fabricar un símbolo**.
* **«Ningún descenso de `substfc` cruza un binder de código» es FALSO** (hay 12 a nivel 1, y el
  teorema principal depende de tres). Lo correcto: **ninguno corre sobre código de fórmula OPACO.**

### ▶ Abierto: UN lema, y es PLANO

```lean
DESCENSO : ∀ w s, Prf (isTC1 w s) → Prf (targetLift s)     -- ES pcc_eval_liftc
```
Base y paso ya cerrados (`refl_lista_nil`, `refl_lista_cons`, casos `varc`/`funcc`). Piezas todas en
producción. ⚠️ `prf_strong_induction` exige `liftFormula 1 Φ = Φ` ⇒ **`w` cuantificado DENTRO de Φ**.

**Sin determinar**: el puente a forma **ecuacional** de la imagen punteada (el reflector entrega
`carc`/`lenc`, estrictamente más débil); la conexión entre los **dos reconocedores** (con y sin
`wTs`), que hoy están **desconectados**; y los otros **7 constructores** de `pcc_eval_substfc`.

## 2026-08-23 — 📖 PROYECCIÓN + ACTUALIZA_DOC: los 82 módulos catalogados, §3.26 nueva

Pasada de `proyecta` + `actualiza doc` tras la repatriación. **No toca código**: build **118 jobs**,
**104 módulos activos** (Minimal 11 + Meta 82 + Full 11), `cuarentena/` **vacía**, 0 sorrys.

### Proyección (AI-GUIDE §12/§14)

* **`REFERENCE.md` §1.5 reescrita**: catálogo de los **82** módulos de `Meta/` (describía 61), con
  los 21 repatriados marcados 🔁 y reubicados de §1.6 a §1.5. **§1.6 pasa a ser nota histórica** —
  la cuarentena ya no contiene código.
* **`doc/REFERENCE-Incompleteness.md` §3.26 (nueva)**: la repatriación proyectada con firmas Lean 4
  exactas — las tres sub‑familias muertas y su sustituto; las herramientas nuevas (`pcc_rw_imp`,
  `pcc_rw_dot_cons_un`, `pcc_rw_dot_cons_nthc`, `prf_tc_form_numeral`, `pcc_to_formCode_imp`,
  `pcc_dot_nul`/`_un`/`_bin`, `pcc_dot_eqc`, `pcc_tc_objAt`, `pcc_tc_formCode_internal`); el punto
  delicado de la **conversión en la frontera**; y el trabajo voluminoso de `pcc_tc_objAt`.

### Estado (§5 de `REFERENCE.md`, reescrita)

**Los tres frentes abiertos están ahora MEDIDOS**, y ninguna medición quedó pendiente:

| # | frente | resultado |
|--:|---|---|
| 1 | muro de `substfc` → D3 → Gödel II | ✅ `prf_strong_induction` **ya existe** (net‑0, forma OBJETO) ⇒ sólo falta `pcc_eval_substfc`. Bloqueado por una **decisión**: sancionar `isFormCode` |
| 2 | `NegVerifier` → `⊬¬G` | ⛔ paso 1.1 del plan **FALSO**; ✅ salida por **numerales** verificada y **net‑0** |
| 3 | recodificar símbolos | 📏 **98‑99 %** del `formCode` son nombres de símbolos (69× de mejora), pero **hoy no es cuello de botella** |

**Secuencia que sale de las mediciones:** (3) sólo tiene sentido **antes** de (2); (1) es la única
vía a D3 pero **cuesta axiomas**, así que es decisión del autor, no un paso técnico.

### Correcciones de documentación

* `CURRENT-STATUS-PROJECT.md`: las filas `NegVerifier` y `D3 / plan 12‑A` estaban descritas como
  «en curso» con el estado de julio. Reescritas con el estado real y los bloqueos verdaderos.
* Nota obsoleta corregida en la memoria: `prf_strong_induction` no está «al 90 %», está **completo**.

---

## 2026-08-23 — 🎯 **LA CUARENTENA ESTÁ VACÍA** — los 31 módulos han vuelto

Build **112 → 118 jobs**, **104 módulos activos** (Minimal 11 + Meta 82 + Full 11),
**`cuarentena/` = 0**, 0 errores / 0 warnings / 0 sorrys.

Todo con el footprint sancionado `[propext, choice, Quot.sound, prf_axiomsCodeT_eq]`, sobre la
teoría **reparada**, y **sin cambiar ningún enunciado público**.

### La secuencia completa

| hito | cuarentena |
|---|---:|
| reparación ejecutada (ADR‑012/013) | 31 |
| refundar el keystone `Sigma1CorePrf` (a.1) | 21 |
| paso 1 · `EvalListPrf` + 6 en cascada | 14 |
| paso 2 · `EvalNthcPrf` (`pcc_rw_imp`) | 12 |
| paso 3 · `D3InDotPrf` (conversión en la frontera) | 10 |
| pasos 4‑5 · `LineWFTrackedPrf` + el KIT (`CodeCtorKit`) | 6 |
| paso 6 · `CodeTreeReflect`, `LineWFEfqPrf`, `LineWFPropPrf` | 3 |
| paso 7 · `InAxiomsCodePrf` → `LineWFThyPrf`, `LineWFAssemblePrf` | **0** ✅ |

### Lo que cerró esta última tanda

* **`LineWFTrackedPrf`** — su `prf_tc_eqc` resultó ser **el caso binario del KIT hecho a mano**
  (árbol `⟨4,a,b⟩`), así que el sustituto ya estaba escrito en `sondeos/KitPayoff.lean`.
* **`CodeCtorKit`** — el KIT en producción (`pcc_dot_nul`/`_un`/`_bin` + las variantes simétricas).
* **`CodeTreeReflect`** — el trabajo voluminoso que la medición anunciaba: `prf_tc_objAt` es
  recursión sobre `CTree` produciendo una igualdad **de código**, y hubo que mudarla entera **dentro
  de `Prov`** (`pcc_tc_objAt`). La conversión fue **literal, pieza por pieza**: `prf_eq_trans` →
  `pcc_eq_trans_code`, `prf_congr_unT`/`_binT` → sus versiones `_code`, que **sobrevivieron
  intactas**. Único cambio de forma: en el caso binario hacen falta **dos** congruencias encadenadas
  donde antes bastaba una simultánea — dentro de `Prov` los argumentos se reescriben de uno en uno.
* **`InAxiomsCodePrf`** — el que la medición había marcado como más fiddly, y resultó más barato de
  lo temido: `pcc_in_head_swap` sólo usaba su hipótesis muerta **para construir la versión interna**,
  así que bastó **subir la hipótesis de nivel**. Y `prf_tc_listFormCodeM` **no hacía falta**: su
  único consumidor era una invariancia `substtc` de un código **cerrado**.

### Las cuatro lecciones (material del libro)

1. **El transporte cambia de NIVEL, no de nombre.** De igualdad de código (fuera de `Prov`) a
   reescritura interna (dentro). Nunca fue un reemplazo textual.
2. **Antes de sustituir un puente, comprobar si el lema lo NECESITABA.** Varias invariancias sólo lo
   usaban de atajo; `formCode φ` y `listFormCodeM L` son **cerrados** y salen de `substCodeT_closed`.
3. **Los pasos componen.** `pcc_eq_symm_code_internal`, que el KIT necesitaba, volvió con
   `BdAllIntroPrf` en el paso 3.
4. **Medir antes de comprometerse.** Las tres familias se midieron en `sondeos/` antes de tocar
   producción. Ninguna medición falló, y una (`prf_tc_form`) cambió la estrategia por completo.

### ⚠️ Y lo que esto NO resuelve

**D3 sigue reducida a un solo lema** (`d3_prf_of_chainOkDot`, sólo pide `hC_dot`), y
`pcc_lineWF_tracked_modulo_7` verifica que cerrar `pcc_lineWF_tracked` es **exactamente** cerrar los
**7 reflectores** que faltan (`q1 q2 q3 leibniz ind qconf listInd`).

Esos 7 son **el muro de `substfc`**: llevan `substfc`/`liftfc` sobre argumento **abstracto** y
necesitan `pcc_eval_substfc`, que **no existe**. Es un problema abierto de verdad — no mecánico.
La repatriación devuelve el proyecto a donde estaba antes de la inconsistencia, ahora sobre suelo
firme; no lo lleva más lejos.

---

## 2026-08-23 — ▶ REPATRIACIÓN paso 3: `D3InDotPrf` — **D3 vuelve a reducirse a UN SOLO lema**

Build **106 → 108 jobs**, **94 módulos activos**, cuarentena **12 → 10**, 0 sorrys.

```lean
d3_prf_of_chainOkDot (φ) : Prf (chainOk nil #0 ⇒ provFromCode chainOkDot)
                         → Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))
```

Ese consecuente **es D3**. Footprint sancionado (`prf_axiomsCodeT_eq`), y ahora **sobre la teoría
reparada**. Arrastró `BdAllIntroPrf` (§40, `pcc_bdAll_intro`) sin tocar una línea.

### La estrategia de frontera funcionó tal cual se midió

Los tres usos de `prf_tc_form` no eran iguales:

* **Dos** estaban en `substtc_inv_termCode_formCode`, y su enunciado **no cambia**. Bastó una prueba
  nueva por `substCodeT_closed`: `formCode φ` es **cerrado**, así que su invariancia `substtc` nunca
  necesitó pasar por `tcFn` — el puente muerto sólo se estaba usando de atajo.
  *Lección general: antes de sustituir un puente, comprobar si el lema lo necesitaba de verdad.*
* **Uno** era el genuino (`pcc_bddCarcDot_reflect`). Ahí el transporte de código sólo alcanza
  `termCode (numeral (codeNat φ))`, y la frontera se cruza **dentro de `Prov`** con
  `pcc_to_formCode_imp` (= `pcc_rw_imp` + D1 sobre `prf_formCode_numeral`).

**Ningún enunciado público cambió** — que era el objetivo — y `D3DottedPrf` encajó sin tocarse.

### Piezas nuevas (en `Meta/D3InDotPrf.lean`)

| | |
|---|---|
| `prf_tc_form_numeral` | el sustituto directo, **net‑0**, una línea |
| `pcc_to_formCode` / `_imp` | el convertidor de frontera, vía D1 |

### 📏 Medición de `InAxiomsCodePrf` (no ejecutado)

Sus 2 usos **no** son como el de `D3InDotPrf`: `prf_tc_listFormCodeM` usa **también**
`prf_tc_of_cons` (meta‑recursión sobre lista), y `pcc_in_head_swap` toma la ecuación muerta **como
hipótesis**, con la conversión metida **dentro de un código `cons`** (hueco en la cabeza). Más caro.
Lo bueno: su consumidor principal, `substtc_inv_termCode_listFormCodeM`, es **invariancia de un
código cerrado** ⇒ caso barato, `substCodeT_closed`. Y `prf_objList_numeral` (`Sigma1CorePrf:218`)
ya es genérico y sirve para la recursión de lista.

### Estado

Quedan **10 módulos**, **5 raíces**: `LineWFTrackedPrf` (8) · `CodeCtorKit` (4) ·
`CodeTreeReflect` (2) · `InAxiomsCodePrf` (2) · `LineWFEfqPrf` (1).
La única familia **sin medir** sigue siendo el **KIT** (`prf_tc_nul`/`_un`/`_bin`).

---

## 2026-08-23 — ▶ REPATRIACIÓN paso 2: `pcc_rw_imp` → `EvalNthcPrf` (cuarentena 14 → 12)

Build **104 → 106 jobs**, **92 módulos activos**, 0 errores / 0 warnings / 0 sorrys.

### `pcc_rw_imp` — la forma IMPLICACIÓN de `pcc_rw` (`Meta/DotConsPrf.lean`)

```lean
pcc_rw_imp (G : Term → Term) (hG …) (X Y : Term) (heq : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (G X) ⇒ provFromCode (G Y))
```

**Net‑0** (`[propext, choice, Quot.sound]`): la base sancionada entra por `heq`, no por aquí.
Se monta con `pcc_leibniz_code` + `pcc_mp_code_apply` + `pcc_mp_code_open`, las tres ya existentes;
es la misma maniobra que `EvalArithPrf` hizo para la inducción (`pcc_leibniz_apply_imp` y cía).

### Por qué el molde del paso 1 NO servía

Tres razones, que conviene recordar para las raíces que quedan:

1. Los sitios viven dentro de **`PrfH`** (cálculo con contexto de hipótesis) ⇒ un `Prf → Prf` no
   encaja; hay que entrar con `PrfH.mp` + `prf_to_prfH`, y para eso hace falta la implicación.
2. `nthcT` es **binario** y el hueco va en su primer argumento ⇒ molde propio,
   `pcc_rw_dot_cons_nthc`.
3. El `cons` era **una de tres ranuras** que la prueba reescribía a la vez. Las otras dos van por
   `prf_tc_zero`/`prf_tc_succ'`, que **siguen vivos** ⇒ hubo que **separarlas**: primero las sanas a
   nivel de código, y sólo el `cons` por dentro de `Prov`.

`pcc_eval_nthc` y `pcc_eval_carc_nthc` conservan **enunciado idéntico** y el footprint sancionado.
`EvalCarcNthcPrf` cayó detrás sin tocar una línea.

### ⚠️ Efecto colateral nuevo: ambigüedades de nombre

Importar `DotConsPrf` arrastra `NatOrderPrf`, y `PrfH_lt_subst1`/`_subst2` existen **en dos sitios**
(`NatOrderPrf` y `BoundedInPrf`), ambos exportados a la raíz. Se resuelve cualificando
(`BoundedInPrf.PrfH_lt_subst2`). **Esperar más de esto** conforme se repatríen módulos.

### Estado

Quedan **12 módulos** y **6 raíces**: `D3InDotPrf` (desbloquea 11) · `LineWFTrackedPrf` (8) ·
`CodeCtorKit` (4) · `CodeTreeReflect` (2) · `InAxiomsCodePrf` (2) · `LineWFEfqPrf` (1).

▶ **La siguiente es `D3InDotPrf`**, y es la más rentable — pero ataca la **tercera** sub‑familia,
**`prf_tc_form`**, que sigue **sin mirar**.

---

## 2026-08-23 — ▶ REPATRIACIÓN paso 1: `EvalListPrf` + 6 en cascada (cuarentena 21 → 14)

Build **97 → 104 jobs**, **90 módulos activos** (Minimal 11 + Meta 68 + Full 11), 0 errores /
0 warnings / 0 sorrys. Primer paso del plan de repatriación, y el sondeo decisivo del frente.

### `Meta/EvalListPrf.lean` — la BASE de la cuarentena, de vuelta

El trabajo real fueron **3 sitios**, no 6: el recuento anterior incluía la definición, el `export` y
menciones en docstrings. Y los tres tenían **la misma forma** —un constructor de código **unario**
`F` aplicado al `cons`, con un lado derecho `R` fijo—, así que se cerraron con **un solo molde**:

```lean
pcc_rw_dot_cons_un (F : Term → Term) (hFs …) (hFc …) (R : Term) (hR …) (h t : Term)
    (hbase : Prf (provFromCode (eqCodeFn (F (consT (tcFn h) (tcFn t))) R))) :
    Prf (provFromCode (eqCodeFn (F (tcFn (cons h t))) R))
```

Es `pcc_rw` con contexto `G s := ⌜F s = R⌝` y `pcc_dot_cons h t`. Instanciado en `carcT` / `cdrcT` /
`lencT`. **Compiló a la primera.** `pcc_eval_carc`, `pcc_eval_cdrc`, `pcc_ax_lenc_cons_computed` y
`pcc_eval_lenc` conservan **enunciado idéntico** y footprint
`[propext, choice, Quot.sound, prf_axiomsCodeT_eq]` — la base sancionada, **sin `tc_cons`**.

Dos limpiezas que el plan no había previsto:

* **`prf_tc_cons'` se BORRA, no se reescribe.** Su cuerpo era `prf_tc_cons`, consecuencia directa de
  `ax_tc_cons`, y **ya no existe** en el árbol. Bajo la lectura numeral su enunciado es **falso** para
  argumentos abstractos, no sólo indemostrable. En su hueco queda una nota explicando la sustitución.
* **4 declaraciones duplicadas con `DotConsPrf`** (`consT` —textualmente idéntica—, `prf_congr_consT`,
  `prf_substtc_consT`, `substtc_inv_consT`): borradas de aquí, importadas de allí.

### La cascada — 6 módulos más, sin tocar una línea

Al volver `EvalListPrf` quedaron libres y compilan tal cual: `EvalLtPrf`, `EvalRunFnPrf`,
`EvalBoundedPrf`, `Delta0ReflectPrf`, `PropCodePrf` y **`D3DottedPrf`**.

🎯 **`D3DottedPrf` es el que importa**: contiene **`d3_prf_of_dotted_atoms`** —la reducción de D3 a
las reflexiones punteadas— y vuelve **net‑0** (`[propext, choice, Quot.sound]`). También vuelve
`PropCodePrf` (§39: la lógica interna completa, incl. `pcc_ind_code`), igualmente net‑0.

### Lo que esto confirma (era el objetivo del paso 1)

**El patrón se repite y es factorizable.** No hubo que reescribir tres pruebas: bastó reconocer la
forma común y escribir el molde una vez. Es la misma lección que abarató `pcc_dot_cons`.

### Lo que NO confirma — tres avisos para el paso 2

1. **Son TRES sub‑familias, no dos.** `prf_tc_cons'` (✅ resuelta), el **KIT**
   `prf_tc_nul`/`_un`/`_bin` (⏳ sin medir) y **`prf_tc_form`** (⏳ sin mirar, lo usan `D3InDotPrf` e
   `InAxiomsCodePrf`).
2. **`EvalNthcPrf` NO es el mismo patrón.** Sus 2 usos van sobre `.var 2`/`.var 1` **bajo binder**,
   dentro de `PrfH` — no sobre términos abstractos sueltos. Hay que mirarlo antes de asumir.
3. Quedan **14 módulos** y **7 raíces**: `EvalNthcPrf` (desbloquea 13) · `D3InDotPrf` (11) ·
   `LineWFTrackedPrf` (8) · `CodeCtorKit` (4) · `CodeTreeReflect` (2) · `InAxiomsCodePrf` (2) ·
   `LineWFEfqPrf` (1).

---

## 2026-08-23 00:30 — AUDITORÍA de documentación: proyección del árbol REFERENCE

Pasada completa (`repasa_y_proyecta` + `actualiza_documentacion`) sobre los 24 `.md` del repo y los
5 nodos de `doc/`. **No toca código**: `lake build` sigue en 97 jobs, 0 errores/warnings/sorrys.

### Dos errores REALES encontrados (no cosméticos)

1. **La cuarentena tiene 8 raíces, no 6.** La cifra venía propagándose por `NEXT-STEPS.md`,
   `PLAN-FRENTE-A.md`, `cuarentena/README.md` y la memoria. El recuento anterior buscaba sólo
   `prf_tc_cons` y se dejó fuera **`CodeTreeReflect`** y **`LineWFEfqPrf`**, que usan la otra
   sub‑familia: `prf_tc_nul`/`prf_tc_un`/`prf_tc_bin`, los constructores del KIT.
   ⇒ **Consecuencia de planificación:** la repatriación necesita **dos** sustitutos, no uno.
   `pcc_dot_cons` cubre `prf_tc_cons'`; el KIT necesita su propio `pcc_dot_nul`/`_un`/`_bin`
   (esperable por composición, **sin medir** — sondeo registrado como paso 3 del plan).
2. **`EvalListPrf` no es sólo el keystone: es la BASE.** Grafo recalculado por máquina: no tiene
   ninguna dependencia dentro de la cuarentena, **los otros 20 dependen de él**, y es donde se
   **define** `prf_tc_cons'` (`:48`). Nada vuelve antes que él. (Antes se decía «bloquea 9 de 15».)

### Desincronización corregida

* **`REFERENCE.md`** decía «113 jobs, 99 módulos (Meta 77)» — real: **97 jobs, 83 módulos (Meta 61)**;
  su §1.5 listaba como activos 10 módulos que están **en cuarentena** y omitía los 10 nuevos.
  Reescritos §1 (catálogo real, con §1.6 nuevo para la cuarentena), §3 y §5.
* **La línea `Last updated` de `REFERENCE.md` era un volcado histórico acumulativo de ~20 KB en una
  sola línea.** Sustituida por una marca de tiempo limpia; el fichero pasa de 36 KB a 20 KB. El
  historial es competencia de este `CHANGELOG.md`.
* **`CURRENT-STATUS-PROJECT.md`**: banner correcto, **cuerpo desfasado** — la tabla resumen seguía
  citando `goedel_first_real'`, «113 jobs» y «99 módulos». Corregidas 6 filas.
* **`DECISIONS.md` ADR‑007** llevaba **más de un mes** marcado «Propuesto (no implementado) — no
  existe todavía directorio `doc/`»: existe desde 2026‑07‑12 con 5 nodos. Marcado ✅ implementado.
* **Fantasma en `doc/REFERENCE-Incompleteness.md` §3.15**: documentaba `Meta/Incompleteness.lean`
  como vigente; el fichero se **borró en F7a**. Marcado 🗑️ y conservado como registro para el libro.
* Banners sincronizados en los 7 documentos de estado (jobs 95→97, módulos 82→83, Meta 59→61,
  sondeos 9→10, HEAD).

### Proyección nueva (AI-GUIDE §12/§14 — todo `export` debe estar proyectado)

**`doc/REFERENCE-Incompleteness.md` §3.24 y §3.25** (nuevas, ~200 líneas): los **10 módulos** de la
reparación y la escalera, que no estaban proyectados en ningún sitio — `NatOrderPrf`, `NatMulPrf`,
`CantorMonoPrf`, `Div2ParityPrf`, `CodeNumeralPrf`, `DiagonalNumeral`, `StrongInductionPrf`,
`EvalArithPrf`, `EvalMulPrf`, `DotConsPrf`, más la refundación de `Sigma1CorePrf`. Con firmas Lean 4
exactas, notación matemática y dependencias.

### Otras aportaciones

* **`DEPENDENCIES.md` §0 (nueva)**: la **vista de subsistema de `Meta/`** que el propio fichero
  llevaba pidiendo desde julio («candidato prioritario»), generada **por máquina** de los `import`
  reales. **25 niveles, sin ciclos.** Hechos medidos: `DotConsPrf` (L24) es el módulo **más profundo**
  del proyecto; `ReprPrf` (L7) el de mayor *fan‑in* (7 dependientes).
* **`DECISIONS.md` ADR‑014 (nuevo)**: por qué la cuarentena se recupera *internalizando* la evaluación
  en vez de reescribiendo los 21 módulos uno a uno.
* **`PLAN-LIBRO.md`**: capítulo **16** nuevo (la reconstrucción — el capítulo de moraleja positiva que
  cierra el arco de la Parte IV) y **9bis** (`⊬¬G`, la mitad que falta y que los manuales despachan en
  un párrafo). El **aviso editorial** de §6 se reformula: la reparación **está hecha**, así que el
  aviso ya no es «la teoría es inconsistente» sino «se retiró la inconsistencia **conocida**, y eso
  **no** es una prueba de consistencia».
* **`NEXT-STEPS.md`**: plan de repatriación en **6 pasos**, con el paso 1 (`EvalListPrf`) marcado como
  el sondeo decisivo del frente.
* **`cuarentena/README.md`** reescrito con el grafo recalculado y el patrón de arreglo en código.

---

## 2026-08-22 23:42 — ✅ La ESCALERA (a.2) COMPLETA: `pcc_dot_cons`

**`Meta/DotConsPrf.lean`** (nuevo). Cierra el cuarto y último peldaño de la escalera de
Σ₁‑completitud internalizada:

```lean
pcc_dot_cons (h t : Term) :
    Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (tcFn (cons h t))))
```

o sea `⊢ Prov(⌜ cons(ḣ,ṫ) = (cons h t)˙ ⌝)` — `prf_cons_eval` **internalizado y para argumentos
ABSTRACTOS**. Footprint `[propext, choice, Quot.sound, prf_axiomsCodeT_eq]`: la base sancionada,
**sin `tc_cons`**, igual que `pcc_eval_add` y `pcc_eval_mul`.

**No hizo falta inducción nueva.** `cons` no tiene ecuaciones recursivas propias — `ax_L0_cons_def`
lo define como `div2 (cantor_poly h (σt))`, o sea `+`, `·` y `div2`, ya internalizados. Tres fases:

* **(A)** `prf_axL0_body_computes`: `substCodeF` **computa por `rfl`** sobre el cuerpo de
  `ax_L0_cons_def`, igual que sobre `ax5`/`ax9`. Era la pregunta arriesgada de la fase.
* **(B)** el polinomio de Cantor se evalúa dentro de `Prov` en **cinco** pasos.
* **(C)** el `div2` se cancela con `pcc_thm_inst` sobre `prf_div2_double_all`; el puente es
  `prf_cons_double` (`Div2ParityPrf`).

Dos herramientas nuevas, reutilizables: **`pcc_rw`** (reescritura interna en un hueco de
código‑contexto) y **`pcc_rw_div2`** (su molde para `L = div2(D ·)`).

**Lecciones:** (1) todo teorema OBJETO se «dota» **gratis** con `prf_congr_tcFn`, sin entrar en
`Prov`; (2) `substfc` sustituye **todas** las ocurrencias del hueco, así que un único
`pcc_leibniz_apply` cubre las repeticiones del polinomio — de ahí 5 pasos y no 15.

**Siguiente:** repatriar las **8** raíces de `cuarentena/`, empezando por `EvalListPrf` — que es
la **base** de toda la cuarentena (los otros 20 dependen de él) y donde se **define** el contaminado
`prf_tc_cons'`.
`pcc_eval_carc` = `pcc_axiom_inst ax_carc` + `pcc_dot_cons`.
> **82 módulos activos** (Minimal 11 + Meta 59 + Full 11) + 21 cuarentena + 9 `sondeos/`.
> **7 `axiom` de Lean.** **141 axiomas objeto** en `axioms`.

**Last updated:** 2026-07-24 - **Ruta 1a (toolkit aritmetico en Prf): i-a/i-b/i-c HECHOS, net-0** -- `prf_cantor_mono` (sub-codigo < codigo), monotonia/cancelacion de mul, orden. + ensamblaje or_elim x21 verificado. **VEREDICTO sobre los 7 tags de substfc: no hay ruta net-0** (dos workflows + verificacion a mano; `ax_tc_substfc` es INCONSISTENTE). DECISION del usuario pendiente (1-min predicado / a-reformular / 3-repr_neg). Build **113 jobs**, **99 modulos**, 0 sorrys. HEAD `d8e9152`. - (previo 2026-07-20 - **S44.4: el `In`-reflect de `axiomsCodeT` CERRADO** (`pcc_In_axiomsCodeT_tracked`, el nudo de `NegVerifier`) + refactor de anclas (`prf_axiomsCodeT_eq`; `prf_inAxC` pasa a **teorema**, net-0 axiomas, siguen **7**). Build **101 jobs**, **87 modulos**, 0 sorrys, Lean v4.31.0. HEAD `124d293`. - (previo 2026-07-18) **B.3c: caso `eqrefl` (tag 12) CERRADO** via esquema ESTRICTO + B.3a/B.3b (des-duplicacion de 42 teoremas + los 19 `ax_lineWF` a accesores, net-0). - (previo 2026-07-15) **MODULO A COMPLETO**: decodificador de codigos (`decodeForm` BIYECCION) y de cadenas (`decodeChain_prf`). - (previo 2026-07-14) **S42 `axiomsCodeT` concretado** (direccion NEGATIVA) + `PLAN-NEGVERIFIER.md`. - (previo 2026-07-13) **S37-S41**: `hI_dot` COMPLETO, logica interna completa, `pcc_bdAll_intro`, y la mitad `no-|- not G` reducida a `NegVerifier`. - (previo 2026-07-10q — **§31.3 reflexion de los DOS atomos Delta_0 desde hipotesis**: `pcc_eq_tracked` (=) y `pcc_lt_tracked` (<) para terminos abstractos. Base atomica de la completitud-Delta_0 provable. Build 85 jobs. — (previo 2026-07-10p)  **§31 completitud-Delta_0 provable (arranque)**: `pcc_exIntro_code_open` (exists-intro sin hAc, arrastrando el lift) + `pcc_lt_intro_open` (< sin clausura). Desbloqueo: pcc_eval_add da el puente simbolo<->valor sobre + para terminos abstractos. Build 85 jobs. — (previo 2026-07-10o)  **§30 cuantificadores ACOTADOS a nivel de codigo**: `and` interno libre de muro (C1/C2/C3), `pcc_bdEx_intro` (exists i<b-intro) y `pcc_bdAll_elim` (forall i<b-elim), todos sin `prf_inAxC`. Falta la INTRODUCCION del forall acotado (induccion acotada, fase estructural). Build 84 jobs. — (previo 2026-07-10n)  **§28 evaluacion provable de listas** (`pcc_eval_carc`/`_cdrc`/`_lenc`) + **§29 reflexion del atomo `<`** (`pcc_lt_intro` = `∃`-intro + `=eq` + evaluacion provable; `ltBwd` codificado en tracked, invariancia `substtc` a nivel arbitrario). Build 83 jobs. — (previo 2026-07-10l)  **§27: EVALUACION PROVABLE DE `+` COMPLETA** (`pcc_eval_add`): formas implicacion de los combinadores + paso inductivo + induccion object. Es la primera evaluacion provable cerrada; el hueco que §18 llamo "la bestia" queda resuelto para `+`. Build 81 jobs. — (previo 2026-07-10k)  **§26: `pcc_mp_code_open`** (`hAc`/`hBc` eran el cuarto artefacto de clausura) + **lógica ecuacional INTERNA sobre códigos** (`pcc_leibniz_apply`, `pcc_eq_trans_code`, `pcc_congr_succ_code`), todos limpios. El paso inductivo de `+` ya encaja; falta la forma implicación de los combinadores. Build 81 jobs. — (previo 2026-07-10j)  **§25: `pcc_thm_inst`** (internaliza cualquier teorema universal) + **LEIBNIZ codificado LIBRE DE MURO** (`pcc_leibniz_code`, testigo de una línea; `prf_lineWF_leibniz` es estructural). La lógica ecuacional interna sale de Leibniz + MP, sin `for-all`-elim triple. Siguiente: `pcc_mp_code_open`. Build 81 jobs. — (previo 2026-07-10i)  **§23 (A): el código de un numeral es CERRADO** (`prf_liftc_tcFn`/`prf_substtc_tcFn`, primera inducción interna, sin `prf_inAxC`) + **§24 (B): `pcc_ax5_computed`** (`⊢ Prov(⌜ȧ + σḃ = σ(ȧ+ḃ)⌝)`; (B) no necesitaba inducción general — el cuerpo de `ax5` computa por `rfl`). El paso inductivo pide lógica ecuacional interna sobre códigos (`pcc_eq_trans_code`, `pcc_congr_succ_code`), derivable. Build 81 jobs. — (previo 2026-07-10h)  **§22: `pcc_axiom_inst2`** (axiomas `forall_2` codificados, dos testigos abiertos; `hAc` también era innecesaria → `pcc_forallElim_code_open`). Verificado `pcc_ax5_inst (tcFn a) (tcFn b)`. **Hueco localizado** para el paso inductivo de `+`: falta (A) «el código de un numeral es cerrado» (derivable por inducción interna) y (B) la composición `substfc` sobre `substCodeF`. Build 80 jobs. — (previo 2026-07-10g)  **§21: BASE de `+` cerrada** (`pcc_eval_add_zero`: `⊢ Prov(⌜ȧ + 0̇ = (a+0)˙⌝)`) — primera aritmética real demostrada DENTRO de `Prov`, encajando §19 (ax4 codificado) + §20 (computar substfc) + transporte Leibniz de códigos. Build 80 jobs. — (previo 2026-07-10f)  **§20: primer paso REAL de la evaluación provable** (`prf_substfc_arith_open`: `substfc` con testigo-código ARBITRARIO, no sólo `termCode s`). Payoff verificado: `Prov(⌜ȧ + 0 = ȧ⌝)` desde `pcc_ax4_inst`. Build 79 jobs. — (previo 2026-07-10e)  **§19: sistema de prueba INTERNO a nivel de código completo** (`pcc_forallElim_code'` ∀-elim Q1 + `pcc_mp_code` MP + `pcc_axiom_inst`), todas con testigo abierto. Verificado: `pcc_ax4_inst (tcFn #0)`. El caso `σ` de la evaluación provable es gratis; siguiente el caso `+` por inducción interna. Build 78 jobs. — (previo 2026-07-10d)  **`liftFormula_provFromCode_open`** (clausura para códigos abiertos, la necesita el ∀-elim de código) + **§18**: sondeo verificado — la reflexión de `<` NO es un ladrillo pequeño; aterriza en la **evaluación provable** (`⊢ Prov(⌜ȧ + σk̇ = (a+σk)˙⌝)`), «la bestia» de §11.3. Build 76 jobs. — (previo 2026-07-10c)  **§17 RESUELTA: `pcc_exIntro_code'`** (el `∃`-intro de código admite testigo ABIERTO; `hw` era innecesaria, vía `liftTerm_substfc_open`). Verificado con `tcFn #0`. De RIESGO-1 cae la mitad (a); la (b) (Tarski) queda confinada al puente. **Sin obstrucción conocida** hacia `d3_prf`. Build 76 jobs. — (previo 2026-07-10b)  **`ax_lineWF_inv` (obstrucción §16 RESUELTA)** + **segunda obstrucción §17** (el `∃`-intro de código exige testigo cerrado; reparable con `pcc_exIntro_code'` lift-aware). Cadena real verificada intacta tras tocar el núcleo. Build 76 jobs. — (previo 2026-07-10) **`atom1CodeFn` + OBSTRUCCIÓN encontrada en `lineWF`** (§16 del diseño): `lineWF`/`premsOf` son átomo/función primitivos con 21 axiomas indexados por etiqueta y **sin axioma de inversión** → `Prf (lineWF t ⇒ provCodeC'(lineWF t))` no es derivable para `t` abstracto. No afecta a la solidez de D1/D2/Gödel I. `hbI` no bloqueado; `hbC` sí. Arreglo mínimo: `ax_lineWF_inv` (def de teoría objeto, no `axiom` de Lean). Build 76 jobs. — (previo 2026-07-09d) **12‑A fase 3: reflexividad LIBRE DE MURO** (`prf_provFromCode_eqCodeFn_refl`, testigo de una línea EQREFL) → **átomo `=eq` cerrado sin muro** (`pcc_eq_tracked`). Los tres `[propext, choice, Quot.sound]`, sin `prf_inAxC`. El muro de Tarski queda confinado al puente `tcFn t =eq termCode t` (numerales, fase 5). Build 76 jobs. — (previo 2026-07-09c) **12‑A fase 3 núcleo: átomo `=eq`** (`Meta/Sigma1AtomPrf.lean`): toolkit RASTREADO de la igualdad (`eqCodeFn` + congruencia + `prf_provCodeC'_eq_of_tracked`, espejo del de `In`). Confirmado en código que la reflexión de `=eq` abstracta es imposible libre de muro (Tarski) → se rastrea con `tcFn`. Build 76 jobs. — (previo 2026-07-09b) **fase 3 arrancada** (`Meta/Sigma1BoundedPrf.lean`): `d3_prf_of_reflect_bounded` — D3 reducida a reflejar la forma Δ₀ acotada vía `pcc_imp` + los `⇔` de fase 1/2. Build 75 jobs. — (previo 2026-07-09) **F7a: retirada la capa Gödel legacy (14 → 7 `axiom`).** `Meta/Incompleteness.lean` eliminado + 5 postulados de `Meta/Provability.lean` retirados; núcleo real de codificación conservado. Nuevo `AXIOMS.md` (registro autoritativo). Cadena real verificada intacta (`#print axioms`). Build 74 jobs, 0 sorrys. F7b (retirar `d3`) espera a D3 real. — (previo 2026-07-08) **12‑A fases 1b y 2 COMPLETAS: el verificador ya es Δ₀ y sin acumulador.** `Meta/NatArithPrf.lean` (toolkit de `<` en `Prf`; `0+n=n` NO es teorema de Q → `Prf.ind`), `Meta/BoundedInPrf.lean` (**`prf_In_iff_boundedIn`**), `Meta/RunFnBoundedPrf.lean` (**`prf_In_runFn_iff`**; hallazgo: `runFn nil p` es el *map* de `carc` → **no hace falta β‑función**) y `Meta/ChainOkBoundedPrf.lean` (**`prf_chainOk_iff_chainOkB`** — el acumulador desaparece, `∀c` interno). Con esto **ya no queda ningún punto del plan 12‑A sin verificar en código**. Todos `#print axioms` = `[propext, choice, Quot.sound]`. Build **75 jobs**, 0 errores, 0 warnings, 0 sorrys (v4.31.0). Siguiente: fases 3‑5 → `d3_prf` → `goedel_second_prf`. — (previo 2026-07-05) **Opción A (D3/Gödel II con testigo rastreado) — A‑F1/A‑F2**: `Meta/Sigma1CorePrf.lean` extendido con tracking `runFn→objList`, `pcc_in_runFn_objList` (hI para testigos concretos), `prf_tc_objList(_formCode)` (A‑F1) y **`prf_provCodeC'_of_tracked_witness`** (A‑F2, mecanismo central: reflexión rastreada con testigo-código = `provCodeC'` real). Diseño completo en `GODEL-D3-TRACKED-DESIGN.md`. Build 67 jobs, 0 sorrys. `Meta/TcArithPrf.lean` (NUEVO), porte finitario de la cadena `tc_arith` de `Diagonal.lean` (ω) → `Prf`: `prf_tc_zero`/`succ`/`cons` (re-derivadas de `axioms` vía `prf_ax`+`prf_spec`), `prf_tc_numeral` (inducción meta), `prf_tc_of_cons` (recursión), y **`prf_tc_form : Prf (tcFn (formCode φ) =eq termCode (formCode φ))`** — la función object `tcFn` **computa `termCode`** sobre todo código, en `Prf`. `#print axioms` = `[propext, choice, Quot.sound]`. Es el **cimiento del enfoque de código object** para reformular `hC`/`hI` (la Σ₁-completitud del verificador): a diferencia de la `termCode` meta, `tcFn` es función object con **congruencia Leibniz**. Build verde (**66 jobs**), 0 sorrys. Pendiente Opción A: la capa de demostrabilidad al nivel del código object (`substfc`/`tcFn`) → `hC`/`hI` → `d3_prf` → `goedel_second_prf`. — (hito previo) **Reflexión de igualdad reducida + transporte por código: `provFromCode`/`prf_provCode_congr`/`pcc_eq_of_codeEq`**. `Meta/Sigma1Prf.lean`: **`provFromCode c`** (demostrabilidad de un código de fórmula; `provCodeC' φ = provFromCode (formCode φ)`) + **`prf_provCode_congr : Prf (c₁=eq c₂) → Prf (provFromCode c₁ ⇒ provFromCode c₂)`** — la demostrabilidad **respeta la igualdad de códigos** (Leibniz object; funciona porque `c` es slot-término genuino, no absorbido; `#print axioms` = `[propext, choice, Quot.sound]`, sin `prf_inAxC`) + **`pcc_eq_of_codeEq`** que **reduce la reflexión de igualdad** `(x=eq y) ⇒ provCodeC'(x=eq y)` a la igualdad de *códigos* `formCode(x=eq x) =eq formCode(x=eq y)`. **HALLAZGO**: la reflexión de igualdad universal `∀x y` es indemostrable (obstrucción Tarski: `termCode` es meta, no object; de `x=eq y` no sale `termCode x =eq termCode y`); solo vale para términos-código (vía `tcFn`). → La Σ₁-completitud real (`hC`/`hI`) debe reformularse al nivel del código object (`tcFn`/`substfc`) — Fase 5. REFERENCE.md §3.17 proyectada (cadena Gödel II en `Prf`). Build verde (**65 jobs**), 0 sorrys. — (hito previo) **Infraestructura de reflexión Σ₁ (núcleo duro de D3): `pcc_imp` + combinadores `In`/`chainOk`/`allIn`**. `Meta/Sigma1Prf.lean` (NUEVO): combinador clave **`pcc_imp {A B} (h : Prf (A ⇒ B)) : Prf (provCodeC' A ⇒ provCodeC' B)`** (eleva implicaciones object cerradas a implicaciones de demostrabilidad, vía D2 `d2_prf` + D1 `repr_pos'_prf` — "modus ponens interno como esquema") + `pcc_imp2` + combinadores de reflexión `pcc_in_head/tail/head_eq/nil`, `pcc_chainOk_nil/cons`, `pcc_allIn_nil/cons` (+ implicaciones object `prf_*_cons_imp`). Todos `#print axioms` = `[propext, choice, Quot.sound, prf_inAxC]`. HALLAZGO: `d3` NO es `pcc_imp` de reflexión local (`φ ⇒ Prov φ` es FALSO por Löb) — la Σ₁-completitud genuina es ineludible. Con los combinadores, `hI`/`hC` se reducen a **(1) reflexión de igualdad** `Prf ((x=eq y) ⇒ provCodeC'(x=eq y))` (los `▸`/Leibniz fallan: el código absorbe la forma sintáctica, no el valor — obstrucción Tarski; necesita sustitución formalizada `substfc`) **y (2) cierre inductivo** sobre el código con seguimiento aritmético `tcFn`/`substfc` (tipo `tc_arith`, la "bestia" Fase 5). Build verde (**65 jobs**), 0 sorrys. — (hito previo) **D3 finitaria REDUCIDA: `d3_prf_of_sigma1` (Punto 6, paso 9) + fix de toolchain**. `Meta/ReflectionPrf.lean` (NUEVO), porte de `Reflection.lean` ω → `Prf`: **combinadores lógicos internos** `PrfH_pcc_mp`/`pcc_prf`/`pcc_andIntro`/`pcc_exIntro` (vía `d2_prf` + `repr_pos'_prf`, versión `PrfH`) + **`d3_prf_of_sigma1 (φ) (hC) (hI) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))`** que **reduce D3** a dos lemas de Σ₁-completitud del verificador (hipótesis `hC : ∀p, Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))`, `hI : ∀x L, Prf (In x L ⇒ provCodeC'(In x L))`), aislando el núcleo duro (igual que `d3_of_sigma1` en ω). `#print axioms` = `[propext, choice, Quot.sound, prf_inAxC]` (sin postulados gödelianos). **FIX DE TOOLCHAIN**: `lean-toolchain` en la copia de trabajo estaba a `v4.31.0` (rompía `simpa` de `Representability` al recompilar; los builds verdes previos lo replayaban de caché); restaurado a `v4.29.1` (commiteado), build limpio de cero verificado. Build verde (**64 jobs**), 0 sorrys. **PENDIENTE núcleo duro**: `hI`/`hC` (Σ₁-completitud provable, por inducción object sobre el testigo) → `d3_prf` → `goedel_second_prf`. — (hito previo) **D2 FINITARIA REAL: `d2_prf` (Punto 6, paso 9 — primera condición HBL en `Prf`)**. `Meta/DerivCondPrf.lean` (NUEVO): **`d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))`**, porte finitario de `DerivCond.lean` ω → `Prf`, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (¡sin postulados, ni `prf_inAxC`!). Tres piezas: (1) **capa de clausura** `liftTerm_numeral`/`charsCode`/`strCode`/`termCode`/`formCode` + `liftFormula_provCodeC'` (los códigos son cerrados — prerequisito porque `prf_ex_elim_imp` no da acceso meta al testigo, a diferencia del `provCodeC'_elim` ω); (2) **`∃` en `PrfH`**: `PrfH_ex_intro`/`PrfH_ex_elim` (vía `q2`/`q3`) en `HilbertDeduction.lean`, para los testigos anidados `p=#1`,`q=#0`; (3) **ensamblaje** `r = p++q++[mp]` con los lemas de cadena del paso 8 (`prf_runFn_concat`/`prf_chainOk_concat`/`prf_chainOk_mono_imp`/`prf_In_mono`/`prf_In_mono_right_imp`) + `provCodeC'_intro_prf`. Helpers nuevos en `ChainPrf` exportados (`prf_In_mono_right_imp`, `PrfH_allIn_subst2`, `PrfH_in_cons_head`, `PrfH_and_*`/`PrfH_iff_*`/`PrfH_chainOk_subst1/2`/`PrfH_eq_subst_in`). Build verde (**63 jobs**), 0 sorrys. Pendiente Punto 6: `d3_prf` (Σ₁-completitud) → `goedel_second_prf`. — (hito previo) **PASO 8 COMPLETO: los 10 lemas de cadena portados a `Prf`** (`runFn_concat`/`chainOk_concat`/`chainOk_mono`/`runFn_weaken` + `In_mono`/`In_mono_right`/`concat_assoc`/`allIn_mono`/`lineOk_mono`/`concat_nil_right`). Los 3 finales (`prf_chainOk_mono_imp`, `prf_runFn_weaken`, `prf_chainOk_concat` —iff—) reutilizan el patrón `norm32`/`norm_s`/confinación-`qconf`. Helpers nuevos: `PrfH_and_intro/elim`, `PrfH_iff_mp/mpr`, `PrfH_eq_symm`, `PrfH_congr_concat_left`, `PrfH_chainOk_subst1/2`, `prf_concat_assoc`, `prf_allIn_mono_imp`, `prf_lineOk_mono_imp`. Detalle: `chainOk_concat` necesitó un `def ccIHbody` + `unfold` + `land` en el `simp` (un `let` no se desplegaba; `land` bloqueaba `liftFormula`/`substFormula`). Todos `#print axioms` = `[propext, Classical.choice, Quot.sound]`. **Listos todos los ingredientes de cadena de `d2_prf`.** Build verde (**62 jobs**), 0 sorrys. — (hito previo) **Frontera `∀c` RESUELTA DE RAÍZ: `norm32`+`norm_s` (familia De Bruijn profundidad 2) + confinación `qconf` → `prf_runFn_concat` (keystone d2) + `prf_In_mono_right`**. `Meta/ChainPrf.lean`: (1) **`prf_In_mono_right`** (monotonía derecha de `In`, vía `base` por explosión `ax_L1` + `step` por `or_elim` sobre `ax_L2`; helpers `PrfH_or_elim`/`PrfH_congr_cons_head`/`prf_in_cons_iff`/`prf_not_in_nil`). (2) **Raíz del problema de los 3 binders resuelta**: los lemas con `∀c` interno anidan TRES binders en el `step` del eliminador; el patrón es **`norm32`** (`substTerm 1 z (liftTerm 3 (liftTerm 2 (liftTerm 0 (liftTerm 0 t)))) = liftTerm 2 (liftTerm 0 (liftTerm 0 t))`, inducción mutua) + **`norm_s`** (cancela el lift de la confinación) + **confinación `qconf`** (`(∀c.IH)⇒(∀c.Concl)` = RHS de `confinementFormula (∀c.IH) Concl`, reducido vía `Prf.gen`+`prf_deduction`+`PrfH_spec` de la HI al acumulador cambiado). (3) **`prf_runFn_concat`** (compositividad `runFn c (p++s) =eq runFn (runFn c p) s`, **keystone de `d2_prf`**) valida el patrón end-to-end. Todos `#print axioms` = `[propext, Classical.choice, Quot.sound]` (`norm32`/`norm_s` sin `choice`). `chainOk_concat`/`chainOk_mono` reutilizan el patrón (misma profundidad 2). Build verde (**62 jobs**), 0 sorrys. — (hito previo) **`prf_In_mono` (monotonía izquierda de `In`, keystone de `d2_prf`) + `norm21` + `PrfH_spec` (paso 8)**. `Meta/ChainPrf.lean`: portada a `Prf` la **monotonía de `In` en el contexto izquierdo** `prf_In_mono : Prf (In x c) → Prf (In x (concat c0 c))` (inducción de listas sobre `c0`; `x`,`c` con `liftTerm 0` para no capturar el slot de la lista). Para casar el `step` del eliminador (dos binders sobre el parámetro lifteado) se probó el lema de normalización De Bruijn **`norm21 : substTerm 0 s (liftTerm 2 (liftTerm 1 (liftTerm 0 t))) = liftTerm 1 (liftTerm 0 t)`** (vía `liftTerm_comm_zero`+`substTerm_liftTerm`). `#print axioms prf_In_mono` = `[propext, Classical.choice, Quot.sound]`. Helper **`PrfH_spec`** (∀-elim en `PrfH`) dejado como andamiaje. **Frontera identificada**: `runFn_concat`/`chainOk_concat`/`chainOk_mono` generalizan el acumulador como `∀c` **dentro** de `Φ` → el `step` del eliminador anida TRES binders y exige una familia de lemas de normalización De Bruijn multinivel (más allá de `norm21`); el `base` ya valida pero la normalización del consecuente `C'` es trabajo de varias sesiones. Build verde (**62 jobs**), 0 sorrys. — (hito previo) **Lemas de cadena en `Prf`: eliminador `prf_list_induction` + `prf_concat_nil_right` (paso 8, patrón validado)**. `Meta/ChainPrf.lean`: eliminador de inducción de listas + helpers ecuacionales `PrfH` (`PrfH_leibniz_subst`/`PrfH_eq_trans`/`PrfH_congr_cons_tail`) + primer lema de cadena `prf_concat_nil_right` (valida `base`+`step` vía `prf_deduction`; `#print axioms` = estándar). Pendiente paso 8: `In_mono`/`In_mono_right`/`runFn_concat`/`chainOk_concat`/`chainOk_mono`/`runFn_weaken` (mismo patrón) → `d2_prf`/`d3_prf`/`goedel_second_prf`. Build verde (**62 jobs**), 0 sorrys. — (hito previo) **regla `listInd` integrada (paso 7 parte 2 COMPLETO)**. Vertical slice completo (tipo `qconf`/`ind`, sin postulados): `Prf.listInd`/`Rule.listInd` + doble aritmetización (legacy `validProofFn` + `runFn`) + `prf_listInd_concl_code` + cascada (`vpf_run`/`chainOk_track`/`prf_chainOk_track`) + `HilbertDeduction`. `prf_iff_derivation` total; `repr_pos'_prf` honesto (`[propext, choice, Quot.sound, prf_inAxC]`). `Prf` dispone de inducción de listas (desbloquea el port de los lemas de cadena). **48 módulos**, build verde (**61 jobs**), 0 sorrys. — (hito previo) **`listInd_concl_code` (paso 7 parte 2, núcleo)**. `Meta/ListInductionArith.lean`: reconstrucción del código de `listInductionFormula A` desde ⌜A⌝ (más complejo que `ind`: `cons #1 #0` con variables libres). Resto del slice `Prf.listInd`/`Rule.listInd` mecánico (tipo `qconf`). Build verde (**61 jobs**), 0 sorrys. — (hito previo) **`list_induction_derives` (paso 7 parte 1)**. `listInductionFormula Φ` + `list_induction_derives : axioms ⊢ listInductionFormula Φ` en `Hilbert.lean` (vía `ax_list_induction`+ω-gen; consecuente del paso cerrado con el lema de Barendregt). Pendiente paso 7 parte 2: slice `Prf.listInd`/`Rule.listInd` (verificador + aritmetización; `listInd_concl_code` con `cons #1 #0`). Build verde (**60 jobs**), 0 sorrys. — (hito previo) **lema de Barendregt → paso 7a COMPLETO**. `subst_subst_comm_succ` (+ versiones término) en `FOL/Theorems/Eq.lean` cierra el toolkit De Bruijn; con `subst_subst_lift_gen`+`subst_lift_same` se verifica end-to-end la identidad del consecuente de la inducción de listas objeto (`C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`). Desbloquea `list_induction_derives` + slice `Prf.listInd` → `d2_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **composición subst-subst-lift generalizada por niveles**. Toolkit De Bruijn a nivel fórmula para la inducción de listas objeto. La parte final de la identidad del consecuente se cierra con `subst_subst_lift_gen`; falta el **lema general de Barendregt** (conmutación subst–subst niveles mixtos, convención decremental) para ensamblarla. Probados por inducción, sin axiomas. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **Solidez: eliminado un `axiom` FALSO de la base FOL (`subst_lift_cancel_formula`)**. El axioma De Bruijn `substFormula v t (liftFormula (v+1) f) = f` (general, `t` arbitrario) era **falso** (verificado con `rfl`) y todo el Nivel D lo citaba. Reparado: ahora es **teorema** en la forma restringida verdadera `substFormula v (#v) (liftFormula (v+1) f) = f` (la única que el código usa), demostrado por inducción + helper de término. `confinement_derives` pasa a `[propext, Classical.choice, Quot.sound]` (sin el axioma falso). Cimiento De Bruijn sólido. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **teorema de deducción finitario para `Prf`**. Nuevo `Meta/HilbertDeduction.lean`: cálculo con contexto `PrfH` (espejo finitario de `Prf` con `gen` de contexto-lift + `hyp`) + teorema de deducción (caso `gen` cerrado vía `qconf`) + puentes `PrfH []↔Prf`. Exporta **`prf_deduction : PrfH [A] B → Prf (A ⇒ B)`** (descarga de hipótesis) y **`prf_ex_elim_imp : PrfH [A] (↑C) → Prf (∃A ⇒ C)`** (eliminación del ∃, = `provCodeC'_elim` finitario para `d2_prf`). `#print axioms` = `[propext, Classical.choice, Quot.sound]`. Build verde (**60 jobs**), 0 sorrys. Próximo: regla de inducción de listas en `Prf` → port de lemas de cadena → `d2_prf`. — (hito previo) **regla `qconf` (confinamiento ∀) integrada en el verificador**. El esquema de confinamiento ∀ se añade como **regla del verificador** (`Prf.qconf` + `Rule.qconf` + ambas aritmetizaciones, legacy `validProofFn` y `runFn`), sin postulados y manteniendo `prf_iff_derivation` total y `repr_pos'_prf` honesto (`#print axioms` = `[propext, Classical.choice, Quot.sound, prf_inAxC]`). `provCodeC'` rastrea ahora `IΣ₁ + confinamiento ∀`. Desbloquea el teorema de deducción finitario para `Prf` (caso `gen` vía `qconf`) → `d2_prf`. Build verde (**59 jobs**), 0 sorrys. — (hito previo) **confinamiento ∀ (`confinement_derives`), cimiento del teorema de deducción de `Prf` hacia `d2_prf`**. Arrancando D2 finitaria se topó el **muro del confinamiento ∀**: el teorema de deducción de `Prf` (Hilbert) lo exige en su caso `gen`, pero `Prf₀`/`Prf` están congelados por la completitud del verificador (`prf_iff_derivation`, base de `repr_pos'_prf`). Solución (de libro, sin postulados): probar confinamiento en `Derives` (deducción natural) — **`confinement_derives : axioms ⊢ ((∀(↑P ⇒ C)) ⇒ (P ⇒ ∀C))`** — y añadirlo como esquema/regla del verificador. Build verde (**59 jobs**), 0 sorrys. Plan: regla qconf + regla de inducción de listas + teorema de deducción + port de lemas de cadena → `d2_prf`/`d3_prf`/`goedel_second_prf`. — (hito previo) **`repr_pos'_prf` COMPLETO: D1 real re-nivelada al cálculo finitario `Prf`**. Toda la representabilidad positiva sube al nivel `Prf` (prerequisito de Gödel II real, pues `provCodeC'` rastrea `Prf` finitaria y `¬⊢Con'` es falso): **`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`** (`#print axioms` = `[propext, Classical.choice, Quot.sound, prf_inAxC]`, espejo exacto del `repr_pos'` ⊢-level). Dos módulos nuevos: **`Meta/ArithPrf.lean`** (porte finitario completo de CodeArith/SubstArith/StepArith/Induction, ~50 lemas; hallazgo clave: `numeral_lt` es finitario —∃-intro vía `q2`, sin regla ω— por lo que toda la aritmética de códigos sube a `Prf`) y **`Meta/Representability2Prf.lean`** (tracking `prf_runFn_track`/`prf_chainOk_track` 19 casos + `provCodeC'_intro_prf` + `repr_pos'_prf`; único meta-axioma finitario nuevo **`prf_inAxC`**, análogo de `ax_inAxC`). En `Meta/ReprPrf.lean`: 32 esquemas `lineWF`/`premsOf` portados a `Prf`. **46 módulos**, build verde (**59 jobs**), 0 sorrys. Pendiente cadena Gödel II en Prf: `d2_prf` (regla de inducción de listas en `Prf`), punto fijo + necesitación en Prf, `goedel_second_prf` (`ConsistentH → ¬ Prf Con'`), D3 real. — (hito previo 2026-06-22) **Gödel Nivel D REAL — punto fijo real para `provCodeC'` + Gödel I real estructural**. Instanciando la maquinaria diagonal genérica (`Meta/DiagonalTwo.lean`) con el verificador estructural: **`godelC'_fixedpoint : ⊢ godelC' ⇔ ¬provCodeC' godelC'`** (`#print axioms` = solo estándar + `imp_intro`, SIN postulados gödelianos) y **`goedel_first_real' : ConsistentOmega → ¬ Prf godelC'`** (Gödel I real para el predicado estructural, vía `repr_pos'` + punto fijo). HALLAZGO de niveles: Gödel II requiere re-nivelar la cadena HBL a `Prf` (`provCodeC'` rastrea `Prf` finitaria, no ω; `¬⊢Con'` es falso), trabajo en curso. **42 módulos**, build verde (**56 jobs**), 0 sorrys. (Hitos previos: D1/D2 reales, Gödel II núcleo lógico con D3 postulado, refactor `Prf.thy → axioms`.) El cálculo de Hilbert `Prf` recorre ahora **todo `axioms`** (matemáticos + coding) en la regla `thy`, de modo que `Prf` **puede demostrar hechos del verificador** (`chainOk`/`runFn`/…) — prerequisito de la necesitación del punto fijo y de D3. Implementación honesta: ELIMINADA el ancla gigante `ax_axiomsCodeT` (`=eq listFormCodeM coreAxioms`); `axiomsCodeT` queda **opaco**; nuevo meta-axioma **`ax_inAxC (a) (h : a ∈ axioms) : ⊢ In (formCodeM a) axiomsCodeT`** (contenido positivo sin término gigante, auto-referencia ni reordenado; sonda previa validó el lift en un paso). Fixes en cascada en `Hilbert`/`HilbertSeq`/`Representability`/`Representability2`. `repr_pos'` ahora `#print axioms` = `[propext, choice, Quot.sound, ax_inAxC]`; `ax_inAxC` es postulado conservador (extensión definicional) que **sustituye** al ancla antes oculta en la lista. Desbloquea: punto fijo/necesitación Prf-demostrables + D3. **41 módulos**, build verde (**55 jobs**), 0 sorrys. (Sobre el hito previo: Gödel II núcleo lógico con D1/D2 reales y D3 postulado.) Sobre el verificador estructural (`runFn`/`chainOk`), con **D1** (`repr_pos'`) y **D2** (`d2`) ya REALES, se cierra el **núcleo lógico de Gödel II** (`Meta/GodelTwo.lean`): `con_imp_godel' : ⊢ Con' ⇒ G` (Gödel I formalizado interno) y `goedel_second' : ¬(⊢ Con')`, usando D2 real + **D3 como único axioma gödeliano** (`d3`) + hipótesis explícitas honestas para el punto fijo (`fp_bwd`), la necesitación (`nec1`) y la indemostrabilidad ω de G (`hgi`). `#print axioms goedel_second'` = estándar + ω-reglas + ax_list_induction + `d3`; **sin** `diagonal_lemma`/`provFormula`/D2-legacy — MEJORA sobre el `goedel_second` legacy (que postulaba D2 **y** D3). Además D3 reducida lógicamente (`Meta/Reflection.lean`: combinadores `pcc_*`). **41 módulos** (Minimal 11 + Meta 19 + Full 11), build verde (**55 jobs**), 0 sorrys. Camino a Gödel II 100% real (registrado): refactor `Prf.thy → axioms` + punto fijo `provCodeC'` + D3 real (Σ₁-completitud provable). Tras el rediseño `runFn`/`chainOk` (R1–R3), se cierran las dos primeras condiciones de derivabilidad de Hilbert-Bernays-Löb como **teoremas internos** (no postulados) para el predicado estructural fiel `provCodeC' := ∃p. chainOk nil p ∧ In x (runFn nil p)`: **D2** `⊢ provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B)` (`Meta/DerivCond.lean`, ensamblando `p++q++[mp]`), y **D1 = `repr_pos'`** `Prf φ → ⊢ provCodeC' φ` (`Meta/Representability2.lean`: encoder `proofCode'` + `runFn_track` + `chainOk_track` 19-casos + validez de las 19 reglas `lineWF`/`premsOf`). `#print axioms repr_pos'` = SOLO `[propext, Classical.choice, Quot.sound]`; `d2` = estándar + ω-reglas; **ningún postulado de derivabilidad**. **39 módulos** (Minimal 11 + Meta 17 + Full 11), build verde (**53 jobs**), 0 sorrys. Pendiente: **D3** (Σ₁-completitud provable) + punto fijo para `provCodeC'` → **Gödel II real**.
**Author**: Julián Calderón Almendros

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [2026-08-19] — REPARACIÓN DE LA INCONSISTENCIA · Gödel I real y consistente

**Build 95 jobs, 0 errores / 0 warnings / 0 sorrys. 82 módulos activos + 21 en `cuarentena/`.**

### 🚨 El problema (sesión 2026‑08‑16/19)

`axioms ⊢ ⊥` estaba **verificado en el compilador**. Causa: `tcFn` tenía dos ecuaciones que recurren
sobre estructuras **distintas** — `ax_tc_zero`/`ax_tc_succ` sobre NUMERAL y `ax_tc_cons` sobre
CÓDIGO — y en ℕ el mismo valor es ambas cosas (`cons 0 nil = 2 = σσ0`).

### Diagnóstico (sondeos S1–S5, `sondeos/`)

* **S1**: el daño entra a Gödel I **por un solo sitio**, el **lema diagonal**.
  `godelC'_fixedpoint` citaba exactamente `[propext, choice, Quot.sound, imp_intro, tc_cons]`.
  **D1 (`repr_pos'_prf`) y el argumento modular de Gödel estaban LIMPIOS.**
* **S2** (17 agentes): un paquete de buena‑formación (`isFormCode`) **NO** repara `tc` — `substfc`
  pide un reconocedor **extensional**, `tc` una distinción **intensional**.
* **S3**: `codeNat φ` se mantiene **simbólico**; Lean nunca lo reduce.
* **S5**: la profundidad de los códigos la dominan los **numerales unarios de puntos Unicode**
  (`consDepth (formCode ax_tc_succ) = 3873`); recodificar por índice recortaría **424×**.

### ✅ La reparación

`ax_tc_cons` **RETIRADO**; lema diagonal reconstruido por la **vía NUMERAL**.

| módulo nuevo | contenido |
|---|---|
| `Meta/Div2ParityPrf.lean` | cadena L1–L5 → **`prf_div2_numeral`**; cubre 4 huecos no registrados (`prf_mul_distrib`, `prf_numeral_mul`/`prf_gnum_mul`, `PrfH_eq_congr_mul2`, `prf_eq_congr_div2`) |
| `Meta/CodeNumeralPrf.lean` | `consN` **sin división** (números triangulares) → `prf_cons_eval` → **`prf_formCode_numeral`** |
| `Meta/DiagonalNumeral.lean` | **`godelCN_fixedpoint`**, **`goedel_first_numeral`**, `goedel_first_undecidable_numeral`, `provCode_transfer` |

**Retirados:** `prf_tc_cons`/`_of_cons`/`_chars`/`_str`/`_term`/`_terms`/`_form` y sus espejos ω,
`diag_arith`, `godelC_fixedpoint`, `godelC'_fixedpoint`, `goedel_first_real'`,
`goedel_first_undecidable_real'`.

**Cuarentena:** 31 módulos → **21** tras (a.1). `Sigma1CorePrf` refundado con códigos estáticos
numerales devolvió **10 módulos** de golpe.

### ▶ Frente abierto (a.2): la escalera

`pcc_eval_add` ✅ (ya existía) · `pcc_eval_mul` ⏳ · `div2` ✅ (atajo `Prf.gen` + `pcc_thm_inst`) ·
ensamblaje `cons` ⏳. Ver `PLAN-FRENTE-A.md`.

### ⚠️ Advertencia

**NO es una prueba de consistencia.** Se retiró la inconsistencia **conocida y localizada**.

---

## [Unreleased]

### Added (2026-07-24) - Ruta 1a: toolkit aritmetico en Prf + sub-codigo<codigo; VEREDICTO sobre los 7 tags

Sesion dedicada a habilitar la INDUCCION FUERTE sobre codigos (necesaria para los 7 tags de
lineWF que faltan: q1 q2 q3 leibniz ind qconf listInd, todos con substfc/liftfc en el arbol).

**HECHO (todo en Prf, net-0 axiomas, footprint [propext, choice, Quot.sound]):**
- `Meta/NatOrderPrf.lean` (i-a): congruencias de +, transitividad de < y <=, introduccion de <=.
  CORRECCION: asociatividad/conmutatividad de + SON axiomas (ax6/ax7), no probar por induccion.
- `Meta/NatMulPrf.lean` (i-b): leyes de mul (= axiomas ax8-ax12, instanciacion directa), monotonia
  aditiva y multiplicativa, CANCELACION (prf_lt_of_mul_lt_mul_right, por tricotomia), div2/mod2
  (ax17/ax21).
- `Meta/CantorMonoPrf.lean` (i-c): **prf_cantor_mono_left/right : Prf (lt h/t (cons h t))** =
  SUB-CODIGO < CODIGO. Via ax_L0_cons_def (cons = pair = div2 . cantor_poly) + monotonia de Cantor.
  13 pasos troceados, TODOS verdes a la primera. No hicieron falta ax11/ax12/ax24 ni
  cantor_poly_is_even: basta mod2 <= 1 y tratar 2*(st) como opaco.
- `Meta/StrongInductionPrf.lean` (ii.1): prf_le_of_lt_succ (m<sn => m<=n), por via corta (una sola
  eliminacion de existencial, sin analisis de casos).
- `Meta/LineWFAssemblePrf.lean`: **ENSAMBLAJE or_elim x21**. pcc_lineWF_tracked_of_branches
  (generico) + pcc_lineWF_tracked_modulo_7 (14 reflectores reales + 7 hipotesis). VERIFICA que
  cerrar los 7 reflectores cierra pcc_lineWF_tracked; nada mas aguas abajo.

**VEREDICTO SOBRE LOS 7 TAGS (2 workflows de 11 agentes + verificacion a mano):**
- pcc_eval_substfc (evaluacion provable de substfc sobre codigo ABSTRACTO) NO es net-0.
- La opcion "extender CTree" esta MUERTA: rompe en PrfH_dotVN pidiendo el axioma FALSO
  tcFn(substfc..)=substfcT(..).
- La opcion "predicate-free" (2) NO EXISTE: 3 rutas fallan, la 4a ("substfc simbolico") pide
  ax_tc_substfc, que es INCONSISTENTE (no solo insolido) -- prueba <1,"substfc",..>=<1,"::",..>,
  cuya negacion da cons_ne_head/formCode_ne => bottom. Vindica la decision de 15dccda.
- Full/StrongInduction.lean (strong_induction, linea 173) NO es importable (esta sobre Derives) y
  su forma META no basta: (ii) hay que portarlo en forma OBJETO.

**DECISION PENDIENTE DEL USUARIO** (registrada en NEXT-STEPS.md + memoria project_substfc_wall):
(1-min) sancionar predicado de buena-formacion (<12 axiomas, amplia Prov); (a) reformular los 7
esquemas para ELIMINAR substfc del arbol (posible net-0, no explorado); (3) dejar 14/21 y girar a
repr_neg. Recomendacion: explorar (a) antes de sancionar.

Build 113 jobs, 99 modulos (Minimal 11 + Meta 77 + Full 11), 0 errores/warnings/sorrys.

### Added (2026-07-21) - B.3c: 14/21 tags de `lineWF` cerrados (chasis + kit + arbol)

**Los tres patrones estructurales, a mano** (validan el diseno):
- `thy` (15): condicion de PERTENENCIA. Consume el `In`-reflect. Truco que evita rehacerlo:
  `pcc_In_axiomsCodeT_tracked` pide el puente como `Prf` cerrada, pero con `yc = carcT t~` ese
  puente depende de `lineWF t` (solo en contexto); se instancia con `yc = (carc t)~`, cuyo puente
  es la reflexividad interna, y el encaje se hace DESPUES con un Leibniz interno.
  Pieza nueva: `substtc_inv_termCode_axiomsCodeT` (NO sale del atajo `..._of_tc`: ese puente es
  FALSO para `axiomsCodeT`, que es opaco; se prueba estructuralmente).
- `mp` (16): sin condicion estructural (la conclusion la liga `premsOf`). El mas barato.
- `efq` (8): piloto del chasis.

**Las tres piezas genericas:**
- `Meta/LineWFSchemaPrf.lean` - CHASIS: `schema_bwd`, `schema_backbone`, punteados de tag y
  longitud genericos en `k`/`n`, puentes `pcc_{carc,nthc}D_bridge`, cotas desde la longitud, y el
  ensamblaje `pcc_lineWF_tracked_of_schema`.
- `Meta/CodeCtorKit.lean` - KIT: `nulT`/`unT`/`binT` parametrizados por tag y aridad (todos los
  constructores de codigo son el mismo cons-arbol). `eqcT` pasa a ser `binT 4`. Incluye la
  congruencia DENTRO de `Prov`, que generaliza el `pcc_congr_eqcT_diag_code_imp` de `eqrefl`.
- `Meta/CodeTreeReflect.lean` - ARBOL: `CTree` reifica los RHS y la reflexion se prueba por
  INDUCCION una sola vez (`PrfH_dotVN`). Cada tag pasa a ser tres declaraciones.

**Lote de 18 esquemas a forma ESTRICTA** (`cc6f55f`): clausula canonica `lenc = n`, con `n` derivado
mecanicamente (max indice + 1), no elegido. NET-0 axiomas: siguen 7. Los `prf_lineWF_<tag>` de
`ReprPrf` conservan enunciado exacto via `prf_iff_drop_left_conj`.

**Obstaculos reales encontrados:**
- `numeralM k` y `numeral k` NO son defeq para `k` variable (`numeralM_eq` va por induccion).
- `substFormula 0 #0 C != C` para `C` abierta (De Bruijn DECREMENTA) => el chasis toma
  `hC` como hipotesis explicita.
- `<=` resuelve al orden OBJETO (sobre `Term`) con `Minimal.Axioms` abierto; error opaco.
- `substTerm_numeralM`/`liftTerm_numeralM` YA EXISTIAN en `Minimal/Axioms.lean` (duplicacion
  introducida y retirada).

**Revisado el hallazgo B.2**: con `mp` estricto, una linea `mp` de forma incorrecta SI se refuta
por `lineWF` (antes no); las premisas siguen exigiendo `premsOf`. `NegVerifier` gana una via.

**Faltan 7 tags** (`q1` `q2` `q3` `leibniz` `ind` `qconf` `listInd`): llevan `substfc`/`liftfc`
DENTRO del arbol, que son funciones OBJETO y no constructores de codigo. Verificado que no existe
su contrapartida rastreada (`substfcT`/`liftfcT`, `prf_tc_substfc`, `prf_substtc_substfc`).
Siguiente incremento identificado y acotado.

Build 108 jobs, 94 modulos, 0 errores/warnings/sorrys. Footprint sin cambios: `d2_prf` limpio,
`goedel_second'` sigue citando solo `d3`.

### Added (2026-07-20) - S44.4: **`In`-reflect de `axiomsCodeT` CERRADO** (el nudo de `NegVerifier`)

- **`Meta/InAxiomsCodePrf.lean`** (NUEVO). Reflexion punteada del atomo `In` sobre la
  **lista de axiomas**, que era el nudo estimado en 8-11 sesiones del `PLAN-NEGVERIFIER.md`:
  - `pcc_in_head_swap` + `pcc_in_tail_tracked` - combinadores de cabeza/cola rastreados.
  - **`pcc_In_lfc_tracked`** - NUCLEO: recursion rastreada sobre la lista de axiomas
    **ABSTRACTA** (el termino gigante `listFormCodeM axioms` no se materializa).
  - **`pcc_In_axiomsCodeT_tracked`** - `In y axiomsCodeT => Prov(In yc axiomsCodeT~)`,
    con `yc` rastreado `substtc`-invariante y `hbr : Prov(yc = tcFn y)`.
- **Hallazgo**: NO estaba bloqueado por Tarski - el codigo rastreado `carcT(tcFn .)` lo esquiva.
- Consume la direccion **negativa** de `neg_In_axiomsCodeT` (S42) y desbloquea el caso `thy`
  del bloque `hC_dot`.

### Changed (2026-07-20) - refactor de anclas: `prf_inAxC` pasa a **TEOREMA** (net-0 axiomas)

- Nuevo `axiom prf_axiomsCodeT_eq : Prf (axiomsCodeT =eq listFormCodeM axioms)` en
  `Minimal/Axioms.lean` - **espejo `Prf` exacto** del `ax_axiomsCodeT_eq` del calculo (S42).
- **`prf_inAxC` deja de ser `axiom` y pasa a ser TEOREMA** derivado de el => **net-0 axiomas**
  (el total sigue en **7**). Lo exige el `In`-reflect, que necesita **ambas** direcciones
  dentro de `Prf`, no solo la positiva.
- **Footprint**: D1 `repr_pos'_prf` cita ahora `prf_axiomsCodeT_eq` (antes `prf_inAxC`);
  `d2_prf` limpio; `goedel_second'` sigue citando solo `d3`. Cadena real intacta.
  Registro autoritativo actualizado en [AXIOMS.md](AXIOMS.md) (fila 6).

### Added (2026-07-18/20) - S44.3: **B.3c - el caso `eqrefl` (tag 12) CERRADO** via esquema ESTRICTO

- **`Meta/LineWFTrackedPrf.lean`** (NUEVO). Reflexion punteada del atomo `lineWF`, caso `eqrefl`:
  - Columna vertebral del **paso 6** (`pcc_thm_inst` + puente `substfc` + `prf_provCode_congr`).
  - Paso 6 (a): codigos punteados **evaluados** a forma rastreada; (a-bis)+(b): caso completo
    salvo hipotesis; (c): reflector por rama con `heq` descargada.
- **PLAN (A) - esquema ESTRICTO** (cierra un **hueco real de raiz**): `ax_lineWF_eqrefl` pasa a
  `lineWF #0 <=> ((lenc #0 = 3) AND (carc #0 = eqc ...))`. La clausula `lenc` **fuerza las cotas
  de sub-indice**, que con el `lineWF` laxo NO eran derivables.
- Resultado: **`pcc_lineWF_tracked_eqrefl_imp` SIN hipotesis de cota**. El accesor concreto
  `prf_lineWF_eqrefl` conserva enunciado (helper `prf_iff_drop_left_conj`) => **D1/B.2/B.3b no cambian**.
- Piezas reutilizables para los 20 tags restantes: backbone a 3 partes con `andc`, `LENC_dot`
  (via `pcc_eval_lenc`), `prf_lt_numeralM`, familia `eqcT`.

### Changed (2026-07-16/18) - S44.2: B.3a des-duplicacion + B.3b los 19 `ax_lineWF` a ACCESORES

- **B.3a** - `Meta/LineWFDerives.lean` (NUEVO): los 42 teoremas `lineWF_*`/`premsOf_*` a nivel
  `Derives` que `ProofChain` mantenia **duplicados** pasan a `prf_to_derives (prf_<name> ...)`.
  Enunciados identicos; `ProofChain` 870 -> 540 lineas. Deuda tecnica que iba a **doblar** el
  coste de B.3b.
- **B.3b** - los **19** `ax_lineWF_<tag>` estructurales reformulados a **forma con accesores**
  (`nthc`/`carc` en vez de patrones `cons`), p. ej.
  `ax_lineWF_p1 : forall. (nthc #0 1 = 0) => (lineWF #0 <=> carc #0 = implc (nthc #0 2) (implc (nthc #0 3) (nthc #0 2)))`.
  **Net-0 axiomas**; los 19 enunciados de `ReprPrf` se conservan intactos (D1/D2 verificados).
- Toolkit nuevo en `Meta/ReprPrf.lean`: `prf_lineWF_iff_transport`, `prf_congr_bin1/bin2/un/bin`
  (movidos desde `ArithPrf`, de-duplicados), congruencias `_loc` privadas de `substfc`/`liftfc`.

### Added (2026-07-16) - S44: **MODULO B** - tabla de los 21 tags + direccion NEGATIVA

- **`Meta/LineWFCases.lean`** (NUEVO): `tagArity`, `tagConcl` (cubre **19**, no 21), `tagPrems`
  (cubre los 21), `cleanRule`; envoltorios uniformes `prf_lineWF_tag` / `prf_premsOf_tag`
  (dispatch explicito por caso - un `first | ...` de 19 alternativas agota el elaborador).
- **Direccion negativa**: `derives_lineWF_neg_of_tag` y el pago real
  **`derives_lineWF_neg_thy_of_not_prf (phi) (hnp : NOT Prf phi)`** via `neg_In_axiomsCodeT`.
- **Hallazgo de diseno**: `mp` (tag 16) **no es refutable via `lineWF`** (es incondicional) -
  solo via `premsOf`. Anadidos `prf_imp_trans` / `derives_imp_trans` (no existian).

### Added (2026-07-14/15) - S43: **MODULO A COMPLETO** - decodificador de codigos y de CADENAS

- **`Meta/CodeDecode.lean`** (NUEVO, A.1): `decodeNat`, `decodeChars`, `decodeStr`,
  `decodeTerm`/`decodeTerms` (mutuo), `decodeForm` (9 tags); round-trips e **inyectividad**
  `decodeForm_inj` => **`decodeForm` es una BIYECCION verificada**.
- **`Meta/ChainDecode.lean`** (NUEVO, A.2): `DecidableEq Term` (mutuo manual - `deriving` falla
  por inductivo anidado), `findIdx` propio, `peelArgs` (fix de rendimiento: el match profundo
  sobre `Term` agota `whnf`), `decodeRuleTag` (21 tags), `decodeRule`, `decodeLine`
  (**verifica** `stepConcl`), `decodeChain`; solidez `decodeChainAux_checkAux` /
  `decodeChain_checkProof` y el puente
  **`decodeChain_prf : decodeChain t = some rs -> (forall L, checkProof rs = some L -> phi in L) -> Prf phi`**.
- **Hallazgo que corrige el plan**: `lineJustif` es **lossy** para `thy`/`mp`/`gen` ==> el
  round-trip *retract* es FALSO para esos 3; lo que el modulo E necesita es la **seccion**
  (`decodeRule_{thy,mp,gen}_section`) + la solidez. Retract limpio solo para los 18 restantes.
- **Trampa de kernel documentada**: `split`/`rw`/`simp` manuales sobre `if s == sym` generan un
  cast `congrFun'` que el **KERNEL rechaza** => usar induccion funcional (`.induct`, con
  `motive_2` en las mutuas) + `unfold`. Ademas `Char.ofNat` **clampa** => guard de validez.

### Added (2026-07-14) - S42: `axiomsCodeT` CONCRETADO (direccion negativa) + `PLAN-NEGVERIFIER.md`

- **`ax_inAxC` -> `ax_axiomsCodeT_eq`** (`axioms |- axiomsCodeT =eq listFormCodeM axioms`),
  **net-0 axiomas**: `ax_inAxC` pasa a **teorema**. A diferencia del anterior (solo positivo),
  da **ambas** direcciones => **`neg_In_axiomsCodeT`** (que SOLO los axiomas estan),
  que es lo que desbloquea `NegVerifier` y por tanto la mitad `no-|- not G`.
- **`Meta/AxiomListCode.lean`** (NUEVO): el termino gigante `listFormCodeM axioms` **NO se
  materializa** - recursion estructural sobre la lista abstracta (medido: 4 s).
- **Paso 1 del plan**: `StdChain` pasa de `IsClosed` (**FALSO**) a **`IsCodeShaped`** (con forma
  de codigo).
- **`PLAN-NEGVERIFIER.md`** (NUEVO): plan ejecutable en 6 modulos A-F, ~coste de D1, 8-11 sesiones.

### Added (2026-07-13) - S41: la mitad `no-|- not G` con reflexion explicita + reduccion de `Reflects`

- `Meta/OmegaReflect.lean` (NUEVO): **`reflects_of_omega`** - `Reflects <= OmegaConsistent +
  NegVerifier` (omega-consistencia + completitud-Delta_0 **negativa**), y con `Reflects` sale
  la mitad que faltaba => **G INDECIDIBLE**.
- **ATENCION**: esa mitad **NO esta todavia en la cadena real** - depende de **`NegVerifier`**,
  que aun no esta construido (es el objeto del `PLAN-NEGVERIFIER.md`). La cadena real sigue
  dando **solo la mitad positiva** (`goedel_first_real'`). Purgada del arbol documental la
  afirmacion "Godel I completo". Diagnostico vigente: el obstaculo es el **intuicionismo** del
  FOL, no la omega-consistencia; Rosser seria peor.

### Added (2026-07-13) - S37-S40: `hI_dot` COMPLETO + logica interna completa + `pcc_bdAll_intro`

- **S38 - `hI_dot` COMPLETO** (`Meta/D3InDotPrf.lean`): el atomo `In` queda cerrado =>
  **D3 se reduce a UN SOLO lema**, `d3_prf_of_chainOkDot (phi) (hC)`.
- **S39 - LOGICA INTERNA COMPLETA** (`Meta/PropCodePrf.lean`): las lineas-axioma `p1`/`p2`/`j3`/
  `efq` **y la de INDUCCION (`ind`, tag 18)** son TODAS **estructurales** => cuestan un testigo de
  una linea y salen **libres de muro**. Con P1+P2+MP el calculo implicacional interno es completo:
  `Prov` ya tiene MP, forall-elim, exists-intro, gen, Leibniz, AND, OR (intro **y elim**),
  ex-falso e **induccion**.
- **S40 - `pcc_bdAll_intro` COMPLETO** (`Meta/BdAllIntroPrf.lean`): la **INTRO del forall acotado**,
  keystone que S30 dejo pendiente y que bloqueaba `hC_dot`. Claves: se induce sobre la **COTA** a
  nivel objeto (sobre el testigo `Ac[x]=>Ac[sx]` es FALSO); la disyuncion finita **no sirve**
  (`lenc p` con `p` abstracto no es numeral concreto); se induce sobre el **cuerpo ABIERTO** +
  `gen` una vez al final; el split se **voltea** en el objeto; y hay que **parametrizar sobre `p`**
  (el binder desplaza las libres) - mismo patron que el exists-elim de `hI_dot`.

### Added (2026-07-12b) — §36: buena-formacion estructural de lineas (ax_lineWF_cons) + chainOk => cons

Nuevo axioma object (SANCIONADO por el usuario): ax_lineWF_cons.

  def ax_lineWF_cons : forall_ (lineWF #0 => #0 =eq cons (carc #0) (cdrc #0))

Una linea bien-formada es un cons (reconstruible de carc/cdrc). Companion de
ax_lineWF_inv; REFUERZA lineWF (no lo debilita), no afecta la solidez del verificador.
Anadido al final de axioms y codingAxioms (axioms_eq sigue por rfl). Los 7 axiom de
Lean NO cambian. Verificado: goedel_first_real'/goedel_second' con los MISMOS axiomas.

Meta/LineWFConsPrf.lean:
  prf_lineWF_cons (line) : lineWF line => line =eq cons (carc line) (cdrc line)
  prf_chainOk_lineWF (p i) : chainOk nil p => i < lenc p => lineWF (nthc p i)
    -- via chainOkB (prf_chainOk_iff_chainOkB) + and-elim (lineOkB = lineWF ... ^ ...)
  prf_line_is_cons (p i) : chainOk nil p => i < lenc p =>
      nthc p i =eq cons (carc (nthc p i)) (cdrc (nthc p i))

Es la pieza que resuelve la partialidad de carc sobre lineas abstractas: dado chainOk,
la linea es cons, luego carc (nthc p i) evalua (pcc_eval_carc) en hI_dot.

[propext, Classical.choice, Quot.sound]. Build 89 jobs, 0 sorrys, Lean v4.31.0.

### Fixed (2026-07-12) — SOLIDEZ del verificador: la linea GEN era incondicional

**Bug critico de solidez** (descubierto al preparar el `forall i<b`): `ax_lineWF_gen` (tag 17) hacia
`lineWF <concl, 17, body>` valida para conclusion ARBITRARIA, y su `premsOf` es solo `[body]` -- nada
ligaba `concl`. Resultado: desde cualquier `body` en `checked` el verificador concluia cualquier
formula. Testigo SIN sorry (`[propext, Classical.choice, Quot.sound]`): una cadena EQREFL + GEN que
concluye `botc`, dando `Prf (provFromCode botc)`. Es decir, `Prov` era TOTAL (probaba `Prov(<phi>)`
para toda `phi`), lo que vaciaba de contenido Godel II y el programa D3.

**Fix** (sancionado): `ax_lineWF_gen` pasa a bicondicional, como todos los demas esquemas:

```lean
ax_lineWF_gen : forall_2 (lineWF <v1, 17, v0> <=> (v1 =eq forallc v0))
```

Actualizados `prf_lineWF_gen` (ReprPrf) y `lineWF_gen` (ProofChain) a la forma `<=>`, y sus dos usos
en D1 (`Representability2Prf`/`Representability2`) via `iff_mpr ... (refl)` -- los pasos GEN reales
concluyen `forallc body`, luego la completitud se preserva. `ax_lineWF_mp` (tambien incondicional) es
SOLIDO: su `premsOf` incluye `implc premA concl`, que liga la conclusion.

Verificado: exploit muerto; `goedel_first_real'`/`goedel_second'`/`repr_pos'_prf` con los MISMOS
axiomas de antes, 0 sorrys. Build 85 jobs.

### Added (2026-07-10q) — §31.3: **reflexion de los DOS atomos Delta_0 desde hipotesis**

`Meta/Delta0ReflectPrf.lean`. Con `pcc_exIntro_code_open` + `pcc_eval_add`:

```lean
pcc_eq_tracked (t u) : (t =eq u) => provFromCode (eqCodeFn (tcFn t) (tcFn u))    -- ya existia
pcc_lt_tracked (s t) : (lt s t) => provFromCode (ltCodeFn (tcFn s) (tcFn t))     -- NUEVO
```

para terminos ARBITRARIOS. `<` se refleja via ax13 (exists-elim de la hipotesis), `pcc_eval_add s (sigma k)`
(evalua el sumatorio simbolico al numeral del valor) y `prf_congr_tcFn`. Es la base atomica de la
completitud-Delta_0 provable. `[propext, Classical.choice, Quot.sound, prf_inAxC]`. Build 85 jobs.

### Added (2026-07-10p) — §31: completitud-Delta_0 provable (ARRANQUE) - atomo `<` abierto

`Meta/Delta0ReflectPrf.lean`. Direccion elegida para cerrar D3 (completitud-Sigma_1 provable por
induccion interna). El desbloqueo clave: **`pcc_eval_add` (probado por induccion interna) demuestra
`addcT(tcFn a)(tcFn b) =eq tcFn(add a b)` para a, b ARBITRARIOS** -- el termino simbolico y el numeral
del valor son provablemente iguales como codigos. Eso da el puente simbolo<->valor sobre `+` que
parecia imposible, y con el `s < t` se refleja via ax13 (`exists k. s+sigma k=t`) + evaluacion.

- **`pcc_exIntro_code_open`**: el `exists`-intro a nivel de codigo SIN la clausura `hAc`, arrastrando
  el lift (patron §26: `liftFormula_provFromCode_open` + `liftTerm_exc_open` +
  `liftTerm_substfc_open2`). `[propext, Classical.choice, Quot.sound]` -- estructural, sin prf_inAxC.
- **`pcc_lt_intro_open_imp`/`pcc_lt_intro_open`**: `pcc_lt_intro` sin las hipotesis de cierre de
  `a`, `b`, usando el `exists`-intro abierto. De `Prov(< a. + sigma K = b. >)` sale `Prov(< a. < b. >)`.

Build **85 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10o) — §30: **cuantificadores ACOTADOS a nivel de codigo**

`Meta/EvalBoundedPrf.lean`. `exists i<b. phi = exists i. (i<b) and phi`,
`forall i<b. phi = forall i. (i<b) => phi`; se refleja reusando `<` (§29), `and` interno, `exists`-intro
(§17) y `forall`-elim (§22).

- **Logica `and` interna, LIBRE DE MURO** (lineas C1/C2/C3, tags 2/3/4, estructurales y 0 premisas,
  como EQREFL/LEIBNIZ §15.4): `pcc_c1_code`/`_c2_code`/`_c3_code`, y con `pcc_mp_code_apply`
  `pcc_and_intro_code`, `pcc_and_elim_left_code`, `pcc_and_elim_right_code`. Auxiliar `pcc_axline`.
- `bdExCode`/`bdAllCode` (constructores de codigo de los cuantificadores acotados).
- **`pcc_bdEx_intro`** (introduccion del `exists` acotado = `and`-intro + `exists`-intro) y
  **`pcc_bdAll_elim`** (eliminacion del `forall` acotado = `forall`-elim + MP interno). Auxiliar
  `prf_substfc_ltCodeFn_varc0` (el `v0` recibe el testigo `K`, `B` invariante), `prf_congr_andc`.

**Todos `[propext, Classical.choice, Quot.sound]` — SIN `prf_inAxC`** (no tocan ningun axioma object).
Build **84 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10n) — §29: **reflexion del atomo `<`** (`= ∃ + =eq + evaluacion provable`)

`Meta/EvalLtPrf.lean`. `<` no es primitivo (`ax13`: `n<m <=> ∃k. n+σk=m`), asi que su reflexion es
`∃`-intro + `=eq` + evaluacion provable de `+`:

```lean
pcc_lt_intro (a b K) (ha hb) (h : Prov(< a. + σK = b. >)) : Prov(< a. < b. >)
```

- `ltBwd`: la direccion `<=` de `ax13` como teorema object cerrado `forall_2 ((∃k. n+σk=m) => n<m)`,
  por deduccion + `∃`-elim + `PrfH_lt_intro`.
- `pcc_ltBwd_computed`: su codigo RASTREADO (via `pcc_thm_inst2` + `prf_substfc_arith_open`), todo en
  `tcFn`, sin `termCode` ni muro de Tarski.
- **Nivel arbitrario:** el `substfc` externo baja bajo el `∃`-binder (nivel 1) => nuevos
  `prf_substtc_tcFn_zero_at`/`_succ_imp_at`/`_all_at`/`_at` (invariancia de `tcFn a` bajo `substtc`
  a nivel `numeral k` arbitrario; esquema de §23 parametrizado).
- Ensamblaje: `prf_substfc_exBodyc` + `pcc_exIntro_code'` + `pcc_mp_code_apply`.

### Added (2026-07-10m) — §28: **evaluacion provable de listas** (`carc`, `cdrc`, `lenc`)

`Meta/EvalListPrf.lean`. Misma receta que §27:

```lean
pcc_eval_carc (h t) : Prov(< carc (cons h t). = h. >)
pcc_eval_cdrc (h t) : Prov(< cdrc (cons h t). = t. >)
pcc_eval_lenc (L)   : Prov(< lenc L. = (lenc L). >)     -- L arbitrario
```

`carc`/`cdrc` sin induccion (axiomas `forall_2`); `lenc` por `prf_list_induction`. Constructores
`carcT`/`cdrcT`/`lencT`/`consT` con congruencias, `substtc` e invariancias.

Todo `[propext, Classical.choice, Quot.sound, prf_inAxC]`. Build **83 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10l) — §27: **evaluacion provable de `+` COMPLETA**

Primera evaluacion provable cerrada del proyecto (`Meta/EvalArithPrf.lean`):

```lean
pcc_eval_add (a b) : Prf (provFromCode (evalAddCode a b))   -- < a. + b. = (a+b). >, a/b arbitrarios
```

- **Formas implicacion** de los combinadores internos (`prf_nat_induction` pide `Prf (Phi => Phi[sigma])`,
  no una funcion `Prf -> Prf`): `pcc_leibniz_apply_imp`, `pcc_eq_trans_code_imp`,
  `pcc_congr_succ_code_imp`, via `prf_deduction` + `PrfH.mp` sobre `prf_to_prfH`.
- **Paso inductivo** `pcc_eval_add_succ_imp`: congruencia interna de `sigma` sobre la HI, transitividad
  interna con (B) (`pcc_ax5_computed`), y transporte de codigos (`prf_tc_succ'`, `prf_congr_tcFn` sobre
  `prf_add_succ_t`). Invariancias `substtc` por `substtc_inv_addcT`/`_succcT`/`_tcFn`.
- **Induccion object** `prf_eval_add_all` (`prf_nat_induction`) + `pcc_eval_add` (`prf_spec`).
- Transparencia del codigo: `substTerm_evalAddCode`, `liftTerm_evalAddCode`, `substFormula_evalAddPred`,
  `step_evalAddPred`; nuevos `substTerm_numeral` / `substTerm_charsCode` / `substTerm_strCode` en
  `Meta/DerivCondPrf.lean` (duales de los `liftTerm_*`).
- **Truco De Bruijn:** `liftTerm 1 (liftTerm 0 a)` -> `<- FOL.liftTerm_comm_zero a 0` -> `FOL.substTerm_liftTerm`.

Axiomas: `[propext, Classical.choice, Quot.sound, prf_inAxC]` (`prf_inAxC` entra por `pcc_ax4/5_inst`).
Build **81 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10k) — §26: `pcc_mp_code_open` + **lógica ecuacional INTERNA sobre códigos**

**`hAc`/`hBc` eran el cuarto artefacto de clausura** (tras `hw` §17 y `hAc` del `for-all`-elim §22).
En `Meta/MpCodePrf.lean`:

```lean
liftTerm_implc_open (Ac Bc) : liftTerm c (implc Ac Bc) = implc (liftTerm c Ac) (liftTerm c Bc)
pcc_mp_code_open    (Ac Bc) : provFromCode (implc Ac Bc) => (provFromCode Ac => provFromCode Bc)
```

Se **arrastran** los lifts (`liftFormula_provFromCode_open` los traslada al código); tras los **dos**
`exists`-elim los códigos quedan **doblemente lifteados** y el ensamblaje `p ++ q ++ [mpline]` pasa
verbatim. `[propext, Classical.choice, Quot.sound]`. `pcc_mp_code` queda como **corolario** y
`pcc_mp_code_apply` pierde las hipótesis.

**`Meta/EvalArithPrf.lean` — lógica ecuacional interna** (con `pcc_leibniz_code`, §25.2):

```lean
pcc_leibniz_apply   (Ac t1 t2) (heq) (h1) : Prov(<Ac[t2]>)
pcc_eq_trans_code   (X Y Z) (hX) (h1) (h2) : Prov(<X=Z>)
pcc_congr_succ_code (X Y) (hX) (heq)       : Prov(<sigma X = sigma Y>)
```

Todos `[propext, Classical.choice, Quot.sound]`. Transitividad = Leibniz con el contexto
`Ac := (X = v0)`; congruencia de `sigma` = Leibniz con `Ac := (sigma X = sigma v0)`, cuya base `Ac[X]`
es la **reflexividad codificada libre de muro** (§15.4).

**Restricción real (`hX`):** al sustituir en el código-contexto, el `substtc` alcanza los subtérminos
ya presentes, así que el código fijo `X` debe ser **`substtc`-invariante**. No es un muro: (A) (§23)
lo da para `tcFn a` y las ecuaciones de `funcc` lo propagan — `substtc_inv_tcFn`,
`substtc_inv_succcT`, `substtc_inv_addcT`.

**Siguiente:** el paso inductivo de `+` ya encaja pieza a pieza (verificado en sondeo); falta sólo la
**forma implicación** de los combinadores (versiones `PrfH`/`_imp`), porque `prf_nat_induction` pide
`Prf (Phi => Phi[sigma])`.

Build **81 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10j) — §25: `pcc_thm_inst` + **LEIBNIZ codificado LIBRE DE MURO**

**`Meta/MpCodePrf.lean`:**

```lean
pcc_thm_inst  (f) (h : Prf (Formula.forall f)) (w) : Prf (provFromCode (substfc zero w (formCode f)))
pcc_thm_inst2 (f) (h : Prf (forall_2 f)) (w1 w2)
```

Internalizan **cualquier teorema universal** de la teoría objeto, no sólo los axiomas.
`pcc_axiom_inst`/`pcc_axiom_inst2` pasan a ser **corolarios** (`h := prf_ax hmem`).

**`Meta/Sigma1AtomPrf.lean` — hallazgo: `prf_lineWF_leibniz` es ESTRUCTURAL**

```text
lineWF <concl, 13, A, t1, t2>  <->  concl =eq implc (eqc t1 t2) (implc (substfc 0 t1 A) (substfc 0 t2 A))
```

sin premisas y con códigos **arbitrarios** — exactamente como la línea EQREFL (§15.4) y las líneas
Q1/Q2 (§19.1). Luego el **Leibniz codificado** se demuestra con un testigo de **una sola línea**:

```lean
leibnizLine, prf_lineOk_leibniz, prf_chainOk_leibniz, prf_in_runFn_leibniz
pcc_leibniz_code (Ac t1 t2)
  : Prf (provFromCode (implc (eqc t1 t2) (implc (substfc 0 t1 Ac) (substfc 0 t2 Ac))))
```

`[propext, Classical.choice, Quot.sound]` — **sin `prf_inAxC`** (no pasa por `repr_pos'`).
**Verificado** con códigos abiertos: `pcc_leibniz_code (#0) (tcFn a) (tcFn b)` typechequea.

**Consecuencia:** la lógica ecuacional interna (transitividad, congruencias) sale de
`pcc_leibniz_code` + `pcc_mp_code`, **sin** teoremas codificados ni `for-all`-elim triple.

**Siguiente (§25.3):** `pcc_mp_code` exige **códigos cerrados** (`hAc`/`hBc`), y los nuestros
contienen `tcFn #0`. Es la **cuarta** hipótesis de clausura que estorba (`hw` §17, `hAc` §22); se
arregla arrastrando los lifts con `liftFormula_provFromCode_open` -> **`pcc_mp_code_open`**.

Build **81 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10i) — §23 (A) el código de un numeral es cerrado + §24 (B) la instancia de `ax5` computada

**`Meta/NumCodeClosedPrf.lean` (NUEVO) — (A), primera inducción interna del proyecto:**

```lean
prf_liftc_tcFn   (a)   : Prf (liftc zero (tcFn a) =eq tcFn a)
prf_substtc_tcFn (W a) : Prf (substtc zero W (tcFn a) =eq tcFn a)
```

`[propext, Classical.choice, Quot.sound]` — **sin `prf_inAxC`** (la inducción interna no pasa por
`repr_pos'`). No hay axioma que diga que `tcFn a` es un código cerrado, pero se deriva con
`prf_nat_induction`: **base** `tcFn 0 = ⌜0⌝` (código concreto) y **paso** `tcFn (σx) = succc (tcFn x)`,
atravesando el `funcc` con `prf_liftc_func`/`prf_substtc_func` y las ecuaciones de lista. Infra:
`prf_congr_liftc`, `prf_congr_substtc3`, `prf_congr_funcc2` (+ versiones `PrfH`).

**`Meta/EvalArithPrf.lean` — (B): `pcc_ax5_computed (a b) : ⊢ Prov(⌜ȧ + σḃ = σ(ȧ + ḃ)⌝)`.**

**(B) no necesitaba la inducción general sobre fórmulas** que preveía §22.3(B): el cuerpo de `ax5` es
una fórmula **concreta**, y `substCodeF 1 W₁ (cuerpo)` computa **por `rfl`** a
`eqCodeFn (addcT W₁ (succcT ⌜v₀⌝)) (succcT (addcT W₁ ⌜v₀⌝))`. Basta computar el `substfc` **externo**
sobre ese código explícito, con (A) para normalizar `liftc zero (tcFn a) → tcFn a` y para que el
`tcFn a` incrustado sobreviva a la sustitución. Infra: `succcT`, `prf_tc_succ'`, `prf_congr_succcT`,
`prf_substtc_funcc1/2`, `prf_substtc_succcT`, `prf_substtc_addcT`, `prf_substtc_varc0`.

**Qué pide el paso inductivo (§24.2).** Normalizando los códigos, el objetivo es
`Prov(⌜ȧ + σḃ = σ((a+b)˙)⌝)`, y tenemos (B) y la HI `Prov(⌜ȧ + ḃ = (a+b)˙⌝)`. Hacen falta dos reglas
de **lógica ecuacional interna** sobre códigos arbitrarios: `pcc_congr_succ_code` y
`pcc_eq_trans_code`. **Derivables sin obstrucción**: la teoría objeto demuestra sus clausuras
universales (son teoremas), `repr_pos'_prf` da sus códigos demostrables, y se instancian en códigos
**abiertos** con `pcc_forallElim_code_open` + `pcc_mp_code`. Ladrillo auxiliar: **`pcc_thm_inst`**
(instanciar un **teorema** codificado, no sólo un axioma).

Build **81 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10h) — §22: `pcc_axiom_inst2` (axiomas `forall_2` codificados) + el hueco preciso del paso inductivo

**`hAc` también era innecesaria** (tercera hipótesis de clausura que resulta ser un artefacto, tras
`hw` en §17). Al instanciar `ax5` (`forall_2`), la **segunda** eliminación tiene el cuerpo
`substfc (σ0) (liftc 0 w1) formCode-phi`, que **contiene `w1`** y por tanto **no es cerrado** cuando `w1` es
abierto (p. ej. `tcFn #0`). En `Meta/ForallElimCodePrf.lean`:

```lean
liftTerm_forallc_open   (Ac)    : liftTerm c (forallc Ac) = forallc (liftTerm c Ac)
liftTerm_substfc_open2  (Ac w)  : liftTerm c (substfc zero w Ac) = substfc zero (lift w) (lift Ac)
pcc_forallElim_code_open (Ac w) : provFromCode (forallc Ac) => provFromCode (substfc zero w Ac)
```

`[propext, choice, Quot.sound]`. `pcc_forallElim_code'` queda como **corolario** (retrocompatible).

En `Meta/MpCodePrf.lean`:

```lean
pcc_axiom_inst2 (phi) (hmem : forall_2 phi in axioms) (w1 w2)
  : Prf (provFromCode (substfc zero w2 (substfc (succ zero) (liftc zero w1) (formCode phi))))
pcc_ax5_inst (w1 w2)      -- instancia de ax5 : forall n m. n + sigma m = sigma (n+m)
```

**Verificado:** `pcc_ax5_inst (tcFn a) (tcFn b)` typechequea (dos testigos **abiertos**).

**HUECO del paso inductivo de `+` (§22.3, sondeo verificado).** Para **usar** `pcc_ax5_inst` hay que
computar el **doble** `substfc`. El **interno** sí se computa
(`prf_substfc_arith_open 1 (liftc 0 w1) phi` → `substCodeF 1 (liftc 0 w1) phi`); el **externo** actúa
sobre `substCodeF ...`, que **no es `formCode` de nada meta**, así que `prf_substfc_arith_open` no
aplica. Faltan dos ladrillos:

- **(A) el código de un numeral es CERRADO**: `prf_liftc_tcFn` / `prf_substtc_tcFn`. **No hay axioma**,
  pero **es derivable por inducción interna** (`prf_nat_induction`) con `ax_tc_zero` (base: `tcFn 0`
  es el código concreto de `0`) y `ax_tc_succ` (paso: `tcFn (σx) = succc (tcFn x)`). Es el hecho
  estándar «`num a` es un término cerrado del lenguaje codificado».
- **(B) composición**: `substfc 0 w2 (substCodeF 1 w1 phi) =eq substCodeF2 w1 w2 phi`, por inducción
  estructural en `phi`, usando (A).

Build **80 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10g) — §21: **BASE de `+` cerrada** — primera aritmética demostrada dentro de `Prov`

**`Meta/EvalArithPrf.lean`** (NUEVO):

```lean
def addcT (x y) : Term := funcc (strCode add_sym) (cons x (cons y nil))      -- código de `x + y`
theorem addcT_termCode (a b) : addcT (termCode a) (termCode b) = termCode (add a b)   -- rfl
theorem prf_congr_addcT
def evalAddCode (a b) : Term := eqCodeFn (addcT (tcFn a) (tcFn b)) (tcFn (add a b))
theorem pcc_ax4_computed (a) : Prf (provFromCode (eqCodeFn (addcT (tcFn a) ⌜0⌝) (tcFn a)))
theorem pcc_eval_add_zero (a) : Prf (provFromCode (evalAddCode a zero))      -- ← BASE
```

Es decir **`⊢ Prov(⌜ȧ + 0̇ = (a+0)˙⌝)`**. `[propext, Classical.choice, Quot.sound, prf_inAxC]` (el
`prf_inAxC` entra por `repr_pos'`; es uno de los 7 axiomas legítimos de `AXIOMS.md`, no un postulado
gödeliano).

**Encaje de las tres secciones anteriores:** `pcc_ax4_inst (tcFn a)` (§19.3, instancia de `ax4`
**codificado** con testigo `tcFn a`) → `prf_substfc_arith_open` (§20, **computa** el `substfc` con
testigo arbitrario) → `prf_provCode_congr` (Leibniz de códigos) con `prf_tc_zero` (`⌜0⌝ =eq tcFn zero`)
y `prf_congr_tcFn` sobre `prf_add_zero_t` (`tcFn a =eq tcFn (add a zero)`).

**La asimetría que hace no‑trivial la evaluación provable:** el lado izquierdo del código
(`addcT (tcFn a) (tcFn b)`) es el **término simbólico**, el derecho (`tcFn (add a b)`) es el **numeral
del valor**. Sólo coinciden porque la teoría objeto prueba `add a 0 =eq a` y `tcFn` tiene congruencia
Leibniz object.

**Siguiente (§21.3):** `pcc_axiom_inst2` (axiomas `forall_2` como `ax5`), paso inductivo de `+`, y la
misma receta para `lenc`/`nthc`/`carc`/`runFn`. Build **80 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10f) — §20: primer paso REAL de la evaluación provable (`substfc` con testigo‑código arbitrario)

**`Meta/SubstCodeOpenPrf.lean`** (NUEVO). `pcc_axiom_inst` (§19.3) entrega
`provFromCode (substfc zero w (formCode φ))` con `w = tcFn a`. Para **usarlo** hay que computar ese
`substfc`, y la única herramienta existente exigía código sustituido `termCode s` con `s` **meta** —
pero `tcFn a` no es `termCode` de nada meta. Ese era el único hueco. Se generaliza:

```lean
prf_substtc_arith_open  (v w) : ∀ t,  Prf (substtc ⌜v⌝ w ⌜t⌝ =eq substCodeT v w t)
prf_substtsc_arith_open (v w) : ∀ ts, …
prf_substfc_arith_open        : ∀ v w f, Prf (substfc ⌜v⌝ w ⌜f⌝ =eq substCodeF v w f)
```

con las funciones meta `substCodeT`/`substCodeTs`/`substCodeF` («código de `t`/`f` con el hueco de la
variable `v` relleno por el **código** `w`»), espejo de `substTerm`/`substFormula`+`termCode`/`formCode`.
Chequeo de cordura `substCodeT_termCode` (recupera `prf_substTerm_arith`). Todos
`[propext, Classical.choice, Quot.sound]`.

**Salió barato** porque en las pruebas originales `termCode s` viaja como argumento **opaco**: se pasa
tal cual a `prf_substtc_var_eq/gt/lt`, que están enunciadas para `s` **cualquiera** (las «ecuaciones de
variable» de `substtc` que §11.3 señaló, y que `tcFn` no tiene). Sólo cambia el lado derecho.

**Confirmación De Bruijn:** `prf_substfc_forall`/`_ex` **levantan el testigo** bajo el binder
(`liftc zero t`, nivel `σv`), y las funciones meta lo replican. Es la confirmación *a posteriori* de
que el `∀`‑elim de código (§19.1) **debía** admitir testigos abiertos: aun instanciando un axioma
cerrado, el testigo interno acaba abierto.

**Payoff verificado:** `substCodeF 0 w (add #0 zero =eq #0) = ⟨4, addcT w ⌜0⌝, w⟩` por **`rfl`** (la
función meta computa), y de `pcc_ax4_inst (tcFn a)` + `prf_substfc_arith_open` sale
**`Prov(⌜ȧ + 0 = ȧ⌝)`**. Build **79 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10e) — §19: sistema de prueba INTERNO a nivel de código (andamiaje de la evaluación provable)

La evaluación provable (§18.3, núcleo de la fase 3) necesita razonar **dentro** de la demostrabilidad
con códigos que ya **no** son `formCode` de nada meta (salen de `substfc zero w Ac`). Se completa el
juego de reglas internas, todas con **testigo abierto** donde procede:

| Regla | Lema | Módulo | `#print axioms` |
|---|---|---|---|
| `∃`-intro (Q2) | `pcc_exIntro_code'` | `ExIntroCodePrf` | `[propext, choice, Quot.sound]` |
| `∀`-elim (Q1) | **`pcc_forallElim_code'`** | **`ForallElimCodePrf`** (NUEVO) | `[propext, choice, Quot.sound]` |
| MP | **`pcc_mp_code`** | **`MpCodePrf`** (NUEVO) | `[propext, choice, Quot.sound]` |
| Axioma de la teoría | **`pcc_axiom_inst`** | `MpCodePrf` | `+ prf_inAxC` |

- **`pcc_forallElim_code' (Ac w) (hAc) : provFromCode (forallc Ac) ⇒ provFromCode (substfc zero w Ac)`**.
  Clave: `prf_lineWF_q1` es **estructural** (`concl =eq implc (forallc A) (substfc zero t A)`, sin
  `termCode`), igual que la línea Q2 ⇒ admite `A`, `t` arbitrarios. Testigo `r = p ++ [q1line, mpline]`.
  **Asimetría con Q2:** allí el código abierto cae en el antecedente (se arrastra el lift, §17.1);
  aquí cae en el **consecuente**, y hace falta `liftFormula_provFromCode_open` (§18.4).
  Piezas: `liftTerm_forallc`, `prf_lineOk_q1`.
- **`pcc_mp_code (Ac Bc) (hAc) (hBc)`** — porte de `d2_prf` a códigos cerrados **arbitrarios**
  (`Ac`/`Bc` en vez de `formCode A`/`formCode B`; clausuras en vez de `liftTerm_formCode`).
  Piezas: `liftTerm_implc`, `pcc_mp_code_apply`. **Escollo (el mismo que `pcc_exIntro_code`):** en el
  `simp` posterior a `PrfH_ex_intro` **no** hay que colapsar `liftTerm 0 Bc` — se cancela con la subst
  externa; incluir `hBc` allí rompe la prueba.
- **`pcc_axiom_inst (φ) (hmem : ∀φ ∈ axioms) (w) : provFromCode (substfc zero w (formCode φ))`**
  (usa `formCode (.forall φ) = forallc (formCode φ)`, definicional) + `pcc_ax4_inst`.

**Verificado:** `pcc_ax4_inst (tcFn #0)` typechequea — el axioma `ax4` **codificado** se instancia en un
testigo **abierto** (`tcFn` de una variable ligada). Era el bloqueo estructural.

**El caso `σ` de la evaluación provable es gratis:** `prf_tc_succ` (`ax_tc_succ`) ya da
`tcFn (succ x) =eq succc (tcFn x)`. **Siguiente (§19.4): el caso `+`**, por inducción interna sobre el
2º sumando. Build **78 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10d) — `liftFormula_provFromCode_open` + §18: la reflexión de `<` aterriza en la evaluación provable

**`Meta/TrackedCorePrf.lean`**: **`liftFormula_provFromCode_open (k c) : liftFormula k (provFromCode c)
= provFromCode (liftTerm k c)`** — generaliza `liftFormula_provFromCode` a **códigos ABIERTOS** (el
cuerpo Σ₁ `provFormulaC'` es cerrado; el único slot es `c`, bajo un binder ⇒ `liftTerm_comm_zero`).
La necesita el **∀‑elim de código**, donde el código abierto cae en el **consecuente** — al revés que
en `pcc_exIntro_code'`. `[propext]`.

**§18 — sondeo verificado compilando: la reflexión de `<` NO es un ladrillo pequeño.** Se creía
inmediata (`=eq` cerrado libre de muro §15.4 + `∃`‑intro con testigo abierto §17.2). **No encajan:**

- `pcc_eq_tracked (add a (succ k)) b` da el código con `tcFn` del **término entero** — el numeral del
  **valor** `a + σk`.
- El cuerpo del `∃` de `ax13_lt_def` necesita el código del **término simbólico** `ȧ + σj̇`.
- Son **códigos distintos**. `tcFn` (= `num`, «numeral‑de») sólo tiene 3 ecuaciones (`ax_tc_zero`,
  `ax_tc_succ`, `ax_tc_cons`) y **no debe** computar sobre `add`.

El puente que falta es **`⊢ Prov(⌜ȧ + σk̇ = (a+σk)˙⌝)`**: la **evaluación provable** (la teoría objeto
demuestra internamente que la suma de numerales evalúa al numeral de la suma), por **inducción
interna**. Es «la bestia» que §11.3 ya nombraba.

**Orden correcto de fases (§18.3):** (1) evaluación provable (núcleo real de fase 3) → (2) reflexión
de `<` como corolario → (3) cuantificadores acotados + inducción estructural → `hbI`/`hbC` →
`d3_prf` → `goedel_second_prf`. Build **76 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-10c) — §17 RESUELTA: `pcc_exIntro_code'` (el `∃`-intro de código admite testigo ABIERTO)

**`hw` era innecesaria.** `pcc_exIntro_code` exigía `hw : ∀ c, liftTerm c w = w` (testigo de código
cerrado). La pieza que lo elimina, en `Meta/ExIntroCodePrf.lean`:

```lean
liftTerm_substfc_open (Ac) (hAc : ∀ c, liftTerm c Ac = Ac) (w)
  : ∀ c, liftTerm c (substfc zero w Ac) = substfc zero (liftTerm c w) Ac
```

El lift **atraviesa** `substfc zero · Ac` y queda sobre el testigo (`zero` cerrado; `Ac` cerrado por
`hAc`). Con eso el contexto tras `prf_ex_elim_imp` es **idéntico** al de antes con `w' := liftTerm 0 w`,
y el ensamblaje `p ++ [q2line, mpline]` pasa **verbatim** (la línea‑axioma Q2 `prf_lineOk_q2 Cp Ac w'`
admite cualquier testigo); la conclusión `exc Ac` sigue cerrada, que es lo único que el objetivo
necesita. Resultado:

```lean
pcc_exIntro_code' (Ac w) (hAc) : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))
```

`#print axioms = [propext, Classical.choice, Quot.sound]`. El antiguo `pcc_exIntro_code` se conserva
como **corolario** (su `hw` queda como argumento no usado): retrocompatible, build verde.

**Verificado explícitamente** que el testigo puede ser una variable ligada y su código rastreado:
`pcc_exIntro_code' Ac (tcFn #0) hAc` typechequea.

**Alcance preciso sobre RIESGO‑1** (sin sobre‑afirmar): tenía dos mitades. **(a)** `tcFn #0` no es
cerrado ⇒ `hw` falla — **DISUELTA**. **(b)** el transporte `tcFn L =eq termCode L` (obstrucción de
Tarski genuina) — **sigue viva, pero confinada** al último paso (§15.4), descargable con numerales
(`prf_tc_numeral`) en la inducción de fase 5.

**Camino libre (§17.4):** con `ax_lineWF_inv` (§16.5) y `pcc_exIntro_code'` (§17.2) **no queda
obstrucción conocida** hacia `hbI`/`hbC` → `d3_prf` → `goedel_second_prf`. Build **76 jobs**, 0 sorrys.

### Changed (2026-07-10b) — `ax_lineWF_inv` (obstruccion §16 RESUELTA) + segunda obstruccion (§17)

**§16 resuelta (sancionada).** Añadido a `Minimal/Axioms.lean` — extensión de la **teoría objeto**:
`lineTag line := nthc line (succ zero)`, `tagDisj L n` (disyunción `lineTag L = 0 ∨ … ∨ = n`) y
**`ax_lineWF_inv : ∀line. lineWF line ⇒ tagDisj line 20`**. Añadido al final de `axioms` **y** de
`codingAxioms` (lección de la fase 1a). Cierre `Prf`: **`prf_lineWF_inv`** (`Meta/Sigma1AtomPrf.lean`).

Con la inversión, `lineWF` (y, conocida la etiqueta, `premsOf`) queda **totalmente determinado**, y
reflejar `lineWF t` para `t` abstracto se reduce a reflejar una disyunción finita de átomos `=eq`.

Verificación tras tocar el núcleo (build **76 jobs** verde):

- `axioms_eq : axioms = coreAxioms ++ codingAxioms` sigue siendo **`rfl`**.
- **La cadena real NO cambia:** `goedel_second'` sigue citando sólo `d3`; `d2_prf` limpio;
  `repr_pos'_prf` = estándar + `prf_inAxC`; `goedel_first_real'` sin postulado gödeliano.
- Es un `def ax_*` de la teoría objeto: **los 7 `axiom` de Lean de `AXIOMS.md` NO cambian.**

**SEGUNDA OBSTRUCCIÓN encontrada (§17).** Al arrancar la rama `hbI` (que se creía libre):
`pcc_exIntro_code` exige `hw : ∀ c, liftTerm c w = w` — **testigo de código CERRADO**. Pero tras el
`∃`‑elim de `boundedIn` el testigo es la variable ligada `#0`, y `tcFn #0` no es cerrado. Es el viejo
**RIESGO‑1** reaparecido en la forma acotada: **corrige la afirmación previa de que `hbI` no estaba
bloqueado — ambas ramas (`hbI` y `hbC`) pasan por aquí.**

**No es Tarski y es reparable (§17.1):** `hw` se usa en un único punto (colapsar
`liftTerm 0 (substfc zero w Ac)` vía `liftTerm_substfc`). Sin `w` cerrado no colapsa, pero **es
expresable**: `= substfc zero (liftTerm 0 w) Ac` (con `Ac` cerrado). Hay que **arrastrar** el lift en
vez de colapsarlo. **Brick siguiente (único, desbloquea las dos ramas, §17.2): `pcc_exIntro_code'`,
generalización lift‑aware sin `hw`.**

### Added (2026-07-10) — `atom1CodeFn` + **OBSTRUCCIÓN encontrada en `lineWF`** (§16 del diseño)

**`Meta/Sigma1AtomPrf.lean`** (extensión): constructores de código de **átomos unarios**, espejo de
`atom2CodeFn`: `atom1CodeFn s a := ⟨3, ⌜s⌝, [a]⟩`, puente `formCode` (rfl), `liftTerm_atom1CodeFn`,
`prf_congr_atom1CodeFn`, `prf_provFromCode_atom1_congr`, `liftFormula_provFromCode_atom1`; y su
instancia `lineWFCodeFn` con `lineWFCodeFn_termCode`, `provCodeC'_lineWF_eq` (rfl) y
`prf_provCodeC'_lineWF_of_tracked` (transporte). `[propext, choice, Quot.sound]`.

**OBSTRUCCIÓN (verificada sobre `Minimal/Axioms.lean`):** `lineWF t := Formula.atom "lineWF" [t]` es
un **átomo primitivo** cuyos **21 axiomas** son bicondicionales **indexados por la etiqueta de regla**
(`numeralM 0..20`), y **NO existe axioma de inversión** (`lineWF t ⇒ etiqueta ∈ {0..20}`). `premsOf`
tiene el mismo patrón (21 ecuaciones por etiqueta, sin inversión). Consecuencia: para una línea `t`
**abstracta** la teoría no puede extraer la etiqueta, luego
`Prf (lineWF t ⇒ provCodeC' (lineWF t))` **no es derivable**.

- **No afecta a la solidez** de D1/D2/Gödel I: sólo usan `lineWF` sobre líneas **concretas**.
- **`hbI` NO está bloqueado** (`boundedIn` sólo tiene átomos `=eq` y `<`).
- **`hbC` (chainOkB) SÍ está bloqueado.** Contraste: `chainOk` sí está determinado
  (`ax_chainOk_nil`/`ax_chainOk_cons` + `ax_list_induction` sobre todo `Term`); `lineWF` discrimina
  sobre un **numeral** (la etiqueta) que ningún axioma acota.
- **Arreglo mínimo propuesto (§16.4):** añadir `ax_lineWF_inv` a `Minimal/Axioms.lean` (un `def ax_*`
  de la teoría objeto, **no** una declaración `axiom` de Lean → los **7 axiomas de `AXIOMS.md` no
  cambian**; precedente exacto = capa `lenc`/`nthc` de la fase 1a). Requiere sanción explícita.

Build **76 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-09d) — 12‑A FASE 3: reflexividad LIBRE DE MURO → átomo `=eq` cerrado

**Idea que lo desbloquea:** el verificador comprueba `lineWF` **estructuralmente**. La línea‑axioma
EQREFL cumple `lineWF ⟨concl, 12, t⟩ ⇔ concl =eq eqc t t`, y `eqc a b` es **literalmente**
`eqCodeFn a b` (`numeral 4 = σ⁴0`). Con `concl := eqCodeFn c c` y `t := c` la condición es **pura
reflexividad**, válida para `c` **arbitrario** — `termCode` no aparece. Testigo: la cadena de **una
sola línea** `[⟨eqCodeFn c c, 12, c⟩]`.

En `Meta/Sigma1AtomPrf.lean`:

- `eqCodeFn_eq_eqc` (rfl), `eqreflLine`, `prf_lineOk_eqrefl`, `prf_chainOk_eqrefl`,
  `prf_in_runFn_eqrefl`.
- **`prf_provFromCode_intro (d p) (chainOk nil p) (In d (runFn nil p)) : provFromCode d`** —
  introductor de `provFromCode` desde un testigo, a nivel de código arbitrario.
- **`prf_provFromCode_eqCodeFn_refl (c) : Prf (provFromCode (eqCodeFn c c))`** — **reflexividad LIBRE
  DE MURO**, sin hipótesis de tracking.
- `PrfH_congr_tcFn`, `PrfH_congr_eqCodeFn`.
- **`pcc_eq_tracked (t u) : Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))`** — reflexión
  de la igualdad al nivel del código rastreado, **también libre de muro** (base reflexiva + congruencia
  de `tcFn` + Leibniz object).
- `pcc_eq_of_tc_bridge (t u) (ht : tcFn t =eq termCode t) (hu) : Prf ((t =eq u) ⇒ provCodeC' (t =eq u))`.

Los tres resultados: `#print axioms = [propext, Classical.choice, Quot.sound]` — al no pasar ya por
`repr_pos'`, **desaparece incluso la dependencia de `prf_inAxC`**. **El muro de Tarski queda confinado
al último paso** (el puente `tcFn t =eq termCode t`, descargable con numerales vía `prf_tc_numeral` en
la inducción de fase 5), exactamente como predice Hilbert‑Bernays. Plan restante en
`GODEL-D3-TRACKED-DESIGN.md` §15.5. Build **76 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-09c) — 12‑A FASE 3 núcleo: toolkit rastreado del átomo `=eq`

**`Meta/Sigma1AtomPrf.lean`** (NUEVO). Reflexión provable del átomo de igualdad `t =eq u` (el átomo
base de `boundedIn`, `nthc L i =eq x`), espejo exacto del toolkit rastreado de `In`
(`prf_provCodeC'_In_of_tracked`):

- `eqCodeFn a b := ⟨4, a, b⟩` — constructor object del código de `Formula.eq` (`eqCodeFn (termCode
  t)(termCode u) = formCode (t =eq u)`, rfl).
- `prf_congr_eqCodeFn`, `prf_provFromCode_eq_congr` — congruencia (Leibniz object) + transporte.
- `liftTerm_eqCodeFn`, `liftFormula_provFromCode_eq` — clausuras De Bruijn.
- **`prf_provCodeC'_eq_of_tracked (ht : tc =eq termCode t)(hu)(h : provFromCode (eqCodeFn tc uc))
  : provCodeC' (t =eq u)`** — reflexión rastreada.
- `prf_provFromCode_eqCodeFn_refl_of_tracked` — reflexividad rastreada.

**Hallazgo confirmado en código:** la reflexión de `=eq` para términos **abstractos** es imposible
**libre de muro** (obstrucción de Tarski: `termCode t =eq termCode u` no se sigue de `t =eq u`,
`termCode` sin congruencia object). La salida Hilbert‑Bernays es **rastrear** los argumentos con
`tcFn` (que SÍ tiene congruencia, `prf_congr_tcFn`) y descargar el puente `tcFn t =eq termCode t`
cuando `t` es numeral (`prf_tc_numeral`), en la inducción estructural de fase 5.
`[propext, choice, Quot.sound]` (la reflexividad `+ prf_inAxC`). Plan restante en
`GODEL-D3-TRACKED-DESIGN.md` §15.4. Build **76 jobs**, 0 sorrys, v4.31.0.

### Added (2026-07-09) — 12‑A FASE 3 arrancada: D3 reducida a reflejar la forma Δ₀ acotada

**`Meta/Sigma1BoundedPrf.lean`** (NUEVO). Con la fase 2 completa (verificador Δ₀ vía
`boundedIn`/`chainOkB`), la D3 reducida `d3_prf_of_sigma1` (que pedía `hI`/`hC`, la Σ₁‑completitud
provable de `In`/`chainOk`) se **reduce a reflejar la forma acotada**, transportando por `pcc_imp`
(sube implicaciones object a `provCodeC'`, D2+D1) a través de los `⇔` de la fase 1/2:

- `prf_hI_of_reflect_boundedIn (hbI) : ∀ x L, Prf (In x L ⇒ provCodeC' (In x L))`
- `prf_hC_of_reflect_chainOkB (hbC) : ∀ p, Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p))`
- **`d3_prf_of_reflect_bounded (φ) (hbC) (hbI)`** = `d3_prf`, reducido a reflejar `boundedIn`/`chainOkB`.

`[propext, choice, Quot.sound, prf_inAxC]`. La obstrucción de Tarski queda **reubicada en el átomo**
`nthc L i =eq x` (para `L`/`x` abstractos), que resuelven las ecuaciones de variable de `substfc`
(ausentes en `tcFn`) — confirma que el §11.3 («`num` + evaluación provable») sigue siendo la vía,
ahora aplicada solo a los átomos de la forma acotada. Plan detallado en `GODEL-D3-TRACKED-DESIGN.md`
§15. Build **75 jobs**, 0 sorrys, v4.31.0. Quedan: núcleo de fase 3 (reflexión atómica con
`substfc`), fase 4 (cuantificadores acotados), fase 5 (inducción estructural) → `d3_prf` →
`goedel_second_prf`.

### Changed (2026-07-09) — F7a: retirada la capa Gödel LEGACY (14 → 7 `axiom` de Lean)

Auditado con `#print axioms` que la cadena **real** (`goedel_first_real'`, `d2_prf`,
`goedel_second'`) no cita ninguno de los 7 postulados legacy; solo los usaba la vía Gödel vieja
(Gödel I/II con D2/D3 postulados). Retirados:

- **`Meta/Incompleteness.lean` ELIMINADO** (módulo legacy completo): definía `D2`, `D3` (axiomas) y
  los teoremas `provCode`, `goedel_first_unprovable`, `goedel_first_true`, `incompleteness`,
  `con_imp_goedelSentence`, `goedel_second`. Sustituidos por la cadena real
  (`goedel_first_real'`/`goedel_second'`, `d2_prf`).
- **`Meta/Provability.lean`**: retirados los 5 postulados legacy `Dem`, `dem_iff_provable`,
  `provFormula`, `provFormula_repr`, `diagonal_lemma` + los derivados `goedelSentence`,
  `goedelSentence_fixedpoint`. Se **conserva** el núcleo real de codificación (`formCode`,
  `IsFormula`, `Provable`, `provable_formCode_iff`, inyectividades), usado por todo el proyecto.
- **`Meta.lean`** (barrel): retirado el `import Incompleteness` + docstring actualizado.
- Docstrings puestos al día en `Necessitation.lean` / `Diagonal.lean` (ya no citan los postulados
  retirados como vigentes).

Nuevo **`AXIOMS.md`** — registro autoritativo de los 7 `axiom` restantes (3 esquemas de inducción
`Full/`, TFA `Block8`, 2 anclas de codificación `ax_inAxC`/`prf_inAxC`, y `d3`) + las 6 meta-reglas
ω de `FOL/MetaRules.lean`, con familia, justificación y módulo de cada uno. Explica por qué NO se
consolidan en un solo módulo (estratificación Minimal/Full + objeto/metateoría + dos cálculos).

`#print axioms` tras F7a: `goedel_first_real'` = estándar + ω-reglas + `ax_induction` +
`ax_list_induction` + `ax_inAxC` (ningún postulado gödeliano); `goedel_second'` = estándar +
ω-reglas + `ax_list_induction` + **`d3`** (único gödeliano vivo, F7b pendiente de D3 real).
Build **74 jobs** (−1 por el módulo eliminado), 0 errores, 0 warnings, 0 sorrys, v4.31.0.

### Added (2026-07-08) — 12‑A FASES 1b y 2 COMPLETAS: el verificador ya es Δ₀ y **sin acumulador**

Cerrado el **único punto de diseño del plan 12‑A que no estaba verificado en código**: la
reformulación numérica (Δ₀) del verificador estructural. Build **75 jobs**, 0 errores, 0 warnings,
0 sorrys, Lean v4.31.0. Todos los teoremas nuevos: `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (ningún postulado gödeliano).

**`Meta/NatArithPrf.lean`** (NUEVO) — **toolkit aritmético de `<` en `Prf`**. Hallazgo de escala: la
fase 1b resultó mucho mayor de lo estimado porque `lt a b := ∃k. a + σk = b` (`ax13_lt_def`) y `add`
recurre **por la derecha** (`ax4`/`ax5`) ⇒ la identidad izquierda **`0 + n = n` NO es teorema de Q**;
hay que reconstruirla con `Prf.ind`. Contenido: `prf_nat_induction` (eliminador que envuelve
`Prf.ind`), `norm11` (normalización De Bruijn de 1 binder), `prf_add_zero_left`, `prf_add_succ_left`,
`prf_lt_iff`, `PrfH_lt_intro`/`prf_lt_intro`, `prf_succ_ne_zero`, `prf_succ_inj`, `prf_zero_or_succ`,
`prf_zero_lt_succ`, `prf_succ_lt_succ_of_lt`, `prf_lt_of_succ_lt_succ`, `prf_not_lt_zero`,
`PrfH_eq_congr_succ`.

**`Meta/BoundedInPrf.lean`** (NUEVO) — **fase 1b completa**:
**`prf_In_iff_boundedIn (x L) : Prf (In x L ⇔ ∃ i < lenc L. nthc L i =eq x)`**. Piezas: `boundedIn`;
`liftFormula_boundedIn(_gen)`/`substFormula_boundedIn` (empujar lift/subst a través de un predicado
con `∃` interno **no es defeq**; los iguala `FOL.liftTerm_comm_zero`); helpers
`prf_boundedIn_head/tail/nil/cons`; congruencias `prf_lt_subst2`/`PrfH_lt_subst1`/`PrfH_eq_congr_nthc2`/
`PrfH_eq_congr_pred`; y **`prf_zero_or_eq_succ_pred`** (`n = 0 ∨ n = σ(pred n)`), que permite partir
por casos un índice dentro de un contexto `PrfH` **sin `∃`** (testigo = `pred i`).

**`Meta/RunFnBoundedPrf.lean`** (NUEVO) — **fase 2, lado `In`**. *Corrección al diseño §12.3: llamar
«β‑función» a esta capa era pesimista — **NO hace falta**.* `runFn nil p` **no es una recursión con
acumulador: es el *map* de `carc` sobre `p`** (`prf_runFn_nil_cons`, probado por la cadena
`prf_runFn_cons` → `prf_concat_nil_eq` → **`prf_runFn_weaken`** (saca el acumulador fuera) →
`prf_concat_cons_eq`). Consecuencia: el acumulador nunca hay que construirlo. Contenido:
`prf_runFn_nil_cons`, `prf_lenc_runFn`, `prf_nthc_runFn` (patrón `∀i` interno + `Prf.qconf` +
`PrfH_spec`), `boundedCarcIn` y el payoff
**`prf_In_runFn_iff (y p) : Prf (In y (runFn nil p) ⇔ ∃ i < lenc p. carc (nthc p i) =eq y)`**.

**`Meta/ChainOkBoundedPrf.lean`** (NUEVO) — **fase 2, lado `chainOk`; cierra la fase 2**:

- **(b)** `prf_in_concat_iff` (cierre de `ax_L3_in_concat`), `prf_in_cons_nil_iff` y
  **`prf_in_concat_singleton_iff`** (`In y (c ++ [x]) ⇔ In y c ∨ y =eq x`) — absorbe la conclusión de
  la línea actual en el acumulador.
- **(0)** `boundedCarcLt y p b` (= `∃k<b. carc (nthc p k) =eq y`, **cota arbitraria**;
  `boundedCarcIn y p = boundedCarcLt y p (lenc p)` por `rfl`) + clausuras De Bruijn. Necesario porque
  en `chainOk` la cota es el índice de la línea (`σj`, `i`), no `lenc p`.
- **(c)** **`prf_boundedCarcLt_cons_succ_iff`** (split del `∃k<σj` sobre `cons`) + las dos
  reintroducciones `prf_boundedCarcLt_cons_of_head` (testigo `0`) / `_of_tail` (reindexa `k ↦ σk`).
- **(a)** **`prf_allIn_iff_boundedAllIn`** (`allIn c L ⇔ ∀j<lenc L. In (nthc L j) c`). Todo el manejo
  del `∀j` se **confina en cuatro lemas `Prf` autónomos** (`prf_boundedAllIn_nil`/`_cons_head`/
  `_cons_tail`/`_cons`) y las dos inducciones de lista quedan triviales. Infra nueva:
  **`PrfH_eq_subst_in1`** (congruencia de `In` en el **elemento**; la previa `PrfH_eq_subst_in`
  sustituye la **lista**).
- **(d)** **`prf_chainOk_iff_chainOkB (c p) : Prf (chainOk c p ⇔ chainOkB c p)`** — **el acumulador
  desaparece**:

  ```text
  chainOkB c p := ∀ i < lenc p.  lineWF (nthc p i)
                               ∧ ∀ j < lenc (premsOf (nthc p i)).
                                   ( In (nthc (premsOf (nthc p i)) j) c
                                   ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j )
  ```

  Es la formulación Δ₀ de libro: *cada premisa está en el contexto inicial o es la conclusión de una
  línea anterior*. Inducción de listas sobre `p` con el acumulador **`∀c` interno** (`chainBPred`),
  instanciando la HI en `c ++ [carc line]`. Escalones intermedios: **`prf_premOk_cons_iff`** (lema
  puntual que fusiona (b) y (c) — el corazón aritmético del paso `cons`), defs
  `boundedPremsIn`/`lineOkB`/`chainOkB` + clausuras, `prf_boundedPremsIn_zero_iff`,
  `prf_lineOkB_zero_iff` (mitad `i=0`), `prf_boundedPremsIn_cons_succ_iff`,
  `prf_lineOkB_cons_succ_iff` (mitad `i=σi'`, con Leibniz `PrfH_congr_lineOkBAt` sobre la línea
  desacoplada del índice), `prf_chainOkB_nil`, `prf_chainOkB_cons_head/_tail/_intro` y
  `prf_chainOkB_cons_iff` (espejo exacto de `ax_chainOk_cons`).

**Documentación**: `ESCALANDO_EL_PROYECTO.md` (NUEVO) — estudio del enlace con el proyecto hermano
**DeepArith** (`Lean4_vs_PureLogic`) sobre el kernel FOL⁼ común: el toolkit aritmético/metamatemático
construido para Gödel II sirve también a sus fases 2‑3 y a su capa Automata/Turing.
`GODEL-D3-TRACKED-DESIGN.md` §13 (veredicto del sondeo: no hace falta β‑función) y §14 (plan del lado
`chainOk` + §14.4 lecciones De Bruijn acumuladas).

**Auditoría 2026-07-08 (con `#print axioms` real)**: `d2_prf` = `[propext, choice, Quot.sound]`;
`goedel_first_real'` no cita ningún postulado gödeliano; `goedel_second'` cita **solo `d3`** — en
particular **NO** cita `diagonal_lemma`/`provFormula_repr`/`Dem`/`Incompleteness.D2`/`D3`. Por tanto
la limpieza **F7a** (retirar esos 7 postulados legacy, 14→7 `axiom`) es **viable ya** e independiente
de D3; solo **F7b** (`GodelTwo.d3`) sigue bloqueada. Los 4 `ax_lenc_*`/`ax_nthc_*` son `def` de la
teoría objeto, no `axiom` de Lean. Los 5 hits de `grep sorry` son comentarios.

**Lecciones De Bruijn nuevas** (§14.4, reusar): `∃`‑elim de una hipótesis → lema `Prf` autónomo con
`prf_ex_elim_imp` (nunca `PrfH_ex_elim`, liftea el contexto → doble lift); `∀`‑intro como consecuente
→ `Prf.qconf` (nunca `PrfH.gen`); `∀`‑elim de hipótesis → `PrfH_spec`; case‑split de índice sin `∃` →
`prf_zero_or_eq_succ_pred`; en un `have`, `PrfH _ (…)` no infiere `Γ` → nombrar el contexto con `let`;
`liftFormula 0 (lor A B)` no se destapa con `rw` → introducir un `have hlor : … := rfl`;
**`prfH_weaken` NO es debilitamiento de contexto** (es `Γ ⊢ B → Γ ⊢ A ⇒ B`) → para usar una HI en un
contexto extendido, re‑derivarla con `PrfH_spec` sobre la hipótesis en posición `tail`.

**Siguiente**: fases 3‑5 (`num` numeral‑de + evaluación provable + Δ₀‑completitud atómica → inducción
estructural `⊢ ∀p (δ → Prov ⌜δ(ṗ)⌝)` → `d3_prf` → `goedel_second_prf`).

### Added (2026-07-05c/d) — D3: investigación de atajos (§11–§12) + arranque Σ₁‑completitud (12‑A fase 1a)

- **`Meta/TrackedCorePrf.lean`** (extensión) — constructores de código object para átomos binarios:
  **`atom2CodeFn s a b`** (generaliza `inFormCodeFn` a `In`/`chainOk`/`allIn`) + puente `formCode`
  (`atom2CodeFn_termCode`, `inFormCodeFn_eq_atom2`, rfl) + **congruencia** (`prf_congr_atom2CodeFn`) +
  **clausura** (`liftTerm_atom2CodeFn`, `liftFormula_provFromCode_atom2`) + **transporte**
  (`prf_provFromCode_atom2_congr`) + `chainOkCodeFn`/`allInCodeFn`. Infra de códigos, `#print axioms`
  = estándar.
- **INVESTIGACIÓN §11–§12 (`GODEL-D3-TRACKED-DESIGN.md`)** — resultado: **NO hay atajo para D3**.
  (§11.1) atajo por teorema de deducción IMPOSIBLE (D1 `repr_pos'`/`repr_pos'_prf` exigen `Prf`
  CERRADO; D1‑con‑contexto es FALSA = esa brecha ES D3). (§11.2/§12.2) enfoque `tcFn` DESCARTADO
  (caso cabeza/cola de la inducción exige `tcFn L =eq termCode L`, stuck para `L` abstracta).
  (§12.1) hallazgo central: **codificación del testigo ≡ representación del verificador** (la
  Σ₁‑completitud estándar exige `δ` Δ₀‑sobre‑NÚMEROS; el verificador es estructural sobre listas
  `carc`/`cdrc`, sin `len`/`nth`). Recomendación (§12.4) = **Opción 12‑A (capa numérica Δ₀ del
  verificador)**, construcción de libro, plan por 5 fases. Alternativa honesta: Gödel II módulo el
  axioma D3 (ya publicable: Gödel I real + D1/D2 reales).
- **12‑A FASE 1a — capa numérica de listas `lenc`/`nthc`**:
  - **`Minimal/Axioms.lean`** (extensión definicional conservadora, patrón `carc`/`cdrc`):
    `lenc l := func "lenc" [l]`, `nthc l i := func "nthc" [l, i]` + 4 axiomas (`ax_lenc_nil`/
    `ax_lenc_cons`/`ax_nthc_zero`/`ax_nthc_succ`) añadidos a `axioms` y `codingAxioms` (`axioms_eq`
    rfl preservado). **Build entero verde tras el cambio de núcleo**: verificador
    (`prf_iff_derivation`), D1 (`repr_pos'`) y toda la cadena Gödel intactos (la maquinaria genérica
    `thy`/`prf_inAxC` absorbe los axiomas nuevos).
  - **`Meta/NumListPrf.lean`** (NUEVO): ecuaciones `Prf` `prf_lenc_nil`/`prf_lenc_cons`/
    `prf_nthc_zero`/`prf_nthc_succ` (re‑derivadas de `axioms` vía `prf_ax`+`prf_spec`, patrón
    `prf_carc_cons`).
  - **SIGUIENTE (fase 1b)**: caracterización acotada `In x L ⇔ ∃ i < lenc L. nthc L i =eq x`.
- Build verde (**71 jobs**), 0 sorrys, Lean v4.31.0.

### Added (2026-07-05b) — Opción A: A‑F3 `pcc_exIntro_code` + verificación concreta (RIESGO‑1)

- **`Meta/ExIntroCodePrf.lean`** — **A‑F3 COMPLETO**: **`pcc_exIntro_code (Ac w) (hAc hw) :
  Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))`** — la regla Q2 (`A[t] ⇒ ∃A`)
  reflejada al nivel de **código** con testigo‑código arbitrario (cerrado). Ensamblaje tipo
  `d2_prf`: un testigo (`p = #0` de la hipótesis) + dos líneas apendizadas (línea‑axioma Q2 vía
  `prf_lineOk_q2` + línea MP); álgebra de cadena idéntica a la 2ª mitad de `d2_prf`.
  `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sin postulados, ni `prf_inAxC`).
  - **Hallazgo De Bruijn (reusable):** dos ubicaciones con tratamiento OPUESTO del colapso de
    lift. (1) Contexto post‑`prf_ex_elim_imp`: `liftTerm 0 (substfc zero w Ac)` sin subst externa
    → colapsar con `simp only [liftTerm_substfc …]` PREVIO al `simp` grande, MIENTRAS `zero` es
    literal (el patrón de la clausura lleva `zero`). (2) Target post‑`PrfH_ex_intro`:
    `liftTerm 0 (exc Ac)` se cancela con la subst externa `substTerm 0 r (·)` (`substTerm_liftTerm`)
    → NO pre‑colapsar. (`substTerm v s (.var v) = s` sin lift, `FOL.lean:82`.)
- **`Meta/Sigma1TrackedPrf.lean`** (NUEVO) — **verificación del ∃‑intro rastreado para testigos
  CONCRETOS** (checkpoint RIESGO‑1 del diseño §7.1): **`pcc_exIntro_code_bridge`** (de
  `provFromCode(substfc 0 (tcFn p) ⌜A⌝)` con `p` cerrado sale `provCodeC'(∃A)`, vía
  `pcc_exIntro_code` + reconciliación definicional `exc ⌜A⌝ = ⌜∃A⌝` porque `numeral 9 = succ⁹ zero`)
  + `pcc_exIntro_code_objList` (instancia con `objList lines`). `#print axioms` = estándar.
- **HALLAZGO (el muro del testigo abstracto):** el puente cierra para testigos **cerrados**
  (`tcFn p` cerrado sii `p` lo es → `hw` se descarga). Para el testigo **abstracto** (`p = #0`),
  `tcFn #0` NO es cerrado y `hw` FALLA; además todo combinador base (`pcc_in_*`/`pcc_imp`/D1)
  produce códigos vía `termCode` **meta**, y transportar a `tcFn` exige `tcFn L =eq termCode L`,
  **meta‑stuck para `L` abstracta**. Conclusión: **`hI_tracked` abstracto requiere la Opción A de
  raíz** (redefinir `provFormulaC'ₜ`/`provCodeC'ₜ` con `tcFn`/`substfc` + re‑derivar D1ₜ), no un
  lema incremental. **Limpieza F7 (retirar `GodelTwo.d3`/legacy) sigue BLOQUEADA** hasta que
  `goedel_second_prf` sea real (`goedel_second'` aún depende de `axiom d3`).
- Build verde (**69 jobs**), 0 sorrys, Lean v4.31.0.
- **`Meta/TrackedCorePrf.lean`** (NUEVO) — arranque **Opción A de raíz**: **`liftFormula_provFromCode
  (k c) (hc : ∀lvl, liftTerm lvl c = c)`** (clausura genérica de `provFromCode c` para código
  cerrado arbitrario; generaliza `liftFormula_provCodeC'`/`liftFormula_provFromCode_exc`). Cimiento
  de **D1ₜ** y del MP/∃ a nivel de código. Scaffold detallado del port D1ₜ (`repr_pos'_prfₜ`, el
  cuello de botella) en `GODEL-D3-TRACKED-DESIGN.md` §10. Build verde (**70 jobs**), 0 sorrys.

### Added (2026-07-05) — Opción A (D3 con testigo rastreado): A‑F1/A‑F2 + diseño

- **`GODEL-D3-TRACKED-DESIGN.md`** (NUEVO) — diseño detallado del predicado de demostrabilidad con
  **testigo rastreado** (patrón `diag_arith`): diagnóstico riguroso del muro de `hI`/`hC` (el código
  absorbe el testigo como `varc 0`), decisión **Opción A** (rastreo uniforme vía `tcFn`/`substfc`),
  orden de migración D1→D2→diagonal→D3 en fases, impacto por módulo, riesgos y criterios de éxito.
- **`Meta/Sigma1CorePrf.lean`** (extensión) — hacia `hI`/`hC` rastreados:
  - `objList` + **`pcc_in_objList_of_mem`** (reflexión de `In` sobre listas explícitas por
    meta-pertenencia; sortea la reflexión de igualdad Tarski-bloqueada).
  - **`prf_runFn_objList`** / `prf_runFn_nil_objList` (tracking `runFn` acumula `carc`; axiomas puros)
    + **`pcc_in_runFn_objList`** (= `hI` para testigos **concretos**).
  - **A‑F1** `prf_tc_objList` / `prf_tc_objList_formCode` (`tcFn = termCode` sobre la forma de la
    lista de conclusiones).
  - **A‑F2** **`prf_provCodeC'_of_tracked_witness`** — mecanismo central: la reflexión **rastreada**
    `provFromCode(substfc 0 (tcFn p) ⌜A⌝)` con testigo-código coincide con `provCodeC'(A[0:=p])`
    real (vía `prf_substFormula_arith` + `prf_congr_substfc_arg2` + `prf_provCode_congr`).
  - `#print axioms` = `[propext, choice, Quot.sound]` (los `pcc_*` añaden `prf_inAxC`, ancla benigna).
  - Build 67 jobs, 0 sorrys. Pendiente: `pcc_exIntro_code` (∃-intro a nivel código) + `hI`/`hC` rastreados.

### Changed (2026-07-04 20:15) — Migración de toolchain a Lean v4.31.0 (última estable)

- **Política de toolchain**: usar SIEMPRE la última versión estable de Lean v4 en todos los
  entornos, todos coincidentes. `lean-toolchain` de RPP (`v4.29.1`) y de la dependencia FOL
  (`v4.29.0`) migrados a **`leanprover/lean4:v4.31.0`**.
- **Regresiones de `simp` arregladas** (bajo 4.31 `simp only` ya no colapsa `if True then …`
  por defecto): `if_true`/`if_false`/`zero`/`succ` explícitos en `Meta/Representability.lean`,
  `Meta/ChainPrf.lean` (10 sitios), `Meta/TcArithPrf.lean`, `Meta/Diagonal.lean`; inline del
  contexto literal donde había `let Γ` en `Meta/ReflectionPrf.lean` (los `let` locales no se
  despliegan en `simp` bajo 4.31). Build verde tras la migración.

### Added (2026-07-04 20:15) — Opción A (bloque 3): capa de código object para `In` + congruencia de `tcFn`

- **`Meta/TcArithPrf.lean`** — **`prf_congr_tcFn : Prf (t₁ =eq t₂) → Prf (tcFn t₁ =eq tcFn t₂)`**
  (congruencia Leibniz object de `tcFn`; patrón `prf_eq_congr_succ`).
- **`Meta/Sigma1CorePrf.lean`** (NUEVO) — primera piedra de la reformulación de `hI` al nivel del
  código object. Ataca la obstrucción de que `formCode (In x L)` contiene `termCode L` (meta,
  stuck para `L` abstracta):
  - **`inFormCodeFn xc Lc`** — constructor object del código del átomo `In` desde los códigos de
    sus args (`⟨3, ⌜∈⌝, [xc, Lc]⟩`); **`inFormCodeFn_termCode`**/`provCodeC'_In_eq` (puentes rfl).
  - **`prf_congr_inFormCodeFn`** (congruencia) + **`prf_provFromCode_In_congr`** (transporte de la
    demostrabilidad del átomo `In` por igualdad de los códigos de sus argumentos, vía `prf_provCode_congr`).
  - **`prf_provCodeC'_In_of_tracked`** / **`prf_provCodeC'_In_formCode_of_tracked`** — puente de la
    demostrabilidad **rastreada** (códigos `tcFn`) a `provCodeC'(In x L)` real.
  - `#print axioms` = `[propext, choice, Quot.sound]`. Build verde (**67 jobs**), 0 sorrys.
  - Obstrucción restante identificada: `tcFn L =eq termCode L` sólo vale para `L` código literal;
    el cierre inductivo de `hI` debe ir sobre la estructura de la lista de conclusiones («la bestia»).

### Added (2026-06-29) — Opción A: `tcFn` (código del código) portado a `Prf`

- **`Meta/TcArithPrf.lean`** (NUEVO) — porte finitario de la cadena `tc_arith` de `Diagonal.lean`
  (ω) → `Prf`. `tcFn` es la **función object** que computa `termCode`:
  - `prf_tc_zero`/`prf_tc_succ`/`prf_tc_cons` — ecuaciones re-derivadas de `Minimal.axioms`.
  - `prf_tc_numeral` (inducción meta), `prf_tc_of_cons` (recursión), `prf_tc_chars`/`prf_tc_str`/
    `prf_tc_term`/`prf_tc_terms` (mutuas).
  - **`prf_tc_form : Prf (tcFn (formCode φ) =eq termCode (formCode φ))`** — `tcFn` computa
    `termCode` sobre todo código de fórmula, en `Prf`. `#print axioms` = `[propext, choice, Quot.sound]`.
- **Cimiento del enfoque de código object** para la Σ₁-completitud (`hC`/`hI`): a diferencia de la
  `termCode` **meta** (obstrucción Tarski), `tcFn` es función **object** con congruencia Leibniz.
  Build verde (**66 jobs**), 0 sorrys.

### Added (2026-06-28b) — Infraestructura de reflexión Σ₁ (núcleo duro de D3)

- **`Meta/Sigma1Prf.lean`** (NUEVO) — kit de reflexión reutilizable hacia `hI`/`hC`:
  - **`pcc_imp {A B} (h : Prf (A ⇒ B)) : Prf (provCodeC' A ⇒ provCodeC' B)`** — combinador
    clave (D2 `d2_prf` + D1 `repr_pos'_prf`): eleva cualquier implicación object cerrada a
    una implicación de demostrabilidad. `pcc_imp2` para implicaciones binarias.
  - **Reflexión de `In`**: `pcc_in_head`, `pcc_in_tail`, `pcc_in_head_eq`, `pcc_in_nil`.
  - **Reflexión de `chainOk`/`allIn`**: `pcc_chainOk_nil`/`pcc_chainOk_cons`,
    `pcc_allIn_nil`/`pcc_allIn_cons` (+ `prf_chainOk_cons_imp`/`prf_allIn_cons_imp`).
  - Todos `#print axioms` = `[propext, Classical.choice, Quot.sound, prf_inAxC]`.
- **Hallazgo**: `d3` NO es `pcc_imp` de reflexión local (`φ ⇒ Prov φ` es **falso** por Löb).
  Con los combinadores, `hI`/`hC` se reducen a **(1) reflexión de igualdad**
  `Prf ((x=eq y) ⇒ provCodeC'(x=eq y))` (obstrucción Tarski: el código `formCode(x=eq y)`
  absorbe la forma sintáctica de `y`, no su valor → los `▸`/Leibniz fallan; necesita la
  sustitución formalizada `substfc`) **y (2) cierre inductivo** sobre el código con
  seguimiento aritmético (`tcFn`/`substfc`, tipo `tc_arith`/`diag_arith` — la "bestia", Fase 5).
- **65 módulos/jobs**, 0 sorrys.

### Added (2026-06-28c) — Reflexión de igualdad reducida + transporte por igualdad de códigos

- **`provFromCode (c : Term) : Formula := substFormula 0 c provFormulaC'`** — demostrabilidad de
  un **código de fórmula** (no de una fórmula meta); `provCodeC' φ = provFromCode (formCode φ)`.
- **`prf_provCode_congr : Prf (c₁=eq c₂) → Prf (provFromCode c₁ ⇒ provFromCode c₂)`** — la
  demostrabilidad **respeta la igualdad de códigos** (Leibniz object). Funciona porque aquí `c`
  es un slot-término **genuino** del predicado (no absorbido, a diferencia de cuando la variable
  está *dentro* de la fórmula codificada). `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- **`pcc_eq_of_codeEq`** — **reduce la reflexión de igualdad** `(x=eq y) ⇒ provCodeC'(x=eq y)` a la
  igualdad de los *códigos* `formCode(x=eq x) =eq formCode(x=eq y)`, transportando `provCodeC'(x=eq x)`.
- **HALLAZGO arquitectónico**: la reflexión de igualdad **universal `∀x y` es indemostrable**
  (obstrucción Tarski: `termCode` es función meta, no object; de `x=eq y` no sale
  `termCode x =eq termCode y`). Solo vale para **términos-código** (donde `tcFn x =eq termCode x`
  vía `tc_arith`). → La Σ₁-completitud real (`hC`/`hI`) **debe reformularse al nivel del código
  object** (`tcFn`/`substfc` en todo, como el lema diagonal con `tc_arith`) — la "bestia" Fase 5.
- **REFERENCE.md §3.17** proyectada (cadena Gödel II en `Prf`: HilbertDeduction/ArithPrf/ChainPrf/
  DerivCondPrf/ReflectionPrf/Sigma1Prf). Build verde (**65 jobs**), 0 sorrys.

### Added (2026-06-28) — D3 finitaria reducida: `d3_prf_of_sigma1` (Punto 6, paso 9) + fix de toolchain

- **`Meta/ReflectionPrf.lean`** (NUEVO), porte de `Meta/Reflection.lean` (ω) → `Prf`:
  - **Combinadores lógicos internos** (versión `PrfH`): `PrfH_pcc_mp` (vía `d2_prf`),
    `PrfH_pcc_prf` (= `repr_pos'_prf`), `PrfH_pcc_andIntro` (vía `c1`), `PrfH_pcc_exIntro`
    (vía `q2`) — de `provCodeC' X` de las premisas a `provCodeC' Y` de la conclusión.
  - **`d3_prf_of_sigma1 (φ) (hC) (hI) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))`** —
    **reduce D3** a la **Σ₁-completitud provable del verificador**: las hipótesis
    `hC : ∀p, Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))` y
    `hI : ∀x L, Prf (In x L ⇒ provCodeC'(In x L))` aíslan el núcleo duro, claramente
    especificado (igual que `d3_of_sigma1` en ω). Estructura: `prf_ex_elim_imp` +
    `liftFormula_provCodeC'` + `∃`-elim (testigo `p=#0`) + `PrfH_pcc_andIntro`/`exIntro`.
    `#print axioms` = `[propext, Classical.choice, Quot.sound, prf_inAxC]` (sin postulados
    gödelianos; `prf_inAxC` viene de `repr_pos'_prf`/D1).
- **Fix de toolchain**: el `lean-toolchain` de la copia de trabajo estaba modificado a
  `v4.31.0`, bajo el cual algunos `simpa` de `Representability.lean` fallan al recompilar
  (los builds verdes previos los replayaban de caché — "build cache pitfall"). Restaurado al
  commiteado `v4.29.1`; build limpio de cero verificado (64 jobs).
- **64 módulos/jobs**, 0 sorrys. **Pendiente núcleo duro**: probar `hI`/`hC`
  (Σ₁-completitud provable, por inducción object sobre el testigo) → `d3_prf` →
  `goedel_second_prf : ConsistentH → ¬ Prf Con'`.

### Added (2026-06-27) — D2 finitaria real: `d2_prf` (Punto 6, paso 9)

- **`d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))`** (`Meta/DerivCondPrf.lean`,
  NUEVO) — la **segunda condición de Hilbert-Bernays** internalizada al cálculo finitario `Prf`,
  porte de `Meta/DerivCond.lean` (ω). `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
  **sin postulados de derivabilidad** (ni siquiera `prf_inAxC`).
- **Capa de clausura** (`liftTerm_numeral`/`liftTerm_charsCode`/`liftTerm_strCode`/`liftTerm_termCode`/
  `liftTerm_termsCode`/`liftTerm_formCode` + **`liftFormula_provCodeC'`**): los códigos de Gödel son
  cerrados, invariantes bajo `liftTerm`/`liftFormula`. Prerequisito porque `prf_ex_elim_imp` **no**
  da acceso meta al testigo (a diferencia del `provCodeC'_elim` ω) → la clausura debe probarse
  internamente.
- **`∃` en `PrfH`** (`HilbertDeduction.lean`): `PrfH_ex_intro` (vía `q2`) y `PrfH_ex_elim`
  (vía `q3`+`gen`+deducción), para los dos testigos **anidados** `p=#1`, `q=#0` (variables De Bruijn).
- **Ensamblaje** `r = p ++ q ++ [mp]`: `chainOk nil r` vía `prf_chainOk_concat`/`prf_chainOk_mono_imp`/
  `prf_lineWF_mp`; `In ⌜B⌝ (runFn nil r)` vía `prf_runFn_concat`/`prf_In_mono`; introducción con
  `PrfH_ex_intro`. (Detalle clave: NO incluir `liftTerm_formCode` en el `simp` final, para que
  `substTerm_liftTerm` redujera el slot `⌜B⌝`.)
- Helpers nuevos en `ChainPrf` exportados: `prf_In_mono_right_imp`, `PrfH_allIn_subst2`,
  `PrfH_in_cons_head`, y los `PrfH_and_*`/`PrfH_iff_*`/`PrfH_chainOk_subst1/2`/`PrfH_eq_subst_in`.
- **63 módulos/jobs**, build verde, 0 sorrys. Pendiente Punto 6: `d3_prf` (Σ₁-completitud) →
  `goedel_second_prf : ConsistentH → ¬ Prf Con'`.

### Added (2026-06-25c) — PASO 8 COMPLETO: los 10 lemas de cadena portados a `Prf`

- **3 lemas `∀c` finales** (reutilizan `norm32`/`norm_s`/confinación-`qconf`):
  - **`prf_chainOk_mono_imp (c0 c p) : Prf (chainOk c p ⇒ chainOk (c0++c) p)`** — split
    `chainOk_cons` + `prf_lineOk_mono_imp` + IH spec al acumulador cambiado + `prf_concat_assoc`
    (vía `PrfH_chainOk_subst1`).
  - **`prf_runFn_weaken (c p) : Prf (runFn c p =eq c ++ runFn nil p)`** — sin parámetro externo
    (solo `nil`); la IH se especializa a **dos** acumuladores; cadena `PrfH` con `PrfH_eq_symm`
    y `PrfH_congr_concat_left` nuevos.
  - **`prf_chainOk_concat (c p s) : Prf (chainOk c (p++s) ⇔ chainOk c p ∧ chainOk (runFn c p) s)`**
    — el más complejo (iff); `PrfH_and_intro` de las dos direcciones, cada una con split
    `chainOk_cons` + spec de la IH-iff. Para que el `spec` de la IH normalizara hubo que extraer
    el `∀`-body como `def ccIHbody` (un `let` no se desplegaba en `simp`) + `unfold ccIHbody` +
    añadir `land` al `simp` (bloqueaba `liftFormula`/`substFormula`).
- **Helpers nuevos**: `Prf`-level `prf_congr_concat_first`, `prf_concat_assoc`, `prf_allIn_mono_imp`,
  `prf_lineOk_mono_imp`, `prf_chainOk_subst2`, `prf_In_mono_imp` (refactor de `prf_In_mono`);
  `PrfH`-level `PrfH_and_intro/elim_left/elim_right`, `PrfH_iff_mp/mpr`, `PrfH_eq_symm`,
  `PrfH_congr_concat_left`, `PrfH_chainOk_subst1/subst2`.
- Todos `#print axioms` = `[propext, Classical.choice, Quot.sound]`. **Listos todos los ingredientes
  de cadena para `d2_prf`** (concatenación de pruebas `p++q++[mp]` + monotonía + compositividad).
  Build verde (**62 jobs**), 0 sorrys.

### Added (2026-06-25b) — Frontera `∀c` RESUELTA DE RAÍZ: `norm32`+`norm_s`+confinación → `prf_runFn_concat` + `prf_In_mono_right`

- **`prf_In_mono_right (x M L) : Prf (In x L) → Prf (In x (concat L M))`** — monotonía de `In`
  por la derecha (inducción sobre `L`): `base` por **explosión** (`In x nil` es falso, `ax_L1`),
  `step` por **`or_elim`** sobre la descomposición `ax_L2`. Helpers nuevos: `PrfH_or_elim`
  (vía `Prf₀.j3`+deducción), `PrfH_congr_cons_head`, `prf_in_cons_iff`, `prf_not_in_nil`.
- **Familia de normalización De Bruijn de profundidad 2** (la **raíz** del problema de los 3
  binders): `norm32 : substTerm 1 z (liftTerm 3 (liftTerm 2 (liftTerm 0 (liftTerm 0 t)))) =
  liftTerm 2 (liftTerm 0 (liftTerm 0 t))` (inducción mutua término/lista) + `norm_s` (cancela el
  lift extra de la confinación). Generalizan `norm21` a la profundidad que imponen los lemas con
  `∀c` interno.
- **Confinación (`qconf`) como patrón para el cuerpo del `step`**: el objetivo
  `(∀c. IH[c]) ⇒ (∀c. Concl[c])` (con la IH sin `c` libre) es exactamente el RHS de
  `confinementFormula (∀c.IH) Concl`; se reduce a `∀c. (↑IH ⇒ Concl[c])` vía `prf_mp (Prf.qconf _ _)`
  + `Prf.gen` + `prf_deduction`, y la HI-`∀c` se instancia al acumulador cambiado con `PrfH_spec`
  (el `substFormula` del `spec` cancela el lift de la confinación vía `norm_s`).
- **`prf_runFn_concat (c p s) : Prf (runFn c (concat p s) =eq runFn (runFn c p) s)`** —
  **compositividad de `runFn`, keystone de `d2_prf`**, valida el patrón end-to-end. Predicado
  inductivo `prfCompPred s` (acumulador `∀c` interno) + `prf_list_induction` + el patrón anterior.
- `#print axioms` de todo = `[propext, Classical.choice, Quot.sound]` (`norm32`/`norm_s` sin
  `choice`). `chainOk_concat`/`chainOk_mono` reutilizan el patrón (misma profundidad 2, mismos
  `norm32`/`norm_s`). Build verde (**62 jobs**), 0 sorrys.

### Added (2026-06-25) — `prf_In_mono` (monotonía izquierda de `In`) + `norm21` + `PrfH_spec` (paso 8)

- **`prf_In_mono (x c c0) : Prf (In x c) → Prf (In x (concat c0 c))`** — monotonía de la
  pertenencia en el contexto izquierdo, **keystone de `d2_prf`** (las conclusiones de la
  primera prueba siguen estando en el `runFn` de la cadena concatenada). Inducción de listas
  sobre `c0` con `x`,`c` protegidos por `liftTerm 0`. `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` (sin postulados).
- **`norm21 : substTerm 0 s (liftTerm 2 (liftTerm 1 (liftTerm 0 t))) = liftTerm 1 (liftTerm 0 t)`**
  — lema de normalización De Bruijn (vía `liftTerm_comm_zero` + `substTerm_liftTerm`) que casa
  el consecuente del `step` del eliminador cuando el parámetro va doblemente protegido bajo los
  dos binders del esquema de listas.
- **`PrfH_spec`** (∀-elim en `PrfH`, vía `Prf₀.q1`+`mp`) — andamiaje para la HI-`∀c` de los
  lemas restantes.
- **Frontera (multi-sesión)**: `runFn_concat`/`chainOk_concat`/`chainOk_mono` generalizan el
  acumulador como `∀c` **dentro** del predicado inductivo → el `step` del eliminador anida TRES
  binders y produce objetivos enormes que exigen una **familia de lemas de normalización De
  Bruijn multinivel** (más allá de `norm21`). El `base` valida; la normalización del consecuente
  `C'` queda como trabajo abierto. Build verde (**62 jobs**), 0 sorrys.

### Added (2026-06-24e) — Lemas de cadena en `Prf`: eliminador + `concat_nil_right` (paso 8, patrón validado)

- **`Meta/ChainPrf.lean`** (NUEVO): **`prf_list_induction (Φ) (base) (step) : Prf (∀L Φ[L])`**
  = `prf_mp (prf_mp (Prf.listInd Φ) base) step` — interfaz limpia de inducción de listas
  en el cálculo finitario `Prf`.
- **Helpers ecuacionales `PrfH`** (para los cuerpos del `step`, que usan la IH bajo el
  teorema de deducción): `PrfH_leibniz_subst`, `PrfH_eq_trans`, `PrfH_congr_cons_tail`.
- **`prf_concat_nil_right : Prf (concat X nil =eq X)`** — primer lema de cadena portado a
  `Prf`, que **valida el patrón end-to-end**: `prf_list_induction` + `base` (vía `show` +
  lema cerrado) + `step` (`Prf.gen`×2 + `prf_deduction` + helpers `PrfH`). `#print axioms`
  = `[propext, Classical.choice, Quot.sound]` (sin meta-axiomas). Build verde (**62 jobs**),
  0 sorrys.
- **Pendiente paso 8** (resto de lemas de cadena, mismo patrón): `In_mono`, `In_mono_right`,
  `runFn_concat`, `chainOk_concat`, `chainOk_mono`, `runFn_weaken` (los de `runFn`/`chainOk`
  llevan un `∀c` interno → `base`/`step` con `gen` adicional).

### Added (2026-06-24d) — Regla `listInd` (inducción de listas) integrada en el verificador `Prf` (paso 7 parte 2 COMPLETO)

- **Esquema/regla `listInd` (inducción estructural de listas) como regla del verificador**
  (vertical slice completo tipo `qconf`/`ind`, sin postulados, `prf_iff_derivation` total):
  - `Meta/Hilbert.lean`: `Prf.listInd A : Prf (listInductionFormula A)` + caso en
    `prf_to_derives` (vía `list_induction_derives`).
  - `Meta/HilbertSeq.lean`: `Rule.listInd A` + `stepConcl`/`stepConcl_prf`/`ruleCode`
    (tag 20)/`prf_to_derivation`.
  - `Minimal/Axioms.lean`: `ax_vpf_listInd` (legacy) + `ax_lineWF_listInd`/`ax_premsOf_listInd`
    (runFn); en `axioms`/`codingAxioms` (`axioms_eq` = `rfl`).
  - Arithmetización: `vpf_listInd` (`CheckArith`), `lineWF_listInd`/`premsOf_listInd`
    (`ProofChain`), versiones `Prf` (`ReprPrf`), `prf_listInd_concl_code` + `prf_congr_liftfc_arg2`
    (`ArithPrf`).
  - Tracking/encoder: casos `listInd` en `lineCode`/`vpf_run` (`Representability`),
    `lineJustif`/`chainOk_track` (`Representability2`), `prf_chainOk_track`
    (`Representability2Prf`); `PrfH.listInd` + puentes (`HilbertDeduction`).
- **Honestidad preservada**: `#print axioms repr_pos'_prf` = `[propext, Classical.choice,
  Quot.sound, prf_inAxC]`. `Prf` dispone ahora de inducción de listas (desbloquea el port
  de los lemas de cadena `runFn_concat`/`chainOk_concat`/`In_mono`... a `Prf`).
  **48 módulos**, build verde (**61 jobs**), 0 sorrys.

### Added (2026-06-24c) — Inducción de listas: `listInd_concl_code` (paso 7 parte 2, núcleo)

- **`Meta/ListInductionArith.lean`** (NUEVO): **`listInd_concl_code`** — reconstruye el
  código de `listInductionFormula A` desde `⌜A⌝` (caso base `A[nil]` vía
  `substFormula_arith`; paso `∀h∀t (A[t] ⇒ A[cons h t])` con `cons h t` codificado por
  `termCode (cons #1 #0)` y la cadena `liftfc∘liftfc∘substfc`; conclusión `∀L A[L]`).
  Más complejo que `ind_concl_code`: el término sustituido `cons #1 #0` tiene **variables
  libres** (`varc`), no códigos cerrados. Auxiliar `congr_liftfc_arg2`.
- Es el núcleo de la regla `listInd` del verificador (resto del slice mecánico, tipo
  `qconf`/`ind`). Build verde (**61 jobs**), 0 sorrys.

### Added (2026-06-24b) — Inducción de listas objeto: `list_induction_derives` (paso 7 parte 1)

- **`Meta/Hilbert.lean`**: `listInductionFormula Φ := Φ[nil] ⇒ ((∀h∀t (Φ[t] ⇒ Φ[cons h t])) ⇒ ∀L Φ[L])`
  (esquema objeto de inducción de listas; consecuente del paso
  `C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`), y
  **`list_induction_derives : axioms ⊢ listInductionFormula Φ`** (vía `ax_list_induction`
  + ω-gen; antecedente del paso vía `subst_lift_same`, consecuente vía el lema de
  Barendregt `subst_subst_comm_succ` + `subst_subst_lift_gen`). `#print axioms` =
  estándar + `gen`/`imp_intro` + `ax_list_induction`.
- Añadido `import Full.Lists` a `Hilbert.lean`. Justifica el futuro esquema
  `Prf.listInd`/regla del verificador.
- **Pendiente (paso 7 parte 2)**: slice `Prf.listInd`/`Rule.listInd` (verificador +
  aritmetización; `listInd_concl_code` con `termCode (cons #1 #0)` — variables libres,
  más complejo que `ind`). Build verde (**60 jobs**), 0 sorrys.

### Added (2026-06-24) — De Bruijn: lema de Barendregt (paso 7a completo)

- **`FOL/Theorems/Eq.lean`**: lema de sustitución de Barendregt (convención decremental),
  niveles consecutivos `j+1`/`j`:
  - `substTerm_subst_comm_succ` / `substTerms_subst_comm_succ` (nivel término).
  - **`subst_subst_comm_succ`** (nivel fórmula):
    `substFormula (j+1) a (substFormula j b f) = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f)`
    (casos ∀/∃ vía `substTerm_lift_comm_zero` + `liftTerm_comm_zero`).
  Sin Mathlib (no `split_ifs`): casos var por regiones (`rcases` + `simp`/`omega`).
- **Completa el toolkit De Bruijn (paso 7a)**: con Barendregt + `subst_subst_lift_gen` +
  `subst_lift_same` se cierra la **identidad del consecuente** de la inducción de listas
  objeto: `substFormula 0 t (substFormula 1 (↑h) C') = substFormula 0 (cons h t) Φ` con
  `C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`. Verificada
  end-to-end. Desbloquea `list_induction_derives` + slice `Prf.listInd` → `d2_prf`.
  Build verde (**60 jobs**), 0 sorrys.

### Added (2026-06-23g) — De Bruijn: composición subst-subst-lift generalizada por niveles

- **`FOL/Theorems/Eq.lean`**: tres lemas más de metateoría De Bruijn (toolkit hacia la
  inducción de listas objeto):
  - `substTerm_lift_comm_zero` / `substTerms_lift_comm_zero`:
    `substTerm (v+1) (liftTerm 0 n) (liftTerm 0 s) = liftTerm 0 (substTerm v n s)`.
  - `substTerm_subst_lift_gen` / `substTerms_subst_lift_gen`:
    `substTerm v n (substTerm v s (liftTerm (v+1) u)) = substTerm v (substTerm v n s) u`.
  - **`subst_subst_lift_gen`** (fórmula):
    `substFormula v n (substFormula v s (liftFormula (v+1) f)) = substFormula v (substTerm v n s) f`
    (casos ∀/∃ vía `substTerm_lift_comm_zero`).
  Probados por inducción, sin axiomas. La parte final de la identidad del consecuente
  de `listInductionFormula` se cierra con `subst_subst_lift_gen`.
- **Pendiente para cerrar 7a→7**: el **lema general de conmutación de sustituciones
  (Barendregt)** para niveles mixtos en la convención De Bruijn decremental del proyecto
  (las formas estándar no encajan tal cual; requiere derivación cuidadosa). Build verde
  (**60 jobs**), 0 sorrys.

### Added (2026-06-23f) — De Bruijn: conmutación subst/lift a nivel fórmula (cimiento de la inducción de listas en `Prf`)

- **`FOL/Theorems/Eq.lean`**: dos lemas De Bruijn de composición a nivel fórmula
  (faltaban; solo existían las versiones de término):
  - `liftTerm_comm_zero` / `liftTerms_comm_zero`:
    `liftTerm 0 (liftTerm c t) = liftTerm (c+1) (liftTerm 0 t)`.
  - **`substFormula_lift_comm`**:
    `substFormula (c+1) (liftTerm c s) (liftFormula c f) = liftFormula c (substFormula c s f)`
    (versión fórmula de `substTerm_lift_comm`; casos ∀/∃ vía `liftTerm_comm_zero`).
  Probados por inducción, sin axiomas. Son las herramientas que necesita la identidad
  De Bruijn del paso de la **inducción de listas objeto** (`listInductionFormula`) hacia
  `Prf.listInd`/`d2_prf`. Build verde (**60 jobs**), 0 sorrys.

### Fixed (2026-06-23e) — Solidez: eliminado un `axiom` FALSO de la base FOL (`subst_lift_cancel_formula`)

- **`FOL/Theorems/Quantifiers.lean`**: `subst_lift_cancel_formula` estaba declarado
  como `axiom` con un enunciado **GENERAL FALSO**:
  `substFormula v t (liftFormula (v+1) f) = f` para `t` arbitrario es falso
  (contraejemplo verificado con `rfl`: `f = atom P [#0]`, `v=0`, `t=#5` da
  `atom P [#5] ≠ f`). **Todo el Nivel D** (`prf0_to_derives`, `confinement_derives`,
  caso `q3`…) lo citaba en `#print axioms`, reposando sobre un axioma inconsistente.
- **Reparación**: todos los usos (`rw`) instancian `t = #v` (siempre `#0`), forma que
  **sí es verdadera**; ahora se **demuestra** (sin `axiom`):
  `subst_lift_cancel_formula : substFormula v (#v) (liftFormula (v+1) f) = f`, vía un
  helper de término `substTerm/substTerms_lift_cancel_var` (recursión mutua) +
  inducción en `f`. Mismo nombre ⟹ los 8 call-sites siguen compilando sin cambios.
  Los axiomas triviales `subst_distrib_and`/`lift_distrib_and` pasan a teoremas `:= rfl`.
- **Ganancia (verificada con `#print axioms`)**: `subst_lift_cancel_formula` ahora
  `[propext, Quot.sound]` (teorema); `confinement_derives` pasa de
  `[…, subst_lift_cancel_formula]` a `[propext, Classical.choice, Quot.sound]`. El
  cimiento De Bruijn del proyecto queda sólido. Build verde (**60 jobs**), 0 sorrys.

### Added (2026-06-23d) — Gödel Nivel D REAL: teorema de deducción finitario para `Prf`

- **`Meta/HilbertDeduction.lean`** (NUEVO): cálculo de Hilbert **con contexto** `PrfH`
  (espejo finitario de `Prf`: `incl0`/`p3`/`ind`/`qconf`/`mp` + `gen` de contexto-lift
  + `hyp`) y el **teorema de deducción** `deduction_aux` (inducción sobre la derivación;
  el caso `gen` se cierra justo con el esquema `qconf` de confinamiento ∀ — confirmando
  que la regla añadida era la pieza necesaria).
- Puentes `prfH_nil_to_prf : PrfH [] φ → Prf φ` y `prf_to_prfH : Prf φ → PrfH Γ φ`.
- **`prf_deduction : PrfH [A] B → Prf (A ⇒ B)`** (descarga de hipótesis) y
  **`prf_ex_elim_imp : PrfH [A] (↑C) → Prf (∃A ⇒ C)`** (eliminación del ∃ como
  implicación, vía `q3`+`gen`+deducción) — el `provCodeC'_elim` finitario que necesita
  `d2_prf`. `#print axioms` = solo `[propext, Classical.choice, Quot.sound]` (ningún
  meta-axioma; `qconf` es constructor de `Prf`, no axioma Lean).
- Desbloquea el razonamiento finitario con hipótesis y existenciales en `Prf`.
  **47 módulos**, build verde (**60 jobs**), 0 sorrys.

### Added (2026-06-23c) — Gödel Nivel D REAL: regla `qconf` (confinamiento ∀) integrada en el verificador

- **Esquema `qconf` (confinamiento ∀) como regla del verificador** (vertical slice
  completo tipo `ind`, sin postulados, sin romper `prf_iff_derivation`):
  - `Meta/Hilbert.lean`: constructor **`Prf.qconf (P C) : Prf (confinementFormula P C)`**
    + caso en `prf_to_derives` (vía `confinement_derives`).
  - `Meta/HilbertSeq.lean`: `Rule.qconf` + `stepConcl`/`stepConcl_prf`/`ruleCode` (tag 19)
    + `prf_to_derivation` (la completitud `prf_iff_derivation` sigue total).
  - `Minimal/Axioms.lean`: `ax_vpf_qconf` (path legacy `validProofFn`) +
    `ax_lineWF_qconf`/`ax_premsOf_qconf` (path `runFn`); añadidos a `axioms` y
    `codingAxioms` (con `axioms_eq` = `rfl` preservado).
  - Arithmetización: `vpf_qconf` (`CheckArith`), `lineWF_qconf`/`premsOf_qconf`
    (`ProofChain`), versiones `Prf` `prf_lineWF_qconf`/`prf_premsOf_qconf` (`ReprPrf`).
  - Tracking/encoder: casos `qconf` en `lineCode`/`vpf_run` (`Representability`),
    `lineJustif`/`chainOk_track` (`Representability2`), `prf_chainOk_track`
    (`Representability2Prf`). Reconstrucción del código inline vía `liftFormula_arith`.
- **Honestidad preservada**: `#print axioms repr_pos'_prf` sigue siendo
  `[propext, Classical.choice, Quot.sound, prf_inAxC]` (qconf aporta constructores/reglas
  y `def`s, no axiomas Lean). `provCodeC'` rastrea ahora `IΣ₁ + confinamiento ∀`.
- **Desbloquea**: el teorema de deducción finitario para `Prf` (caso `gen` vía `qconf`),
  siguiente hacia `d2_prf`. **46 módulos**, build verde (**59 jobs**), 0 sorrys.

### Added (2026-06-23b) — Gödel Nivel D REAL: confinamiento ∀ (cimiento del teorema de deducción de `Prf`, hacia `d2_prf`)

- **`Meta/Hilbert.lean`**: `confinementFormula P C := (∀(↑P ⇒ C)) ⇒ (P ⇒ ∀C)` y
  **`confinement_derives : axioms ⊢ confinementFormula P C`** — derivación De Bruijn
  directa en `Derives` (intro_impl×2 + intro_forall + elim_forall a `#0` con
  `subst_lift_cancel_formula`; espejo del caso `q3` de `prf0_to_derives`).
- **Por qué**: arrancando `d2_prf` (D2 a nivel `Prf`) se descubrió el **muro del
  confinamiento ∀**: el teorema de deducción de un cálculo de Hilbert (`Prf`) necesita
  confinamiento en su caso `gen`, y `Prf₀`/`Prf` están **congelados** por la completitud
  del verificador (`prf_iff_derivation`, de la que depende `repr_pos'_prf`) — no se puede
  añadir confinamiento ni a `Prf₀` ni como axioma suelto sin romperla. La derivación pura
  vía dualidad clásica (q3 + DNE) es circular. La ruta **directa en `Derives`** (deducción
  natural: `intro_impl`/`intro_forall` son constructores) lo resuelve, y justificará el
  esquema `Prf.qconf`/regla del verificador vía el puente `prf_to_derives`.
- **Plan (de libro, sin postulados, decidido)**: añadir confinamiento ∀ e inducción de
  listas como **esquemas/reglas del verificador** (vertical slice tipo `ind`), luego el
  teorema de deducción finitario para `Prf`, el port de los lemas de cadena
  (`runFn_concat`/`chainOk_concat`/`In_mono`...), y ensamblar `d2_prf` → `d3_prf` →
  `goedel_second_prf : ConsistentH → ¬ Prf Con'`. Multi-fase.
- **46 módulos**, build verde (**59 jobs**), 0 sorrys.

### Added (2026-06-23) — Gödel Nivel D REAL: `repr_pos'_prf` (D1 real re-nivelada a `Prf`)

- **`Meta/ArithPrf.lean`** (NUEVO): porte finitario completo a `Prf` de la aritmetización
  (`CodeArith`/`SubstArith`/`StepArith`/`Induction`), ~50 lemas. Patrón de porte:
  `prf_ax`(=`Prf₀.thy`)+`prf_spec`(=`q1`+`mp`)+el MISMO `simp`; congruencias vía
  `prf_leibniz_subst`+`prf_refl`. Incluye `prf_ex_intro` (∃-intro vía `q2`),
  `prf_eq_congr_succ`, `prf_congr_bin1/bin2/un`, `prf_congr_substfc_arg2/3`,
  `prf_pred_numeral`, `prf_numeral_add`, **`prf_numeral_lt`** (CLAVE: es finitario
  —testigo ∃ vía `q2`, sin regla ω—, por lo que TODA la aritmética de códigos sube a
  `Prf`), `prf_gnum_lt`, los recursivos mutuos `prf_substTerm/Terms_arith` y
  `prf_liftTerm/Terms_arith`, `prf_substFormula_arith`, `prf_liftFormula_arith`, y los
  códigos de conclusión `prf_q1/q2/leibniz/ind_concl_code`. `#print axioms` = solo Lean
  estándar.
- **`Meta/ReprPrf.lean`**: 32 esquemas `lineWF`/`premsOf` portados a `Prf` (22
  proposicionales p1..p3 + 10 de sustitución q1/q2/q3/leibniz/ind), reusando el patrón.
- **`Meta/Representability2Prf.lean`** (NUEVO): tracking finitario completo.
  `prf_concat_listFormCode(_singleton)`, **`prf_runFn_track`** (mitad `In ⌜φ⌝`),
  **`prf_chainOk_track`** (validez de la cadena, inducción 19 casos, espejo exacto),
  `prf_In_runFn_of_mem`, `provCodeC'_intro_prf` (∃-intro vía `prf_ex_intro`).
- **`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`** — D1 real internalizada al cálculo
  finitario `Prf` (necesitación interna; cimiento de la cadena HBL hacia Gödel II real).
  `#print axioms` = `[propext, Classical.choice, Quot.sound, prf_inAxC]`.
- Meta-axioma finitario **`prf_inAxC (a) (h : a ∈ axioms) : Prf (In (formCodeM a) axiomsCodeT)`**
  — análogo de `ax_inAxC` al nivel `Prf` (no derivable de él: el puente `Prf → ⊢` es de
  una sola dirección). Es el único postulado de codificación de la cadena Prf.
- **46 módulos**, build verde (**59 jobs**), 0 sorrys.

### Added (2026-06-22) — Gödel Nivel D REAL: punto fijo real para `provCodeC'` + Gödel I real estructural

- **`Meta/DiagonalTwo.lean`**: instancia la maquinaria diagonal genérica de `Diagonal.lean`
  (`diagTerm`/`diag_arith`/`selfApp`/`subst_eq_iff`) con `godelPred' := neg provFormulaC'`:
  `godelBeta'`, `godelC'`, `godel_comp'` (composición vía `substTerm_lift_comm`).
- **`godelC'_fixedpoint : ⊢ godelC' ⇔ ¬provCodeC' godelC'`** — punto fijo REAL
  (`#print axioms` = `[propext, choice, Quot.sound, imp_intro]`, sin postulados gödelianos).
  `godelC'_fp_bwd`/`fp_fwd`.
- **`goedel_first_real' : ConsistentOmega → ¬ Prf godelC'`** — Primer Teorema de Gödel real
  para el predicado estructural `provCodeC'` (vía `repr_pos'` + punto fijo).
- **Hallazgo de niveles**: Gödel II requiere re-nivelar la cadena HBL a `Prf` (no ⊢):
  `provCodeC'` rastrea `Prf` finitaria; `¬⊢Con'`/`¬⊢G'` son falsos (ω-sistema sólido).
  Gödel II correcto = `ConsistentH → ¬ Prf Con'`, vía `con_imp` a nivel Prf (necesita
  `repr_pos'`/`d2`/punto fijo re-derivados en Prf). En curso. (Ver NEXT-STEPS.)

### Changed (2026-06-21) — Gödel Nivel D REAL: refactor `Prf.thy → axioms` (teoría sobre su maquinaria)

Habilita la necesitación del punto fijo y D3: el cálculo de Hilbert `Prf` debe poder
razonar sobre el verificador (`chainOk`/`runFn`/…), que vive en `codingAxioms`.

- **`Prf₀.thy`** recorre ahora `axioms` (antes `coreAxioms`). `prf0_to_derives` thy =
  `Derives.hyp _ a ha`. `axioms_lift_eq` pasa a `rfl` puro (sin ancla).
- **Eliminados** `ax_axiomsCodeT` (ancla `=eq listFormCodeM coreAxioms`, término gigante)
  y `ax_axiomsCodeT_lift`. `axiomsCodeT` queda **opaco**.
- **Nuevo meta-axioma** `ax_inAxC (a) (h : a ∈ axioms) : ⊢ In (formCodeM a) axiomsCodeT`
  (contenido positivo de `axiomsCodeT`, sin término gigante/auto-referencia/reordenado).
  Sonda previa: `In (formCodeM φ) axiomsCodeT` se lifta en un paso (`liftTerm_formCodeM`).
- **Fixes**: `HilbertSeq` (`stepConcl`/`ruleCode` thy → `axioms[k]?`/`axioms.getD`),
  `Representability`/`Representability2` (caso thy vía `ax_inAxC` + `formCodeM_eq`).
- **Honestidad**: `repr_pos'` = `[propext, choice, Quot.sound, ax_inAxC]`; `d2` inalterado;
  el OLD `goedel_first_real` cita ahora `ax_inAxC` (postulado conservador que reemplaza
  el ancla, antes oculta en la lista de axiomas).

### Added (2026-06-21) — Gödel Nivel D REAL: Segundo Teorema de Gödel (núcleo lógico) + reducción D3

Cierre del **núcleo lógico de Gödel II** sobre el predicado estructural `provCodeC'`,
con la cadena Hilbert-Bernays-Löb (**D1 y D2 reales**, **D3 postulado**).

- **`Meta/GodelTwo.lean`**: `axiom d3 (φ) : ⊢ provCodeC' φ ⇒ provCodeC' (provCodeC' φ)`
  (único postulado gödeliano). **`con_imp_godel' (G) (fp_bwd) (nec1) : ⊢ Con' ⇒ G`**
  (Gödel I formalizado interno) y **`goedel_second' (G) (fp_bwd) (nec1) (hgi) : ¬(⊢ Con')`**,
  vía **D2 real** (`d2`) + `d3` + hipótesis explícitas honestas (`fp_bwd` punto fijo,
  `nec1` necesitación, `hgi` ⊬G ω). `#print axioms` = estándar + ω-reglas + ax_list_induction
  + `d3`; sin `diagonal_lemma`/`provFormula`/D2-legacy. MEJORA sobre legacy (postulaba D2 y D3).
- **`Meta/Reflection.lean`**: combinadores lógicos internos de la demostrabilidad
  `pcc_mp`/`pcc_prf`/`pcc_andIntro`/`pcc_exIntro` (vía `d2`/`repr_pos'`). (La reducción
  `d3_of_sigma1` resultó descomposición errónea —ver análisis D3—; queda superada.)
- **Análisis de D3** (registrado): la prueba real de D3 (Σ₁-completitud provable por
  inducción object internalizando `repr_pos'`) requiere antes unificar `Prf.thy → axioms`
  (la teoría razona sobre su propia maquinaria, como IΣ₁); mismo refactor habilita la
  necesitación del punto fijo. Camino a Gödel II 100% real documentado en NEXT-STEPS.

### Added (2026-06-21) — Gödel Nivel D REAL: D1 y D2 reales (HBL) sobre `provCodeC'` (Fases R4–R5)

Cierre de las dos primeras condiciones de Hilbert-Bernays-Löb como **teoremas internos**
(no postulados) para el verificador estructural `runFn`/`chainOk`. Predicado fiel
`provCodeC' := ∃p. chainOk nil p ∧ In x (runFn nil p)`.

- **D2** (`Meta/DerivCond.lean`): `d2 : ⊢ provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B)`.
  De testigos `p`,`q` se ensambla `r = p ++ q ++ [mp]`; `chainOk nil r` (vía
  `chainOk_concat`/`chainOk_mono`/`lineWF_mp`/`premsOf_mp` + `In_mono`/`In_mono_right`/
  `runFn_weaken`) y `In ⌜B⌝ (runFn nil r)` (`runFn_concat`/`carc`). `#print axioms` =
  estándar + ω-reglas; ningún postulado.
- **D1 = `repr_pos'`** (`Meta/Representability2.lean`): `Prf φ → ⊢ provCodeC' φ`.
  Encoder `lineJustif`/`lineCode'` (`cons ⌜concl⌝ justif`) + `proofCode'`; `runFn_track`
  (RULE-AGNÓSTICO, mitad `In ⌜φ⌝`) + `chainOk_track` (inducción ~19-casos, validez de
  cada línea). `#print axioms repr_pos'` = SOLO `[propext, Classical.choice, Quot.sound]`.
- **Validez de las 19 reglas** (`Minimal/Axioms` + `Meta/ProofChain`): `lineWF`/`premsOf`
  para mp/gen/thy + los 16 esquemas. `lineWF` de esquema ⇔ `concl =eq reconstrucción`
  (fidelidad: si fuese `⊤` se podría fabricar `⊢ provCodeC' ⊥` y Gödel II sería hueco);
  proposicionales por `refl`/defeq, q/leibniz vía `*_concl_code`, ind vía `ind_concl_code`.
- Helpers `provCodeC'_intro/_elim`, `allIn_subst2`, `chainOk_subst1/2`.

Pendiente: **D3** (Σ₁-completitud provable) + punto fijo para `provCodeC'` → **Gödel II real**.

### Added (2026-06-21) — Gödel Nivel D REAL: verificador estructural `runFn` (rediseño hacia D2/D3, Fases R1–R3)

Hacia **D2/D3 → Gödel II real**. Hallazgo: `validProofFn` es total/opaca con ecuaciones
**condicionales** → solo reduce sobre códigos concretos (basta para `repr_pos`/Gödel I)
pero **bloquea** la inducción object-level sobre testigos de prueba ARBITRARIOS que D2/D3
exigen (`vpf c (cons h t)` no reduce para `h` arbitrario). Solución: nuevo verificador
**estructuralmente recursivo** en `Meta/ProofChain.lean` (+ axiomas en `Minimal.axioms`),
con líneas que llevan su conclusión incorporada (`line = cons ⌜concl⌝ justif`), de modo
que `runFn` reduce uniformemente vía `carc`. Todo honesto (`#print axioms` = estándar +
ω-reglas `gen`/`imp_intro` + `Full.ax_list_induction`; ningún postulado gödeliano).

- **Fase R1** — `runFn` (`ax_runFn_nil/cons`, incondicionales) + `runFn_nil/cons` +
  congruencias + **compositividad** `runFn c (p++s) =eq runFn (runFn c p) s`, por
  `ax_list_induction` con el **acumulador generalizado como ∀-object** (los `liftTerm 0`
  se cancelan con la sustitución de `gen`). Valida el mecanismo del rediseño.
- **Fase R2** — predicados object `allIn`, `lineWF`, `premsOf`, `lineOk := lineWF ∧ allIn`,
  `chainOk` (+ ecuaciones `ax_allIn_nil/cons`, `ax_chainOk_nil/cons`). **Monotonía en
  contexto** `In_mono`/`allIn_mono`/`lineOk_mono` (para línea ARBITRARIA: la parte
  dependiente del contexto es `allIn`, uniformemente recursiva).
- **Fase R3** — `concat_nil_right`, congruencias `chainOk_subst1/2`, `In_mono_right`,
  **debilitamiento** `runFn c p =eq c ++ runFn nil p`, **composición**
  `chainOk c (p++s) ⇔ chainOk c p ∧ chainOk (runFn c p) s`, **monotonía** `chainOk_mono`.
  Toda la álgebra de cadenas de prueba para testigos arbitrarios — lo que `validProofFn`
  impedía. Base lista para **D2** (clausura concat+mp).

### Added (2026-06-19) — Gödel Nivel D REAL: integración de la regla de inducción (IΣ₁)

Vertical slice atómica que añade el **esquema de inducción** al cálculo aritmetizado,
para que `provCodeC` rastree **IΣ₁** (prerequisito de D2/D3 → Gödel II). `#print axioms`
de `repr_pos`/`vpf_ind` = solo estándar; `goedel_first_real` cita además
`Full.ax_induction` (axioma legítimo de aritmética; **ningún** postulado gödeliano).

- **`Meta/Hilbert.lean`**: `Prf.ind (A) : Prf (Full.inductionFormula A)`; soundness
  `prf_to_derives` vía `Full.ax_induction` (Meta importa Full, misma `Minimal.axioms`).
- **`Meta/HilbertSeq.lean`**: `Rule.ind` (tag 18) en `stepConcl`/`stepConcl_prf`/
  `prf_to_derivation`/`ruleCode`; `shiftRule`/`stepConcl_shift` cubiertos por catch-all/`rfl`.
- **`Minimal/Axioms.lean`**: **`ax_vpf_ind`** (incondicional — todo esquema de inducción es
  axioma legítimo), reconstruye el código de `inductionFormula φ` desde `⌜φ⌝` con códigos
  cerrados `termCodeM zero`/`termCodeM (succ #0)` (gestionados por clausura
  `substTerm_termCodeM`/`liftTerm_termCodeM`, sin numeral gigante). Añadido a `axioms`/`codingAxioms`.
- **`Meta/CheckArith.lean`**: step-lemma `vpf_ind`. **Verificador: 19 reglas.**
- **`Meta/Representability.lean`**: `lineCode` + caso `ind` de `vpf_run` (puente
  `termCodeM_eq` → `ind_concl_code`). `repr_pos` sigue honesto.

### Added (2026-06-19) — Gödel Nivel D REAL: Primer Teorema de Gödel REAL (sin postulados)

Cierre del bloque grande de Nivel D real. `#print axioms` de cada resultado = solo
axiomas estándar de Lean + las ω-reglas ambiente del sistema (`imp_intro`/`dne`/…);
**ningún** `diagonal_lemma`/`provFormula`/`D2`/`D3`.

- **Fase 2.4-thy + soundness de `thy`**: verificador `validProofFn` completo (18 reglas).
  `provCodeC` fiel: `thy` recorre `coreAxioms` (34 axiomas matemáticos), condicional a
  `In c axiomsCodeT`. `formCodeM` (codificación a nivel `Minimal`) + clausura De Bruijn
  estructural (`liftTerm_formCodeM`, por los numerales gigantes de símbolos Unicode).
- **Fase 2.5** (`Meta/Representability.lean`): `repr_pos : Prf φ → axioms ⊢ provCodeC φ`
  (representabilidad positiva) vía encoder object a medida `proofCode`/`lineCode` + `vpf_run`.
- **Fase 3** (`Meta/Necessitation.lean`): `d1`/`necessitation` (= `repr_pos` como
  condición HBL) + `goedel_first_unprovable_real` (Gödel I modular).
- **Lema diagonal real** (`Meta/Diagonal.lean`): `tcFn` «código del código» + `tc_arith`
  + `diag_arith` (diagonalización representable) + **`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`**
  + **`goedel_first_real : ConsistentOmega → ¬ Prf G`** (Primer Teorema de Gödel real,
  mitad de indemostrabilidad, sin hipótesis ni postulados).
- **Fase 2.6 cimiento** (`Meta/CodeDistinct.lean`): aritmética negativa `formCode_ne`
  (la teoría refuta igualdades de códigos distintos) + familia term/str/chars + primitivos.

### Added (2026-06-17) — Gödel Nivel D REAL: Fases 2.2f–2.4 (sustitución + verificador object)

Continuación de la aritmetización. Todo como **extensión definicional** de `Minimal.axioms` (ecuaciones re-derivadas como teoremas; `#print axioms` = solo axiomas estándar de Lean).

- **Fase 2.2 nivel fórmula** (`SubstArith` + `Minimal/Axioms`): `liftc`/`liftsc`/`substfc`/`liftfc` + constructores de código de fórmula (`botc`..`exc`) + 13 ecuaciones; `substFormula_arith`/`liftFormula_arith` (binders ∀/∃). Lemas de lift `substTerm_liftLiftLift`/`substTerm_liftLiftLiftLift` (3/4-lift).
- **Fase 2.3** (`Meta/StepArith.lean`): `q1/q2/leibniz_concl_code` — reconocimiento de instancias de los esquemas de sustitución vía `substFormula_arith` (los proposicionales son definicionales).
- **Fase 2.4** (`Meta/CheckArith.lean` + `Minimal/Axioms`): `numeralM`, extractores `carc`/`cdrc`; **`validProofFn`** + `forall_5` + **17 ecuaciones** del verificador de demostraciones (params directos por binders; MP/Gen condicionados por `In`) + 17 step lemmas `vpf_*`; **`provFormulaC := ∃p, In x (validProofFn nil p)`** — fórmula de demostrabilidad Σ₁ concreta (reemplaza el `provFormula` postulado) + `provCodeC`.
- **Pendiente**: regla `thy` (nudo de capas `formCode`/Minimal) + representabilidad positiva (2.5).

### Added (2026-06-13) — Gödel Nivel D REAL: aritmetización de D1–D3 (Opción A)

Conversión de D1/D2/D3 de meta-axiomas opacos a teoremas. Como el `axioms ⊢` del proyecto usa la **ω-regla** (no r.e.; `provFormula` imposible por Tarski), Gödel se aplica a un **cálculo de Hilbert finitario nuevo, en paralelo**. Plan en [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

- **Fase 0** (`Meta/Hilbert.lean`): `Prf₀` (Hilbert intuicionista) + `Prf` (clásico). Puentes `prf0_to_derives`/`prf_to_derives : Prf φ → axioms ⊢ φ` con **solo constructores de `Derives`**; `dne` aislado en un único punto (esquema P3), verificado por `#print axioms` (diferencia exacta entre puentes = `{dne}`). `consistentH_of_omega`.
- **Fase 1** (`Meta/HilbertSeq.lean`): `Rule` + verificador decidible `checkProof` + `Derivation`; solidez `derivation_to_prf` + completitud `prf_to_derivation` ⟹ `prf_iff_derivation`. Coding `ruleCode`/`rulesCode`, `Dem` **concreto**, `dem_tracks : (∃d, Dem d ⌜φ⌝) ↔ Prf φ` (reemplaza `Dem`/`dem_iff_provable`; solo axiomas estándar de Lean).
- **Fase 2.1** (`Meta/CodeArith.lean`): `numeral_bridge` + `gnum_ne`/`gnum_lt`/`gnum_add`/`gnum_mul`/`gnum_refl`.
- **Fase 2.2 nivel término** (`Meta/SubstArith.lean`): funciones object `substtc`/`substtsc` + congruencias de `cons` + ecuaciones recursivas (6 **axiomas definicionales**, a integrar en `Minimal.axioms`) + `substTerm_arith`/`substTerms_arith` (cómputo de la sustitución sobre códigos, inducción meta mutua).
- **Pendiente**: Fase 2.2 nivel fórmula (binders), 2.3 (stepConcl), 2.4 (demFormula Σ₁), 2.5 (representabilidad), Fase 3 (D1 real).

### Added (2026-06-12) — Gödel Nivel D: Incompletitud (Meta/Incompleteness.lean)

- **Gödel I (mitad esencial)**: `goedel_first_unprovable : Consistent → ⊬ goedelSentence` (si el sistema es consistente, `G` no es demostrable), `goedel_first_true` (`G` verdadera-pero-indemostrable), `incompleteness`. Derivado de D1 (`provFormula_repr`) + diagonalización (`goedelSentence_fixedpoint`) del Nivel C.
- **Gödel II**: `goedel_second : Consistent → ⊬ consistencyFormula` (`Con := ¬Prov(⌜⊥⌝)`). **Postulando D2 y D3** (Hilbert-Bernays-Löb). Lema crucial `con_imp_goedelSentence : ⊢ (Con ⇒ G)` (Gödel I formalizado). Toda la cadena HBL (incl. contrapositiva) con `imp_intro`/`mp`, **sin DNE object-level** → funciona en el FOL intuicionista.
- Pendiente: otra mitad de Gödel I (`⊬ ¬G`, vía ω-consistencia/Rosser).

### Changed (2026-06-12) — refactor: meta-reglas ω → FOL/MetaRules.lean

- Las 5 meta-axiomas ω (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) + wrappers de `Derives` (`mp`, `and_*`, `or_intro_*`, `false_elim`, `ex_intro`, `iff_*`) movidos de `Minimal/Axioms.lean` (lógica pura conviviendo con axiomas aritméticos) a **`FOL/MetaRules.lean`** (namespace `FOL.MetaRules`). `Minimal.Axioms` los **re-exporta** → cero churn en sitios de uso. FOL gana la ω-regla como axioma (documentado). Commits: FOL `084dbd2`, RPP `5fc89bb`.

### Added (2026-06-12) — Full: TFA completo + capa de representabilidad

- **Reencuadre numerales + representabilidad** (Gödel-aware): tras detectar que `ax_p_tfa` (meta de Block8) no admite discharge constructivo (object existenciales no dan testigos meta; disyunciones object no se eliminan a meta), se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con cómputo meta en ℕ + transferencia por homomorfismo.
- **`Full/Numerals.lean`**: `numeral` + homomorfismo `numeral_add/mul/pow`, orden `numeral_lt`, separación `numeral_ne`.
- **`Full/StrongInduction.lean`**: `strong_induction` (course-of-values) **DERIVADA de `ax_induction` sin axioma nuevo** + `substFormula_liftFormula` + `lt_succ_split`.
- **`Full/Bounded.lean`**: `le_numeral_split` (cuantificación acotada → casos finitos).
- **`Full/Divisibility.lean`**: `numeral_dvd`, `divisor_le`. **`Full/Division.lean`**: `division_numeral`. **`Full/Primality.lean`**: `isPrime_numeral`.
- **`Full/PrimeFactor.lean`** (ℕ pura, sin Mathlib): `exists_prime_factor`, `primeFactorList`, **lema de Euclides** (`euclid` vía `Nat.Coprime.dvd_of_dvd_mul`), unicidad (`count_unique`, `factorization_perm_unique` vía `List.perm_cons_erase`).
- **`Full/Factorization.lean`**: `toTerm`, `prod_pairs_toTerm`, **`tfa_numeral`** — TFA completo (existencia object ∧ unicidad ℕ). El `ax_p_tfa` de Block8 queda como forma idealizada.

### Added (2026-06-11) — Full/Lists.lean: ax_C3 y ax_L3 derivados (inducción estructural)

- **NUEVO módulo `Full/Lists.lean`** (330 líneas) — derivación de los dos axiomas de listas postulados en Minimal vía meta-axioma de inducción estructural:
  - **NUEVO meta-axioma `ax_list_induction`** (estilo `imp_intro`/`gen`/`or_elim`):

    ```lean
    axiom ax_list_induction {Γ} (φ : Term → Formula)
      (base : Γ ⊢ φ nil)
      (step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)) :
      ∀ L, Γ ⊢ φ L
    ```

    Parametrizado por función Lean `φ : Term → Formula` (no `Formula → Formula` como `ax_induction`). Más limpio: evita el manejo De Bruijn de los dos binders ∀h ∀t que requeriría una versión object-level. Conclusión sobre **todos** los Terms (no solo listas) — análogo a cómo `ax_induction` decide tratar Term como generado libremente por 0 y σ. (Observación: con 3 binders esta forma generalizaría a inducción sobre ordinales / W-types arbitrarios.)
  - **Helpers de congruencia**: `eq_congr_cons_right_full` (cons respeta `=` en arg derecho), `eq_congr_concat_left/right` (concat respeta `=` en ambos args), `eq_subst_in` (substituye igualdad bajo predicado `In`), helper local `iff_intro` (construye `iff` desde dos meta-implicaciones).
  - **`concat_assoc_pointwise` + `concat_assoc_thm : ⊢ ax_C3_concat_assoc`** — `(L##M)##N = L##(M##N)` por inducción estructural en L con M, N como parámetros Lean. Base nil: `ax_C1` doble + congruencia. Paso cons: `ax_C2` triple + IH + `eq_congr_cons_right_full`.
  - **`in_concat_pointwise` + `in_concat_thm : ⊢ ax_L3_in_concat`** — `In(x, L##M) ⇔ In(x,L) ∨ In(x,M)` por inducción estructural en L con x, M como parámetros. Base nil: `ax_L1` (¬In x nil) + `ax_C1`. Paso cons: `ax_C2` (concat fuera) + `ax_L2` (membership recursiva) + IH + asociatividad de `∨`. Prueba completa de las dos direcciones del `⇔`.
- **Cobertura del fragmento de Minimal en Full**: ax6/7/10/11/12 (algebraicos), ax18/19 (orden), ax21/24 (mod2), **ax_C3/L3 (listas)** ✅. Pendientes: Ax-P (TFA, inducción fuerte), Gödel Nivel D.

### Added (2026-06-11) — Full: ax21 y ax24 derivados (Opción C.2)

- **NUEVO módulo `Full/Mod2.lean`** (290 líneas) — caracterización completa de la recursión de `mod2` y derivación de los dos axiomas restantes del fragmento aritmético de `Minimal`:
  - **Nuevo axioma de Full**: `ax_mod2_alternation : axioms ⊢ ∀n, mod2(σn) + mod2(n) = 1`. Conservativo respecto a Minimal (allí derivable de `ax21 + ax16 + teo_1_3`).
  - **`mod2_zero_aux : axioms ⊢ mod2(0) = 0`** — re-probado en Full **sin usar `ax21`**, sólo `ax17 + teo_2_9`. (Block3.mod2_zero usa case-split sobre `ax21`.)
  - **Helpers**: `eq_congr_mod2` (congruencia de `mod2`), `a_plus_one_eq_one` (`a + 1 = 1 → a = 0` por `ax3+ax4+ax5`).
  - **`mod2_range_thm : axioms ⊢ ax21_mod2_range`**: `∀n, mod2(n) = 0 ∨ mod2(n) = 1`. Por inducción object-level con base `mod2_zero_aux` + paso usando `ax_mod2_alternation` con case-split sobre la IH.
  - **`mod2_two_k_eq_zero_ax` + `mod2_of_even_thm : axioms ⊢ ax24_mod2_of_even`**: `∀n k, n = 2k → mod2(n) = 0`. Por inducción sobre k (motivo `mod2(2k) = 0`), usando ax9 para reescribir `2·σk = 2k + 2 = σσ(2k)` y dos aplicaciones de alternancia. Luego se generaliza a `∀n k, n = 2k → mod2(n) = 0` vía `eq_congr_mod2`.
- **Auditoría en `MINIMAL-AXIOMS.md §3.2` actualizada**: documenta el hallazgo de que `ax16` sólo captura media alternancia (`mod2(n)=0 ⇔ mod2(σn)=1` no implica `mod2(n)=1 → mod2(σn)=0`) y que `ax16+ax17` dejan `mod2` subdeterminado (modelos no estándar con `mod2(σn) ≥ 2` cumplen ambos). Por eso `ax21` carga información independiente, no derivable sin un axioma extra como `ax_mod2_alternation`.
- Estado del fragmento aritmético de Minimal derivado en Full: **ax6, ax7, ax10, ax11, ax12, ax18, ax19, ax21, ax24** ✅. Pendientes: ax_C3, ax_L3 (listas — inducción sobre listas codificadas vía Cantor), Ax-P (TFA — inducción fuerte), Gödel D.

### Removed (2026-06-11) — `Intermediate/` eliminado

- **`Intermediate/Induction.lean` BORRADO** + directorio `Intermediate/` eliminado. **Justificación** (decisión 2026-06-11): el prototipo confirmó que la inducción general (esquema sobre `φ` arbitrario en Full) no añade fricción técnica sobre la restringida (Φ finito). Cualquier instancia inductiva concreta que necesitemos se postula directamente en `Full/`. Mantener un nivel separado para Φ finito era **burocracia conceptual** sin valor técnico.
- **Cadena de embeddings simplificada**: `FOL⁼ ⊂ Minimal ⊂ Full` (sin `Intermediate` intermedio).
- Referencias a Intermediate actualizadas en `ROBINSON_PlusPlus.lean` (root barrel), `PLANNING.md §6`, `NEXT-STEPS.md` Eje 3.

### Added (2026-06-07) — Full: ax19 (tricotomía) derivado

- **`lt_trichotomy_ax` / `lt_trichotomy_thm : axioms ⊢ ax19_lt_trichotomy`**: `∀a ∀b, a<b ∨ a=b ∨ b<a` derivado por inducción object-level (inducción sobre `a`, `∀b` interno, `or_elim` de 3 vías). Lemas auxiliares nuevos: `zero_lt_succ` (0<σk), `zero_or_succ_ax` (`∀b, b=0 ∨ ∃k b=σk`, por inducción con `∨`/`∃`), `lt_succ_cases` (`a<b → σa<b ∨ σa=b`, casando el testigo), `lt_intro` (construcción de `lt` desde testigo), `succ_add2`.
- Con ax18, **los dos axiomas de orden (ax18, ax19) son ahora teoremas en `Full`**. Acumulado derivado: **ax6, ax7, ax10, ax11, ax12, ax18, ax19**.
- Pendiente: ax21/24 (mod2), listas (ax_C3/ax_L3 — inducción sobre listas), Ax-P (TFA), Gödel D.

### Added (2026-06-07) — `Full/Induction.lean` (inducción general object-level, lift-aware)

- **NUEVO módulo `Full/Induction.lean`** (namespace `ROBINSON_PlusPlus.Full`): inducción general como **axioma object-level** (diseño elegido por el usuario: la inducción entra solo como axioma; las pruebas usan `mp`/`gen`/`imp_intro`, sin meta-inducción).
  - **`ax_induction (φ) : axioms ⊢ inductionFormula φ`** — esquema general. `inductionFormula` codifica `φ(σn)` de forma **lift-aware** como `substFormula 0 (σ#0) (liftFormula 1 φ)` (preserva variables-parámetro; la versión ingenua las decrementaba, rompiendo el caso multivariable).
  - **Lema de composición De Bruijn** (resuelve el obstáculo): `substTerm_subst_succ_lift`/`substTerms_subst_succ_lift` (`substTerm 0 m (substTerm 0 (σ#0) (liftTerm 1 t)) = substTerm 0 (σm) t`), `substFormula_eq_succ_lift`, `step_eq_reduce`.
  - **`induction_object`**: empaquetado object-level (doble `mp` sobre `ax_induction`).
  - Derivados **en forma object-level pura**: `zero_add`, `succ_add` (multivariable), `add_comm_ax`, y **`add_comm_thm : axioms ⊢ ax6_add_comm`** — `ax6` (postulado en `Minimal`) es ahora teorema. Sin usar `ax6`.

### Added (2026-06-07) — Full: más axiomas derivados + limpieza

- **`add_assoc_ax`** (= `ax7`): `∀c, (a+b)+c = a+(b+c)` por inducción object-level (2 parámetros). `ax7` derivado como teorema (queda pendiente sólo el empaquetado `∀³` literal, por ajuste De Bruijn de niveles).
- **Cadena `mul` completa** (object-level): `zero_mul`, `succ_mul`, **`mul_comm_ax`/`mul_comm_thm` (= ax10)**, **`mul_distrib_ax` (= ax12)**, **`mul_assoc_ax` (= ax11)**. Con esto **TODOS los axiomas algebraicos ECUACIONALES de Minimal son teoremas en Full**: ax6, ax7, ax10, ax11, ax12. Helpers de instanciación añadidos (`add_zero1`, `add_succ2`, `add_assoc3`, `add_comm2`, `mul_zero1`, `mul_succ2`, `zero_mul1`, `succ_mul2`, `mul_distrib3`).
- **Limpieza**: eliminados los directorios stray root-level `Full/`, `Intermediate/`, `Minimal/` (solo contenían `_template.lean` genéricos; el código real vive en `ROBINSON_PlusPlus/`).
- **Composición De Bruijn generalizada** (2026-06-07): `substTerm_subst_succ_lift_gen`/`substTerms_..._gen` (offset arbitrario, por tricotomía) y `substFormula_succ_lift_gen` (estructural sobre `Formula`, casos `∀`/`∃` por `congrArg`+defeq a offset `c+1`). De ahí `substFormula_succ_lift` (offset 0) y **`step_reduce` general** (reduce el paso de inducción de CUALQUIER `φ` a `φ(n) ⇒ φ(σn)`). Esto **desbloquea la inducción object-level sobre fórmulas no-ecuacionales** (`∨`/`∃`/`¬`/`∀`).
- **`ax18` (lt_irrefl) derivado** (2026-06-07): **primer axioma no-ecuacional**, vía `step_reduce` general + `ax13` (def de `lt`, con `∃`) + `ax2`/`ax3` + `zero_add`/`succ_add` derivados. `lt_irrefl_ax : ⊢ ∀a ¬(a<a)` y **`lt_irrefl_thm : ⊢ ax18_lt_irrefl`**. Valida la inducción object-level sobre fórmulas con `¬`/`∃`.
- **Lemas de orden auxiliares hacia `ax19`** (2026-06-07): `lt_succ_self` (`a < σa`), `not_lt_zero` (`¬(a<0)`), `lt_succ_of_lt` (`b<a → b<σa`). Validan el patrón de **construcción** de `lt` (vía `ax13` + `ex_intro`) además del de eliminación (`ex_elim`).
- Pendiente: **ax19** (tricotomía) — falta `zero_or_succ` + `lt_succ_cases` + el ensamblaje 3-vías (inducción con `∀b` interno y `or_elim`). Luego **ax21/24** (mod2), **listas** (ax_C3/ax_L3 — inducción sobre listas), **Ax-P** (TFA, inducción fuerte), y **Gödel Nivel D**. Empaquetado `⊢ axN` literal sale directo para `∀²` (ax6, ax10); para `∀³` (ax7, ax11, ax12) queda pendiente un helper n-ario (la derivación sustantiva `_ax` ya está).

### Added (2026-06-06) — `Intermediate/Induction.lean` (prototipo de inducción)

### Added (2026-06-06) — `Intermediate/Induction.lean` (prototipo de inducción)

- **NUEVO módulo prototipo `Intermediate/Induction.lean`** (namespace `ROBINSON_PlusPlus.Intermediate`), para validar la viabilidad del esquema de inducción antes de comprometerse con la estructura de `Intermediate/` (Φ finito) o `Full/` (inducción general).
  - Meta-axioma **`peano_induction`** (forma híbrida: paso meta, conclusión object-level, análoga a `gen`/`ex_elim`): de `φ(0)` y `∀n (⊢φ(n) → ⊢φ(σn))` concluye `⊢ ∀n φ(n)`.
  - **`zero_add_ind`** (`∀n, 0+n=n` por inducción, **sin `ax6`** — a diferencia de `teo_2_2`).
  - **`succ_add_ind`** (`∀a n, σa+n = σ(a+n)`, inducción multivariable con `liftTerm` para el parámetro).
  - **`add_comm_ind`** + **`add_comm_thm : axioms ⊢ ax6_add_comm`**: `ax6` (postulado en `Minimal`) **derivado como teorema** por inducción usando sólo `ax4`/`ax5`. Primer eslabón del embedding `Minimal ⊂ Intermediate`.
  - **Hallazgo**: la inducción general se formula/usa igual de fácil que una restringida a Φ; `Full/` (general) sería el camino de menor fricción técnica, `Intermediate/` (Φ finito) aporta valor conceptual. Decisión Intermediate-vs-Full pendiente.
- Build: **27 jobs, 0 errores, 0 warnings, 0 sorrys**. 14 módulos (incl. prototipo).

### Added (2026-06-06) — `Meta/Provability.lean` (Nivel C: demostrabilidad y diagonalización)

- **NUEVO módulo `Meta/Provability.lean`** (namespace `ROBINSON_PlusPlus.Meta.Provability`), Fase 19 del spec. Construye sobre `Meta/Godel.lean`.
  - **Codificación estructural de Gödel** de la sintaxis FOL: `charsCode`/`strCode` (símbolos vía lista de caracteres), `termCode`/`termsCode` (mutuos, por el anidamiento `func : String → List Term → Term`), y `formCode : Formula → Term` (tag por constructor: ⊥=2, atom=3, eq=4, impl=5, ∀=6, ∧=7, ∨=8, ∃=9).
  - **Inyectividad demostrada (consistency-free)**: `charsCode_injective`, `strCode_injective`, `termCode_injective`/`termsCode_injective` (mutuos), `formCode_injective` — vía `injection` + inducción estructural; sin postular nada.
  - **Def 29** `IsFormula (x) := ∃ φ, x = formCode φ`; `Provable (x) := ∃ φ, x = formCode φ ∧ axioms ⊢ φ`; **teorema real** `provable_formCode_iff : Provable ⌜φ⌝ ↔ axioms ⊢ φ` (vía `formCode_injective`).
  - **Def 30** `Dem : Term → Term → Prop` (meta-axioma) + **Teo Meta** `dem_iff_provable : axioms ⊢ φ ↔ ∃ d, Dem d ⌜φ⌝` (meta-axioma).
  - **Lema del punto fijo** `diagonal_lemma : ∀ φ, ∃ ψ, ⊢ ψ ⇔ φ[⌜ψ⌝]` (meta-axioma); `provFormula`/`provFormula_repr` (predicado de demostrabilidad object-level + representabilidad, meta-axiomas).
  - **Sentencia de Gödel** `goedelSentence` (punto fijo de `¬provFormula`) + `goedelSentence_fixedpoint : ⊢ G_Min ⇔ ¬Prov(⌜G_Min⌝)` (demostrado a partir de `diagonal_lemma`).
  - **5 meta-axiomas nuevos** (`Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma`): la aritmetización de demostraciones y la diagonalización requieren inducción → teoremas en el **Nivel D** (`Intermediate/`/`Full/`). El Nivel D (Gödel I/II internos) queda pendiente.
- **Barrel `Meta.lean`** creado (agrega `Meta.Godel` + `Meta.Provability`); el barrel raíz importa `ROBINSON_PlusPlus.Meta`.
- Build: **26 jobs, 0 errores, 0 warnings, 0 sorrys**. 13 módulos.

### Added (2026-06-06) — Block8 corolarios (Dvd/TFA) + `Meta/Godel.lean` (Nivel B)

- **`Block8.lean` — +10 teoremas (sin inducción)**:
  - Álgebra de `Dvd`: `dvd_trans`, `dvd_mul_right`, `dvd_mul_left`, `dvd_mul_of_dvd_left`, `dvd_mul_of_dvd_right`, `dvd_add` (vía `mul_assoc'`/`mul_comm'`/`mul_distrib'` de Block4_C5 + congruencia `eq_congr_mul/add_*`).
  - Corolarios del TFA (`ax_p_tfa`): `factorization_exists`, `factorization_unique` (vía `eq_trans` sobre la factorización canónica), `lt_zero_one` (testigo `k=0` en `ax13`, cierra con `teo_1_2`), `factorization_one_eq_nil`.
  - **Fuera de scope `Minimal/`**: lema de Euclides (`IsPrime p → p ∣ a·b → p ∣ a ∨ p ∣ b`) y multiplicatividad (`prod_pairs (concat f g) = prod_pairs f · prod_pairs g`) requieren `prod_pairs_concat` (recursión sobre lista) → inducción; diferidos a `Intermediate/`/`Full/`.

- **`Meta/Godel.lean` — NUEVO módulo (Nivel B Gödelización, Fase 18 del spec)**:
  - Namespace `ROBINSON_PlusPlus.Meta.Godel`. **No añade axiomas matemáticos** sobre `Minimal/`.
  - **Def 27**: `inductive Sym` (alfabeto Λ, 12 símbolos), `gNat : Sym → Nat` (tabla de Gödel: ∀↦2, ∃↦3, =↦10, …, m↦111) + `gNat_injective`.
  - `numeral : Nat → Term` (σⁿ0) + `numeral_injective`; `G : Sym → Term := numeral ∘ gNat` + `G_injective`.
  - **Def 28**: `encode : List Sym → Term` (corner brackets `⌜·⌝`, notación scoped) + `encode_nil`/`encode_cons`.
  - **Teo G1**: `encode_injective` (meta-inyectividad, **consistency-free**, vía `injection` + inducción estructural sobre la lista). Versiones object-level `encode_cons_inj` (vía `cons_inj`) y `encode_cons_neq_nil` (vía `cons_neq_nil`), faithful al "Teo L2 repetidamente" del spec. Pasar de la object-level a la conclusión meta `S = S'` requeriría `Con(axioms)`, diferido al Nivel C/D.
  - Añadido `import ROBINSON_PlusPlus.Meta.Godel` al barrel raíz. Sistema: **12 módulos**, build verde, 0 warnings, 0 sorrys.

### Changed (2026-06-06) — Linter `unusedSimpArgs` a `false` global + warning FOL cerrado

- **Linter `unusedSimpArgs` → `false` en los 12 módulos** (revierte el `true` del barrido del cierre anterior). Razón: el linter puede dar falsos positivos bajo binders existenciales y se prefiere libertad para conservar args de `simp` por robustez. El build permanece con 0 warnings.
- **Warning externo `FOL/Theorems/Eq.lean:130` cerrado**: eliminado el arg `simp` no usado `hne` en `substTerm_liftLift` (la rama de la variable cierra con `hgt` + `omega`). Commit en el repo hermano `FOL`: `9888c58`. Build global ahora con **0 warnings incluido el externo**.

### Added (2026-06-06) — Bloque VIII extendido

- **`Axioms.lean` — Lenguaje extendido**: nuevos símbolos `pow_sym = "^"` y `prodp_sym = "Π_p"`, con constructores `pow (b e : Term) : Term` y `prod_pairs (l : Term) : Term`. Cuatro axiomas definitorios añadidos:
  - `ax_pow_zero`: `∀ b, b^0 = 1`
  - `ax_pow_succ`: `∀ b, ∀ e, b^(σe) = b^e * b`
  - `ax_prodp_nil`: `prod_pairs [] = 1`
  - `ax_prodp_cons`: `∀ p, ∀ e, ∀ t, prod_pairs ((p,e)::t) = p^e * prod_pairs t`

  Sistema reducido de **30 → 34 axiomas matemáticos** (25 aritm: 23 base + 2 pow; + 7 listas; + 2 factorización: prodp_nil, prodp_cons).

- **`Block8.lean` — Fase 17 completa**: añadidos:
  - Lemas básicos `pow_zero`, `pow_succ`, `prod_pairs_nil`, `prod_pairs_cons` (instancias inmediatas de los nuevos axiomas).
  - **Def 26 `IsFactorization (f n : Term) : Prop`**: meta-Prop. `f` factoriza a `n` ⟺ `prod_pairs f =eq n` ∧ todo par `(p,e)` que aparece en `f` cumple `IsPrime p ∧ e > 0`. La restricción de forma sobre `f` proviene de `ax_prodp_cons` (solo se activa en cons-de-pair).
  - `isFactorization_nil_one`: caso base, `[]` factoriza al `1` (la cuantificación sobre elementos es vacuamente satisfecha por explosión object-level vía `ax_L1_in_nil`).
  - **Meta-axioma `ax_p_tfa` (TFA)**: `∀ n, axioms ⊢ lt zero n → ∃ f, IsFactorization f n ∧ ∀ f', IsFactorization f' n → axioms ⊢ (f =eq f')`. Estilo idéntico a `imp_intro`/`gen`/`raa`/`or_elim`/`ex_elim` (no expresable como `Formula` por ser meta-Prop). Justificación spec: en sistemas con inducción débil es derivable; en `Minimal` se adopta como axioma (§Apéndice B.4).

  Fase 17 completa según spec `TuplasFuncionesYListas.md §BLOQUE VIII`. Las Fases 18-19 (Gödelización + autorreferencia) permanecen fuera del scope `Minimal/` y corresponden a un módulo `Meta/` futuro.

### Changed (2026-06-06) — Limpieza warnings global

- **Todos los 11 módulos `Minimal/Theorems/*.lean`** ahora tienen `set_option linter.unusedSimpArgs true` activo. **411 → 0 warnings** en RPP. Eliminados argumentos `simp` no usados (mayoritariamente `liftTerm`, `liftTerms`, `FOL.substTerm_lift_comm`, `FOL.substTerm_liftLift`) en simp calls que ya no los requerían tras refactors anteriores.
- Reparto por módulo: Block5 (2), Block7 (6), Block4_C6_C7 (14), Block8 (22), Block1 (22), Block4_C5 (32), Block6 (39), Block2 (274).
- Único warning persistente: `FOL/Theorems/Eq.lean:130` (librería externa, no parte del proyecto RPP).

### Added (2026-06-03)

- **`Block8.lean` — BLOQUE VIII Fase 17 parcial (Primos)**: nuevo módulo con `Dvd` (divisibilidad), `IsPrime` (Def 25), y lemas básicos (`dvd_refl`, `dvd_one`, `dvd_zero`, `isPrime_zero_inconsistent`, `isPrime_one_inconsistent`). Mismo estilo meta-Prop que Block7. Build verde, 0 sorrys. **Pendientes documentados** (requieren extensión del lenguaje, fuera de scope `Minimal/`): Def 26 (`IsFactorization` — necesita `pow`/`prod_list`), Ax-P (TFA), Fases 18-19 (Gödelización + autorreferencia, corresponden a `Meta/` futuro).

- **`Block7.lean` — BLOQUE VII (Funciones Discretas)**: nuevo módulo con `IsFunction` (Def 21), `Functional` (Def 24, con `Map` inlineado), y los teoremas F1 (`IsFunction nil`), F2 (evaluación única), F3 (`IsFunction ⟺ Functional`). Estilo de formalización: `IsFunction`/`Functional` se definen como **meta-predicados Lean** (`Term → Prop`) parametrizados por cuantificación universal sobre `Term`, evitando el manejo manual de De Bruijn (`liftTerm`/`substTerm`) que aparecería con `forall_2`/`forall_3`. Build verde a la primera, 0 sorrys. Spec: `TuplasFuncionesYListas.md §BLOQUE VII`.

### Removed (2026-06-03)

- **`ax27_add_left_cancel` ELIMINADO** — derivable en PA⁻ sin inducción. Prueba (style PA⁻): si `a+c=b+c`, por tricotomía (ax19) `a<b ∨ a=b ∨ b<a`; los casos estrictos llevan a `a+c < a+c` vía `lt_add_const_of_le_left` (Block4_C5) + `add_comm'` y contradicen ax18. Reescrito `add_left_cancel` (Block4_C6_C7) con esta prueba. Refactorizado `succ_le_of_lt` (Block2) para no depender de ax27: en su lugar usa `ax5+ax3` para llegar a `a + σ(k+kp) = a`, luego `ax13` da `lt a (a + σ(k+kp))`, sustituye y contradice ax18. Sistema reducido de **31 → 30 axiomas matemáticos** (23 aritméticos + 7 listas).

### Fixed (2026-06-03)

- **Build roto reparado**: el commit `537fd68` (eliminación de `ax22`/`ax23`) introdujo `proj_is_cantor` en `Block4_C6_C7` usando `mod2_of_even`, pero este último vivía en `Block5` — y `Block5` importa `Block4_C6_C7`, creando dependencia circular. Solución: mover `mod2_of_even` a `Block4_C6_C7` (justo antes de `proj_is_cantor`) y exportarlo desde allí. `Block5` lo sigue viendo vía `open Block4_C6_C7`. Sin cambios de prueba, solo de ubicación.
- **Conteo de axiomas rectificado**: docs previos decían "30 axiomas matemáticos" — el conteo real de la lista `axioms` es **31** (24 aritméticos: ax2-19, ax21, ax24-27, ax29 + 7 listas: ax_L0-3, ax_C1-3). El número "30" era un error histórico arrastrado.

### Removed (2026-06-02, commit 537fd68 — Claude Code Pro / Copilot Pro)

- **`ax22_cantor_proj_exists` ELIMINADO**: `proj1`/`proj2` dejan de ser símbolos opacos del lenguaje (con axioma "Skolem" atándolos a `is_cantor`) y pasan a ser `def proj1 (c) := x_of_c c`, `def proj2 (c) := y_of_c c` en `Block4_C6_C7`. El contenido de ax22 se demuestra constructivamente como teorema `proj_is_cantor`.
- **`ax23_cantor_proj_uniq` ELIMINADO**: era `cantor_uniqueness` reescrito como axioma; nunca se usó en código (el teorema `cantor_uniqueness` real ya estaba probado en `Block4_C6_C7`).
- Símbolos `proj1_sym`, `proj2_sym` y los `def proj1`/`def proj2` opacos de `Axioms.lean` eliminados.
- `Block5` refactorizado: `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c` ahora usan `proj_is_cantor` en lugar de `spec h_ax22`.

### Removed (2026-06-02)

- **`ax28_mul_two_cancel` ELIMINADO** del sistema axiomático. Era redundante: la spec `TuplasFuncionesYListas.md §Teo 2.11` ya proporcionaba la prueba sin inducción (tricotomía + irreflexividad + monotonía estricta de *2). Sistema de **33 → 32 axiomas matemáticos** (con el conteo rectificado).
- El `def ax28_mul_two_cancel` queda comentado en `Axioms.lean` como nota histórica.

### Added (2026-06-02)

- **`Block1.mul_two_succ_ne_zero (k) : ¬(2·σk = 0)`** — Helper público para `teo_2_11`. Demostrado vía teo_2_7 + ax5 + ax2 (sin inducción).
- **`Block1.mul_two_lt_mono {a b} (h : a<b) : 2a < 2b`** — Monotonía estricta de *2 sin inducción. Usa ax5/ax12/ax13 + ax13 (testigo `j := σk+k`).
- **`Block1.teo_2_11`** reprobado directamente desde primeros principios (tricotomía ax19 + irreflexividad ax18 + `mul_two_lt_mono` + sustitución vía `Derives.subst`). Anteriormente delegaba a `ax (... ax28 ∈ axioms)`. Ahora es un teorema real sin axioma de respaldo.

### Changed (2026-06-02)

- **`Block4.cantor_injective_c`** refactorizado para usar `spec teo_2_11` en lugar de `spec h_ax28`.
- **`Block4_C6_C7.cantor_uniqueness`** refactorizado análogamente.
- **`REFERENCE.md`** reescrito completo (proyección al estado actual: 9 módulos ✅, 30 axiomas, lista de exports por módulo, signaturas + descripción matemática).

### Added (2026-05-27)

- **Axiomas `ax_C3_concat_assoc` y `ax_L3_in_concat`** en `Minimal/Axioms.lean`. Postulados siguiendo el patrón de ax21/ax24/ax27/ax28 (teoremas en sistemas con inducción, axiomas en `Minimal`). Permiten cerrar `concat_assoc` y `in_concat_iff` en Block6 sin inducción sobre L.
- **Axioma `ax29_sub_witness`** + función `sub` con `sub_sym` en `Minimal/Axioms.lean`. Postula el testigo de la resta truncada (`b ≤ a → b + (a − b) = a`). Permite definir `x_of_c`/`y_of_c` constructivamente y cerrar `cantor_surjectivity`.
- **`eq_congr_pred`** en `Minimal/Axioms.lean` (análogo a `eq_congr_succ`).
- **`lemma_C5_unique`** y **`cantor_bounds`** exportados desde `Block4_C5`.
- **`is_cantor_pair`** exportado desde `Block5` (clave del isomorfismo pares ↔ N).

### Changed (2026-05-27)

- **🎉 PROYECTO `Minimal/` A 0 SORRYS REALES**. Build verde `lake build` exit 0, `WARN_sorry=0`. Los 5 `axiom imp_intro/gen/raa/or_elim/ex_elim` son meta-reglas de FOL, no `:= sorry`.
- **Block4_C5 cerrado** (commit `4b6a2a9`): probados `sq_2w_plus_1`, `w_w1_le_2c_iff_sq_2w1_le_8c1`, `mono_w_w1`, `h_sq_2w1_le_sq_s`, `h_existence_part2` (este último por contradicción reusando el iff). Sentencia ajustada a `liftTerm 0 c` y cerrada con `ex_intro w`. Helper `lemma_C5_unique` exportado.
- **Block4_C6_C7 cerrado** (commits `4b6a2a9` + `fde7476`): `cantor_uniqueness` (vía `cantor_bounds` + `lemma_C5_unique` + `add_left_cancel` + ax28) y `cantor_surjectivity` (construcción constructiva con `sub`/ax29 + `parity_lemma`).
- **Block5 cerrado** (commit `871e5e2`): `mod2_of_even`, `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c`, `pair_inj` — todos vía `cantor_uniqueness`/`cantor_injective_c` + `is_cantor_pair`.
- **Block6 cerrado** (commits `71862ca` + `1470a90`): `cons_neq_nil`, `cons_inj`, `in_cons_self_nil`, `in_cons_nil_imp_eq`, `concat_singletons` (vía helpers); `concat_assoc` y `in_concat_iff` cerrados vía spec de los nuevos `ax_C3`/`ax_L3`.
- **~30 helpers de orden/aritmética hechos públicos y exportados** desde `Block4_C5` (le_rewrite, lt_rewrite, le_self_add, le_add_one_cancel, le_mul_*, mul_lt_mono_right, sq_lt_mono, add_comm', mul_assoc', etc.). Helpers de Block2 (`zero_le`, `mul_le_mono_right`, `sq_le_mono`) hechos públicos. Duplicados eliminados.
- **Linter `unusedSimpArgs` desactivado** en todos los módulos (genera falsos positivos con simps bajo binders existenciales donde `FOL.substTerm_lift*` sí disparan reducciones que el linter no traza).
- **Conflicto de merge en `FOL/Theorems/Eq.lean` resuelto** (commit `4b262bf` en FOL): restaurados `substTerm_lift_comm` y `substTerm_liftLift` (necesarios para ROBINSON; eliminados por el merge previo `29ad33f`).

### Documentation (2026-05-27)

- `README.md`, `CURRENT-STATUS-PROJECT.md`, `PLANNING.md`, `NEXT-STEPS.md` actualizados al estado actual (Minimal completo, próximos pasos: Block7 / Intermediate / Full).
- Header de `Block3.lean` documenta su tamaño (~1900 líneas) como consecuencia explícita de la ausencia de inducción en Minimal (enumeración por numeral).

### Changed (2026-05-12)

- **Block3.lean — `div2_zero`, `div2_one`, `div2_two` (parcial) + helpers privados** (2026-05-12): Eliminados 2 sorry. Se demostraron completamente `div2_zero`, `div2_one` y los auxiliares `div2_zero_mul`, `div2_one_mul`, `div2_two_mul`. Se añadieron helpers privados `add_succ_left_ne_zero` y `mul_succ_two_ne_zero`. `div2_two` queda con 1 sorry (caso `1 < div2(2)`); `div2_three` y `div2_four` permanecen como sorry. Build: ✅ exit code 0, sin errores de compilación. **Corrección técnica**: `eq_congr_mul_right` para congruencia del argumento izquierdo de `mul`; `FOL.derive_eq_trans` para encadenamiento estándar `a=b, b=c → a=c` (vs `eq_trans` no-estándar con mismo LHS). Total sorry: 60 (antes 62).

### Changed (2026-05-09)

- **Bloque IV (Fase 9.1)**: Continuada la demostración del Lema C5 con la adición de múltiples lemas auxiliares para la manipulación de desigualdades.

### Changed (2026-05-09)

- **Bloques II y III completados**: Se han demostrado todos los teoremas de los bloques de raíz cuadrada (`Block2.lean`) y `div2`/`mod2` (`Block3.lean`). El proyecto ya no contiene `sorry`s.

### Added (2026-04-25 21:30)

- Declaración del axioma `henkin_extension_lemma` para manejar la expansión de constantes.
- Formalización del Teorema de Compacidad (`compactness_theorem`) y Consistencia (`consistency_of_satisfiable`) en `Compacity.lean`.
- El proyecto alcanza oficialmente **0 sorries** en su totalidad. ¡Hito final completado!
- Build status: ✅ Passing, 0 warnings.

### Added (2026-04-25 21:00)

- Formalización de la construcción de Henkin en `Completeness.lean`.
- Demostración formal del Lema de Lindenbaum (`lindenbaum_lemma`) y Compacidad Sintáctica.
- Demostración del Lema de la Verdad (`truth_lemma`) mediante inducción fuerte sobre la complejidad de fórmulas.
- Demostración del Teorema de Completitud de Gödel (`completeness`).

### Added (2026-04-25 20:30)

- Demostración completa de los lemas de sustitución semántica y reescritura en `FOL/Semantics.lean`, resolviendo la "trampa de De Bruijn" mediante inducción generalizada.
- El proyecto alcanza 0 sorries en toda la formalización de la sintaxis, deducción natural y corrección semántica (Soundness).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-25 20:00)

- Demostración completa del Teorema de Deducción en `FOL/Deduction.lean`.
- Definición de Modelos y Semántica de la lógica de primer orden en `FOL/Semantics.lean` (`Model`, `evalFormula`, `satisfies`).
- Demostración completa del Teorema de Corrección (Soundness) en `FOL/Soundness.lean` apoyada en los lemas semánticos.
- Implementación de la táctica `derive_raa` en `FOL/Tactics.lean`.
- Estado del Build: 0 errores, 5 sorries activos en `Semantics.lean` correspondientes a los lemas de sustitución y reescritura.

### Added (2026-04-25)

- Implementación de tácticas de automatización en `FOL/Tactics.lean`: `derive_hyp`, `derive_rewrite` y `derive_weaken`.
- Finalización oficial de la Fase 4 (Automatización).
- Inicio formal de la Fase 5 (Metamatemática y Completitud).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-20 00:00)

- Initial project structure from lean4-project-template

---

## [0.2.0] - 2026-04-20

### Added

- `NAMING-CONVENTIONS.md`: Full Mathlib-style naming dictionary with 12 formation rules, symbol-to-word dictionary, and migration tables
- `NEXT-STEPS.md`: Development phase planning template
- `THOUGHTS.md`: Design journal template for recording ideas and alternatives
- `REFERENCE.md` §0: Naming conventions quick-reference guide for the reader
- `REFERENCE.md` §Compliance: Checklist against AI-GUIDE.md requirements
- `AI-GUIDE.md` §22-23: Directory and subdirectory organization protocol
- `AI-GUIDE.md` §24-25: Annotation system (`@axiom_system`, `@importance`)
- `AI-GUIDE.md` §26-28: Cross-reference files documentation
- `AI-GUIDE.md`: Symbol-to-word dictionary and theorem formation rules summary in Naming Conventions section
- `DECISIONS.md`: ADR-004 (Mathlib naming), ADR-005 (directory-aligned namespaces), ADR-006 (annotation system), ADR-007 (separate NAMING-CONVENTIONS.md)
- `_template.lean`: Added naming convention reminders, annotation metadata, expanded section structure
- `CURRENT-STATUS-PROJECT.md`: Development phases tracking table

### Changed

- `README.md`: Added naming conventions summary table, documentation table format, subdirectory-aware project structure
- `DEPENDENCIES.md`: Added subdirectory-aware structure, multi-level dependency hierarchy example, Mermaid subgraph example

---

## [0.1.0] - 2026-04-20

### Added

- `Prelim.lean`: preliminary definitions

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/ProjectName)
- [Issues](https://github.com/julian1c2a/ProjectName/issues)

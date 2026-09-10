# Auditoría del proyecto — 2026-09-10

**Alcance:** el código (`ROBINSON_PlusPlus` + `FOL`) y el libro (`doc/book/`).
**Estado del árbol en el momento de auditar:** `HEAD = 37e582c`, rama `master`, **árbol limpio**.
**Método:** todo se ha medido contra el árbol. Cada afirmación va marcada:

| marca | significa |
|---|---|
| **[medido]** | verificado en el código o en `git`, aquí, hoy |
| **[documentado]** | lo dice un `.md` del proyecto y no se ha podido comprobar sin `lake` |
| **⛔ [contradicho]** | un documento dice una cosa y el árbol dice otra |

Lo **no medido** se declara al final, en §7. En particular: **no se ha ejecutado `lake build`**, así
que ningún `#print axioms` de este informe está verificado — los *footprints* son [documentado].

---

## 1 · El código, en cifras

### 1.1 · Tamaño **[medido]**

| | ficheros `.lean` | líneas |
|---|---:|---:|
| producción (`ROBINSON_PlusPlus/` + raíz) | **127** | **55 326** |
| ↳ `Meta/` | 103 | 44 600 |
| ↳ `Minimal/` | 11 | — |
| ↳ `Full/` | 11 | 2 498 |
| `sondeos/` | 60 | 69 848 |
| `Probe/` | 334 | 253 042 |
| `cuarentena/` | **0** (sólo su `README.md`) | 0 |

**Casi seis veces más código fuera del build que dentro.** No es desorden: es el método. Un
`sondeo/` es un experimento *compilado* que contesta una pregunta antes de tocar producción, y los
`Probe/` son mediciones. La proporción es la huella de una disciplina: **medir antes de
comprometerse**, adoptada después del episodio de julio (§4).

El cierre de imports desde `ROBINSON_PlusPlus.lean` alcanza **los 127 módulos: cero huérfanos**.
Todo lo que está en el árbol de producción está en el build.

### 1.2 · Salud **[medido]**

| | producción | sondeos | Probe |
|---|---:|---:|---:|
| `sorry` reales | **0** | 0 | 0 |
| `admit` reales | **0** | 0 | 0 |
| `native_decide` reales | **0** | 0 | 0 |

Medido despojando comentarios anidados y literales de cadena. En producción hay 9 líneas que
*mencionan* `sorry` en prosa y **ningún token real**. La afirmación «0 sorrys» del proyecto es
correcta y se ha verificado de forma independiente.

### 1.3 · La base: 7 axiomas de Lean **[medido]**

Exactamente siete, **los mismos que el 2026-09-09**: ninguno nuevo, ninguno retirado.

| fichero:línea | axioma | qué es |
|---|---|---|
| `Full/Induction.lean:166` | `ax_induction` | el esquema de inducción de la teoría objeto |
| `Full/Lists.lean:55` | `ax_list_induction` | inducción sobre listas |
| `Full/Mod2.lean:85` | `ax_mod2_alternation` | alternancia de la paridad |
| **`Meta/GodelTwo.lean:60`** | **`d3`** | **la tercera condición de derivabilidad — la deuda viva** |
| `Meta/Representability2Prf.lean:104` | `prf_axiomsCodeT_eq` | ancla de codificación |
| `Minimal/Axioms.lean:1594` | `ax_axiomsCodeT_eq` | ídem, para `⊢` |
| `Minimal/Theorems/Block8.lean:302` | `ax_p_tfa` | teorema fundamental de la aritmética |

### 1.4 · Los axiomas objeto: 34 + 107 = 141 **[medido, reconfirmado]**

| lista | `def` en | elementos |
|---|---|---:|
| `coreAxioms` | `Minimal/Axioms.lean:944` | **34** |
| `codingAxioms` | `Minimal/Axioms.lean:1548` | **107** |
| `axioms` | `Minimal/Axioms.lean:1417` | **141** |

Con `axioms_eq : axioms = coreAxioms ++ codingAxioms := rfl` (`:1574`), y 34 + 107 = 141 cuadra.
Confirma la medición del 2026-09-03 que sostiene el capítulo 3 del libro: **tres veces más
maquinaria de codificación que aritmética.**

---

## 2 · Qué está demostrado

### 2.1 · Los teoremas grandes **[medido: fichero, línea y firma]**

| resultado | dónde | hipótesis REALES (leídas de la firma) |
|---|---|---|
| **punto fijo** `godelCN_fixedpoint` | `Meta/DiagonalNumeral.lean:112` | **ninguna** |
| **D1** `repr_pos'` / `repr_pos'_prf` | `Meta/Representability2.lean:365` · `…2Prf.lean:348` | **ninguna** |
| **D2** `d2_prf` | `Meta/DerivCondPrf.lean:110` | **ninguna** |
| **D3** | `Meta/GodelTwo.lean:60` | **es un `axiom`** |
| **Gödel I**, mitad `⊬G` `goedel_first_numeral` | `Meta/DiagonalNumeral.lean:119` | consistencia simple, **cero postulados gödelianos** |
| Gödel I, indecidibilidad `…_undecidable_numeral` | `Meta/DiagonalNumeral.lean:124` | `Reflects` (hipótesis meta explícita) |
| Gödel I, vía ω `…_undecidable_omega` | `Meta/OmegaReflect.lean:168` | ω-consistencia + **`NegVerifier`** |
| **Gödel II** `goedel_second'` | `Meta/GodelTwo.lean:98` | 3 hipótesis + **`axiom d3`** |
| evaluación de `substfc` `pcc_eval_substfc_wit` | `Meta/EvalSubstfcPrf.lean:1541` | **ninguna** (guardas internalizadas) |
| no-vacuidad `prf_hasWitF_real` | `Meta/CodeWitnessPrf.lean:2142` | **ninguna** |
| **reflejo de `lineWF`** `pcc_lineWF_tracked` | `Meta/SubstTreeReflect.lean:1157` | **ninguna** ← cerrado HOY |

**La mitad demostrada del primer teorema está limpia**: `⊬G` sale de la consistencia simple y de
nada más. La otra mitad, `⊬¬G`, cuelga entera de `NegVerifier`, que existe como enunciado y **no
está construido** (§2.3).

### 2.2 · C3 cerrado: el muro de `substfc` cobra sus consecuencias **[medido]**

Es el cambio grande desde ayer, y ocurrió **hoy**:

- los **siete** reflectores que faltaban están cerrados e incondicionales, todos en
  `Meta/SubstTreeReflect.lean` (q1 `:773`, q2 `:806`, leibniz `:841`, q3 `:876`, qconf `:909`,
  ind `:1014`, listInd `:1024`);
- `pcc_lineWF_tracked` (`:1157`) **ya no tiene hipótesis**: el caso «tags que no existen» se paga
  con `pcc_tag_vacuous` (`:1146`);
- la pieza que los desbloqueó, `prf_hasWitF_liftfc` (`Meta/LiftfcWitnessPrf.lean:637`), está
  probada, y su deuda declarada saldada en `:651`.

`pcc_lineWF_tracked_modulo_7` —el teorema que *medía lo que faltaba*— sigue en el árbol pero ya no
lo consume nadie. **Diez días entre romper el muro (2026-08-31) y cobrarlo (2026-09-10).**

### 2.3 · Lo que sigue abierto **[medido]**

| frente | estado |
|---|---|
| **D3** | `d3` sigue siendo `axiom`, y se consume de verdad: `con_imp_godel'` (`GodelTwo.lean:86`) lo usa, y `goedel_second'` pasa por ahí |
| ↳ mitad (a), `lineWFDotAt` | **probada** (`Meta/D3BodyPrf.lean:71`, incondicional) |
| ↳ mitad (b), `premsDotAt` | **abierta**: B1 (cruzar a `Prov` el nivel objeto ya hecho), B2 (puente de la cota), B3 (ensamblaje de `pcc_bdAll_intro`) |
| **`NegVerifier`** | `def : Prop` en `Meta/OmegaReflect.lean:147`. **Ningún teorema en producción lo concluye.** Su bloqueo (`codeNat_ne`, `consN_inj`) vive sólo en `sondeos/CodeNatInj.lean`, fuera del build |

⚠️ **Hueco de ensamblaje no señalado en ningún documento [medido]:** `hA_lineWFDotAt` está probado
e incondicional, pero **no tiene ningún consumidor en todo el árbol**. No existe un
`d3_prf_of_hB` que descargue (a) y deje D3 pidiendo una sola mitad. Formalmente, **el enunciado más
reducido de D3 hoy sigue pidiendo las dos**. Es trabajo de ensamblaje, no de investigación, pero
hoy no está escrito.

---

## 3 · El libro

### 3.1 · Estado **[medido]**

**94 páginas · 80 fragmentos de código citados · cinco controles en verde**, cada uno con su
control positivo pasado. Commiteado en `92a0df7` (2026-09-09).

| parte | capítulos | estado |
|---|---|---|
| I · El problema | 1 Hilbert y Gödel · 2 qué hay que construir · 3 los lenguajes · 4 lo mínimo de Lean | ✅ completa |
| II · El terreno | 5 el kernel FOL⁼ · 6 cuánta metateoría hace falta · 7 Robinson Q++ | ✅ completa |
| III · Aritmetización | 8 codificar estructuras · 9 códigos de sintaxis · 10 el verificador · 11 representabilidad y D1 | ✅ completa |
| IV · Los teoremas | 12–17 | ⬜ **sin empezar** |
| V · Lo que no sale en los libros | **18 el muro de `substfc`** · 22 códigos como numerales | 2 de 12 |
| Apéndices | glosario · notación · licencia | 3 de 6 |

### 3.2 · Los cinco controles, y qué garantiza cada uno **[medido]**

Ésta es la parte del libro que más trabajo ha costado y la que decide su fiabilidad. **Ninguno es
declarativo: cada uno tiene un control positivo comprobado** —se rompe algo a propósito y se
verifica que el control lo caza—.

| control | garantiza | pasa hoy |
|---|---|---|
| `extraer.py` | el código citado **existe**, está en el build, y su nivel objeto/meta está declarado | ✅ 80 fragmentos |
| `verificar_pdf.py` | el código **impreso en el PDF** coincide con el del repo, y nada se sale de la caja | ✅ |
| `simbolos.py` | todo `\ident{}` de la **prosa** nombra algo real; ningún número de capítulo a mano; nada de Markdown filtrado | ✅ 155 identificadores |
| `terminos.py` | ningún término técnico se usa antes de definirse, en orden de lectura real | ✅ 24 términos + 4 notaciones |
| `ambito.py` | sólo el libro entra en el área de preparación | ✅ |

### 3.3 · La deuda del libro **[medido]**

1. **Los 80 fragmentos imprimen «(declarado, sin medir)».** `make axiomas` necesita `lake` y `lean`
   en el PATH y no se ha podido ejecutar desde esta tarea. Es el mayor incumplimiento vivo del
   propio §2.2(c) del plan: el libro promete el *footprint* medido debajo de cada enunciado y hoy
   no lo entrega en ninguno. **No invalida nada de lo impreso** —la marca dice la verdad— pero es
   una promesa a medias.
2. **La bibliografía del capítulo 1 sigue sin verificar** (títulos y fechas de 1930 y 1931, y la
   atribución de D1–D3 a Hilbert–Bernays 1939). Es la única afirmación del libro sin respaldo
   mecanizado. Nota: en esta sesión sí se verificó la otra afirmación histórica del capítulo —la
   frase de Gordan— y resultó **mal atestiguada**; el libro la imprime ya con esa salvedad.
3. **Nueve capítulos de la Parte V y los seis de la Parte IV** siguen sin escribir.

---

## 4 · El camino real

Lo que sigue no es la historia que contaría el índice. Es la que cuenta `git log`.

### 4.1 · Forma del historial **[medido]**

**582 commits en `master`**, del **2026-03-08** al **2026-09-10**: seis meses y dos días.

| mes | commits |
|---|---:|
| 2026-03 | 19 |
| 2026-04 | 16 |
| 2026-05 | 58 |
| 2026-06 | 102 |
| **2026-07** | **189** |
| 2026-08 | 69 |
| 2026-09 | 129 |

El pico de julio y la caída de agosto no son ritmo de trabajo: son el episodio de §4.2. Julio es el
mes en que se construyó mucho sobre suelo inconsistente; agosto, el de pararlo todo y repararlo.

### 4.2 · El arco central: una inconsistencia que duró 38 días **[medido]**

| fase | fecha | commit | qué pasó |
|---|---|---|---|
| **entrada** | 2026-06-18 | `a94de56` | se declara `ax_tc_cons` junto a `tcFn`, como cimiento del lema diagonal |
| latencia | 38 días | — | se construye encima D1, D2, `hI_dot`, los 14 primeros tags |
| **detección** | **2026-07-26** | `d7eb1ee` | «axioms ⊢ bottom VERIFICADO — la teoría objeto es inconsistente» |
| alcance | 2026-07-26 | `99c08f4` | «el daño LLEGA A `Prf` con footprint LIMPIO» |
| pausa | 21 días | — | sin commits |
| diagnóstico | 2026-08-16 | 7 commits | auditoría de **todas** las familias de axiomas: `tc` es la única, «no hay una segunda bomba latente» |
| **reparación** | **2026-08-18** | `6f66e61` → `acdc36a` | `ax_tc_cons` retirado; el lema diagonal, reconstruido por vía numeral. **Coste: −1 axioma, ninguno nuevo** |
| **cuarentena** | 2026-08-18 | mismo commit | 31 módulos apartados, **no borrados** (ADR-013) |
| **recuperación** | **2026-08-23** | `220c1bb` | «la cuarentena está VACÍA — los 31 módulos han vuelto» |

**66 días de episodio; 28 de ciclo activo.** Y el dato que ordena la Parte V del libro: **la
detección llegó 38 días tarde, y el árbol estuvo verde todo ese tiempo.** Una teoría objeto
inconsistente compila.

Los cuatro intentos de reparación descartados están registrados **con evidencia compilada**, no con
una nota: partir `tcFn` (reproduce el mismo ⊥), retirar el axioma sin sustituto (decapita la
diagonalización), relativizar por axiomas (imposible: tricotomía + orden prueban el sucesor sin
inducción), y el paquete de buena formación (`substfc` pide un reconocedor extensional, `tc` una
distinción intensional). El quinto —**códigos como numerales**— es ADR-012 y es el capítulo 22 del
libro.

⚠️ El repositorio insiste, en tres sitios, en que **esto no es una prueba de consistencia**: se
retiró la inconsistencia *conocida y localizada*.

### 4.3 · El segundo arco: el muro de `substfc` **[medido]**

| fecha | commit | hito |
|---|---|---|
| 2026-07-22 | `15dccda` | el muro se identifica: «el plan era erróneo en su forma» |
| 2026-07-24 | — | veredicto: `ax_tc_substfc` sería **inconsistente**, no sólo insólido |
| 2026-07-25 | `f01e029` | la puerta de reescribir los esquemas, **cerrada por imposibilidad estructural** |
| 2026-08-30 | `2f27a29` | el descenso, cerrado |
| **2026-08-31** | **`c1fd804`** | **el muro está roto** |
| 2026-09-07 | `61edd46` | en producción: deja de ser sondeo y pasa a ser teorema |
| **2026-09-10** | `61ecbe8`, `9a608c9` | **los siete reflectores; `pcc_lineWF_tracked` incondicional** |

**Cuarenta días de muro, diez de consecuencias.** Es el capítulo 18 del libro, actualizado hoy con
el cierre.

### 4.4 · Las 21 ADR, y las que se corrigen entre sí **[medido]**

Veintiuna decisiones registradas, de 2026-04-20 a 2026-09-10. Las nueve últimas son todas del
episodio y de lo que vino detrás. Lo notable no es que existan, sino que **se corrigen unas a
otras y lo dicen**:

- **ADR-014 → ADR-015**: sancionar la buena formación no es «más caro», **es otro teorema** —
  cambiaría `axiomsCodeT` y con él la sentencia $G$.
- **ADR-015 → ADR-020**: ADR-020 declara en cabecera que **corrige el argumento de coste** de
  ADR-015. La conclusión sobrevive; la contabilidad, no.
- **ADR-016** corrige un diseño previo del propio proyecto y lo etiqueta **«error trazable»**: la
  restricción R-6 ya decía «dos predicados mutuamente recursivos» y se diseñó uno fusionado sin
  reconciliarlo.
- **ADR-021** (hoy) anota una regla **forzada por una medición, no elegida**: `hPl` no era difícil,
  era **falsa**.

⚠️ Ninguna ADR está marcada formalmente `Obsoleto` ni `Sustituido por`, aunque la plantilla lo
contempla. Las supersesiones están en prosa.

### 4.5 · Los callejones sin salida — el activo menos visible **[medido]**

Se han localizado **25 resultados negativos documentados**, la mayoría con evidencia compilada.
Una muestra de los que más ahorraron:

| qué se intentó | por qué no | evidencia |
|---|---|---|
| `ax_tc_substfc` como axioma objeto | **inconsistente**: prueba que dos cabezas distintas son iguales | derivación en 5 pasos; el nombre aparece 9 veces en el árbol, siempre como aviso |
| extender `CTree` para los 7 tags | vía **muerta**: pide el mismo axioma falso | CHANGELOG 2026-07-24 |
| opción «predicate-free» | **no existe**: 3 rutas fallan y la 4ª pide el axioma inconsistente | 2 workflows, 11 agentes, `d8e9152` |
| `canon_ne` (paso 1.1 de `PLAN-NEGVERIFIER.md`) | **falso**: daría ⊥ | `sondeos/CanonNeRefuta.lean` |
| `consOk` global en el reflector A3 | teorema **verdadero y vacío**: se queda sin testigos. Mató 2 de los 4 intentos | `sondeos/A3ConsOkRefuta.lean` |
| el reconocedor **fusionado** de 12 disyuntos | **no discrimina**: acepta basura | `crit_isFC_junk_REFUTED` |
| **acotar** el número de lifts | acotar y la clausura son **inter-construibles** — reordena la contabilidad, no cambia el residuo | probado en las dos direcciones |
| A4: `hasWitF` sobre argumento abstracto | ⛔ **imposible, no pendiente** | `CRIT_isFC1_rejects_varc` |
| alcanzabilidad por `import` como criterio de limpieza | **falsos negativos** — sólo `#print axioms` es concluyente | trampa documentada tras escaparse un módulo |

Ese último merece subrayarse: es un error de **método** que el proyecto encontró, documentó y
sustituyó por una técnica que sí funciona (convertir el puente sospechoso en `axiom` de Lean y
dejar que `#print axioms` delate a sus consumidores).

---

## 5 · ⛔ Contradicciones documento ↔ árbol

Es el hallazgo con más valor operativo de esta auditoría, y confirma —otra vez— el principio §2.6
del libro: **un documento da fe de lo que su autor creía en una fecha, no del estado del sistema.**

| # | dice el documento | dice el árbol | dónde |
|---|---|---|---|
| 1 | «⬜ **5 de 7** reflectores; bloqueado por `prf_hasWitF_liftfc`» | **7 de 7**; `prf_hasWitF_liftfc` probado | `CURRENT-STATUS-PROJECT.md:17` — **banner del commit de hoy** |
| 2 | «`prf_hasWitF_liftfc` es un FRENTE… no existe ni la mitad TÉRMINO» | probado en 657 líneas | `CURRENT-STATUS-PROJECT.md:25` |
| 3 | fila autoritativa de D3: «(a) ⬜ 5 de 7… (b) no depende de C3» | (a) cerrada; y el propio código corrige que (b) **sí** depende | `CURRENT-STATUS-PROJECT.md:241` |
| 4 | «`pcc_lineWF_tracked` **sigue siendo condicional**»; «esperan a `pcc_eval_liftfc`, **que no existe en ningún sitio**» | está **en el mismo fichero, 400 líneas más abajo** | docstring de `Meta/SubstTreeReflect.lean` |
| 5 | «nada lo consume todavía» | los cuatro tags ya cerrados | docstring de `Meta/EvalLiftfcPrf.lean` |
| 6 | «112 módulos activos… build 124 jobs» | 127 módulos | `PLANNING.md:11` |
| 7 | «**Gödel I — COMPLETO** (`goedel_first_undecidable_real'`)» | ese teorema **no existe** — y el mismo fichero lo dice 13 líneas antes | `PLANNING.md:35` vs `:22` |
| 8 | «D3 reducida a UN SOLO lema… ~2-4 sesiones» | la reducción ha bajado tres niveles desde ahí | `PLANNING.md:40` |
| 9 | `cuarentena/README.md` presenta los 7 reflectores como problema abierto | cerrados | última edición 2026-08-23 |
| 10 | `PLAN-NEGVERIFIER.md` §B declara un bloqueo | `NEXT-STEPS.md:534` dice que **es falso desde julio** | el plan no se ha corregido |

**El patrón, y es el importante:** los cuatro primeros están **dentro del commit de hoy**
(`37e582c`, titulado precisamente «proyectar C3 CERRADO»). El documento contiene a la vez el bloque
nuevo y correcto (`:166-178`) y el **banner viejo** (`:14-25`) y la **fila de tabla vieja** (`:241`)
sin actualizar. Quien lea las primeras treinta líneas del documento autoritativo se lleva un estado
**dos sesiones obsoleto**.

Y el #4 es el más peligroso de todos: **es un docstring que niega un teorema de su propio fichero.**

`PLANNING.md` lleva cuatro días y unos quince commits de retraso: es hoy el documento menos fiable
de los tres de estado.

### 5.1 · Lo que esta auditoría ya ha corregido

- **Capítulo 18 del libro**, actualizado hoy con el cierre de los siete reflectores, el enunciado
  incondicional de `pcc_lineWF_tracked`, y la advertencia de que esto **no** cierra D3.
- Las mediciones del **capítulo 6** se han vuelto a comprobar contra el árbol de hoy y **siguen
  siendo ciertas**: dos usos de `Classical`, cero `Sort u`, un solo `termination_by`.
- Los **80 fragmentos** citados siguen coincidiendo con el repositorio pese a que el código se
  movió: el control §2.1 lo verifica en cada compilación.

---

## 6 · Balance

**Lo conseguido, en una frase:** una formalización completa y sin `sorry` de la aritmetización de
la sintaxis, con D1 y D2 demostradas desde la base, el punto fijo construido, la mitad demostrada
del primer teorema de Gödel limpia de postulados, y el segundo teorema disponible **módulo un
axioma declarado**.

**Lo que falta, sin adornos:** la mitad (b) del cuerpo de D3 —tres piezas identificadas—, y
`NegVerifier`, que cierra `⊬¬G` y hoy no tiene ni una línea de construcción en producción.

**Lo que este proyecto hace y casi ningún otro:** guardar los fracasos. Veinticinco resultados
negativos documentados, la mayoría compilados; una cuarentena que apartó 31 módulos en vez de
borrarlos y los devolvió en cinco días; y ADRs que se corrigen unas a otras dejando por escrito
cuál era el error. El libro existe porque ese material existe.

**El riesgo mayor, y no es matemático:** la deriva entre los documentos de estado y el árbol. Diez
contradicciones vivas, cuatro de ellas en el commit de hoy, y una dentro de un docstring que
contradice a su propio fichero. El proyecto ya tiene la doctrina (§2.6) y la herramienta
(`check-doc-sync.bash`); lo que falta es aplicarla al **cuerpo** de los documentos y no sólo a su
banner.

---

## 7 · Lo que NO se ha medido

Se declara para que nadie lo lea como verificado:

1. **Ningún `#print axioms`.** No se ha ejecutado `lake build`. Todas las afirmaciones «net-0» y
   «footprint = base sancionada» de este informe y del libro son **[documentado]**.
2. **El estado del build** (jobs, tiempo, warnings).
3. **El contenido de 10 de los 60 `sondeos/`**, no catalogados en su `README.md` (los seis
   `Medir*`, entre otros).
4. **La fecha exacta en que la inconsistencia se hizo explotable**: `ax_tc_cons` entra el
   2026-06-18, pero la interacción concreta con `ax_L0_cons_def` que produce ⊥ podría ser anterior
   si esa segunda pieza ya existía. No se ha datado.
5. **El reflog**: no se ha buscado commits huérfanos o reescritos. Las cifras 582 (`master`) y 608
   (todas las refs) se explican por dos ramas remotas muertas de mayo y tres de trabajo.

---

*Auditoría hecha sobre `HEAD = 37e582c`. Las cifras de este documento caducan: se han medido hoy y
el proyecto avanza a más de veinte commits por día. Lo que no caduca es el método — volver a
medirlo, no volver a citarlo.*

---
---

# Reauditoría del mismo día — 2026-09-10, tarde · **D3 CERRADA**

`HEAD = 50e8864`. Entre la auditoría de arriba y ésta han pasado **siete commits y unas seis
horas**, y el proyecto ha cerrado su frente principal. Se deja como continuación y no como
documento nuevo, porque la lección está justo en la distancia entre las dos mitades.

## R1 · Lo que ha cambiado **[medido]**

| | antes (`37e582c`) | ahora (`50e8864`) |
|---|---|---|
| `d3` | `axiom` (`Meta/GodelTwo.lean:60`) | **`theorem`** (`:71`), **cero hipótesis**, misma firma exacta |
| `axiom` de Lean en producción | **7** | **6** |
| mitad (a) de D3 | probada, **sin consumidores** | consumida por `d3_prf_real` |
| mitad (b) de D3 | abierta, en tres piezas | **cerrada** |
| Gödel II | «módulo el `axiom d3`» | sin esa condición |

**El commit que la cierra es `9ca5e66`**, y toca sólo dos ficheros. La secuencia entera, en una
tarde:

| hash | qué cerró |
|---|---|
| `e7a82d1` | **B1** — `premsOf` reflejado dentro de $\Prov$, las 21 ramas (`Meta/PremsOfDotPrf.lean:1007`) |
| `c4e81b5` | **B2** — la cota, cruzada dentro de $\Prov$ (`Meta/D3BodyPrf.lean:202`) |
| `6323561` | **B3** — el chasis inductivo interior, ocho de sus nueve obligaciones |
| `e237474` | la **novena** (`premsBody_deuda`, `Meta/PremsBdAllPrf.lean:1064`) |
| **`9ca5e66`** | **el ensamblaje y la retirada del axioma** (`d3_prf_real`, `:1351`) |

### El hueco de ensamblaje que señaló la auditoría de la mañana: **cerrado** **[medido]**

Se reportó que `hA_lineWFDotAt` estaba probada e incondicional y **no la consumía nadie**. Hoy
tiene dos consumidores reales, los dos en `Meta/PremsBdAllPrf.lean` (`:1348` y `:1352`), y el
segundo es literalmente `d3_prf_of_halves φ hA_lineWFDotAt hB_premsDotAt`. Era ensamblaje, como se
dijo, y se hizo.

### Lo que no cambió, y es la moraleja

Ni el enunciado de D3, ni el de `goedel_second'`, ni una línea de su demostración: `con_imp_godel'`
sigue invocando `d3` en la misma línea de siempre. Lo único que cambió es que `d3` ya no se supone.
**Retirar un axioma sólo puede fortalecer lo que había** — y eso vale porque el postulado estuvo
todo el tiempo a la vista y con la firma exacta que iba a tener el teorema.

## R2 · El frente nuevo: `NegVerifier` **[medido]**

Sigue **exactamente igual** que esta mañana: `def : Prop` en `Meta/OmegaReflect.lean:147`, y
**ningún teorema en producción lo concluye**. Sus tres usos lo toman como hipótesis.

Contra el plan (`PLAN-NEGVERIFIER.md` §2), que propone seis módulos con nombre de fichero:

| módulo | fichero previsto | estado real |
|---|---|---|
| A · decodificador | `Meta/CodeDecode.lean` | ✅ 438 líneas |
| B · los 21 tags | `Meta/LineWFCases.lean` | ✅ 245 líneas |
| C · refutar `lineWF` | `Meta/LineWFNeg.lean` | ⛔ **no existe** |
| D · `runFn`/`In`/`chainOk` negativos | `Meta/ChainNeg.lean` | ⛔ **no existe** |
| E · solidez estructural | `Meta/VerifierSound.lean` | ⛔ **no existe** |
| F · ensamblaje | `Meta/NegVerifierPrf.lean` | ⛔ **no existe** |

⭐ **Y el bloqueo que el plan declara ya no existe.** `codeNat_ne` y `consN_inj` —que según
`PLAN-NEGVERIFIER.md:41` y `NEXT-STEPS.md:533` «sólo viven en `sondeos/`, fuera del build»— están
**en producción desde el 2026-09-02** (`Meta/CodeNatInjPrf.lean:191` y `:85`). El plan lleva sin
tocarse desde el 2026-09-01, un día antes.

## R3 · ⛔ La deriva documental, ahora con causa raíz medida

Esta mañana se reportaron diez contradicciones. Ninguna de las tres que seguían vivas se ha
corregido, y el cierre de D3 ha creado una cosecha nueva. **Lo más grave:**

| dónde | qué afirma hoy |
|---|---|
| **`Meta/GodelTwo.lean:38`** | «D3 — **postulado** (`d3` abajo)… la pieza pendiente más grande» — **33 líneas por encima del teorema** |
| **`Meta/GodelTwo.lean:110`** | docstring de `goedel_second'`: «D2 real, **D3 postulado**» |
| **`Meta.lean:12`** | el barril: «Gödel II, **módulo el axioma d3**» |
| **`AXIOMS.md:59`** | encabezado «Axiomas de Lean (**7**)» — con la fila 7 tachada y marcada RETIRADA justo debajo |
| **`REFERENCE.md:298`** | «7 `axiom` de Lean» — contradice a `:8` y `:190` del mismo fichero, que dicen 6 |
| **`doc/REFERENCE-Incompleteness.md:15`** | la **cabecera**: «módulo `axiom d3`, y la construcción **en curso** de D3» — y §3.67 del mismo fichero documenta el cierre |
| **`CURRENT-STATUS-PROJECT.md:259`** | «D3 está FUERA de la cadena activa (la capa rastreada está en `cuarentena/`)» — doble falsedad: `cuarentena/` está vacía desde el 23 de agosto |
| **`PLANNING.md:35`** | «Gödel I — COMPLETO» — sigue contradiciendo a `:19-23` del mismo fichero, **sin cambios desde el 4 de septiembre** |

### ⭐ La causa raíz, y es reparable

**`check-doc-sync.bash:108`**: *«ALCANCE: sólo la REGIÓN DE CABECERA (primeras 100 líneas) de cada
doc autoritativo.»*

Eso explica el patrón entero. El commit `50e8864` pudo declarar la sincronía en verde con ocho
contradicciones vivas **a partir de la línea 218** del documento autoritativo. No es que nadie
mire: es que el control mira sólo el banner, y el banner es justamente la parte que sí se
actualiza.

Es el mismo principio §2.6 de este libro, en su forma más pura: **el control existía, pasaba, y no
cubría el cuerpo**. Auditar el banner es auditar lo que ya está bien.

## R4 · Lo que esta reauditoría corrigió en el libro

El cierre de D3 dejó falsas cuatro afirmaciones impresas, todas escritas **esa misma mañana**:

- **Capítulo 15**, reescrito de medio en adelante: «D3: el axioma que queda» → «la que Gödel
  anunció, y estuvo postulada hasta anteayer», con `theorem d3`, `d3_prf_real`, `pcc_eval_premsOf`
  y las dos mitades cerradas. Incluida la lección que el episodio regala: *retirar un axioma sólo
  puede fortalecer lo que había*, y por qué eso hace que esta clase de deuda sea segura de contraer.
- **Capítulo 18**: el aviso de que aquello «no cerraba D3» pasa a decir cuánto tardó en cerrarla —
  seis horas más.
- **Capítulo 11**: la tabla decía «Gödel II, más el `d3` pendiente».
- **`PLAN-LIBRO.md`**: la base sancionada listaba siete axiomas, y el capítulo 17 se llamaba
  «Gödel II, módulo `d3`». Reorientado: ya no va de publicar con una condición al margen, sino de
  qué hipótesis quedan cuando no queda ninguna deuda.

## R5 · Dos notas de operación

1. **El árbol no está limpio, y no es del libro.** La otra tarea tiene preparados
   `sondeos/NegVerifierModE.lean`, `PLAN-NEGVERIFIER.md`, `sondeos/README.md` y
   `Meta/PremsOfDotPrf.lean`: está trabajando en `NegVerifier` ahora mismo. `scripts/ambito.py`
   lo detecta y **se niega a preparar el libro** — que es exactamente lo que debe hacer. El commit
   del libro tiene que esperar a que esa tarea cierre el suyo.
2. **`make` completo ya no cabe en una sola llamada** desde esta tarea: con 110 páginas, extraer +
   tres pasadas de LaTeX + los tres controles pasa del límite de tiempo del shell, y una compilación
   interrumpida **deja corrupto `libro.out`** (el fichero de marcadores) y hace fallar la siguiente
   con un «Runaway argument». Se arregla vaciando `libro.out`, `libro.aux` y `libro.toc` y forzando
   la recompilación. Anotado en el `README.md` del libro.

---

## R6 · 🏁 Qué se hizo con esta auditoría — **cerrada el mismo día**

Se escribe aquí porque una auditoría que no registra su desenlace es exactamente el tipo de
documento del que ella misma se queja.

### R6.1 · La causa raíz: **reparada**

§5 y R3 midieron que `check-doc-sync.bash` recorría **sólo las primeras 100 líneas** — *«auditar el
banner es auditar lo que ya está bien»*. La otra tarea añadió el bloque **`[A2]`**, que recorre el
cuerpo entero con los mismos filtros de historicidad.

⚠️ **Con un matiz que la auditoría no tenía, y que es justo anotar**: la acotación **no era un
descuido**. Sin ella, los diarios de `NEXT-STEPS.md` disparan una docena de falsos positivos, y un
control que grita lobo se deja de usar — que es el otro fallo, el de §27.1 del `AI-GUIDE`. Por eso
`[A2]` entra como **AVISO** y no como error: lo que rompe sigue siendo la cabecera. Documentado en
`AI-GUIDE.md` §27.2.

### R6.2 · Las contradicciones: **corregidas**

Con el control puesto salieron **52 líneas**. Ocho eran afirmaciones de estado **actual** y falsas,
y son las que R3 listaba:

| dónde | qué decía | estado |
|---|---|---|
| `Meta/GodelTwo.lean:38` | «D3 — **postulado**… la pieza pendiente más grande» | ✅ corregido |
| `Meta/GodelTwo.lean:110` | docstring de `goedel_second'`: «D2 real, **D3 postulado**» | ✅ corregido |
| `Meta.lean:12` | el barril: «Gödel II, **módulo el axioma d3**» (y citaba dos teoremas inexistentes) | ✅ corregido |
| `AXIOMS.md:59` | cabecera «Axiomas de Lean (**7**)» | ✅ corregido |
| `REFERENCE.md` | «7 `axiom` de Lean» en el cuerpo; §5 tres sesiones obsoleta; «consolidar Gödel II **módulo el axioma D3**» | ✅ corregido |
| `doc/REFERENCE-Incompleteness.md:15` | la cabecera: «módulo `axiom d3`, y la construcción **en curso** de D3» | ✅ corregido |
| `CURRENT-STATUS-PROJECT.md:259` | «D3 está **FUERA** de la cadena activa (la capa rastreada está en `cuarentena/`)» — doble falsedad | ✅ corregido |
| `PLANNING.md:35` | «Gödel I — **COMPLETO**» citando un teorema que no existe | ✅ marcado **entero** como histórico |

Y dos más que la auditoría no había listado y `[A2]` sacó: `GODEL-STATUS.md` citaba
`goedel_first_real'` (**inexistente**) y daba `NegVerifier` por «no construido, módulo B en curso»;
y `cuarentena/README.md` presentaba los **7 reflectores** como «un problema abierto de verdad»
desde el 23 de agosto.

El resto de las 52 eran historia legítima a la que sólo le faltaba la **marca**; se marcaron.

### R6.3 · Y `NegVerifier` se movió esa misma tarde

R2 lo dejaba con **cuatro** módulos inexistentes de seis. Hoy:

| módulo | estado |
|---|---|
| **E** · solidez estructural | 🏁 **hecho** — y en diez líneas: el decisor no tiene que ser el verificador objeto, basta el decodificador meta, y entonces `verifier_sound` **es** `decodeChain_prf` |
| **C**, **D** · completitud negativa | ⬜ **enunciados** (`DEUDA_chainNeg`, `DEUDA_inNeg`) y desbloqueados por \textsc{adr}-022 |
| **F** · ensamblaje | ⬜ — pero `negVerifier_of_deudas` ya hace su parte |

⭐ **Y R2 acertó de pleno en una cosa**: el bloqueo que el plan declaraba «ya no existe». Lo que la
auditoría no podía saber es que el bloqueo **real** era otro —la clase de testigos admitía basura
cuya refutación exigía evaluar Cantor—, y que se resolvería estrechándola (\textsc{adr}-022).

### R6.4 · La lección de método que este episodio deja al libro

**Un lector que sólo puede LEER resultó el mejor detector de deriva que tiene el proyecto.** El
libro tiene los `.lean` en sólo lectura (§0 de `PLAN-LIBRO.md`), y precisamente por eso audita sin
poder «arreglarlo de paso» — que es como se generan la mitad de las contradicciones que encuentra.

Es material para la Parte V, junto a M-6 de `MATERIALES.md`.


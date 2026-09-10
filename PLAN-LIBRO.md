# PLAN — Libro en LaTeX: *Incompletitud, formalizada*

> ## ESTADO REAL — 2026-09-10h · `master` · **Parte IV escrita hasta el cap. 15**
>
> **Build 142 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **128 módulos activos** (Minimal 11 + Meta 106 + Full 11) **+ 0 en `cuarentena/` + 61 en `sondeos/`.**
> **6 `axiom` de Lean · 141 axiomas objeto** en `axioms` (= 34 `coreAxioms` + 107 `codingAxioms`).
>
> ⚠️ El banner anterior (2026-09-04, `1ab7a96`) decía **123 jobs · 109 módulos · 7 axiom**, con
> `d3` todavía postulado. Es exactamente la deriva que la auditoría de `doc/book/AUDITORIA-2026-09-10.md`
> §5/R3 documenta — y que, por una vez, se corrige aquí en vez de anotarse.
>
> **Ubicación acordada: `doc/book/`** (no `libro/`, como decía la versión anterior de este plan).
> Formato **LaTeX**. Idioma **español**.
>
> ⚠️ Este plan **fusiona** los dos planes previos del libro — el técnico (`PLAN-LIBRO.md`
> 2026-08-22) y el pedagógico (`Sobre_el_libro.md`) — y **corrige** las afirmaciones que el
> proyecto ha refutado desde entonces. El registro de correcciones está en §8.

**Última actualización:** 2026-09-09 (2ª) — **Parte I escrita** y migración 3b completada;
previo, **§3 reestructurado**: nueva **Parte I pedagógica**
(los artículos de Gödel, los lenguajes, lo mínimo de Lean) y cinco partes en total; **nuevo §2.9**
(ninguna parte empieza sin decir qué pregunta contesta) con los números de capítulo mecanizados;
previo, **§2.8** (una fórmula se lee en voz
alta la primera vez) y **M-4** en la cantera; previo, **`MATERIALES.md`**, la cantera de material
pendiente de capítulo; previo, **§2.7** (nada se usa antes de estar
definido, sin exenciones) + capítulo de apertura; previo, **§2.6** (un docstring es testimonio,
nunca evidencia) + registro `DOCSTRINGS-NO-FIABLES.md`; previo, **licencia doble** (prosa CC BY-SA 4.0, código MIT);
previo, **§0: MANDATORY de ámbito de escritura**
(mecanizado en `scripts/ambito.py`); previo, **§2.5** (el nivel objeto/meta
se imprime, en dos ejes); previo, **§2.2** («sólo se expone lo
demostrado desde la base»); fusión de los dos índices, corrección del cap. 11 (`⊬¬G`), cierre del
arco de la cuarentena y cuatro capítulos nuevos (Parte IV)
**Creado:** 2026-08-19 · **Autor:** Julián Calderón Almendros

---

## 0 · ⚠️ MANDATORY — ámbito de escritura de la tarea del libro

**Q++ está en desarrollo activo.** La tarea del libro y la tarea de programación y prueba corren en
paralelo sobre el mismo repositorio, así que el libro escribe en un ámbito **cerrado**:

| escribible | sólo lectura |
|---|---|
| `PLAN-LIBRO.md` | todo `*.lean` |
| `Sobre_el_libro.md` | los `.md` de estado (`NEXT-STEPS`, `CURRENT-STATUS-PROJECT`, `DECISIONS`, `AXIOMS`, `REFERENCE.md` + `doc/REFERENCE-*.md`, `CHANGELOG`, …) |
| todo `doc/book/**` | los scripts de la raíz, `lakefile.lean`, `Makefile`, `.gitignore` |

**Consecuencias, y no son sólo de cortesía:**

- **Cada commit tiene un único dueño.** Un commit de la tarea del libro que tocara un `.lean` haría
  imposible saber, luego, si un fallo de build vino del libro o del desarrollo.
- **El libro se alimenta del repo, nunca al revés.** Si al escribir un capítulo se descubre que un
  documento de estado miente —y ha pasado ya tres veces—, **no se corrige aquí**: se anota en el
  capítulo o se reporta, y lo arregla la otra tarea. La única excepción es `PLAN-LIBRO.md`, que es
  del libro.
- **`doc/book/` no toca la compilación Lean**: la `lean_lib` sólo alcanza `.lean` importables desde
  `ROBINSON_PlusPlus.lean`. `lake build` debe seguir dando **el mismo número de jobs**.

**Está mecanizado.** `doc/book/scripts/ambito.py` comprueba el **área de staging** —que es lo que de
verdad se sube— y falla si hay preparado algo fuera del ámbito. Los ficheros modificados fuera del
ámbito no son un error (son el trabajo en curso del autor) pero se listan, para que nadie los
arrastre por descuido.

```bash
make ambito                    # comprueba
make subir MSG='...'           # compila + verifica + prepara SÓLO el libro + commitea
```

`make subir` **nunca** hace `git add -A`: añade explícitamente `PLAN-LIBRO.md`,
`Sobre_el_libro.md` y `doc/book`, y aborta si el guardián encuentra un intruso.

---

## 1 · Contexto y propósito

`ROBINSON_PlusPlus` lleva **109 módulos Lean 4 activos** (más 57 sondeos compilados fuera del
build) formalizando los teoremas de incompletitud de Gödel sobre un kernel FOL⁼ propio, sin
Mathlib. Todo el conocimiento acumulado vive en **25 ficheros `.md` de raíz + 5 nodos
`doc/REFERENCE-*.md`** que son **notas de trabajo**, no exposición: `NEXT-STEPS.md` es un puntero de
reanudación, `CHANGELOG.md` un diario, `DECISIONS.md` un registro de ADRs.

El libro convierte ese material en una **obra expositiva** con tres hilos entretejidos en todo
momento:

| hilo | qué aporta |
|---|---|
| **Matemática pura** | enunciados y demostraciones en notación estándar, legibles sin Lean |
| **Código Lean 4 real** | el mismo resultado, tal y como está formalizado y **compilando** |
| **Lenguaje pedagógico** | la estructura general: por qué se hace así, qué se intentó antes, qué falló |

**Tesis del libro (lo que lo hace distinto):** casi toda la literatura presenta Gödel como un
resultado terminado y elegante. Este libro cuenta **la formalización real**, incluidos los muros y
los errores — que es donde está el contenido didáctico que no aparece en los manuales.

**Público:** el propio autor primero (es una guía personal para seguir y dirigir el proyecto), y
después el lector que sabe algo de lógica y quiere ver una formalización de verdad, no un esquema.

### 1.1 · La fusión de los dos planes previos

Existían dos documentos con dos libros distintos dentro. Este plan se queda con lo mejor de cada uno
y **retira ambos como planes autónomos**:

| documento | qué aportaba | qué se conserva aquí |
|---|---|---|
| `PLAN-LIBRO.md` (2026-08-22) | estructura técnica I–IV, **Parte IV como núcleo original**, regla de extracción automática, infraestructura LaTeX | **todo**, actualizado y ampliado |
| `Sobre_el_libro.md` | la **progresión pedagógica**: arrancar por FOL, lenguaje natural, teoría objeto vs meta como capítulo propio, gramática y reglas de inferencia explícitas antes de la autorreferencia | **la ordenación de las Partes I–III** y el capítulo 3, que el plan técnico no tenía |

⚠️ `Sobre_el_libro.md` pasa a ser **nota histórica**: no se borra, pero deja de ser normativo. Si
diverge de este fichero, manda este fichero.

---

## 2 · Principios editoriales

Son **nueve**, y los nueve nacen de un fallo real de este proyecto. Ninguno es estético.

### 2.1 · Sólo se publica lo que compila

**Regla dura:** todo bloque de código Lean del libro se **extrae del repo**, nunca se escribe a
mano en el `.tex`. Si un módulo no compila, su sección no entra.

Motivo: el proyecto descubrió que una inconsistencia latente sobrevivió meses de trabajo. Un libro
con código copiado a mano acumularía el mismo tipo de deriva silenciosa.

Mecanismo: cada fragmento se referencia por **fichero + nombre de declaración**, y
`doc/book/scripts/extraer.py` los vuelca a `doc/book/extraido/` antes de compilar. Nada de
copiar-pegar. El extractor **falla ruidosamente** si la declaración citada no existe.

### 2.2 · Sólo se expone lo que está demostrado **desde la base**

Que un fragmento compile **no basta**. Un teorema entra en el libro **sólo si la cadena entera que
lo sostiene está en el repo y en el build**, desde los axiomas hasta él: sin `sorry`, sin hipótesis
colgante, sin lema prestado de fuera, y con su **footprint auditado**.

Tres razones, las tres aprendidas a golpes aquí:

1. **La cuarentena.** 31 módulos de teoremas *formalmente correctos* resultaron **vacuos**: estaban
   demostrados sobre una teoría que probaba ⊥. **Compilar no es probar; probar es probar sobre una
   base sancionada.**
2. **`lake build` puede dar verde sin construir lo que crees.** La `lean_lib` sólo construye lo
   alcanzable desde el módulo raíz: un fichero puede estar en su sitio, compilar suelto, y no formar
   parte de nada. Señal de alarma histórica: **el número de jobs no cambia** al añadir módulos.
3. **La alcanzabilidad por `import` da falsos negativos**, y un crawler de dependencias no funciona
   en Lean 4. Lo único concluyente es **`#print axioms`**.

**Regla operativa — la comprueba el extractor.** Para toda declaración citada como teorema:

| | control |
|---|---|
| **(a)** | es **alcanzable desde `ROBINSON_PlusPlus.lean`** — está en el build, no sólo en el disco |
| **(b)** | `lake build` está **verde** en el commit citado, con su número de jobs registrado |
| **(c)** | su **`#print axioms` se imprime en el libro** junto al enunciado |
| **(d)** | ese footprint está contenido en la **base sancionada**, y cada elemento suyo tiene entrada en el Apéndice A |

**La base sancionada** — y no hay más:

| capa | contenido |
|---|---|
| kernel de Lean | `propext`, `Classical.choice`, `Quot.sound` |
| meta-reglas ω de FOL (6) | `imp_intro`, `gen`, `raa`, `dne`, `or_elim`, `ex_elim` (`FOL/MetaRules.lean`) |
| `axiom` de RPP (**6**) | `ax_induction`, `ax_list_induction`, `ax_mod2_alternation`, `ax_p_tfa`, `ax_axiomsCodeT_eq`, `prf_axiomsCodeT_eq` — **`d3` RETIRADO el 2026-09-10** (`9ca5e66`): pasó a teorema |

Cualquier símbolo que aparezca en un `#print axioms` **fuera de esa tabla** es un error del libro,
no una nota a pie de página.

**Los resultados «módulo algo» no quedan prohibidos: quedan obligados a declararlo en el enunciado.**
Hay exactamente **dos** en el estado actual, y los dos son teoremas legítimos del libro *siempre que
se impriman con su condición a la vista, no en una nota al pie*:

- ~~**`goedel_second'`** — módulo el `axiom d3`~~ — **SALDADO el 2026-09-10**: `d3` es teorema. Le quedan sus tres hipótesis explícitas (`fp_bwd`, `nec1`, `hgi`), que no son ninguna de las condiciones de derivabilidad;
- **`goedel_first_undecidable_numeral`** — toma **`Reflects` como hipótesis META explícita**, sin
  descargar (para descargarla falta `NegVerifier`).

✅ **Corolario que afectaba al calendario, SALDADO (2026‑09‑08).** El capítulo 24 (la rotura del
muro de `substfc`) narraba un resultado que vivía en `sondeos/`, **fuera del build**. Ya no:
`prf_hasWitF_real` está en `Meta/CodeWitnessPrf.lean:2142` (medido el 2026-09-09; la nota decía 2140), y `pcc_eval_substfc` /
`pcc_eval_substfc_wit` en `Meta/EvalSubstfcPrf.lean` desde la promoción **B3.4** (§3.42), con
footprint = la base sancionada. ⇒ **el capítulo 24 ya puede presentar sus resultados como teoremas
del libro**, sin la marca «fuera del build». Era la única dependencia real del libro respecto al
desarrollo, y queda cerrada.

### 2.3 · Los `sondeos/` son citables, pero se etiquetan — y no sostienen teoremas

57 de los resultados más valiosos del proyecto viven en `sondeos/`, **fuera del build de `lake`**.
No citarlos empobrecería gravemente la Parte IV; citarlos como si fueran producción violaría §2.2.

| uso | ¿admisible? |
|---|---|
| **narrar el episodio** (qué se intentó, qué se midió, qué se aprendió) | ✅ sí |
| **resultado NEGATIVO** — una refutación compilada (`canon_ne` es falso, A4 es imposible, la línea basura de la rama C) | ✅ sí: la refutación *es* el resultado, y su evidencia es exactamente que compila |
| **medición** (líneas, footprint, censo, cuánto queda) | ✅ sí, con la fecha de la medición |
| **teorema de la exposición** en las Partes I–III | ⛔ **no**, hasta que esté promovido a `Meta/` y sea alcanzable desde la raíz |

**Marcado obligatorio:** todo fragmento de `sondeos/` se imprime con la marca visible
**«fuera del build»**, la orden exacta con la que se recompila
(`lake env lean sondeos/<fichero>.lean`, `EXIT=0`) y su footprint. Lo mismo para `cuarentena/` si
algún día vuelve a tener contenido.

#### 2.3bis · Código de OTRO proyecto: se cita como evidencia, nunca como base

*(Añadido el 2026-09-09, al escribir el capítulo 6.)* El libro cita código de proyectos hermanos del
autor —hoy `Peano`— cuando ese código es **la evidencia de una afirmación sobre el ecosistema**:
que una técnica es portable, que un experimento ya se hizo, que una deuda se saldó. Es un tercer
estatuto, distinto de producción y de sondeo, con reglas propias:

| | producción | sondeo | **externo** |
|---|---|---|---|
| alcanzable desde la raíz | ✅ obligatorio | ⛔ prohibido | ⛔ prohibido |
| footprint impreso | ✅ obligatorio | opcional | **⛔ no se imprime** |
| puede sostener un teorema del libro | ✅ | ⛔ | **⛔** |
| marca visible | — | «fuera del build» | **«otro proyecto: NOMBRE»** |

La prohibición del footprint no es un descuido: medir la base de un teorema **ajeno** e imprimirla
con la misma tipografía que las nuestras invitaría a leerlo como parte de nuestra cadena. Se declara
con `"capa": "externo"` y un campo `"proyecto"` obligatorio; `scripts/extraer.py` falla si falta, y
`scripts/simbolos.py` informa aparte de los identificadores que sólo existen en esos proyectos.

### 2.4 · El libro no puede afirmar lo que el proyecto ha refutado

Este principio nace de la auditoría de §8. El libro se escribe **contra el estado real**, no contra
la memoria de cómo estaban las cosas. Hay una **lista de afirmaciones prohibidas** que a día de hoy
son falsas y que versiones anteriores de la documentación —incluida la anterior de este plan— daban
por buenas:

| ⛔ no escribir | ✅ el hecho |
|---|---|
| «el obstáculo de `⊬¬G` es el intuicionismo del kernel FOL» | el paso DNE no ocurre en `Prf` sino en `⊢`, que es **clásico** (`FOL/MetaRules.lean:59`), compilado en `Meta/DiagonalTwo.lean:129`. **Resuelto** (`NEXT-STEPS.md` §3.32.3) |
| «hace falta construir `repr_neg`» | **no existe ni hace falta**: su papel lo juega `Reflects`, reducido en `reflects_of_omega` (`Meta/OmegaReflect.lean:157`) |
| «`NegVerifier` es indemostrable mientras `axiomsCodeT` sea opaco» (`PLAN-NEGVERIFIER.md` §B) | **falso desde julio**: `ax_axiomsCodeT_eq` levantó la opacidad y `neg_In_axiomsCodeT` (`Meta/AxiomListCode.lean:70`) está compilado desde el 14-jul |
| «`canon_ne` es el paso 1.1 del plan» | **`canon_ne` es FALSO**: un `cons` *es* un número (`cons nil nil = 2`), refutado en `sondeos/CanonNeRefuta.lean`. Sustituto net-0: `codeNat_ne` |
| «falta probar `hasWitF` sobre argumento abstracto» (A4) | **es imposible, no pendiente**: `ENS.CRIT_isFC1_rejects_varc` lo refuta para cualquier testigo |
| «la cuarentena tiene 21 módulos» / «31 módulos perdidos» | la cuarentena está **VACÍA**: 31 → 0, repatriación completa |
| «G es indecidible» a secas | sólo se tiene **`⊬G`**. Ver cap. 11 |
| «Gödel I sobre una teoría consistente» | se retiró la inconsistencia **conocida y localizada**. **No es una prueba de consistencia** |

**Procedimiento:** antes de cerrar cualquier capítulo, releer `NEXT-STEPS.md` (banner + árbol de
ramas) y `doc/REFERENCE-Incompleteness.md` §3.24–§3.32. Y aplicar la lección de `AI-GUIDE.md` §27:
**recorrer el cuerpo, no sólo el banner.**

### 2.5 · El nivel —objeto o meta— **se imprime**

En un libro de metamatemática la pregunta *¿esto es lenguaje objeto o lenguaje meta?* se plantea en
cada línea, y responderla mal es lo que costó 31 módulos: `tcFn` es una operación sobre **sintaxis**
declarada como función **objeto**, y una función objeto sólo puede depender de **valores**
(ADR-012). Una distinción cuya violación produce una inconsistencia no puede quedar en convención
mental: **tiene que verse.**

**Y no es binaria.** Son **dos ejes independientes**, y cada fragmento de código y cada enunciado del
libro llevan una chapa con los dos:

**Eje 1 — ¿quién afirma?** No son «dos cálculos»: son **cuatro relaciones de derivabilidad de
tipos distintos**, y la chapa lleva el tipo a la vista (si arrastra contexto, con `Γ`).

| chapa | tipo en Lean | ¿contexto? | ¿r.e.? | papel |
|---|---|:--:|:--:|---|
| `Lean` | — | — | — | la metateoría: un teorema *sobre* el sistema |
| `Γ⊢` | `List Formula → Formula → Prop` | sí | **no** | el cálculo ω; sólido en ℕ |
| `Prf₀` | `Formula → Prop` | no | sí | Hilbert **intuicionista** |
| `Prf` | `Formula → Prop` | no | sí | Hilbert clásico: **el que se aritmetiza** |
| `ΓPrfH` | `List Formula → Formula → Prop` | sí | sí | variante con contexto; ahí vive la deducción |

Los puentes van en un solo sentido —`Prf₀ φ → Prf φ → ∀Γ, PrfH Γ φ` y `Prf φ → axioms ⊢ φ`— y el
**recíproco `axioms ⊢ φ → Prf φ` es falso, y tiene que serlo**: si valiera, `⊢` sería r.e. y Tarski
cerraría el paso. Esa asimetría *es* la razón de que haya dos cálculos, así que la chapa tiene que
decir en cuál se afirma. Medido: `prf0_to_derives` no usa ninguna meta-regla ω y `prf_to_derives`
usa `dne` una vez — la diferencia entre los dos puentes es exactamente `{FOL.MetaRules.dne}`.

**Eje 2 — ¿sobre qué?** Cinco valores:

| valor | qué es |
|---|---|
| `Lean` | objetos nativos: `Nat`, listas, recursión estructural |
| `sintaxis` | la representación en Lean de la sintaxis: `Term`, `Formula` |
| `objeto` | enunciados de la teoría aritmética: `+`, `·`, `σ`, sus axiomas |
| `código` | términos objeto que **denotan** sintaxis: `⌜φ⌝`, `numeral` |
| `Prov` | dentro del predicado de demostrabilidad: la teoría hablando de sí misma |

Tres enunciados que ocupan tres casillas distintas, y que conviene comparar en el libro:
`two_mul_consN` afirma **en Lean** sobre `Nat`; `prf_formCode_numeral` afirma **en `Prf`** sobre
**códigos**; `hFN` afirma lo mismo pero **en `⊢`**. Y `pcc_dot_cons` afirma en `Prf` **dentro de
`Prov`**: cuatro niveles de distancia entre el primero y el último.

**Regla operativa.** El campo `nivel: [afirma, sobre]` es **obligatorio** en `fragmentos.json`; el
extractor rechaza el fragmento que no lo lleve, y emite la chapa sobre la caja de código. Además usa
**la convención de nombres del proyecto como control cruzado** —`pcc_` afirma en `Prf` sobre `Prov`,
`prf_` afirma en `Prf`, `ax_` es objeto en `⊢`— y avisa cuando el prefijo y el nivel declarado no
cuadran. Es aviso y no error: las convenciones tienen excepciones legítimas, y un control que grita
lobo se acaba ignorando (misma doctrina que `check-doc-sync.bash` [B]). Los avisos **se adjudican
uno a uno** con el campo `nivel_excepcion`, que exige escribir la razón — el caso típico es un
**puente**: `prf_to_derives` empieza por `prf_` pero su conclusión vive en `⊢`, porque la chapa
marca dónde se afirma, no de dónde se parte.

⚠️ **La elisión no puede cambiar un token.** Con `solo_firma`, el extractor conserva el terminador
real (`:= by`, `:=`, `where`) y sólo elide lo que sigue: imprimir `:=` donde el fuente dice `where`
sería alterar el código, o sea violar §2.1. Y el marcador `…` **no** se puede ignorar globalmente al
verificar —aparece en 43 ficheros `.lean`—, sólo cuando cierra la línea.

La leyenda se imprime **una vez**, al principio del libro, y desde ahí las chapas se leen solas.

### 2.6 · Un docstring es testimonio, nunca evidencia

El libro se escribe **leyendo el árbol que compila**, así que las cabeceras y docstrings de los
módulos de producción son **material fuente**. Y hay que decir en voz alta lo que eso implica:
**`lake build` en verde garantiza los teoremas, no la prosa que los rodea.** El compilador no lee un
docstring.

No es un riesgo teórico. El 2026-09-03 aparecieron **cuatro** afirmaciones falsas en cabeceras de
producción, todas en módulos del frente vivo: símbolos anunciados que **no existen**
(`DescMutua`, `S_Descenso`/`S_Paso2`), un sondeo citado como si fuera producción
(`EvalSubsttc.prf_isTermCodeE1_of_In`), un «EL RESULTADO CENTRAL DE ESTE MÓDULO» con **cero usos** y
una premisa que nadie aguas abajo puede aportar, y un «NO ES VACUO» que medía otra cosa.

⚠️ **Y el caso enseña algo más, porque uno de los cuatro cambió al día siguiente.** La cita
`EvalSubsttc.prf_isTermCodeE1_of_In` era falsa el 09-03 —nombraba un sondeo— pero el 09-04 la
promoción **B2** puso ese lema **en producción**, en `CodeWitnessPrf.SinWTs`. El docstring sigue
mal —el módulo que nombra no existe— pero el hecho que afirmaba pasó a ser cierto por otra vía.
Moraleja para la Parte IV: **un docstring no sólo puede ser falso, puede dejar de serlo sin que
nadie lo toque.** Es testimonio fechado, no descripción. Refuerza la regla, no la debilita.

Una segunda tanda (09-04) elevó la cuenta a **37 hallazgos en bruto** —21 falsas, 6 engañosas, 10
imprecisas— repartidos en cinco clases que **se comprueban de forma distinta cada una**:
existencia (censo de `env.constants`, **no `grep`**), citas `fichero.lean:NNN` (**72 números en 60
sitios**, y derivan en cuanto alguien inserta líneas más arriba), footprint (`#print axioms` real
contra el texto), significado (censo de **consumidores** y dirección de las hipótesis) y cifras
(contar **la familia entera**). Auditoría en curso; ver la **rama G** de `NEXT-STEPS.md`.

📌 **Nota de ruta** (2026-09-04): el registro vive en **`doc/book/DOCSTRINGS-NO-FIABLES.md`**, y
los dos scripts en **`doc/book/scripts/`**. Este plan los cita a veces en forma corta
(`DOCSTRINGS-NO-FIABLES.md`, `scripts/extraer.py`, §§20, 574, 614) y a veces con la ruta completa
(§§50, 117). La forma corta es **ambigua desde la raíz del repo**, donde existe un `scripts/`
distinto, con otros cinco `.py` que no son éstos. Conviene unificar a la ruta completa.

*Anécdota que vale como ejemplo del capítulo*: verificando esto se afirmó primero —por un chequeo
que resolvía los nombres desde la raíz— que el registro **no existía**. Existía. Es exactamente el
fallo que §2.6 describe: **afirmar sobre el contenido sin medir bien**, cometido al comprobar §2.6.
La medición estaba mal apuntada, no ausente; y una medición mal apuntada es indistinguible de una
ausencia hasta que se mira dos veces.

Es el fallo de `AI-GUIDE.md` §27 —«se actualiza el banner y no el cuerpo»— **una capa más adentro**:
`check-doc-sync.bash` vigila los `.md` autoritativos y **no mira dentro de los `.lean`**.

**Regla.** Un docstring se puede **citar como testimonio** —lo que el autor creía en ese momento, que
a veces es justo lo interesante para la Parte IV— pero **nunca usar como evidencia** de lo que un
módulo contiene. Toda afirmación del libro sobre qué hay en un módulo se respalda con una
**medición**: censo de `env.constants`, `#print axioms`, o `grep`. Y si se cita un docstring como
testimonio, se dice que es un docstring.

**Está mecanizado.** `doc/book/scripts/simbolos.py` recoge cada `\ident{}` y `\modulo{}` de los
capítulos —troceando las expresiones en identificadores— y comprueba que nombran algo declarado en
el repo, diciendo si está en producción o sólo en `sondeos/`. Corre en `make` y **falla** si hay un
símbolo sin respaldo; las excepciones legítimas (palabras de Lean, nombres históricos, retirados o
propuestos) se declaran **con su razón** en `doc/book/simbolos-exentos.json`.

Los casos detectados se registran en **`doc/book/DOCSTRINGS-NO-FIABLES.md`**. ⚠️ Corregirlos
**no** es competencia de esta tarea (§0): se registran para que el libro no los cite, y los arregla
la tarea de desarrollo.

### 2.7 · Nada se usa antes de estar definido — sin exenciones

Los seis principios anteriores protegen la **verdad** de lo que el libro dice. Éste protege que se
pueda **leer**: quien llegue con bases tiene que poder avanzar desde la primera página sin
tropezarse con una palabra que el libro aún no le ha dado.

**La capa sintáctica va delante de todo.** El libro abre con un capítulo —antes del índice— que da
los cuatro alfabetos, y en este orden, que no es arbitrario:

1. **Las palabras.** El vocabulario mínimo: teoría objeto, metateoría, aritmetización, numeral,
   punto fijo, condiciones de derivabilidad, Σ₁-completitud, ω-regla, r.e., footprint, net-0,
   sondeo, cuarentena, código de Gödel, índice de De Bruijn, axioma objeto.
2. **Los niveles.** La tipología de dos ejes de §2.5 — *quién afirma* y *sobre qué*. Va aquí, y no
   antes, porque no se puede explicar que una chapa distingue objeto de meta sin haber dado antes
   esas dos palabras. (El control lo destapó: la leyenda usaba «lenguaje objeto», «metateoría»,
   «numeral» y «r.e.» sin definirlos.)
3. **Los nombres.** La gramática de identificadores: conclusión primero con `_of_`, bicondicionales
   en `_iff`, símbolos deletreados — y sobre todo que **el prefijo dice el nivel**: `ax_` (154
   símbolos) es objeto, `prf_` (585) es el cálculo finitario, `pcc_` (214) es dentro de `Prov`. Con
   eso, un lector lee un nombre y sabe en qué nivel está antes de leer el enunciado.
4. **Los signos.** `⊢`, `Prf`, `≐`, `#0`, `⌜φ⌝`, `ȧ`, `Prov`, `Δ₀`/`Σ₁`.

**Regla, sin exenciones:** todo término del vocabulario controlado
(`doc/book/terminos.json`) debe introducirse con `\defterm{}` y **no puede aparecer en el texto
antes**. Se comprueba con `doc/book/scripts/terminos.py`, que reconstruye el **orden real de
lectura** —expandiendo los `\input` en su sitio, no concatenándolos al final— y falla si un término
se adelanta. No hay fichero de excepciones para este control, a diferencia de §2.6: aquí una
excepción es exactamente el fallo que se quiere evitar.

### 2.8 · Una fórmula que se muestra se lee en voz alta la primera vez

§2.7 protege las **palabras**; ésta protege los **signos**. Cuando una notación aparece por primera
vez —`Prf₀ φ → Prf φ → (∀Γ, PrfH Γ φ)`, `Prf φ → axioms ⊢ φ`, `⌜φ⌝`, `Prov(⌜φ⌝)`— el libro hace dos
cosas antes de seguir: **una introducción mínima** de qué es cada pieza, en una línea por pieza; y
**la lectura en voz alta** de la fórmula entera, con el macro `\selee{}`.

No es cortesía. Una cadena de flechas entre cuatro relaciones de demostrabilidad es ilegible para
quien no sepa ya cuál es cuál, y el lector que se la salta pierde justo la asimetría que justifica
que haya dos cálculos.

**Mecanizado con la misma máquina que §2.7**: las notaciones controladas se declaran en
`doc/book/terminos.json` bajo `notaciones`, **por su macro** —que es lo que se puede buscar en el
`.tex` sin ambigüedad, a diferencia del glifo—, se introducen con `\defnot{}`, y `terminos.py` falla
si una se usa antes. Tampoco hay fichero de excepciones.

⚠️ Efecto de orden que este control destapó: la sección de **signos** tuvo que pasar por delante de
la de **niveles** en el capítulo de apertura, porque la explicación de los dos ejes usa `⊢`, `Prf` y
`Prov`. El orden final es **palabras → signos → niveles → nombres**.

### 2.9 · Ninguna parte técnica empieza sin decir qué pregunta contesta

Los ocho principios anteriores protegen la verdad y la legibilidad de lo que el libro dice. Éste
protege que **se entienda para qué**.

**Regla.** Cada parte abre con un puente narrativo de media página que remite a la Parte I y dice
qué pregunta contesta la parte que empieza. Y ningún capítulo técnico entra en materia sin haber
dicho, en su primer párrafo, qué se sabe ya y qué falta.

**Por qué es una regla y no una buena intención:** la prosa pedagógica es lo primero que se
sacrifica cuando hay prisa, y su ausencia no rompe ningún build. Escrita como principio, al menos
se nota cuando falta.

**Corolario mecanizado — prohibido escribir «capítulo 13» a mano.** Un número de capítulo escrito
en el texto deja de ser cierto en cuanto se reordena el libro, y nada lo avisa: es exactamente la
mentira silenciosa que persigue todo el aparato de controles. Se usa `\ref{}`/`\cref{}` cuando el
capítulo existe y **`\capfuturo{...}`** —que imprime «el capítulo dedicado a …», sin número— cuando
todavía no. `scripts/simbolos.py` falla si encuentra uno escrito a mano.

**Corolario de nomenclatura — los ficheros de capítulo no llevan número.** `cap-kernel-fol.tex`, no
`cap02-kernel-fol.tex`. El orden lo fija **sólo** `libro.tex`. Un fichero llamado `cap04-` que
acabara siendo el capítulo 8 es el mismo fallo con otro disfraz.

---

### 2.10 · El texto se revisa en Markdown, pero la fuente sigue siendo el LaTeX

*(Añadido el 2026-09-09.)* Revisar prosa en `.tex` es incómodo: las macros se comen la frase y el
autor acaba corrigiendo marcado en vez de leyendo. Y revisar en Markdown tiene el peligro contrario:
dos fuentes que divergen en silencio, que es exactamente el modo de fallo contra el que va todo
este documento.

La regla que resuelve las dos cosas: **el Markdown es una VISTA, generada, de un solo sentido.**

| | fuente | vista |
|---|---|---|
| dónde vive | `capitulos/*.tex` | `revision/LIBRO.md` |
| quién la escribe | Claude, aplicando lo acordado | `scripts/revisar.py`, de la fuente |
| qué se imprime | esto | nada |
| qué pasa si divergen | manda la fuente | se regenera y punto |

**El ciclo**, y las tres cosas que lo hacen fiable:

1. `make revision` — regenera `revision/LIBRO.md` del LaTeX, con las notas abiertas recolocadas.
2. El autor **anota** (líneas que empiezan por `>>`) y/o **reescribe la prosa** directamente.
3. `make recoger` — las notas y el diff de prosa pasan a `revision/bitacora.json`.
4. Claude lo aplica **al LaTeX**, responde con `revisar.py responder <ID> "..." --estado ...`, y
   vuelve al paso 1.

**(0) Se puede revisar en el procesador de textos, y es lo que pasa.** `make revision` deja
`revision/LIBRO.odt` al día junto al `.md`, y `recoger` lee el que sea **más reciente**. Dos
consecuencias que hubo que programar: la marca de nota es `>>` **y también `»`**, porque el
autocorrector convierte lo primero en lo segundo en cuanto escribes detrás; y desde un `.odt` **no
vale un diff de líneas** —el conversor pierde el marcado, reescribe las tablas y vuelve a partir
los párrafos, así que saldría todo cambiado—, sino una comparación de párrafos normalizados que
sólo recoge lo que cambia de palabras. Las anclas, que en el `.odt` desaparecen por ser comentarios
HTML, se recuperan buscando en `.base.md` el bloque que más se parece al contexto de la nota.

**(a) El código no se revisa aquí.** Los bloques ```lean``` de la vista se leen **del repositorio**,
no del `.tex` generado — la misma lectura canónica que usa `verificar_pdf.py` (§2.1). Editarlos en
el Markdown no tiene efecto, y `recoger` avisa si el diff los toca. Si un fragmento está mal, lo que
se cambia es el código.

**(b) Nada se pierde por desfase.** `recoger` compara con `.base.md` —copia exacta de lo último
generado—, no con el LaTeX de hoy. Se puede anotar sobre una versión vieja: las notas se recogen
igual, y las que ya no encuentran su párrafo se re-emiten al principio marcadas como **huérfanas**,
con el extracto que las ancló. Una nota nunca desaparece en silencio.

**(c) La conversación es acumulativa y es un documento del proyecto.** `revision/BITACORA.md`
guarda cada nota, cada respuesta y cada estado (`abierta` · `aplicada` · `discutida` ·
`descartada`), con su fecha, **incluidas las descartadas y su razón**. Es el registro de por qué el
libro dice lo que dice, y se commitea con él. `.base.md` no: es un espejo, no un documento.

---

## 3 · Estructura

> **Reestructurado el 2026-09-09.** El libro abría con el capítulo de nomenclatura —bueno como
> referencia, malo como primera página: obligaba a definir «teoría objeto» antes de que el lector
> supiera por qué le importa—. Ahora abre con una **Parte I puramente pedagógica**, y la
> nomenclatura pasa a ser recapitulación en los apéndices.

### Parte I — El problema

Sin una sola línea de Lean hasta el capítulo 4. Es la prosa que guía el resto del libro: las partes
siguientes se leen a través de ella (§2.9).

1. **1931: qué preguntó Hilbert y qué contestó Gödel.** Los dos artículos —la completitud de 1930 y
   la incompletitud de 1931—, el programa de Hilbert y por qué la respuesta tuvo que pasar por
   aritmetizar la sintaxis.
   ⭐ **El gancho que abre el libro:** el artículo de 1931 lleva un **«I»** en el título. Gödel
   anunció una segunda parte con la demostración detallada del segundo teorema y **nunca la
   escribió**; las condiciones de derivabilidad las suministraron Hilbert–Bernays en 1939. Es decir:
   **D1, D2 y D3 son el artículo que Gödel no llegó a publicar**, y este proyecto lleva meses
   peleando con D3. Eso da tesis a la Parte V y sentido al libro entero en un párrafo.
   ⚠️ `[citado]` — verificar títulos, fechas y la atribución a Hilbert–Bernays antes de imprimirlo.
2. **Qué hay que construir para decirlo hoy.** De la prosa de Gödel al código: hace falta un
   lenguaje, una teoría, un cálculo, una codificación y un verificador. Es el mapa del libro y
   justifica el orden de las partes.
3. **Los lenguajes de este libro.** El capítulo que hoy no existe y hace más falta.
   * **Tres metateorías, no una.** La de Gödel era informal pero **deliberadamente finitaria**, para
     que Hilbert la aceptara. La de FOL⁼ admite la **ω-regla**, luego `⊢` **no es r.e.** y es *más
     fuerte* que el cálculo del que Gödel hablaba. La de Lean es más fuerte todavía —aunque el
     proyecto sólo use dos niveles de ella y ninguna impredicatividad—. *Material:*
     `doc/book/MATERIALES.md` M-1.
   * **Cuatro lenguajes objeto, no uno.** FOL⁼ desnudo (gramática sin signatura) → **Q++** (signatura
     aritmética + 34 axiomas) → Q++ **con la capa de codificación** (+107, los símbolos opacos del
     verificador) → la **extensión con inducción** de `Full/`. Cada uno es una teoría distinta y
     demuestra un teorema de incompletitud distinto. Es [ADR-015](DECISIONS.md) dicho al principio
     en vez de al final, y es lo que resuelve la ambigüedad de `axiomsCodeT` (¿34 o 141?) registrada
     en `doc/book/DOCSTRINGS-NO-FIABLES.md` caso 5.
   * Aquí se introducen **narrativamente** las chapas de nivel de §2.5.
4. **Lo mínimo de Lean: cuatro palabras.** `inductive`, `def`, `theorem`, `axiom`. Nada más.
   ⭐ Con el enganche que lo hace memorable: **las tres últimas son las tres categorías morales del
   proyecto.** Un `def` no cuesta nada —nombra—. Un `theorem` se gana. Un `axiom` es una **deuda**, y
   por eso el proyecto los inventaría uno a uno en `AXIOMS.md` y este libro imprime el *footprint*
   debajo de cada enunciado. El lector entiende de golpe qué es esa línea gris.

### Parte II — El terreno

5. **El kernel FOL⁼** ✅ — `Term`, `Formula`, De Bruijn, `Derives`, las 6 meta-reglas ω, las cuatro
   relaciones de derivabilidad, el toolkit medido, y el axioma que era falso (ADR-011).
6. **¿Cuánta metateoría hace falta?** ✅ — *(reorientado el 2026-09-09; ver §8 entrada 13.)* El
   solapamiento se revisó y era total: «los dos cálculos, su puente y el recíproco que no existe»
   ya está escrito, y bien, en el capítulo 5. Lo que faltaba —y no está en ningún otro sitio— es la
   pregunta de la **fuerza**: por qué Lean no es PA (la inducción como esquema frente al motivo de
   segundo orden, los universos, los tres axiomas del núcleo), cuánto de esa fuerza se usa de verdad
   (**dos niveles**, cero `Sort u`, cero cuantificación sobre `Prop`), cómo se traduciría a una
   metateoría aritmética (curso de valores + esquema de inducción ≈ IΣ₁), los **dos** usos de
   `Classical` y por qué uno es el principio de Markov, el experimento ya hecho en `Peano`
   (`#assert_constructive`, 1425 invocaciones, con su propio control positivo) y qué transferiría y
   qué no una metateoría-Peano. Cierra la asimetría que el libro necesita decir en voz alta: **la
   metateoría no tiene que ser más fuerte que la teoría de la que habla.**
   *Material:* `doc/book/MATERIALES.md` M-1 — consumido entero por este capítulo.
7. **La teoría objeto: Robinson Q++** ✅ — el núcleo de Q, lo que Q no prueba, el precio de cada
   símbolo nuevo, qué se consigue sin inducción, la frontera con `Full/`, los otros 107, y por qué
   reducir hoy cambia el teorema.

### Parte III — Aritmetización

8. **Codificar estructuras como números** ✅ · 9. **Códigos de términos y fórmulas** ✅ ·
10. **El verificador de pruebas** ✅ · 11. **Representabilidad y D1** ✅

### Parte IV — Los teoremas

12. **Autorreferencia** ✅ — el mentiroso y el cambio de «falsa» por «no demostrable» (Tarski);
    `selfApp`, `diagTerm` y por qué ahí hace falta el código *dotado*; que la teoría **sepa hacer**
    la diagonalización (`diag_arith_num`); la sentencia; `godelCN_fixedpoint` **sin hipótesis**; las
    dos representaciones y el paso de Leibniz que abarató la reparación; y tres lecturas falsas de
    `G` desmontadas con la fórmula delante.
13. **Gödel I** ✅ — el argumento en cuatro pasos, la prueba de Lean **impresa entera** (son las
    mismas cuatro líneas), la descarga, y las tres cosas que el capítulo tiene que decir y casi
    ningún libro dice en el mismo sitio: que la hipótesis es la **consistencia simple** y no la
    ω-consistencia (con la trampa `ConsistentOmega`/`OmegaConsistent`, ver `MATERIALES.md` M-5);
    que la teoría es la **reparada** (`\avisoreparacion`); y que sólo está cerrada **una de las dos
    mitades** (`\avisomediagodel`). Con Rosser 1936 como contrapunto: eliminó la ω-consistencia
    cambiando la sentencia, y este proyecto no tomó esa ruta.
14. **La mitad que falta: `⊬¬G`** ✅ — el argumento hasta donde llega y el paso (4) que no es
    lógica; `Reflects` como hipótesis honesta; **por qué el atajo lo cierra Gödel II** (para `φ=⊥`
    la reflexión ES `Con(T)`; para `φ=G`, equivale a `⊢G`); el postulado de junio que la escondía
    —un bicondicional cuya mitad izquierda era falsa, bajo consistencia simple: *decía de más*—;
    la descarga por ω-consistencia + `NegVerifier`, con el uso de Markov en su sitio; y la cifra
    incómoda: `NegVerifier` **enunciado, con cero teoremas que lo concluyan**.
15. **Las condiciones de derivabilidad** ✅ — las tres en una página; **externo contra provable**
    como la distinción que lo gobierna todo; D1 y D2 **teoremas** (D2 es el que suele postularse);
    `d3` como el único `axiom` que el proyecto considera deuda; por qué D3 es difícil (una función
    frente a una inducción); y **cuánto falta con nombres**: `d3_prf_of_halves`, la mitad (a)
    cerrada por el episodio del cap. 18 y la (b) en tres piezas. Incluye el **hueco de ensamblaje**
    que la auditoría del 2026-09-10 encontró y que ningún documento del proyecto señala.
16. **La inducción como precio** — por qué Q sola no basta. *Material:* `AXIOMS.md` §1.1.
17. **Gödel II** — *(reorientado el 2026-09-10, al cerrarse D3.)* Ya no va de «publicar módulo un axioma»: va de qué hipótesis le quedan y por qué son de otra clase. El punto fijo y la necesitación son piezas construibles; `hgi` es la mitad demostrada de Gödel I. Y el contraste que ahora se puede hacer: el capítulo 15 cuenta cómo se pagó la deuda, y éste cuenta qué queda cuando ya no hay ninguna.

### Parte V — Lo que no sale en los libros

**18. El muro de `substfc`** ✅ — qué es `substfc` y por qué está en el centro (`diagTerm`);
los 7 reflectores de 21 que bloqueaban D3, y `pcc_lineWF_tracked_modulo_7` como *teorema que mide
lo que falta*; **el axioma `ax_tc_substfc` que lo resolvía y hace INCONSISTENTE la teoría**, con la
derivación en cinco pasos; por qué una teoría objeto inconsistente **compila**; el obstáculo real
(evaluación sobre argumento abstracto ⇒ inducción sobre códigos dentro de `Prov`); la puerta (a)
cerrada por imposibilidad estructural; y los 40 días, con `pcc_eval_substfc` como está hoy.
· 19. Una inconsistencia latente · 20. Cómo se localiza el daño ·
21. Cuatro reparaciones que no funcionan · **22. La reparación: códigos como numerales ✅** ·
23. La cuarentena · 24. La reconstrucción · 25. Definir en vez de axiomatizar (ADR-015) ·
26. La partición que hace posible la inducción (ADR-016) · 27. Cómo se rompió el muro (ADR-017/018) ·
28. Cuando la tarea pendiente es imposible · 29. Método.

*(El contenido detallado de cada uno se conserva sin cambios respecto a la versión anterior de este
plan; sólo cambian los números.)*

### Apéndices

Sin letra: LaTeX las asigna por orden, y una letra escrita a mano deriva igual que un número de
capítulo (§2.9).

- Inventario de los 7 `axiom` de Lean (`AXIOMS.md`).
- Mapa de módulos y grafo de dependencias (`REFERENCE.md`, `DEPENDENCIES.md` §0).
- Trampas de Lean 4 encontradas (memorias `feedback-lean-*`).
- **Glosario** ✅ — recapitulación de los términos, generado de `terminos.json`.
- **Notación** ✅ — recapitulación de los signos y de cómo se lee un nombre.
- **Licencia** ✅ — CC BY-SA 4.0 para la prosa, MIT para el código citado.

### ✅ Migración completada (2026-09-09)

El capítulo *Nomenclatura, niveles y notación* que abría el libro **ya no existe**. Sus cuatro
secciones se repartieron así: las **palabras** y los **signos** se introducen ahora narrativamente
en la Parte I y recapitulan en los apéndices; los **dos ejes** son la última sección del
capítulo~3; y **cómo se lee un nombre** va al apéndice de notación.

Un detalle del método que conviene registrar: **no hizo falta el modo «recapitulación»** que este
plan preveía. `terminos.py` toma el **primer** `\defterm{}` en orden de lectura, así que basta con
que la introducción narrativa vaya antes; el glosario del apéndice puede seguir marcándolos sin
romper nada. Un paso menos del previsto.

---

## 4 · Infraestructura

**No existe nada de LaTeX en el repo** (verificado: sin `.tex`, `.bib`, `.sty`). Se crea de cero
**en `doc/book/`**:

```text
doc/book/
  libro.tex             # documento maestro
  preamble.tex          # paquetes, entornos, estilo
  capitulos/*.tex       # un fichero por capítulo
  extraido/*.tex        # GENERADO — fragmentos Lean, nunca editar a mano
  bib/libro.bib         # Gödel, Rosser, Hilbert-Bernays, Paulson, O'Connor…
  scripts/extraer.py    # extrae declaraciones Lean del repo a extraido/
  Makefile              # extraer + latexmk
```

**Decisiones técnicas:**

- `\lstset` o `minted` para Lean 4 (evaluar cuál da mejor resaltado de Unicode: el proyecto usa
  `σ`, `⟹`, `⊢`, `≐`, `⌜·⌝` intensivamente).
- Entornos propios: `\begin{lean}` (código), `\begin{matematica}` (enunciado formal),
  `\begin{leccion}` (nota pedagógica), `\begin{muro}` (obstrucción encontrada) y
  `\begin{refutado}` (resultado negativo compilado — lo pide la Parte IV).
- **Marcas de nivel (§2.5)**: `\nivel{afirma}{sobre}` (la chapa), `\obj{}`, `\cod{}`, `\prov{}`
  para prosa y fórmulas, y `\leyendadeniveles` (se imprime una vez).
- ⚠️ **`listings` está prohibido**: con Unicode reordena los caracteres —imprime `φ( : Formula)`
  donde el fuente dice `(φ : Formula)`—, o sea altera el código en silencio, justo lo que §2.1
  prohíbe. Se usa `fancyvrb`+`fvextra`, y **el resaltado lo hace el extractor**. El símbolo de
  continuación de línea es `›` y no una flecha, porque `pdftotext` extrae `↪` como `→`, que es un
  token legítimo de Lean.
- Idioma: **español**, coherente con toda la documentación del proyecto.
- **Licencia doble** (decidida 2026-09-03): la **prosa, las figuras y la maquetación** bajo
  **CC BY-SA 4.0**; los **fragmentos de código Lean 4** siguen bajo la **MIT** del repositorio, y no
  cambian de licencia al ser citados. Declarada en `doc/book/LICENSE`, en la portada y en el
  apéndice E, que reproduce el aviso MIT íntegro —lo exige esa licencia al distribuir porciones
  sustanciales—. El articulado de CC **no se transcribe**: transcribir un texto legal de memoria es
  introducir erratas en una licencia; se enlaza al canónico.
  ⚠️ **Pendiente para la otra tarea**: `README.md` de la raíz declara «Licencia MIT» sin mencionar
  la excepción de `doc/book/`. Está fuera del ámbito del libro (§0), así que se reporta, no se toca.
- `doc/book/` queda **fuera** del build de `lake`: la `lean_lib` sólo alcanza `.lean` importables
  desde `ROBINSON_PlusPlus.lean`, así que no interfiere.
- **`doc/book/MATERIALES.md` — la cantera.** Lo que se descubre hablando se pierde si no se escribe:
ahí van los hallazgos, mediciones y razonamientos que deben acabar en el libro pero cuyo capítulo aún
no está escrito. **Cada entrada lleva su destino** (qué capítulo) y **cada afirmación su estatuto**
—`[medido]` con la orden que lo comprueba, `[citado]` con su referencia, `[razonado]`, `[conjetura]`—,
que es §2.6 aplicado también a lo que escribimos nosotros. Nada sale de la cantera a un capítulo sin
volver a pasar los controles de `make`: toda cifra se remide en el momento de escribirla.

Contenido a 2026-09-04: **M-1** la fuerza de la metateoría (cuántos universos se usan de verdad —dos—,
la impredicatividad que no se usa, los dos únicos `Classical` y por qué uno de ellos es exactamente el
principio de Markov, y qué transferiría y qué no una metateoría-Peano); **M-2** el reparto 34/107 de
los 141 axiomas objeto; **M-3** las tres funciones `numeral`; **M-4** por qué «Q tiene 7 y nosotros 34» engaña, el historial
de cinco reducciones, y por qué reducir hoy **cambia el teorema** en vez de simplificarlo.

⚠️ **Comprobar** que `bash check-doc-sync.bash --quick` sigue verde tras crear el directorio —
  sus controles [C]/[D] recorren `.md` y no deben confundirse con los del libro.

---

## 5 · Orden de ejecución

| fase | entregable | estado | por qué en este orden |
|---|---|---|---|
| **−1** | **este plan, puesto al día** | ✅ **HECHO 2026-09-03** | sin él, la fase 2 escribiría afirmaciones que el proyecto ya refutó (§2.4) |
| **0** | esqueleto `doc/book/` + `Makefile` + capítulo piloto (19) | ✅ **HECHO 2026-09-03** | validar la cadena LaTeX **y** el extractor antes de escribir |
| **1** | `scripts/extraer.py` + capítulo 2 (kernel) + capítulo de apertura | ✅ **HECHO 2026-09-03** | el kernel es estable y no está afectado por la inconsistencia |
| **3a** | Aritmetización completa (hoy Parte III) + Robinson Q++ | ✅ **HECHO 2026-09-04** | el terreno y la aritmetización están estables y no dependen del frente vivo |
| **2** | Parte IV: capítulos 16-19, 21 y **22-25** | ⏳ **siguiente** | **escribir ahora, mientras el episodio está fresco** — es el material más valioso y el más fácil de perder |
| **3** | Partes I–III (con el cap. 11 corregido) | ⏳ | exposición sistemática; se apoya en `doc/REFERENCE-*.md` ya escritos |
| **3b** | Parte I (los 4 capítulos pedagógicos) + migración del glosario a apéndices | ✅ **HECHO 2026-09-09** | guía el resto del libro (§2.9) |
| **4** | Apéndices y bibliografía | ⏳ | mecánico |

✅ **Dependencia real del desarrollo (§2.2), SALDADA (2026‑09‑08).** El capítulo 24 ya puede
**enunciar sus resultados como teoremas**: la rama B promovió `pcc_eval_substfc` (B3.4,
`Meta/EvalSubstfcPrf.lean`) y `prf_hasWitF_real` (`Meta/CodeWitnessPrf.lean`) a `Meta/`. Ya no hace
falta la marca «fuera del build». Era el único punto del libro que esperaba al proyecto.

⚠️ **La fase 2 va deliberadamente antes que la I–III.** El capítulo de la inconsistencia se escribe
mejor ahora que dentro de seis meses — y ahora hay **cuatro capítulos más** en esa situación
(22-25), del arco 24-ago → 3-sep, que la versión anterior de este plan no conocía.

**Estado al cierre del 2026-09-03.** `doc/book/` monta: `libro.tex`, `preamble.tex` (5 entornos +
chapas de nivel), `Makefile`, `fragmentos.json` (30 fragmentos), `terminos.json` (18 términos, fuente
del glosario), `simbolos-exentos.json`, `DOCSTRINGS-NO-FIABLES.md`, `LICENSE`, y cinco scripts
(`extraer`, `verificar_pdf`, `simbolos`, `terminos`, `ambito`). Escritos: **capítulo de apertura**
(nomenclatura, niveles y notación), **capítulo 2** (kernel FOL⁼), **capítulo 19** (códigos como
numerales) y **apéndice E** (licencia). 34 páginas. `make` encadena extraer → compilar → verificar →
símbolos → términos, y **los cinco controles tienen su control positivo hecho**. Nada commiteado.

**Estado al cierre del 2026-09-09.** Escritas **las Partes I, II y III enteras** (1 Hilbert y
Gödel · 2 qué hay que construir · 3 los lenguajes · 4 lo mínimo de Lean · 5 el kernel FOL⁼ ·
**6 ¿cuánta metateoría hace falta?** · 7 Robinson Q++ · 8-11 la aritmetización), el capítulo 22 de
la Parte V y **tres apéndices** (glosario, notación, licencia). Los cinco puentes narrativos de
§2.9, puestos. Y de la Parte V, los capítulos **18** (el muro de `substfc`) y 22.
**94 páginas, 79 fragmentos (1 de ellos externo), cinco controles en verde**, cada uno con su
control positivo pasado.

**Primera vuelta de revisión cerrada (2026-09-09)**, por el bucle de §2.10 y con el autor
revisando en `.odt`: tres notas, las tres aplicadas — el finitismo como estrategia y no como
creencia (§3 del cap. 1, con la cita de Gordan puesta en su sitio: mal atestiguada, impresa por
primera vez veinticinco años después en una necrológica); la escala PRA / IΣ₁ / HA / PA con
$\mathrm{PA}^\omega=\mathrm{Th}(\mathbb{N})$, que sitúa el $\omega$-cálculo **fuera** de la
escala y no un escalón por encima; y la distinción Q++ / Q++ codificante en el cuadro de estratos.
Queda en `doc/book/revision/BITACORA.md`.

**Falta escribir**: de la Parte IV, los capítulos 16 y 17; diez capítulos de la Parte V (19-21,
23-29); y tres apéndices (inventario de axiomas, mapa de módulos, trampas de Lean).

**Siguiente sesión**, por este orden: (1) `make subir` desde el shell del autor — hay además
renombrados de fichero pendientes de registrar; (2) `make axiomas` con Lean en el PATH — **los 67
fragmentos de producción siguen marcados «declarado, sin medir»**, que es la verdad, y es hoy el
mayor incumplimiento de §2.2(c); (3) **verificar la bibliografía del capítulo 1** (títulos y fechas
de los artículos de 1930 y 1931, y la atribución a Hilbert–Bernays 1939), que es hoy la única
afirmación del libro sin respaldo mecanizado; (4) seguir la fase 2 —Parte V— por el
capítulo 19 (la inconsistencia latente), que enlaza directamente con el 18 ya escrito.

**Materia prima ya disponible, verificada y citable** (nada de esto hay que reconstruirlo):
`sondeos/` (**57** experimentos compilados, con su `README.md` de 41 KB), `cuarentena/README.md`
(grafo de recuperación, episodio cerrado), `DECISIONS.md` **ADR-012 a ADR-018**,
`doc/REFERENCE-Incompleteness.md` §3.24–§3.32, `AXIOMS.md` §1.1, y las memorias
`project-inconsistencia-tcfn-cons`, `project-reparacion-via-numeral`, `project-escalera-sigma1`,
`project-substfc-wall`, `feedback-auditoria-footprint`.

---

## 6 · Relación con el desarrollo en curso

El libro **no bloquea ni es bloqueado** por el desarrollo:

- Partes I–III describen lo que **ya está probado y compila**: kernel, Q++, verificador, D1, D2,
  Gödel I vía `goedel_first_numeral`, y Gödel II con las tres condiciones **demostradas**.
- La Parte IV documenta el problema, su reparación y **la reconstrucción**, con el arco **cerrado**.
- Lo que **está vivo** en el proyecto (rama B de promoción, `hC_dot`, D3 real, `NegVerifier`) entra
  en el libro como **frente abierto declarado**, no como hueco silencioso.

### ⚠️ Los dos avisos editoriales obligatorios

> **(1)** El libro **debe decir explícitamente** que lo que se retiró fue la inconsistencia
> **conocida y localizada** (`ax_tc_cons`), y que **eso no es una prueba de consistencia** de Q++
> extendido. Gödel I (`goedel_first_numeral`) es un teorema real sobre la teoría **reparada**;
> presentarlo como «Gödel I sobre una teoría consistente» sería engañoso, igual que lo habría sido
> publicarlo antes sin advertir del ⊥.

> **(2)** Gödel I está **a medias**: sólo `⊬G`. La indecidibilidad (`⊬¬G`) **no está cerrada** en la
> cadena real — ver capítulo 11. El libro no puede enunciar «G es indecidible» sin esa salvedad.

---

## 7 · Verificación

- `make -C doc/book` compila el PDF sin errores ni referencias rotas.
- El extractor **falla ruidosamente** si una declaración citada no existe en el repo — así el libro
  no puede desincronizarse en silencio del código.
- Todo fragmento de `sondeos/` lleva su marca «fuera del build» y su footprint (§2.3), y no
  sostiene ningún teorema de las Partes I–III.
- Toda declaración citada como teorema pasa los cuatro controles (a)-(d) de §2.2, y su
  `#print axioms` está impreso y contenido en la base sancionada.
- Todo fragmento lleva su **chapa de nivel** (§2.5), y los avisos de incoherencia con el prefijo
  están adjudicados uno a uno.
- `make simbolos` en verde (§2.6): cada `\ident{}` del libro nombra algo que existe, o está exento
  con su razón. **Ninguna afirmación sobre el contenido de un módulo descansa en su docstring.**
- `make terminos` en verde (§2.7 y §2.8): ningún término aparece antes de su `\defterm{}`, ninguna
  notación antes de su `\defnot{}`.
- `make verificar` en verde. Comprueba dos cosas: que el **código impreso en el PDF** coincide línea
  a línea con el del repo, y que **nada se sale de la caja de texto** (`Overfull \hbox`). Lo segundo
  se añadió tras detectar a ojo una tabla 88 pt más ancha que la página: depender de que alguien mire
  no es un control. Receta cuando salta: pasar la tabla a `tabularx` con una columna `X`, y sacar de
  la tabla toda cabecera `\multicolumn` larga — en una celda `l` no parte líneas, y es la causa
  habitual.
- Antes de cerrar un capítulo: releer §2.4 y comprobar que ninguna afirmación prohibida ha entrado.
- `lake build` sigue verde y con **el mismo número de jobs**: `doc/book/` no toca la compilación.
- `make ambito` en verde (§0): no hay nada preparado para subir fuera de `PLAN-LIBRO.md`,
  `Sobre_el_libro.md` y `doc/book/**`.
- `bash check-doc-sync.bash --quick` sigue verde.

---

## 8 · Registro de correcciones a la versión anterior de este plan

Auditoría del **2026-09-03**, aplicando `AI-GUIDE.md` §27 a este mismo fichero. La versión anterior
(2026-08-22 23:55) había caído exactamente en el fallo que ese apartado describe: **banner
actualizado, cuerpo sin recorrer**.

| # | qué decía | qué se ha hecho |
|---|---|---|
| 1 | «83 módulos activos (+21 en cuarentena, +10 sondeos)», «24 ficheros `.md`» | cifras al día: **109 / 0 / 57**, y 25 `.md` de raíz + 5 nodos `doc/` |
| 2 | cap. 9bis: «el obstáculo de fondo es el **intuicionismo** del kernel FOL» | **falso** desde §3.32.3 — corregido en el cap. 11 y añadido a la lista de §2.4 |
| 3 | cap. 9bis: material `PLAN-NEGVERIFIER.md` sin salvedad | ese documento se **autodeclara parcialmente falso**; se cita con la lista de §2.4 delante |
| 4 | cap. 15: «31 módulos a cuarentena… y cómo se recupera» | la recuperación **está hecha**: 31 → 0. El cap. 20 tiene final |
| 5 | ausencia total del arco 24-ago → 3-sep | **cuatro capítulos nuevos**: 22 (ADR-015), 23 (ADR-016), 24 (ADR-017/018), 25 (refutaciones) |
| 6 | ubicación `libro/` | **`doc/book/`** |
| 7 | dos planes en conflicto (`PLAN-LIBRO.md` / `Sobre_el_libro.md`) | **fusionados** (§1.1); `Sobre_el_libro.md` pasa a nota histórica |
| 8 | nada sobre citar `sondeos/` | **§2.3**: admisibles con recompilación, marca visible y footprint, pero **no sostienen teoremas** |
| 9 | ningún control contra afirmaciones caducadas | **§2.4**: lista de afirmaciones prohibidas + procedimiento de cierre de capítulo |
| 11 | nada obligaba a distinguir objeto de meta a la vista | **§2.5 (nuevo)**: chapa de dos ejes obligatoria en cada fragmento, leyenda al principio, y la convención de nombres del proyecto como control cruzado |
| 12 | nada preveía citar código de otros proyectos del autor | **§2.3bis (nuevo)**: capa `externo`, sin footprint y con marca visible; el capítulo 6 la estrena con `Peano` |
| 18 | el bucle §2.10 suponía que se revisa en un editor de texto | **falso a la primera vuelta**: la revisión real llegó en `.odt`. `revisar.py` lee ahora ODT, acepta `»` como marca y compara por párrafos normalizados |
| 17 | no había forma cómoda de revisar la prosa: leerla en `.tex` es leer marcado | **§2.10 (nuevo)**: `scripts/revisar.py` genera `revision/LIBRO.md` del LaTeX, recoge notas y retoques, y los guarda en una bitácora acumulativa. El Markdown es vista; el LaTeX sigue siendo fuente |
| 16 | §2.9 sólo vigilaba números; «los tres capítulos siguientes» derivaba igual y en silencio | el control cuenta ahora también los **recuentos escritos con palabras** («dos…diez capítulos»). Deliberadamente NO cubre «partes»: «las dos partes se reduzcan al mismo término» habla de una ecuación |
| 14 | nada impedía que la sintaxis Markdown del material de partida se colara en el LaTeX | **control nuevo en `scripts/simbolos.py`**: `**negrita**`, `` `código` `` y `# encabezado` en un capítulo son error. Había **tres** casos vivos, en tres capítulos |
| 15 | `scripts/terminos.py` no aceptaba un `\defterm{}` de una **variante** declarada | corregido: `\defterm{axiomas objeto}` ya introduce «axioma objeto». El fallo estaba latente desde §2.7 y sólo lo destapó el primer uso en prosa llana |
| 13 | cap. 6 era «teoría objeto y metateoría — los dos cálculos y su puente» | **solapamiento total con el cap. 5**, comprobado al escribirlo. Reorientado a la pregunta de la **fuerza** de la metateoría, que no estaba en ninguna parte |
| 10 | «sólo se publica lo que compila» era el único criterio de admisión | **§2.2 (nuevo)**: *sólo se expone lo que está demostrado **desde la base*** — alcanzabilidad desde el módulo raíz, footprint impreso y contenido en la base sancionada, y los «módulo algo» obligados a declararlo en el enunciado |

---

**Autor**: Julián Calderón Almendros · Licencia MIT

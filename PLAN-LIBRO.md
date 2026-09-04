# PLAN — Libro en LaTeX: *Incompletitud, formalizada*

> ## ESTADO REAL — 2026-09-04 · `master` HEAD `1ab7a96` · **fase 0 sin arrancar**
>
> **Build 123 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **109 módulos activos** (Minimal 11 + Meta 87 + Full 11) **+ 0 en `cuarentena/` + 57 en `sondeos/`.**
> **7 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> **Ubicación acordada: `doc/book/`** (no `libro/`, como decía la versión anterior de este plan).
> Formato **LaTeX**. Idioma **español**.
>
> ⚠️ Este plan **fusiona** los dos planes previos del libro — el técnico (`PLAN-LIBRO.md`
> 2026-08-22) y el pedagógico (`Sobre_el_libro.md`) — y **corrige** las afirmaciones que el
> proyecto ha refutado desde entonces. El registro de correcciones está en §8.

**Última actualización:** 2026-09-04 11:30 — **nuevo principio §2.8** (una fórmula se lee en voz
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

Son **ocho**, y los ocho nacen de un fallo real de este proyecto. Ninguno es estético.

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
| `axiom` de RPP (7) | `ax_induction`, `ax_list_induction`, `ax_mod2_alternation`, `ax_p_tfa`, `ax_axiomsCodeT_eq`, `prf_axiomsCodeT_eq`, `d3` |

Cualquier símbolo que aparezca en un `#print axioms` **fuera de esa tabla** es un error del libro,
no una nota a pie de página.

**Los resultados «módulo algo» no quedan prohibidos: quedan obligados a declararlo en el enunciado.**
Hay exactamente **dos** en el estado actual, y los dos son teoremas legítimos del libro *siempre que
se impriman con su condición a la vista, no en una nota al pie*:

- **`goedel_second'`** — módulo el `axiom d3`;
- **`goedel_first_undecidable_numeral`** — toma **`Reflects` como hipótesis META explícita**, sin
  descargar (para descargarla falta `NegVerifier`).

⚠️ **Corolario que afecta al calendario.** El capítulo 24 (la rotura del muro de `substfc`) narra un
resultado que hoy vive en `sondeos/`, **fuera del build**: `pcc_eval_substfc` y `prf_hasWitF_real`
están probados y medidos, pero no son alcanzables desde el módulo raíz. Bajo este principio pueden
**contarse** como episodio y su código citarse con las marcas de §2.3, pero **no pueden presentarse
como teoremas del libro** hasta que la **rama B** los promueva a `Meta/`. Ésa es la única dependencia
real del libro respecto al desarrollo, y conviene tenerla escrita.

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

---

## 3 · Estructura

### Apertura (antes del índice)

0. **Nomenclatura, niveles y notación** — las palabras, los dos ejes, la gramática de nombres y los
   signos. Es la capa sintáctica de §2.7, y va delante de todo.

### Parte I — El terreno

1. **¿Qué dice Gödel, y qué hay que construir para decirlo?** — el enunciado informal, y por qué
   formalizarlo obliga a construir tres cosas: un lenguaje, una teoría y una aritmetización.
2. **El kernel FOL⁼** — `Term`, `Formula`, índices de De Bruijn, `substFormula`/`liftFormula`, la
   relación `Derives` (`⊢`) y las **6 meta-reglas ω** (`imp_intro`, `gen`, `raa`, `dne`, `or_elim`,
   `ex_elim`). *Material:* `doc/REFERENCE-Kernel.md`, `FOL/REFERENCE.md`.
   *Lección:* por qué De Bruijn, y el precio que se paga por ello.
3. **Teoría objeto y metateoría: dos gramáticas y DOS cálculos.** ← capítulo que venía de
   `Sobre_el_libro.md` y que el plan técnico no tenía. Es la clave arquitectónica de todo el
   proyecto: `⊢` incluye la ω-regla `gen`, luego **no es r.e.**, y por Tarski ningún `Prov` puede
   satisfacer el bicondicional; de ahí el cálculo de Hilbert **finitario** `Prf` en paralelo, con
   los puentes `prf_to_derives` / `prf0_to_derives`. *Material:* `GODEL-D-ARITHMETIZATION.md`,
   ADR-010 (por qué las meta-reglas son `axiom` y no teoremas).
4. **La teoría objeto: Robinson Q++** — los 34 axiomas matemáticos de `Minimal/`, los 141 axiomas
   objeto de la lista `axioms`, y la frontera `Minimal` / `Full`. Qué se puede **sin inducción**:
   Cantor, pares, listas, funciones discretas, TFA vía Ax-P.
   *Material:* `MINIMAL-AXIOMS.md`, `AXIOMS.md`, `TuplasFuncionesYListas.md`, `DISCUSIONES.md`.

### Parte II — Aritmetización

5. **Codificar estructuras como números** — emparejamiento de Cantor, `cons`/`nil`, listas,
   proyecciones, y el engarce con los tipos inductivos de Lean.
   *Material:* `TuplasFuncionesYListas.md`, `FOL/ENGARCE-ROBINSON-FOL.md`.
6. **Códigos de términos y fórmulas** — `strCode`, `termCode`, `formCode` y sus 9 tags; el espejo
   meta `codeNat`; `numeral`; la inyectividad (Teo G1). *Material:* `doc/REFERENCE-Godelization.md`.
7. **El verificador de pruebas** — `lineWF`, `premsOf`, `runFn`, `chainOk`, `validProofFn`, los
   **21 tags**, y `provCodeC'`. *Material:* `doc/REFERENCE-Incompleteness.md`,
   `GODEL-D-ARITHMETIZATION.md`.
8. **Representabilidad y D1** — de `Prf φ` a `Prov(⌜φ⌝)`: `repr_pos` y `repr_pos'_prf`. Por qué D1
   es la Σ₁-completitud **externa** y por eso sale sin inducción.

### Parte III — Los teoremas

9. **Autorreferencia** — el mentiroso, la sustitución diagonal, y el punto fijo real
   **`godelCN_fixedpoint`**. ⚠️ El código va escrito como **numeral**; el porqué es el cap. 19,
   y aquí basta con anunciarlo.
10. **Gödel I** — **`goedel_first_numeral : ConsistentOmega → ¬ Prf godelCN`**, con su footprint
    auditado. Con el aviso editorial de §6.
11. **La mitad que falta: `⊬¬G`.** Casi todos los libros enuncian Gödel I como *«G es indecidible»*
    y despachan la segunda mitad en un párrafo. En la formalización **no es un párrafo**: `⊬G` sale
    de la consistencia, pero `⊬¬G` necesita **reflexión** —de `Prov(⌜φ⌝)` volver a `φ`—, y eso
    exige un **verificador negativo**. El capítulo cuenta:
    * **(a)** que el proyecto llegó a «tenerlo» y era **falso**: `provFormula_repr` se postuló como
      bicondicional y su dirección `.mp` es representabilidad **negativa**, que no se sigue de la
      consistencia simple. Retirado en F7a — **arreglo de solidez, no regresión**;
    * **(b)** ⚠️ **CORREGIDO respecto al plan anterior**: el obstáculo **no** es el intuicionismo del
      kernel (ver §2.4), y `repr_neg` **no hace falta**. La obligación real y única es
      **`NegVerifier`**, reducida en `reflects_of_omega`;
    * **(c)** por qué `canon_ne` era el plan y **es falso** — un `cons` es un número —, y cómo la
      salida es la misma que la del cap. 19: **numerales** (`consN_inj → codeNat_inj → codeNat_ne`);
    * **(d)** por qué Rosser sería **peor**, no mejor, en este marco.
    *Material:* `PLAN-NEGVERIFIER.md` (⚠️ **leer con la lista de §2.4 delante**), `GODEL-STATUS.md`,
    `sondeos/CanonNeRefuta.lean`, `sondeos/CodeNatInj.lean`.
12. **Las condiciones de derivabilidad** — D1 ✅, **D2 `d2_prf`** ✅, y el **muro de D3**: por qué
    D3 es la Σ₁-completitud **provable** y por eso no sale sin inducción. Estado: D3 reducida a
    **un solo lema**, `d3_prf_of_chainOkDot`, que sólo pide `hC_dot`.
13. **La inducción como precio** — por qué Q sola no basta y `Full` es imprescindible; el reparto
    verificado con `#print axioms` (D1 y D2 limpios; Gödel I y II citan `ax_induction` /
    `ax_list_induction`). *Material:* `AXIOMS.md` §1.1 (ya escrito, se puede trasladar casi tal cual).
14. **Gödel II, módulo `d3`** — `goedel_second'` montado, y qué significa exactamente publicar un
    teorema «módulo un axioma»: el estado es **honesto y publicable**, y el inventario de los 7
    `axiom` es la garantía. *Material:* `AXIOMS.md`, `Meta/GodelTwo.lean`.

### Parte IV — Lo que no sale en los libros ← **el núcleo original**

> El arco está **cerrado y compilando**: inconsistencia → diagnóstico → cuatro reparaciones fallidas
> → la que funciona → la cuarentena → **la reconstrucción** → **la vía de cero axiomas** → **el muro
> roto**. Esta parte se puede escribir entera hoy.

15. **El muro de `substfc`** — cuando una función objeto no se puede evaluar sobre un código
    abstracto. Planteamiento del problema; su resolución es el cap. 24.
    *Material:* memoria `project-substfc-wall`.
16. **Una inconsistencia latente.** La derivación en cinco pasos; `cons 0 nil = 2 = σσ0`; el error
    de categoría (`tcFn` es una operación sobre **sintaxis** declarada como función **objeto**, que
    sólo puede depender de **valores**). **La lección central:** la inconsistencia era **latente
    desde el principio**, y la hizo visible un teorema *net-0* — `prf_cantor_mono`, que no añadía
    nada. El peligro no estaba en lo que se añadía, sino en lo que ya estaba.
    *Material:* memoria `project-inconsistencia-tcfn-cons`, ADR-012.
17. **Cómo se localiza el daño** — capítulo **metodológico**, y quizá el más útil para el lector.
    Por qué fallan las dos técnicas obvias: la alcanzabilidad por `import` da **falsos negativos**,
    y un crawler de dependencias **no funciona en Lean 4** (`value?` devuelve `NONE` para teoremas
    importados y sólo recorre tipos). La técnica que sí vale: **convertir el puente sospechoso en
    `axiom` de Lean y leer `#print axioms`**, con un **control positivo** que debe salir contaminado.
    Resultado: el daño entra a Gödel I **por un solo sitio**, el lema diagonal.
    *Material:* memoria `feedback-auditoria-footprint`, `sondeos/README.md`, `sondeos/S1Audit.lean`.
18. **Cuatro reparaciones que no funcionan** — el capítulo de **valor negativo**, el que ahorra meses:
    * **Partir el símbolo en dos** (`tcNum`/`tcCode`): insuficiente — las **hojas** de un árbol de
      código son numerales, luego `tcCode` necesitaría las dos recursiones y reproduce el mismo ⊥.
    * **Quitar el axioma sin más**: **decapita la diagonalización**. El «código del código» no es un
      accidente de implementación: es lo que Gödel **exige** para construir `G = β(⌈β⌉)`.
    * **Relativizar por axiomas** en un lenguaje mono-sortido: imposible; tricotomía y orden prueban
      `∀x. x=0 ∨ ∃k. x=σk` **sin inducción**, así que no hay sitio para un `cons` que no sea ni cero
      ni sucesor.
    * **Un paquete de buena-formación** (`isFormCode`): no repara `tc`. **La razón es bonita y
      general**: `substfc` pide un reconocedor **extensional** (un subconjunto de ℕ); `tc` pide una
      distinción **intensional** (qué sintaxis escribimos para el número 9). Un predicado *es* un
      subconjunto: no separa lo que no está separado en los valores.
    ⚠️ Nota de continuidad: la cuarta reparación vuelve en el cap. 22, pero **por otro motivo y con
    otro veredicto** — no confundir «no repara `tc`» con «no sirve para la buena-formación».
19. **La reparación: códigos como numerales.** Por qué el numeral **es** canónico y el árbol no.
    La aritmética **sin división** (números triangulares) que hace exacta la mitad del polinomio de
    Cantor. Y una lección de **método de ingeniería**: se **pilotó antes de ejecutar**, asumiendo el
    resultado costoso como axioma de Lean para comprobar que la cadena cerraba.
    **Coste: −1 axioma, ninguno nuevo.** *Material:* `sondeos/PilotoDiagonal.lean`,
    `sondeos/DescargaHFN.lean`, memoria `project-reparacion-via-numeral`, ADR-012.
20. **Lo que se pierde, y por qué «perder» es la palabra equivocada.** 31 módulos a cuarentena: los
    14 tags, `hI_dot`, el chasis. Eran teoremas **correctos** sobre una teoría que probaba ⊥, o sea
    **vacuos**. El capítulo trata la pregunta incómoda: *¿qué significa haber demostrado algo sobre
    una teoría inconsistente?* ✅ **Y tiene final**: la cuarentena está **vacía**, 31 → 0, por
    **keystone** y **niveles** (argumentos concretos vs abstractos). *Material:*
    `cuarentena/README.md`, `PLAN-FRENTE-A.md`, ADR-013.
21. **La reconstrucción: internalizar en vez de reescribir.** Roto el puente `prf_tc_cons'`, había
    dos vías: reescribir los 21 módulos caídos uno a uno, o **reconstruir el puente dentro de
    `Prov`** con un solo teorema. Se eligió la segunda (ADR-014).
    * **Por qué se pudo:** `cons` **no tiene ecuaciones recursivas propias** — `ax_L0_cons_def` lo
      define por `div2 (cantor_poly h (σt))`, o sea `+`, `·` y `div2`, ya internalizados. Lo que
      parecía un quinto peldaño de inducción resultó ser **ensamblaje**. *Lección general: antes de
      inducir, mirar si el símbolo está definido o es primitivo.*
    * **Las dos técnicas que lo abarataron**, exportables a cualquier formalización con capa de
      códigos: (1) **dotar un teorema OBJETO es gratis** — `tcFn` es símbolo de función, luego es
      congruente, luego cualquier `⊢ a = b` sube a `⊢ ȧ = ḃ` sin entrar en `Prov`; (2) **la
      sustitución cubre todas las ocurrencias del hueco** — un único paso de Leibniz cierra las dos
      apariciones de `x+y` en el polinomio. Cinco pasos en vez de quince.
    * **Y el método:** el rédito se **verificó antes de celebrarlo** (`sondeos/CarcPayoff.lean`).
      «Debería desbloquear» no es un resultado; «desbloquea, aquí está compilado» sí.
    *Material:* `Meta/DotConsPrf.lean`, `doc/REFERENCE-Incompleteness.md` §3.25, memoria
    `project-escalera-sigma1`.
22. **Definir en vez de axiomatizar** ← **NUEVO (ADR-015)**. Los 7 tags de `lineWF` necesitaban un
    predicado de buena-formación sobre códigos. Dos opciones: sancionarlo como ~15-18 axiomas
    objeto, o definirlo por **testigo de parseo** en vocabulario **ya existente**. Se eligió la
    segunda, **y la razón de peso no es el ahorro de líneas**: `ax_axiomsCodeT_eq` ancla a `axioms`,
    luego los axiomas nuevos entrarían en `axioms`, `axiomsCodeT` los absorbería, el verificador
    interno los citaría y **`provCodeC'` cambiaría ⇒ G cambiaría** (141 → ~159 axiomas).
    **La opción cara no es más cara: es OTRO TEOREMA.** Lección general para cualquier
    formalización con verificador interno: **añadir axiomas a la teoría objeto cambia el sujeto del
    teorema de incompletitud.** Corolario elegante: aunque algún día se sancionaran, los sondeos de
    la vía definitoria son su **certificado de conservatividad**.
    *Material:* ADR-015, `doc/REFERENCE-Incompleteness.md` §3.27.
23. **La partición que hace posible la inducción** ← **NUEVO (ADR-016)**. El primer diseño usó **un
    solo** predicado de 12 disyuntos que fusionaba códigos de FÓRMULA y de TÉRMINO. No era un
    defecto estético: **era la razón de que la inducción no existiera**. El cuadre correcto es
    **8 ↔ 8 / 2 ↔ 2 / 2 ↔ 2** contra las ecuaciones de `substfc`/`substtc`/`substtsc`, y
    `pcc_eval_substfc` se atascaba **porque 12 ≠ 8**. Y el fusionado **no discriminaba**:
    `prf_isFC_junk` compilaba —`implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ`, cuyas dos «subfórmulas» son códigos de TÉRMINO,
    **pasaba** el reconocedor—; el partido lo **refuta**. El total de disyuntos **no crece**
    (12 = 8+2+2): es partición, no recubrimiento. **Lección de método, en palabras del propio ADR:
    releer la restricción de diseño ANTES de diseñar, no tras compilar.**
    *Material:* ADR-016, `sondeos/SubCodesCritica.lean`, `sondeos/ParticionTresPredicados.lean`,
    `sondeos/ParticionDiscrimina.lean`.
24. **Cómo se rompió el muro de `substfc`** ← **NUEVO (ADR-017/018, §3.28–§3.31)**. El cierre del
    cap. 15, y el capítulo con más contenido técnico transferible del libro. Cuatro ideas, ninguna
    prevista:
    * **el testigo va ABIERTO** — la clausura era un artefacto de la ruta de prueba, y **acotar es
      circular** (acotar y la clausura de un paso son inter-construibles, probado en las dos
      direcciones). Consecuencia: `ind`/`listInd` **no cambian de aridad y no hace falta sanción**;
    * **UNA sola inducción, con conclusión CONJUNTIVA** — la lectura natural pedía dos inducciones
      mutuamente recursivas; el término y su lista de argumentos viajan juntos, así que la
      conjunción hace de par mutuo. Tres estrategias independientes convergieron por separado en
      este mismo motivo;
    * **la guarda va DENTRO de `Φ`** — `hasWit` es un `∃` **interno**, así que no añade binder
      exterior y el gate `liftFormula 1 Φ = Φ` sigue pasando. La alternativa exigía un lema de
      lifting de **derivaciones** que no existe;
    * **un solo sort**, y **la moneda de la inducción OBJETO**: un lema de caso con la HI como
      hipótesis META (`Prf A → Prf C`) **no sirve** — hay que enunciarlo Γ-paramétrico
      (`∀ Γ, PrfH Γ A → PrfH Γ C`) desde el principio.
    Resultado: `pcc_eval_substfc` **probado**, y su **no-vacuidad** `prf_hasWitF_real` también, con
    footprint **net-0 puro**. *Material:* ADR-017, ADR-018,
    `doc/REFERENCE-Incompleteness.md` §3.28–§3.31, `sondeos/EvalSubstfcPrf.lean`,
    `sondeos/HasWitFReal.lean`, `sondeos/DescensoLiftc.lean`.
25. **Cuando la tarea pendiente es imposible** ← **NUEVO**. El capítulo sobre el valor de **refutar
    tu propio plan**, con cinco casos reales del proyecto:
    `canon_ne` (falso: un `cons` es un número) · `consOk` global (haría el teorema verdadero y
    **vacío**) · **A4** (`hasWitF` sobre argumento abstracto: refutado para *cualquier* testigo) ·
    las **dos primeras vías de la rama C** (la guarda no sale del antecedente — hay una **línea
    basura** que satisface `lineWF`; y cargarla por la cadena daría una D3 **vacua**) ·
    y el propio `PLAN-NEGVERIFIER.md`, que declaraba imposible algo que ya estaba compilado **al día
    siguiente** de escribirse. Moraleja doble: un plan no auditado envejece hacia la falsedad, y
    **una refutación compilada vale más que una tarea abierta**.
    *Material:* `sondeos/README.md` (veredictos negativos), `NEXT-STEPS.md` §3.32.
26. **Método** — qué funcionó al formalizar: trocear y compilar entre pasos; **probar primero lo más
    arriesgado**; **medir antes de construir** (dos veces reveló que la tarea escrita no era la
    tarea real: 155 declaraciones → 21; 1 900-2 700 líneas → 800-1 300); verificación adversarial;
    `#print axioms` como auditoría; y las **trampas caras**, todas reales: no lanzar sondeos contra
    un árbol que cambia; `lake build` puede dar **verde sin construir lo que crees** —señal de
    alarma: el número de jobs no cambia—; filtrar **comentarios de bloque** al buscar usos; y el
    fallo que descubrió la auditoría del 2026-08-22: **los documentos de estado se actualizan por su
    banner y no por su cuerpo** (un ADR llevaba un mes diciendo «no implementado» sobre algo hecho).
    *Material:* memorias `feedback-*`, `AI-GUIDE.md` §27.

### Apéndices

- **A.** Inventario de los 7 `axiom` de Lean con su justificación (`AXIOMS.md`).
- **B.** Mapa de módulos y grafo de dependencias por niveles (`REFERENCE.md`, `DEPENDENCIES.md` §0).
- **C.** Trampas de Lean 4 encontradas (memorias `feedback-lean-*`; incluye `Char.ofNat` clampa,
  `∨` sombreado por `FOL/FOL/FOL.lean:38`, `<=` que resuelve al orden OBJETO con `Minimal.Axioms`
  abierto).
- **E.** Licencia: CC BY-SA 4.0 para la prosa, MIT para el código citado (aviso íntegro).
- **D.** Glosario de símbolos: `⊢` vs `Prf` vs `Prov`, `⌜·⌝` vs `⌈·⌉`, el punto de «dotar» (`ȧ`),
  y la convención de prefijos (`prf_`, `pcc_`, `ax_`, `CRIT_`).

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
| **3a** | Parte II completa (capítulos 5-8) + capítulo 4 | ✅ **HECHO 2026-09-04** | el terreno y la aritmetización están estables y no dependen del frente vivo |
| **2** | Parte IV: capítulos 16-19, 21 y **22-25** | ⏳ **siguiente** | **escribir ahora, mientras el episodio está fresco** — es el material más valioso y el más fácil de perder |
| **3** | Partes I–III (con el cap. 11 corregido) | ⏳ | exposición sistemática; se apoya en `doc/REFERENCE-*.md` ya escritos |
| **4** | Apéndices y bibliografía | ⏳ | mecánico |

⚠️ **Dependencia real del desarrollo (§2.2).** El capítulo 24 puede **escribirse** en la fase 2,
pero sus resultados sólo pueden **enunciarse como teoremas** cuando la **rama B** promueva
`pcc_eval_substfc` y `prf_hasWitF_real` de `sondeos/` a `Meta/`. Hasta entonces el capítulo va como
episodio con código marcado «fuera del build». Es el único punto del libro que espera al proyecto.

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

**Estado al 2026-09-04.** Escritos: **apertura** (nomenclatura, niveles y notación), **capítulo 2**
(kernel FOL⁼), **capítulo 4** (Robinson Q++), **Parte II completa** —5 codificar estructuras,
6 códigos de sintaxis, 7 el verificador, 8 representabilidad y D1— **capítulo 19** y **apéndice E**.
67 fragmentos, 50 páginas, cinco controles en verde. Nada commiteado.

**Siguiente sesión**, por este orden: (1) `make subir` desde el shell del autor, para que el libro
entre en git; (2) `make axiomas` con Lean en el PATH — **los 64 fragmentos de producción están hoy
marcados «declarado, sin medir»**, que es la verdad, y esto los pasa a medidos; (3) capítulo 16
(la inconsistencia latente), o los capítulos 1 y 3 para cerrar la Parte I.

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
  Gödel I vía `goedel_first_numeral`, Gödel II módulo `d3`.
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
| 10 | «sólo se publica lo que compila» era el único criterio de admisión | **§2.2 (nuevo)**: *sólo se expone lo que está demostrado **desde la base*** — alcanzabilidad desde el módulo raíz, footprint impreso y contenido en la base sancionada, y los «módulo algo» obligados a declararlo en el enunciado |

---

**Autor**: Julián Calderón Almendros · Licencia MIT

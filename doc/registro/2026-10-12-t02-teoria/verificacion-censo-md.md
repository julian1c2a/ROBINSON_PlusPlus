# Verificación del censo de los .md

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

Ninguno de los tres apartados cierra limpio. **(a)** De los 48 hallazgos que tocaba revisar (sin contar PLAN-LIBRO), 32 están arreglados, 15 siguen falsos, 1 hay que reclasificarlo y ninguno es ERROR. **(b)** De 30 hallazgos CIERTO o HISTORICO-MARCADO revisados, 4 no lo son. **(c)** Hay 8 omisiones, y dos las introdujo la propia pasada.

Incidente: un script mío creó por error un fichero vacío `x` en la raíz del repositorio. Lo borré en el acto y `git status` vuelve a coincidir con el de partida. No hay cambios sin indexar ni ficheros nuevos.

## (a) Estado de los FALSO-VIGENTE, HISTORICO-SIN-MARCA y DUDOSO (líneas del árbol de hoy)

**ARREGLADO (32):**

| # | dónde | nota |
|---|---|---|
| 1 | README:105 | AXIOMS §0 (l.101), §0.3 (l.157) y ADR‑134 (DECISIONS:10127) ya existen |
| 2 | README:93-94 | |
| 13, 15 | AXIOMS:70, :88-90 | |
| 18 | AXIOMS:288 | nota en :291-306; queda la ✏️ de :276 (c5) |
| 20, 24 | AXIOMS:321-323, :449-450 | |
| 31-34 | CURRENT-STATUS:295-299 | cubiertos por el banner de registro de :285 |
| 47 | REFERENCE:375 | |
| 71-78 | NEXT-STEPS:4363…4553 | cubiertos por el banner de :4357 |
| 79 | REFERENCE-Kernel:10-13 | queda el título de :1, «Teoría objeto `Minimal/Axioms`» |
| 80 | REFERENCE-Kernel:129 | la tabla tiene 34 filas, contadas |
| 87 | REFERENCE-Incompleteness:427 | |
| 90 | sondeos/README:115 | ✏️ en :93-96; quedan otras filas (c7) |
| 95-97, 99 | MINIMAL-AXIOMS | aviso en :7-11 y nota en :350-357 |
| 102 | GODEL-D-ARITHMETIZATION:54 | |
| 103 | ESCALANDO:50 | queda el resto del fichero (c6) |
| 114 | PLAN-SORTES:17 | |
| 115 | FEEDBACK-PARA-EL-LIBRO:278 | |

**SIGUE-FALSO (15):**

| # | dónde | trabajo | arreglo |
|---|---|---|---|
| 35, 40, 41 | CURRENT-STATUS:319, :533, :562 («Full/: inducción general object-level», que toca la teoría) | T26 | Extender el banner de :285 a Status by Module, Pending Work y Architecture |
| 45 | REFERENCE:299 «no hay modelo de los 142» | T27 | «toman hcon; desde ADR‑120 lo descarga `consistencia`» |
| 46 | REFERENCE:324 «⊬¬G sigue SIN cerrar» | T27 (no está en su lista) | ✏️ «desde ADR‑121, `goedel_I_neg`» |
| 49 | REFERENCE:429-431 (modelo, ⊬¬G y Tarski dados por pendientes) | T27 | Un «Hoy» nuevo, sólo con Rosser; el de 10‑04, a registro |
| 52 | DEPENDENCIES:299 (las meta‑reglas «en FOL/MetaRules.lean») | T30 | Tachar y remitir a :377 |
| 55 | DECISIONS:310 (ADR‑010: «sigue en pie para cuatro») | ninguno | ✏️ «retirados todos (ADR‑115 §8)» |
| 69 | NEXT-STEPS:4112 (sección :4107-4251, sin marca) | ninguno (el más cercano, T36) | Subir el banner de :4357 a :4107 |
| 85 | REFERENCE-Incompleteness:9-10 | T29 | Banner de ADR‑120/121 encima |
| 92, 94 | TEOREMAS:72, :119-120 | T09 | Lo que ya pide T09 |
| 101 | GODEL-D-ARITHMETIZATION:15-16 (también :118 y :140) | ninguno (encaja en T55) | Aviso de vigencia en la cabecera |
| 111 | PLANNING:24 | ninguno (T55) | ✏️ en la línea, y en el banner de :3 cambiar «:33» por una marca de texto |
| 120 | NAMING-CONVENTIONS:348 | ninguno | «eran … (retirados con ADR‑115)» |

**RECLASIFICAR (1):** #60, DECISIONS:9164-9172 (ADR‑117 §4). Es el «Lo que NO dice» de un ADR fechado y ADR‑120/121 lo superan pocas líneas abajo. Pasa a HISTORICO-MARCADO. Los bullets equivalentes de ADR‑119 y ADR‑120 tampoco llevan ✏️, y el censo no los cuenta. La ✏️ es opcional (DECISIONS:9137: «registros con fecha se califican»).

**Aparte:** los 7 de PLAN-LIBRO (#104-#110) siguen sin tocar, por decisión (ADR‑134 §7). No aparecieron líneas de `doc/book/`.

## (b) Revisión de 30 CIERTO / HISTORICO-MARCADO

**Se sostienen (comprobado contra el árbol y el código):**
- #0: la lista AUTHORITATIVE de `check-doc-sync.bash:186-187`.
- #3, #4 (Hilbert.lean:153-160: 7 constructores, con `ind`, `qconf` y `listInd`), #5 (SolidezVerificador.lean:558), #7 (Consistencia.lean:50), #8 y #9.
- #22, #43, #44, #54, #59, #64, #89, #93 y #121.
- HISTORICO-MARCADO: #10, #11, #12, #14, #16, #17, #19, #21, #23, #27, #37, #42, #50, #62, #63, #66, #67, #81-#84, #86, #100, #112 y #113.

**Con reparo:**
- #6 (README:130-133) abre con «Siguen siendo CONDICIONALES» y lleva dos ✏️ anidadas; conviene reescribirlo.
- #26 está bien marcado, pero GODEL-STATUS:74 sigue diciendo que el estado vivo está en el bloque «LO QUE QUEDA» (c4).
- #28, #29 y #36 sólo tienen una marca débil (T28/T26).

**Fallan (4):**
- **#88**, REFERENCE-Incompleteness:463-464 (y :471): dice «hay que reconstruirla [0+n=n] con `Prf.ind`». Es FALSO-VIGENTE, no CIERTO: `ax6` es axioma de la lista y 0+n = n+0 = n por `ax4`. El mismo nodo lo dice en :1257-1259, y ADR‑134 corrigió esto en NatArithPrf.lean pero no en el `.md`. Corresponde a T02 (o T29).
- **#38**, CURRENT-STATUS:407: misma afirmación, en una entrada fechada (HISTORICO-MARCADO), y ya era falsa entonces: TuplasFuncionesYListas:233 la prueba con Ax 6. Pide la misma ✏️.
- **#68**, NEXT-STEPS:3704/:3709: la ✏️ nueva dice «dos frases de esta nota son falsas» y deja sin calificar «la cadena real ya vive en Full» y «`Minimal` es la teoría OBJETO que se aritmetiza». Al acotar, las avala. Arreglo: nombrarlas en la ✏️ o declarar registro la nota entera.
- **#98**, MINIMAL-AXIOMS:347: es DUDOSO, no CIERTO. «Estrictamente más débil que PA» no está demostrado (la nota de :350-357 ya lo dice).

## (c) Omisiones (fuera de bloques de registro)

1. **sondeos/README.md:111** (fila nueva de esta pasada): «D1 usa la inducción (`prf_zero_or_succ`, `prf_add_zero_left`…: hechos que Q no demuestra)».
   - Por qué es falso: `prf_zero_or_succ` es Q3, un axioma de Q. Además, los dos salen sin inducción de la lista; el docstring del sondeo (InduccionTitulares.lean:41) lo dice bien.
   - Trabajo: T02.
   - Arreglo: «Q3: axioma de Q, no de la lista; uso evitable (§0.3)».

2. **doc/REFERENCE-Incompleteness.md:123**: «inductive Prf … -- clásico: incl (Prfᵢ) + p3 (DNE) + mp + gen».
   - Por qué es falso: es la única firma de `Prf` en el árbol REFERENCE y omite `ind`, `qconf` y `listInd`; describe un cálculo sin inducción. GODEL-D-ARITHMETIZATION:118 dice lo mismo.
   - Trabajo: T02 / T29.
   - Arreglo: añadir los tres constructores y remitir a AXIOMS §0.

3. **PLAN-PRUEBAS.md:126** (P‑4): «la consistencia de los 142 axiomas no está probada (no hay modelo)».
   - Por qué es falso: hay prueba desde ADR‑120. Es la gemela de FEEDBACK:278, que sí se arregló, y el documento es normativo.
   - Trabajo: T02 (o T21).
   - Arreglo: ✏️ «2026‑10‑05 (ADR‑120): probada, `consistencia`».

4. **NEXT-STEPS.md:4146-4148, :4128, :4149, :4224-4234** (dentro de «LO QUE QUEDA»):
   - Qué dicen: «OmegaConsistent … es creíble (toda teoría sólida la cumple)», «la ω‑regla gen», «Falta sólo NegVerifier» y un orden de lectura caducado.
   - Por qué es falso: OmegaConsistent es refutable por su definición (L1‑4, `sondeos/OmegaConsistentRefutable.lean`) y `gen` no es la ω‑regla (ADR‑027).
   - GODEL-STATUS:74 todavía manda a ese bloque como «estado vivo» (T28).
   - Arreglo: el mismo que #69, más corregir el puntero de GODEL-STATUS:74.

5. **AXIOMS.md:276 y :281** (§1.1): la ✏️ del 2026‑10‑02 dice «El argumento sigue en pie —Gödel II pide inducción—», y :281 responde «No.».
   - Por qué es falso: contradicen la nota nueva de :291-306 (Q ⊬ Con_Q).
   - Trabajo: T02.
   - Arreglo: «lo pide la vía HBL, no el teorema».

6. **ESCALANDO_EL_PROYECTO.md:82**: «el puente es que `Prf → Derives` (`prf_to_derives`)».
   - Por qué es falso: se retiró con ADR‑115 y hoy no hay puente en ninguna dirección (AXIOMS §0.1, T67). También están mal :52 («TFA sin inducción», probado), :102 y :115.
   - Trabajo: ninguno (T55).
   - Arreglo: aviso de vigencia en la cabecera.

7. **sondeos/README.md:103, :104, :131**: «⊬¬G sobre Prf necesita OmegaConsistentProv o Rosser», «no hay modelo» y «Falta el modelo de los 141».
   - Por qué sigue abierto: la ✏️ de :93-96 cubre los docstrings y sólo «la fila de ADR‑085».
   - Trabajo: T02.
   - Arreglo: nombrar también estas filas en la ✏️.

8. **El cierre sobredice**: DECISIONS.md:10230 (ADR‑134 §6) afirma «se corrigieron las que describen la teoría o lo que se supone», y AUDITORIA-SUELO:155 dice «y lo que encontraron los dos censos».
   - Por qué no es así: quedan REFERENCE:299 y :429-431, TEOREMAS:119, PLAN-PRUEBAS:126 y las filas del punto 7. Son de lo que se supone, no de ⊬¬G, que es lo único que §7 (:10238) deja a otros trabajos.
   - Arreglo: que §7 diga «REFERENCE:299 y §5 → T27; TEOREMAS:119 → T09».
   - Menor: en DECISIONS:10246, para contener a PA basta `ind`; no hacen falta «dos constructores».

Lo más grave de las tres listas es el punto 2 (la firma de `Prf` sin inducción en un nodo AUTHORITATIVE), #88 y PLAN-PRUEBAS:126.

Mis scripts y volcados están en `<tmp>\scratchpad\verif_t02\`; el que más sirve es `loc_targets.txt`, con cada hallazgo y su línea actual.

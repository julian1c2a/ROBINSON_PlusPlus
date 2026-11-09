# Las auditorías del proyecto: qué hubo, en qué estado están y qué queda

**Last updated:** 2026-11-09 — creado con [ADR‑263](../DECISIONS.md): el índice de las auditorías de RPP y FOL, con el
estado de sus hallazgos medido en `doc/control/hallazgos.tsv`, y lo que queda de todas ellas.
**Autor:** Julián Calderón Almendros

> **Qué es esto.** Un índice, no un informe nuevo: cada auditoría tiene su documento o su registro, y cada uno de sus
> hallazgos tiene su fila, con su estado y dónde se cerró, en `doc/control/hallazgos.tsv` (426 IDs; `[R]` de
> `check-doc-sync.bash` comprueba en cada push que son los de sus fuentes y que todos tienen estado). Las cifras de §1
> salen de esa tabla el 2026‑11‑09; §2 junta lo que las auditorías dejaron para decidir, lo aprobado que no se ha
> ejecutado y lo que queda medido sin ser deuda.

## 1 · Las auditorías, por fecha

| fecha | auditoría | dónde está | hallazgos | estado | cerrada por |
|---|---|---|---|---|---|
| 2026‑09‑10 | del libro (el camino de vuelta: lo que el libro imprimió y el código ya no dice) | `doc/book/AUDITORIA-2026-09-10.md` (no se toca: el libro está en espera, ADR‑136 §3) | fuera del registro | en espera con el libro; lo que el código ha cambiado desde entonces lo mide la CI en cada run (ADR‑242) y lo recoge `doc/FEEDBACK-PARA-EL-LIBRO.md` | — |
| 2026‑09‑11 | dos ciclos, en las dos direcciones | `doc/AUDITORIA-2026-09-11.md` | 11 | 11 hechos | ADR‑024 y los commits del día |
| 2026‑09‑12 | unificada de FOL y su engarce con RPP | `doc/AUDITORIA-FOL-2026-09-12.md` | 36 | 32 hechos · 2 descartados · 2 sustituidos | ADR‑026…030, 114, 115, 133, 202, 254, 257, 258 |
| 2026‑09‑18 | el panel A1–A5 y los cuatro planes de capa | `doc/AUDITORIA-2026-09-18.md` | 9 | 5 hechos · 4 descartados (los planes de capa) | ADR‑069, 072, 073, 258 |
| 2026‑09‑27 | la constructividad de FOL | `../FOL/auditoria/constructividad-2026-09-27/README.md` | fuera del registro | la vigila `check-choice.bash` (ADR‑193); re‑medida el 2026‑10‑27 | ADR‑110, ADR‑193 |
| 2026‑09‑28 | una cita (sin registro versionado) | — | 1 | 1 hecho | ADR‑117 |
| 2026‑10‑02 | de la base, ronda 1 | `doc/AUDITORIA-BASE-2026-10-02.md` y `doc/registro/2026-10-02-auditoria-base/ronda1/` | 36 | 31 hechos · 4 descartados · 1 sustituido | ADR‑114…122, 129, 154, 188, 190, 192, 197, 253, 254, 257, 258, 260 |
| 2026‑10‑02 | de la base, ronda 2 | `doc/registro/2026-10-02-auditoria-base/ronda2/` | 43 | 37 hechos · 4 descartados · 2 sustituidos | ADR‑115…121, 129, 141, 154, 192, 258 |
| 2026‑10‑05 | adversarial de ADR‑120/121 | `doc/registro/2026-10-05-auditoria-adr120-121/` | 31 | 30 hechos · 1 descartado | ADR‑121, 128, 212, 257 |
| 2026‑10‑05 | adversarial de ADR‑123 | `doc/registro/2026-10-05-auditoria-adr123/` | 12 | 10 hechos · 2 descartados | ADR‑124, 125 |
| 2026‑10‑05 | adversarial de ADR‑124 | `doc/registro/2026-10-05-auditoria-adr124-126/` | 18 | 11 hechos · 7 descartados | ADR‑127, 180 |
| 2026‑10‑05 | adversarial de ADR‑125/126 | `doc/registro/2026-10-05-auditoria-adr124-126/` | 20 | 14 hechos · 6 descartados | ADR‑127, 153 |
| 2026‑10‑12 | del suelo (170 candidatos, agrupados en 81 trabajos T) | `doc/AUDITORIA-SUELO-2026-10-12.md` y `doc/registro/2026-10-12-auditoria-suelo/` | 170 | 168 sustituidos por su T · 2 descartados; los 81 T, hechos | ADR‑132…248 (el último, el 2026‑11‑02) |
| 2026‑10‑28 | de la base, ronda 3 (la última) | `doc/registro/2026-10-28-ronda3/`, `2026-11-04-ronda3/` y `2026-11-04-ronda3b/` | 39 | 39 hechos | ADR‑210…213, 228, 253, 255, 256 |
| 2026‑10‑29 | T71, la mitad semántica de FOL | `../FOL/auditoria/t71-semanticos-2026-10-29/README.md` | fuera del registro | cerrada (ADR‑221); deja preguntas de investigación abiertas (§2, D) | ADR‑221 |
| | **total del registro** | `doc/control/hallazgos.tsv` | **426** | **221 hechos · 0 pendientes · 32 descartados · 173 sustituidos** | |

Un hallazgo DESCARTADO lo está con su razón en la tabla: «sin acción» (18: 17 positivos, «se sostiene», y uno
informativo), lo dejó sin objeto o lo refutó otra medida (11, con los cuatro planes de capa del 2026‑09‑18), o lo decidió el propietario (L5‑02 y L5‑04, ADR‑254;
y RUT‑15, al agrupar la auditoría del suelo). Uno SUSTITUIDO lo está por el trabajo T de la auditoría del suelo que lo
absorbe, y los 81 están hechos.

## 2 · Lo que queda (2026‑11‑09)

Ningún hallazgo de ninguna auditoría está pendiente. Lo que queda es de cuatro clases: decisiones que las auditorías
dejaron al propietario; lo aprobado que no se ha ejecutado; residuos medidos que no son deuda; y preguntas abiertas.

| # | qué | de dónde viene | estado hoy | siguiente paso, y quién |
|---|---|---|---|---|
| **A** | **Decisiones del propietario** | | | |
| A1 | El libro | T49; ADR‑136 §3, ADR‑242; la auditoría del 2026‑09‑10 | EN ESPERA desde el 2026‑10‑14; «al final» (el propietario, 2026‑11‑03). La deriva del código frente al libro, medida en cada run de la CI | cuándo se retoma: el propietario |
| A2 | `PLAN-LIBRO.md`: su cabecera, y su deuda de `[E]` (la única que queda) | ADR‑262 §4 | ADR‑136 §3 no deja tocarlo; la cabecera propuesta, en `doc/registro/2026-11-09-deuda/plan-libro-propuesta.diff.txt` | aceptar esa cabecera (una excepción a ADR‑136, como la de ADR‑138) o dejarlo en la deuda: el propietario |
| A3 | El job `libro` de la CI sale ROJO en master sólo si un push toca `doc/book/` | ADR‑247 §5 | la rama `ci/…` no lo ve | cambiarlo, o darlo por informe: el propietario |
| A4 | Gentzen | T69; ADR‑140, ADR‑244, ADR‑259 | fuera de RPP, en su propio repositorio; medidos los primeros pasos (la forma de los 120 axiomas; `listInd` admisible desde `ind`, en el build) | cuándo empieza: el propietario (`doc/GENTZEN-ALCANCE.md`) |
| A5 | La versión de Lean | T42; ADR‑176, ADR‑181, ADR‑236 | el par en v4.35.0, la última estable (la vigilancia semanal, hoy); el arreglo de lean4#15822 llega con v4.37 | subir cuando haya estable, con `update-toolchain.bash`; al llegar a v4.37, revisar `sondeos/IteSimboloNucleo.lean` y la receta de ADR‑130 |
| A6 | El token de la CI caduca el 2027‑01‑26 | ADR‑216 | la CI de FOL avisa a 30 días | renovarlo en GitHub: el propietario |
| A7 | Tres mejoras del núcleo de `[B]` | ADR‑262 §7 | propuestas: «se RETIRÓ» y «**BORRARON**» no casan como marcador (locale C, la negrita), y las tácticas del proyecto no se indexan | un commit SOLO (ADR‑167), si el propietario lo aprueba; quitaría la mayoría de los falsos positivos de C1 |
| A8 | La regla «DEBE `export`» de la guía de FOL (§17) | ADR‑262 (la revisión de AI‑GUIDE de FOL) | la cumplen 6 de los 70 módulos de FOL; en RPP se enmendó (ADR‑206: opcional) | enmendarla como en RPP, o cumplirla: el propietario |
| A9 | Los usuarios de `prf_list_induction` (D2 entre ellos) podrían ir por `prf_list_induction_sin`, sin `Prf.listInd` | ADR‑259 §4 | no se ha hecho: cambiaría lo que usa la prueba de un titular | el propietario |
| A10 | La ω‑consistencia «honesta», definida y demostrada con el modelo | RUT‑15 (auditoría del suelo), descartado al agrupar: «no es suelo y va contra una decisión escrita» | descartado | sólo si el propietario lo reabre |
| A11 | La tabla de reglas del verificador como dato de Lean | L5‑04; ADR‑254 §1 | descartado, con condición | se reabre si algún día cambian las reglas de `Prf` |
| **B** | **Aprobado y sin ejecutar** | | | |
| B1 | Las capas DENTRO de RPP: un manifiesto módulo→capa, un control de la dirección de los imports y contratos generados | ADR‑139 paso 3, aprobado en ADR‑140 §1; NEXT‑STEPS («Pendiente además de Rosser») | no hay manifiesto ni control (lo que sí está: `DEPENDENCIES.md` generado, ADR‑238, y el contrato de los titulares, T07) | diseñarlo en un ADR: el propietario decide cuándo |
| B2 | PeanoRF: importar `FOL.Calculus.*` en vez de llevar copias | ADR‑218 | su repositorio sigue BLOQUEADO (2026‑10‑01) | cuando se desbloquee |
| **C** | **Residuos medidos (no son deuda)** | | | |
| C1 | `[B]`: 10 citas en RPP y 29 en FOL | ADR‑262 §6 | falsos positivos, cada uno con su razón en `doc/registro/2026-11-09-deuda/LEEME.txt` | caerían casi todos con A7 |
| C2 | Citas de ejemplo y de historia en documentos que no están en la lista de `[B]` (AI‑GUIDE 38, NAMING‑CONVENTIONS 129 en RPP y 168 en FOL, los históricos) | ADR‑262 §7 | fuera del universo de `[B]` por diseño | ninguno |
| C3 | 241 de las 1399 declaraciones de FOL y TheoryFramework que nadie usa | FOL0912:B‑5; ADR‑254 §4 | medidas y etiquetadas en `doc/control/fol-sin-uso.tsv`, sin borrar (decisión del propietario) | la CI las vuelve a medir en cada push |
| C4 | Los pasos clásicos (`p3`) que construyen las pruebas de algunos titulares | TEOREMAS §1; AXIOMS §0.3 | medidos (los cuatro de T75e, entre otros); no es un defecto: `Prf` es clásico | ninguno, salvo que se quiera la variante sin `p3` (ADR‑140 §3) |
| **D** | **Preguntas abiertas (investigación, opcional)** | | | |
| D1 | Qué separa los cinco enunciados semánticos de DNS y de ¬¬EM; si la compacidad implica Markov para las ecuaciones diofánticas, como la completitud; si KSst es estrictamente más fuerte que WKS sin Markov; si WLEM + ¬¬EM bastan para los cinco | T71; `../FOL/auditoria/t71-semanticos-2026-10-29/README.md` («Lo que queda abierto») | abiertas; hay esbozos sin compilar | si se quiere seguir con la matemática inversa de FOL |

**Véase también:** `doc/control/hallazgos.tsv` (cada hallazgo, con su estado), NEXT‑STEPS («Lo que queda»), ADR‑241 (el
registro y `[R]`), ADR‑254 (las cuatro propuestas decididas), ADR‑262 (la deuda de documentación).

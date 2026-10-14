# Registro: artefactos rescatados al árbol

**Last updated:** 2026-10-14 — las carpetas de T02 (ADR‑134) y T09 (ADR‑135). Antes, 2026-10-12 — creado con ADR‑132 (T00 de `doc/AUDITORIA-SUELO-2026-10-12.md`): lo que sólo vivía en el
directorio temporal de la sesión o en la carpeta de la sesión, fuera de git.

**Por qué.** Varias afirmaciones de los ADR («37 de 90 sondeos compilan», «revisión adversarial aplicada», la crítica
del plan de Rosser, la validación de `strip-lean.awk`) descansaban en ficheros fuera del repositorio, y el directorio
temporal es volátil. Ver la memoria del proyecto: *una medición en un scratchpad se evapora; el artefacto va al árbol*.

**Qué es esto y qué no.** Es REGISTRO: copias de lo que produjeron los workflows y las sondas en su día, tal cual. No
es documentación vigente: sus afirmaciones son de su fecha, y lo que diga sobre el código puede haber dejado de ser
cierto. Lo vigente está en `DECISIONS.md`, `NEXT-STEPS.md` y `doc/AUDITORIA-SUELO-2026-10-12.md`. Ningún control de
`check-doc-sync.bash` mira estos ficheros (`[A]` y `[B]` sólo leen los autoritativos), salvo `[E]`, que exige la marca
`**Last updated:**` a este `README.md`.

**Cómo se copiaron.**
* Contenido intacto, salvo las rutas locales absolutas, saneadas por sustitución: `<sesión>` es la carpeta de la sesión de
  Claude Code (`~/.claude/projects/<proyecto>/<sesión>`), `<tmp>` su directorio temporal, `<memoria>` y `<memoria-FOL>` las
  memorias de los dos chats, `<home>` el directorio del usuario. Los JSON siguen siendo JSON válido.
* Las sondas `.lean` del registro se guardan como `.lean.txt`, para que ni Lake ni ningún control las tome por módulos.
  Para recompilar una, copiarla a `sondeos/` (muchas ya están allí, promovidas por ADR‑114).
* Omitido por tamaño: `2026-10-02-auditoria-base/ronda2/ronda2_R22/parsed.json` (4,3 MB; lo regenera `parse.py`) y
  los `__pycache__/`.

## Lo que hay

| carpeta | qué es | origen | lo sostiene / lo cita |
|---|---|---|---|
| `2026-10-02-auditoria-base/ronda1/` | la ronda 1 de la auditoría de la base: `resumen.txt`, `salida_workflow_ronda1.json`, `extraer.py`, las 20 sondas `sonda_L*.lean.txt` y `F1Verif.lean.txt` | `wf_6ab7eb53-016` (2026‑10‑02) | ADR‑114, `doc/AUDITORIA-BASE-2026-10-02.md`; su estado por ID es T37 |
| `2026-10-02-auditoria-base/ronda2/` | la ronda 2: `resumen.txt`, `salida_workflow_ronda2.json`, `ronda2_script.js`, las sondas `sonda_R2-*.lean.txt`, y los scripts y salidas de `r2l4/` y `ronda2_R22/` (grafo de dependencias, censos) | `wf_0f4ca25d-649` (2026‑10‑02) | ADR‑115; T37 |
| `2026-10-05-adr122-d7-rosser/` | la medición de D7 y de lo que pedía Rosser: `resultado.json` (el plan de siete etapas y su crítica) y `workflow.json` (script y resultado) | `wf_f04aaaa5-037` (2026‑10‑05) | ADR‑122 §1–§2; T01 (el plan, a versionar con su ADR) |
| `2026-10-05-auditoria-adr120-121/` | la auditoría adversarial de W1, `⊬¬G`, E10, Tarski y la promoción del modelo | `wf_68cece92-90b` | ADR‑121 |
| `2026-10-05-auditoria-adr123/` | la comprobación adversarial del sondeo de ADR‑123 | `wf_107c9121-80b` | ADR‑123…125 |
| `2026-10-05-auditoria-adr124-126/` | la auditoría de ADR‑124…126 | `wf_e04d70c1-e0c` | ADR‑127 |
| `2026-10-05-d7-exploracion/` | la exploración de D7 antes de ejecutarla: `workflow.json` (el diseño de la macro `sym!`), los inventarios `inv_*.txt` (los 24 + 28 ficheros, los 164 literales, los riesgos R1–R5), las pasadas en seco `dry_*.txt` (229, 210 y 105 líneas) y `lit_rpp.txt` | `wf_cac4ffca-a10` (2026‑10‑05) | ADR‑129 §2–§3, `Minimal/SymLit.lean` |
| `2026-10-05-d7-revision/` | D7: la corrección de la prosa de FOL y RPP y su revisión adversarial (`resultado.json`, `workflow.json`, `revisiones.txt` con las dos revisiones, `hechos.txt` con lo que era cierto tras D7) | `wf_4c5aee66-ebf` (2026‑10‑05) | ADR‑129 («revisión adversarial aplicada»); T17 |
| `2026-10-12-auditoria-suelo/` | esta auditoría: `candidatos.json` (los 163 candidatos de los seis barridos, con el veredicto de su verificador), `workflow-barridos.json` y `workflow-cierre.json` | `wf_1f61bc0d-738` (2026‑10‑05) y `wf_7a6e4ce2-b37` (2026‑10‑12) | `doc/AUDITORIA-SUELO-2026-10-12.md`, ADR‑132 |
| `2026-10-12-t02-teoria/` | T02: los hechos y los censos de cómo describían la teoría los documentos (`workflow-hechos.json`, script y resultados), el workflow de revisión que murió por el límite de sesión (`workflow-revision-fallida.json`), los cinco informes del 2026‑10‑14 (`revision-*.md`, `verificacion-censo-*.md`), la salida del sondeo de la inducción y la medición de leanchecker; y en `comentarios/` el lote de comentarios de los `.lean`: los encargos (`INSTRUCCIONES.md`, `grupo-*.md`), los siete informes de corrección y las tres revisiones adversariales. El build y los controles del día (`build-…`, `control-…`) son de antes de aplicar esas tres revisiones, que sólo tocaron comentarios | `wf_54bdca87-06c` (2026‑10‑12), `wf_22f6795d-314` (2026‑10‑13) y agentes sueltos (2026‑10‑14) | ADR‑134 |
| `2026-10-14-t09-teoremas/` | T09: la salida del sondeo `sondeos/InduccionTitulares.lean` con `#modelo` (`sondeo-induccion-modelo-2026-10-14.txt`: las clases de los 18 titulares) y la prueba del control `[T]`, verde sobre el documento y rojo con el fallo puesto (`control-T-2026-10-14.txt`) | el sondeo y `check-doc-sync.bash` (2026‑10‑14) | ADR‑135 |

Fuera de esta carpeta, rescatado en el mismo commit:

| ruta | qué es |
|---|---|
| `scripts/sondeos_todos.ps1` | el runner que produjo las tablas de las pasadas de sondeos (rutas hechas relativas al repo; sigue con `lake env lean`, ver T06) |
| `sondeos/pasadas/tabla_adr121.txt`, `tabla_adr127.txt`, `tabla_d7_antes_de_migrar.txt`, `tabla_adr129.txt` | las tablas «fichero\|exit\|segundos\|primer error» de esas pasadas (T06/T10) |
| `scripts/pruebas/b/` | `b_medir.bash`, la réplica de `[B]` con cuatro juegos de marcadores, y sus salidas `bdeuda.txt` y `citas_prod.txt` (T04) |
| `scripts/pruebas/leanlex.py` | el lexer de referencia, función a función el de Lean v4.31.0, con el que se validó `strip-lean.awk` (ADR‑116; las cuatro copias del temporal eran idénticas) |
| `scripts/pruebas/scan_mangle.py` | busca en los scripts de control las huellas de una cadena de herramientas que «come» escapes |
| `scripts/pruebas/strip-lean/` | `v5/` (los mutantes de `strip-lean.awk` v5 y sus pruebas de humo) y los fixtures `fx/`, `synth/` y `censo-entorno/` de las revisiones de ADR‑116, guardados como `.lean.txt`: llevan `sorry` a propósito y `check-sorry.bash` recorre todo `.lean` del árbol. ⚠️ Sus scripts todavía apuntan a `<tmp>/scratchpad` y esperan `.lean`: hacerlos ejecutables desde aquí es T47 |

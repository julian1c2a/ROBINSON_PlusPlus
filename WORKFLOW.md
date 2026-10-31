# Development Workflow

**Author**: Julián Calderón Almendros
**Last updated:** 2026-11-01 — [ADR‑235](DECISIONS.md) (T21): los controles, contra el código (el gate es la CI entera; los ganchos versionados de T14; qué mira cada control). Antes, 2026-10-28 — ADR‑212: el orden del bump del toolchain (Parte 4). Antes, 2026-06-05 — Adaptado a flujo IA + opción legacy `git-lock.bash`.

Guía operativa para colaborar en este proyecto. Cubre los **dos modos** activos: sesiones con asistente IA (modo principal) y trabajo humano con `git-lock.bash` (legacy, opcional).

---

## Parte 1 — Setup inicial (una vez por máquina)

### Requisitos

* **Lean 4, la versión de `lean-toolchain`** (v4.35.0 desde el 2026‑10‑21, ADR‑181; gestionado por elan), la MISMA en RPP y en FOL (M‑3): la CI de RPP da rojo si los dos `lean-toolchain` difieren. ✏️ 2026‑10‑31 (T21, ADR‑235): decía «v4.29.1», la versión de mayo (v4.31.0 desde julio).
* **`lake`** (incluido con Lean).
* **`git`** y acceso al repo `julian1c2a/ROBINSON_PlusPlus`.
* **FOL** clonado como proyecto sibling en `../FOL` (referenciado en `lakefile.lean`).

### Clonar

```bash
git clone https://github.com/julian1c2a/ROBINSON_PlusPlus.git
cd ROBINSON_PlusPlus
lake build                                     # RPP y lo que importa de FOL (sus jobs, en CURRENT-STATUS-PROJECT §1;
                                               # en la CI, 185 s en frío: la primera medida del presupuesto, ADR‑203)
lake build "@FOL/FOL" "@FOL/TheoryFramework"   # FOL entero, desde la raíz de RPP (M‑3)
# ✏️ 2026‑10‑31 (T21, ADR‑235): decía «~23 jobs, ~1–3 min en caché fría», las cifras de junio.
```

### (Opcional) Los ganchos versionados

Los de `git-lock.bash` (Parte 3): pre-commit (bloqueados y congelados) y commit-msg (un thaw cita su ADR de RPP). Git
no activa ganchos solo, y la CI no depende de ellos:

```bash
bash git-lock.bash init    # activa los ganchos versionados de .githooks/ (core.hooksPath), una vez por clon
```

✏️ 2026‑10‑31 (T21, ADR‑235): era «git hook legacy», «solo si vas a trabajar en modo humano con bloqueos por archivo»:
hasta T14 (ADR‑234), «init» instalaba un pre-commit sin versionar.

---

## Parte 2 — Modo IA (flujo principal)

Sesiones colaborativas con Claude Code (u otro asistente). Sin locks por archivo; el control de cambios se hace por commits frecuentes y la CI en verde como gate (ver «Gate de calidad»). ✏️ 2026‑10‑31 (T21, ADR‑235): decía «build verde»; desde ADR‑136, el gate es el job entero de la CI.

### Ciclo de trabajo típico

1. **Orientación**: el asistente lee `REFERENCE.md` (mapa del proyecto), `NEXT-STEPS.md` (qué toca ahora), `CURRENT-STATUS-PROJECT.md` (sorrys + módulos), `MEMORY.md` (checkpoints de sesiones previas).
2. **Edición directa**: el asistente modifica `.lean` con la herramienta `Edit` o `Write`; cada cambio significativo seguido de `lake build` para detectar regresiones inmediatas.
3. **Commit frecuente** tras cada milestone (un módulo cerrado, un axioma eliminado, una doc actualizada). El resumen empieza por su ADR (y su tarea, si la hay: «ADR‑NNN: Txx — …»), y el cuerpo dice el porqué y lo medido (ver «Convención de commits»). En FOL, el resumen cita el ADR de RPP, «(ADR‑NNN de RPP)», y un thaw está obligado a citarlo (el gancho commit-msg y, en la CI de FOL, check-congelados.bash). ✏️ 2026‑10‑31 (T21, ADR‑235): decía Conventional Commits («tipo(scope): resumen»); desde el 2026‑10‑01 ningún resumen de RPP lleva esa forma, y casi todos empiezan por su ADR.
4. **Push** al final de cada milestone (no esperar al final de la sesión), a una rama ci/… —FOL antes que RPP (M‑12)—: con su CI en verde, master avanza hasta ese commit y se vigila su run (AI‑GUIDE, «guarda_y_sube»; ADR‑136, ADR‑204). ✏️ 2026‑10‑31 (T21, ADR‑235): decía sólo «Push»; desde ADR‑136, master sólo admite un commit con la CI ya verde.
5. **Doc sync** al cerrar un bloque de trabajo: actualizar `REFERENCE.md`, `CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md` y el ADR de `DECISIONS.md` según los cambios (`CHANGELOG.md` está congelado desde ADR‑142; ✏️ 2026‑10‑31, T21, ADR‑235: lo nombraba entre los que se actualizan), y dejar `bash check-doc-sync.bash` en verde (AI‑GUIDE §27, M‑6): la CI lo pasa en cada push, y su rojo no deja avanzar master. Su [E] exige que la marca «Last updated» de cada documento no sea anterior a su último commit (hoy, si tiene cambios), salvo los de sus dos tablas de deuda —E_DEUDA, de contenido (la marca, vieja), y E_DEUDA_FORMATO, de formato (sin marca; vacía)—, que sólo pueden bajar: su techo son las de la base verificada (T24, ADR‑233).
6. **Checkpoint** al cerrar sesión: guardar archivo en `memory/project_session_YYYY-MM-DD.md` con el estado y el siguiente paso, e indexarlo en `MEMORY.md`.

### Gate de calidad

* `lake build` y `bash check-doc-sync.bash` deben pasar **antes de commitear** (AI‑GUIDE, «guarda_y_sube», paso 1; PLAN‑PRUEBAS §3 pide además `check-sorry.bash` y, en el frente tocado, `check-footprints.bash`); si se toca FOL, también `lake build "@FOL/FOL" "@FOL/TheoryFramework"`. En local nada lo impone: el gate es la CI. master está protegido (ADR‑136) y sólo avanza hasta un commit cuyo job «lake build» de `.github/workflows/build.yml` salió verde en una rama ci/…, y ese job da rojo con cualquiera de sus pasos: el mismo toolchain en RPP y en FOL (M‑3), los dos builds (el de RPP con `#pureza_titulares`, `#contrato_titulares` y `#pureza` dentro), leanchecker y su cobertura, el segundo núcleo, el presupuesto de tiempo y memoria (y un tope de tiempo para el job entero), check-sorry, check-estratos, check-footprints, check-choice, check-doc-sync, check-warnings, los sondeos de control, la prueba de los controles y los thaws de FOL (scripts/thaws-fol.bash). Sólo avisa «El par registrado» (el FOL de `doc/control/fol-sha.txt`). El job «libro» no es obligatorio: corre en el push a master, cuando toca `doc/book/`. ✏️ 2026‑10‑31 (T21, ADR‑235): decía sólo `lake build`, que en junio era todo el gate: la CI de la plantilla («Build» y un «Check for sorry» que sólo avisaba) no arrancó hasta el 2026‑09‑09, porque su YAML no parseaba (4f6f8e1).
* **0 `sorry` reales** es la línea base desde 2026-05-27, y desde ADR‑116 (2026‑10‑04) un `sorry` es ROJO en la CI, sin excepción. Lo buscan `check-sorry.bash` (el token —sorry, admit, stop o `sorryAx`— en el código sin comentarios ni cadenas de todo .lean del repo, `sondeos/` incluidos) y `check-estratos.bash` (`sorryAx` en el entorno de RPP, FOL y TheoryFramework), y con master protegido (ADR‑136) no llega a él. ✏️ 2026‑10‑31 (T21, ADR‑235): decía que un `sorry` nuevo pedía «justificación explícita en el commit»: hasta ADR‑116, «Check for sorry» sólo avisaba.
* El linter unusedSimpArgs está activo por omisión en todo módulo, y desde ADR‑227 cualquier aviso es ROJO en la CI (`check-warnings.bash`, con la tabla vacía): el argumento señalado se quita. Si hay que conservarlo, «set_option linter.unusedSimpArgs false in» delante de esa declaración, y su cuenta (por fichero, opción y forma) entra en `doc/control/opciones.tsv` (sólo con un ADR), que `check-warnings.bash` compara con igualdad: cuenta las de fichero y las «… in», y de fichero no queda ninguna (ADR‑229). ✏️ 2026‑10‑31 (T21, ADR‑235): decía «si está activo en el módulo editado» —lo apagaban opciones de fichero, que ADR‑229 pasó a «… in»— y que bastaba documentar por qué se conserva.

### Comandos formales (definidos en `AI-GUIDE.md`, sección "Comandos Interactivos para la IA")

El usuario puede invocar estos verbos para que el asistente ejecute flujos predefinidos:

| Comando | Qué hace |
|---|---|
| `dame situación` | Reporte read-only: build, sorries, módulos, último cambio. |
| `actualiza doc` | Pasada completa de documentación tras una sesión de desarrollo. |
| `proyecta` | Extrae exports nuevos a `REFERENCE.md`. |
| «guarda_y_sube» | `lake build` y `bash check-doc-sync.bash`; commit; push a una rama ci/…; con la CI en verde, avance rápido de master (protegido, ADR‑136) y vigilancia de su run (ADR‑204). ✏️ 2026‑10‑31 (T21, ADR‑235): decía «guarda y sube» y «Build + commit + push». |

### Convención de commits

```text
ADR-NNN: Txx — <resumen: qué cambia>

<cuerpo: el porqué, lo medido (con el control que lo mide), las decisiones y lo pendiente>

Co-Authored-By: Claude Opus X.Y <noreply@anthropic.com>
```

Txx, la tarea, si la hay. En FOL, el resumen cita el ADR de RPP: «… (ADR‑NNN de RPP)». ✏️ 2026‑10‑31 (T21, ADR‑235):
aquí estaba la plantilla de Conventional Commits («tipo(scope): resumen corto», con los tipos feat, fix, chore,
docs y refactor, y el módulo como scope), que los commits de RPP no siguen desde octubre.

---

## Parte 3 — Modo humano legacy (`git-lock.bash`)

Flujo histórico con bloqueos explícitos por archivo (ADR-003). **En RPP no se usa en sesiones IA** (no hay ficheros bloqueados ni congelados), pero la infraestructura sigue disponible; en FOL, sus congelados y bloqueados rigen todo commit, también en las sesiones IA (✏️ 2026‑10‑31, T21, ADR‑235: decía «No se usa en sesiones IA»).

### La regla de un solo archivo

> **A lo sumo un `.lean` puede estar desbloqueado en cualquier momento.**

### Ciclo

```bash
bash git-lock.bash list                                # qué hay bloqueado o congelado (lo desbloqueado es el resto)
bash git-lock.bash unlock ROBINSON_PlusPlus/X.lean     # desbloquea para editar
# … editar X.lean …
bash git-lock.bash lock   ROBINSON_PlusPlus/X.lean     # bloquea al terminar
```

Si cambias de archivo a mitad de sesión: lock el actual antes de unlock el siguiente.

### Los ganchos: pre-commit y commit-msg

El gancho pre-commit rechaza un commit que toque un fichero de `locked_files.txt` o de `frozen_files.txt` (también un
renombre) y avisa, sin bloquear, de los `sorry` de los ficheros preparados. Su hermano, commit-msg, rechaza un thaw (una
entrada que sale de `frozen_files.txt`) cuyo mensaje no cite el ADR de RPP que lo autoriza («ADR‑NNN de RPP»). Los dos
están versionados en .githooks/, y `bash git-lock.bash init` los activa (core.hooksPath), una vez por clon: git no
activa ganchos solo. La CI no depende de ellos: la de RPP comprueba que son los mismos que los de FOL, y que cada thaw
de FOL se apoya en un ADR de RPP que existe y nombra al propietario (scripts/thaws-fol.bash); la de FOL los
prueba (check-gancho.bash) y vigila los congelados, con el ADR en el mensaje de cada thaw (check-congelados.bash).
✏️ 2026‑10‑31 (T21, ADR‑235): decía «Bloquea commits que toquen archivos en locked_files.txt (o frozen_files.txt).
Instalado con bash git-lock.bash init»; hasta T14 (ADR‑234), «init» copiaba a .git/hooks/pre-commit un heredoc sin
versionar que, con las listas en CRLF (core.autocrlf=true), no casaba ninguna entrada y no bloqueaba nada (R3‑4‑01, que
ADR‑212 sólo arregló en FOL).

### Freeze y thaw

Un módulo completo se congela con `bash git-lock.bash freeze`: «unlock» lo rechaza, y el gancho pre-commit rechaza el
commit que lo toque. Sólo lo descongela «thaw … --confirm», por decisión del propietario escrita en un ADR de RPP que el
mensaje del commit cita (el gancho commit-msg; para los de FOL, también su CI y la de RPP). Las extensiones se hacen en
un módulo «FooExt.lean» que importa el congelado (ver `AI-GUIDE.md` §21). En RPP no hay ninguno congelado
(`frozen_files.txt` está vacío): los congelados son de FOL. ✏️ 2026‑10‑31 (T21, ADR‑235): decía «permanentemente
inmutables», sin el thaw, que T14 (ADR‑234) ata a un ADR.

---

## Parte 4 — Toolchain

```bash
# PROBAR el par con otra versión de Lean (por defecto, la última estable), en worktrees aparte y SIN commit
# (T42, ADR‑176): builds de FOL y RPP, leanchecker (sin su cobertura) y cinco controles —footprints, warnings,
# estratos, sorry y los sondeos de control—, con la versión que corre comprobada.
# ✏️ 2026‑10‑31 (T21, ADR‑235): decía «leanchecker y los controles»: no pasa check-choice, check-doc-sync, el segundo
# núcleo, el presupuesto, la prueba de los controles ni los thaws de FOL, que la CI sí (R3‑3‑08).
bash update-toolchain.bash [v4.x.x]        # o: --check, sólo dice si hay otra
# El bump, si se decide, va por un ADR y a mano, en los dos repos (M‑12: FOL primero). El ORDEN (R3‑3‑02, ADR‑212):
#   1. FOL, el commit del bump en una rama ci/…: su CI compara con el master de RPP, aún viejo, y AVISA (no rompe);
#      verde, avance de su master. ⚠️ Ese avance lanza la CI de RPP contra su master, aún viejo (ADR‑216), que, como la
#      cruzada diaria, sale ROJA en «El mismo toolchain…» hasta el paso 2: la ventana de M‑12, no una regresión;
#   2. RPP, el commit del bump en ci/…: su CI compara con el master de FOL, ya nuevo, y ROMPE si difieren; verde, avance.
# La vigilancia semanal:
# .github/workflows/toolchain.yml, contra doc/control/toolchain-vigilado.txt (la última versión probada).
# En la CI, elan va fijado, con su sha256 (T40, ADR‑202).
```

---

## Parte 5 — Mantenimiento

### Añadir un módulo

Se crea a mano en su capa —Minimal, Meta o Full: fuera de ellas [L] es rojo— (ROBINSON_PlusPlus/Meta/Nombre.lean, …) y
se importa desde su barril (`ROBINSON_PlusPlus/Meta.lean`, o la raíz `ROBINSON_PlusPlus.lean`). Los dos barriles se
curan a mano: sus comentarios dicen por qué entró o salió cada módulo. Los `globs := #[.andSubmodules …]` del lakefile
compilan todo `ROBINSON_PlusPlus/`, se importe o no, y [L] de `check-doc-sync.bash` es rojo si un fichero no está en el
cierre de imports del barril o no está en git. En la misma subida, o la CI sale roja, van también: su entrada en el
catálogo de `REFERENCE.md` §1 ([C]); las cifras de módulos activos, de Meta y de jobs de los documentos autoritativos
([A] y [A2]); una fila en la tabla de `check-footprints.bash` por cada `#print axioms` que traiga ([COBERTURA]); y una
línea en `doc/control/choice.tsv` por cada constante con `Classical.choice`, noncomputable o `String`
(`check-choice.bash`).

✏️ 2026‑10‑18 (T15, ADR‑163): aquí estaban `gen-root.bash` y `new-module.bash`, retirados. El primero reescribía el
barril y borraba sus comentarios; el segundo pedía una plantilla, `_template.lean`, que ya no existía.

### Verificar estado

```bash
lake build                                     # RPP y lo que importa de FOL (dentro, #pureza_titulares, #contrato_titulares y #pureza)
lake build "@FOL/FOL" "@FOL/TheoryFramework"   # FOL entero, desde la raíz de RPP (M‑3)
bash check-sorry.bash                 # sorry, los agujeros de confianza y las órdenes que evalúan el ancla: rojo con cualquiera
bash check-estratos.bash              # por entorno: los estratos, y ningún sorryAx, axioma de confianza, implemented_by/extern ni partial sin declarar
bash check-footprints.bash            # el footprint de cada fila de su tabla, y [COBERTURA]
bash check-choice.bash                # choice, noncomputable y String, contra doc/control/choice.tsv
bash check-doc-sync.bash              # documentación ↔ código: [A], [A2], [B], [C], [D], [E], [F], [H], [I], [L], [M], [N], [T] y [EOL]
bash check-warnings.bash              # cero avisos, y las opciones que apagan un linter o suben un límite, contra doc/control/opciones.tsv
bash check-sondeos.bash --controles   # los sondeos de control (sondeos/CONTROLES.txt)
bash scripts/thaws-fol.bash           # cada thaw de FOL, con su ADR de RPP; git-lock.bash y .githooks/, iguales en los dos repos (pide python3)
bash git-lock.bash list               # qué archivos están en estado lock/frozen
# Lo demás que bloquea en la CI —el mismo toolchain en RPP y en FOL (M‑3), elan con su sha256, leanchecker y su cobertura, el segundo núcleo (scripts/segundo-nucleo.bash: el cierre
# de los titulares, el modelo incluido, por núcleos independientes del de Lean; ADR‑228), el presupuesto y la prueba de
# los controles—, en .github/workflows/build.yml; qué comprueba cada control y qué no, en PLAN-PRUEBAS.md §1.
# ✏️ 2026‑10‑31 (T21, ADR‑235): aquí sólo estaban lake build, check-sorry y git-lock list; en junio la CI no arrancaba
# (su YAML no parseaba hasta el 2026‑09‑09, 4f6f8e1), y hasta ADR‑116 sólo avisó de los sorry.
```

---

## Parte 5bis — Tres reglas operativas que salieron del 2026‑09‑10h

Van aquí porque las tres son de **método de trabajo**, no de un frente concreto.

### 5bis.1 · ⚠️ Un `sorry` en el `simp set` **no mide una ruta: la FABRICA**

Al medir «cuánto falta» para un empaquetado se metió en el `simp set` un lema propio dejado en
`sorry`. **Tres** objetivos compilaron con él — y el lema era **falso**. `simp` usa la ecuación para
reescribir **el objetivo**, así que puede llevarlo justo donde está la hipótesis: el verde no midió
la distancia, **la borró**. ⇒ un `sorry` sirve para **posponer una rama**, nunca para **completar un
`simp set`**; y si hace falta un lema de cancelación, **buscarlo primero** (`FOL/Theorems/`).

### 5bis.2 · ⚠️ Subsumir la CLASE no es descargar la OBLIGACIÓN (M‑8)

Un sondeo compilado concluía que no había que estrechar una clase porque otra la subsumía. El
**teorema era cierto** y la **conclusión falsa**: la obligación que dejaba pedía decidir una
igualdad numérica **incalculable**. ⇒ ante un «X ya cubre Y, no hay que tocar nada», preguntar
**qué obligación queda después** y si **se puede pagar**.

### 5bis.3 · 🔑 Cada axioma que se RETIRA audita lo que se apoyaba en él

Al demostrar un postulado apareció un **círculo** que llevaba meses en el árbol: `A` se «derivaba»
de `B` y `B` de `A`. **Lean lo aceptaba porque el círculo pasaba por un `axiom`.** ⇒ retirar un
postulado no sólo fortalece: **revisa**. Y al romperlo, decidir cuál es el primitivo **buscando un
modelo**, no argumentando.

---

## Parte 6 — Estructura de archivos clave

| Archivo | Propósito |
|---|---|
| `AI-GUIDE.md` | **Lee primero**: protocolos, naming, comandos formales. |
| `REFERENCE.md` | Mapa técnico del proyecto (módulos, defs, teoremas, axiomas). |
| `NEXT-STEPS.md` | Qué toca hacer ahora. Actualizado por sesión. |
| `CHANGELOG.md` | Historia cronológica de cambios hasta ADR‑113: CONGELADO desde ADR‑142 (el registro es `DECISIONS.md`, y git log). |
| `CURRENT-STATUS-PROJECT.md` | Snapshot del build + métricas. |
| `TEOREMAS-E-HIPOTESIS.md` | Los titulares y quién descarga cada hipótesis ([T]). |
| `AXIOMS.md` | El inventario de los axiomas (M‑1). |
| `PLAN-PRUEBAS.md` | Qué comprueba cada control, y qué no (normativo; autoritativo para `check-doc-sync.bash`). |
| `DEPENDENCIES.md` | Grafo de dependencias ANTERIOR a ADR‑115: no describe el árbol de hoy (el catálogo, en `REFERENCE.md` §1), y ningún control lo compara con los import (T30). ✏️ 2026‑10‑31 (T21, ADR‑235): decía «verificado contra imports». |
| `MINIMAL-AXIOMS.md` | Análisis comparativo del sistema axiomático vs Q/PA⁻. |
| `DECISIONS.md` | ADRs (decisiones arquitectónicas). |
| `THOUGHTS.md` | Diario informal (no normativo). |
| `DISCUSIONES.md` | Discusión histórica sobre axiomas eliminados. |
| `PLANNING.md` | Plan estratégico de largo plazo. |
| `TuplasFuncionesYListas.md` | Especificación fundacional del sistema `Minimal`, histórica: buena parte se retiró (aviso de vigencia, ADR‑134). Ningún control la congela. |
| `NAMING-CONVENTIONS.md` | Convenciones Mathlib-style con 12 reglas. |
| `.github/workflows/build.yml` | La CI: el gate de master (ADR‑136). |
| `doc/control/` | Las tablas versionadas con las que comparan los controles: las deudas de [A2] y [B], choice, las opciones, el presupuesto, el segundo núcleo, el par de FOL, el toolchain vigilado y los thaws de FOL. |
| `WORKFLOW.md` | Este archivo. |

---

## Parte 7 — Diferencias respecto a la versión anterior

Esta revisión (2026-06-05) reconoce que el modo de trabajo dominante es la colaboración con IA, no el flujo humano con `git-lock.bash`. Cambios:

* **Modo IA** documentado como flujo principal (Parte 2), no como nota a pie.
* **`git-lock.bash` movido a "Parte 3 — legacy"**: sigue funcional para sesiones humanas pero deja de presentarse como obligatorio.
* **Eliminado** el "Step 1 — Clone the template" / "Step 2 — Run setup": el proyecto ya existe, no hay setup desde plantilla.
* **Añadidos** comandos formales (`dame situación`, `actualiza doc`, etc.) que el usuario invoca por nombre — son la verdadera interfaz cuando trabajas con el asistente.
* **Convención de commits** explicitada con ejemplos Conventional + `Co-Authored-By` para sesiones IA.

Si quieres recuperar la versión template original, sigue en el historial git (`git log --all WORKFLOW.md`).

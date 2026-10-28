# PLAN DE PRUEBAS — ROBINSON_PlusPlus

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Las cifras de hoy, cada una con el control que la mide, en [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md).

**Creado:** 2026‑09‑11 (lo abrió la auditoría, `doc/AUDITORIA-2026-09-11.md` F‑4) · **Autor:** Julián Calderón Almendros
**Last updated:** 2026-10-28 — [ADR‑210](DECISIONS.md): V10, con los 32 titulares. Antes, el mismo día — [ADR‑209](DECISIONS.md) (T34): la cita del `.gitignore`, sin número de línea. Antes, el mismo día — [ADR‑202](DECISIONS.md) (T41): P‑3, el tiempo y la memoria de la CI, vigilados. Antes, 2026-10-27 — [ADR‑194](DECISIONS.md) (T46): V11, las once nociones. Antes, 2026-10-21 — [ADR‑185](DECISIONS.md) (T28): entra en AUTHORITATIVE (lo miran `[A]` y `[A2]`); el
banner, sin las cifras del 2026‑09‑11; V3, V5, V7 y su recuadro (lo que bloquea en la CI: hoy, todo el job de build),
V10 (32 titulares desde ADR‑210), y las filas V11–V16 de los controles que faltaban: los censos por entorno, los avisos,
`leanchecker`, los sondeos de control, las herramientas de los controles y la vigilancia de versiones.

---

## 0 · Por qué este documento existe

La auditoría del 2026‑09‑11 midió que **cero ficheros del repo contenían las palabras «plan de
prueba»**. El plan existía —y era bueno— pero **sólo como práctica**. Eso tiene un coste concreto:
la disciplina más distintiva del proyecto —*medir en un sondeo compilado antes de tocar
producción*— sólo se podía inferir de que hay 61 ficheros en un directorio.

⚠️ **Y un plan de pruebas que no está escrito no se puede auditar.** Es el mismo principio §2.6 del
libro aplicado a la verificación: *un control da fe de lo que comprueba, no de lo que crees que
comprueba.*

---

## 1 · Qué se verifica, y con qué

| # | control | qué garantiza | qué **NO** garantiza |
|---|---|---|---|
| **V1** | `lake build` | **todo el árbol activo typechequea** en el kernel de Lean. Es la única prueba *fuerte* que hay: una demostración que compila **es** una demostración | nada sobre si el **enunciado** es el que se quería *(✏️ 2026‑10‑18: el de los 24 titulares lo fija V10)* |
| **V2** | `bash check-sorry.bash` | **cero `sorry`/`admit`/`native_decide`** reales, despojando comentarios y literales | que no haya `axiom`s haciendo el papel de `sorry` — eso lo mira V3 |
| **V3** | `bash check-footprints.bash` (`#print axioms` de cada titular declarado, en los dos sentidos, y `[COBERTURA]`) | el **footprint exacto**: qué postulados sostienen cada teorema | que el postulado sea *razonable* (eso lo decide un ADR); ni los axiomas que habitan un inductivo (V11) |
| **V4** | `bash check-doc-sync.bash` | `[A]` cifras de cabecera · `[A2]` cifras del cuerpo (aviso) · `[B]` citas muertas (rompe desde ADR‑166, con trinquete por cita) · `[C]` proyección · `[D]` marcas de tiempo · `[E]` frescura del titular (aviso) *(✏️ 2026‑10‑18: hoy rompen todos salvo `[A2]`, y hay más: `[F]`, `[H]`, `[M]`, `[T]` y `[L]`, la librería = el cierre de imports, ADR‑163)* | **la verdad de las frases**. Ver §4 |
| **V5** | `sondeos/*.lean` | resultados **compilados** de preguntas cerradas antes de tocar producción; los de CONTROL, en la CI (V14) | que la pregunta fuese la correcta |
| **V6** | `doc/book/scripts/*.py` | que todo `\ident{}` del libro **exista** en el repo, que el vocabulario se introduzca antes de usarse, y que el código **impreso** sea el del repo | que lo impreso sea *verdad* — sólo que **cite bien** |
| **V7** | CI (`.github/workflows/build.yml`) | **job `build`**, en cada push: ⛔ **todos sus pasos BLOQUEAN** —V1, V13, V2, V11, V3, V4, V12, V14 y V15—, y `master` está protegido: sólo entra un commit con ese job en verde (ADR‑136; en FOL, ADR‑168). **job `libro`**: V6 entero **sólo cuando el push toca `doc/book/`** — el libro y el código son **dos tareas con commits separados** (PLAN‑LIBRO §0) | ⚠️ que un cambio en `.lean` rompa una cita del libro **no se ve hasta el siguiente push del libro**: el precio de las dos tareas, medido el 2026‑09‑11 al retirar `goedel_second'` |

> 🔶 **Qué BLOQUEA y qué AVISA, exactamente.** ✏️ 2026‑10‑21 (ADR‑185): este recuadro decía que `check-sorry` sólo
> avisaba; es BLOQUEANTE desde ADR‑116 (2026‑10‑04), y desde entonces se añadieron los demás pasos. Hoy:
>
> | paso de CI | efecto |
> |---|---|
> | todo el job `build` (de `lake build` a `probar-controles`) | ⛔ **bloquea** |
> | los cuatro del job `libro` | ⛔ bloquean, salvo §2.1 (`verificar_pdf.py`), que avisa |
>
> ⭐ Y por dos sitios a la vez: un `sorry` lo ven V2 (el texto) y V11 (el entorno), y `[A]` compara la cifra de
> `sorry` de los documentos.
| **V8** | 🆕 **`TEOREMAS-E-HIPOTESIS.md`** | por cada teorema cabecera, **quién descarga cada hipótesis**. Es la única defensa contra **F‑1** | es **a mano**: ningún script lo comprueba *(✏️ 2026‑10‑14, [ADR‑135](DECISIONS.md), T09: ya no del todo. Está en AUTHORITATIVE, y `[T]` de `check-doc-sync.bash` comprueba que cada titular de su universo declarado tenga fila y que ninguna fila sobre. Lo que sigue a mano es «quién descarga» y «qué usa la prueba»; la segunda la mide `#modelo`, `sondeos/InduccionTitulares.lean`, y la mecanizará T08)* |
| **V9** | 🆕 `#pureza_titulares` (`Meta/PurezaTitulares.lean`, ADR‑143, T08) | que el cierre de los 12 titulares de la clase (i) no nombra la semántica, con tres controles positivos que tienen que nombrarla | una prueba que use la verdad en ℕ sin pasar por `FOL.Metamath.Semantics` ni `SolidezPrf`; y el enunciado |
| **V10** | 🆕 `#contrato_titulares` (`Meta/PurezaTitulares.lean`, ADR‑165, T07) | el ENUNCIADO de los 32 titulares de `T_UNIVERSO` (24 en ADR‑165, 29 hasta ADR‑210) y el valor de las definiciones de las que depende: el cierre de sus tipos, una huella por constante, contra `Meta/ContratoTabla.lean`, en los dos sentidos | las pruebas; lo de Lean; que el enunciado fijado sea el que se quería (F1 habría quedado fijado) |
| **V11** | 🆕 `bash check-estratos.bash` (ADR‑115/116; señuelo, ADR‑179) | POR ENTORNO: qué `axiom` habita cada una de las 11 nociones de derivabilidad (RPP y FOL), con su solidez, su completitud y su puente, y que §0bis de REFERENCE es esa tabla (T46, ADR‑194), y ninguna constante que use `sorryAx`, un axioma ajeno a los tres de Lean, `implemented_by`/`extern` o un `partial` no declarado; un señuelo permanente con una constante de cada clase prueba en cada ejecución que el censo las ve | lo que no es un `axiom` ni nombra `sorryAx`: una declaración metida sin pasar por el núcleo (eso, V13) |
| **V12** | 🆕 `bash check-warnings.bash` (ADR‑060) | los avisos del build, declarados uno a uno (fichero, clase, cuenta), en los dos sentidos | que un aviso declarado sea inofensivo |
| **V13** | 🆕 `leanchecker` (en la CI, ADR‑116) | re‑envía al núcleo cada declaración de RPP, FOL y TheoryFramework: caza la que entró sin pasar por él (`debug.skipKernelTC`, `addDeclWithoutChecking`) | no es un núcleo independiente: es el mismo (T23; «lean4lean» y «nanoda» vienen con el toolchain desde v4.35.0). En local, con `LEAN_NUM_THREADS=4` (ADR‑181) |
| **V14** | 🆕 `bash check-sondeos.bash --controles` (ADR‑141) | los 11 sondeos de control (`sondeos/CONTROLES.txt`) compilan, y sus `#guard_msgs` fijan los mensajes que miden | los de registro, que no van a la CI |
| **V15** | 🆕 `make probar-controles` (ADR‑180) | que el despojador `strip-lean.awk` cuadre con su oráculo (en los `.lean` del árbol y los fixtures), que sus mutantes los mate el humo de `check-sorry`, y que `lineWFT` sea la traducción de sus axiomas (en la CI, los dos primeros) | que el oráculo siga al lexer de la versión de Lean en uso: se comprueba al subir de versión (ADR‑181) |
| **V16** | 🆕 `update-toolchain.bash` y `.github/workflows/toolchain.yml` (ADR‑176) | cada lunes, si hay una versión estable de Lean que el par no ha probado; la prueba, en worktrees aparte y sin commit | que subir sea buena idea: lo decide el propietario |

---

## 2 · La regla que estructura el trabajo: **el sondeo previo**

> ⭐ **Antes de tocar producción en un frente no trivial, se abre un `sondeos/*.lean` que conteste
> la pregunta que decide el diseño — y se compila.**

No es burocracia: está **medido** que paga. Tres casos, los tres del historial:

* `NegVerifierModE.lean` — el plan daba al módulo E riesgo **ALTO** y 300‑500 líneas; el sondeo midió
  que salía en **diez**, y que el riesgo estaba **en otro sitio** (C y D).
* `MedirF_Censo.lean` — midió el censo de los 21 tags y **cazó un docstring falso de producción**.
* `CanonNeRefuta.lean` — **refutó** un paso del plan (`canon_ne`) antes de que costara un frente.

⚠️ **Y la trampa recíproca, también medida**: un sondeo puede ser **un teorema cierto con una
conclusión falsa** (regla **M‑8**). Lo que hay que preguntarle a un sondeo no es «¿compila?» sino
**«¿qué obligación queda después, y se puede pagar?»**.

### 2.1 · `Probe/` vs `sondeos/` — la frontera, escrita (F‑9)

| | qué es | ¿versionado? |
|---|---|---|
| **`Probe/`** | **borrador**: medir si algo casa, tantear una táctica, leer un error | ❌ **no** (`.gitignore`) — es ruido, y correctamente |
| **`sondeos/`** | **resultado**: la pregunta que se contestó, con su respuesta compilada | ✅ **sí**, con su fila en `sondeos/README.md` |

> ⛔ **MANDATORY (M‑9)**: **un `Probe/` que decide un ADR se promueve a `sondeos/` antes de cerrar
> ese ADR**, o la decisión queda sin evidencia versionada. Si el probe pasó **a producción**
> (como `Probe/Fuerza.lean` → `Meta/OmegaStrength.lean`, retirado con la capa `⊢`, ADR‑115), la evidencia es el módulo y no hay nada
> que promover.

---

## 3 · Cuándo se ejecuta cada cosa

| momento | qué se ejecuta |
|---|---|
| durante el trabajo | `lake build` sobre el módulo (`lake env lean <fichero>`) |
| antes de commitear código | **V1 + V2**, y **V3** en el frente tocado |
| antes de cerrar una pasada de documentación | **V4 en verde** (M‑6), con `[A2]`, `[B]` y `[E]` **adjudicados uno a uno** *(✏️ ADR‑166: `[B]` rompe; adjudicarlo es arreglar o marcar)* |
| antes de commitear el libro | **V6** + `doc/book/scripts/ambito.py` |
| en cada push | **V7** |

⚠️ **Desde PowerShell**, no desde Git Bash: `lake` no está en el PATH de Bash y `check-doc-sync`
**se salta la cifra de jobs** sin avisar más que en una línea.

---

## 4 · ⛔ Lo que NINGÚN control garantiza — y es la parte útil

Sale de `doc/AUDITORIA-2026-09-11.md` §4. **Escribirlo es la única defensa que hay contra ello.**

| nadie comprueba | cómo se manifestó | mitigación |
|---|---|---|
| que **las hipótesis de un teorema cabecera sean descargables** | **F‑1**: `goedel_second'` anunciado como Gödel II durante meses, con una hipótesis que ninguna pieza podía dar | ⬜ no mecanizable. **La pregunta**: *por cada teorema cabecera, ¿quién descarga cada hipótesis, y con qué?* |
| que el **cálculo del enunciado** sea el que el resultado necesita | **F‑1**: `⊢` resultó ser **sintácticamente completo** (`Meta/OmegaStrength.lean`) ⇒ no puede ser sujeto de incompletitud | ⬜ ninguna. Se decide al **enunciar** |
| que la **frase** de un banner siga siendo cierta | **F‑2**: seis documentos con el mismo titular falso **y las cifras al día** | 🔶 `[E]` mira la **fecha**, no la frase |
| que el **README** describa el proyecto que existe | **F‑3**, meses | ⬜ ninguna |
| que un **`sorry` de andamiaje** no falsee una medición | un `sorry` en el `simp set` **fabrica** el verde | ⬜ ninguna. **Regla**: un `sorry` pospone una rama, nunca completa un `simp set` |
| que un **postulado** no esconda un **círculo** | `ax21` ⇄ `ax_mod2_alternation`, invisible mientras uno fue `axiom` | ⬜ ninguna. **Regla**: cada axioma retirado **audita** lo que se apoyaba en él |
| ⭐ que **el control mismo** no esté roto por un artefacto de la cadena de herramientas | **2026‑09‑11**: `check-doc-sync.bash` llevaba un **byte 0x01** donde iba la retro‑referencia de `sed`, y su patrón sólo cubría una de las **dos** salidas de `check-sorry.bash` ⇒ **la cifra de `sorry` no se midió nunca**: se comparaba contra una constante. ⚠️⚠️ **El byte se reprodujo solo al arreglarlo** ⇒ no era una errata, es lo que produce escribir esa secuencia a través de la cadena de herramientas | 🔶 **Regla nueva**: en un control, **ninguna retro‑referencia** — extraer con `grep -oE`. Y **probar el control con el fallo puesto**: se verificó metiendo un `sorry` real y comprobando que `[A]` ROMPE |

---

## 5 · Lo que falta por montar

| | qué | estado |
|---|---|---|
| **P‑1** | `verificar_pdf.py` en CI | 🏁 **HECHO — y RE‑HECHO el mismo día**, porque la primera versión **no podía ejecutarse nunca**. Job **`libro`** (no `libro-pdf`: el nombre estaba mal aquí), con TeX Live y sólo cuando cambia `doc/book/`. ⛔⛔ **Medido el 2026‑09‑11**: el checkout era *shallow* ⇒ `github.event.before` no existía como objeto ⇒ el `git diff` de la puerta abortaba, su stderr iba a `/dev/null` y la puerta daba **siempre `run=false`**, con el job **en verde** y **cero controles ejecutados**. Corregido con `fetch-depth: 0`, una puerta que **falla hacia EJECUTAR** ante la duda, los checkouts hermanos de `FOL` y `Peano` que `simbolos.py` necesita para su cierre de imports, `poppler-utils` para §2.1 y `PYTHONIOENCODING`. ⚠️ **Sigue sin verificarse en el runner** hasta el primer push que toque el libro |
| **P‑2** | un control de **hipótesis descargadas** | 🏁 **HECHO**: **`TEOREMAS-E-HIPOTESIS.md`** — teorema → hipótesis → **quién la descarga**. ⚠️ Es **a mano**: se actualiza en el mismo commit que toca un teorema cabecera. Una fila «⬜ nadie» es información; una fila **ausente** es el fallo *(✏️ 2026‑10‑14, ADR‑135: la fila ausente de un titular de `T_UNIVERSO` la caza hoy `[T]`; uno nuevo que no se añada allí, no: ver V8)* |
| **P‑3** | medir el **tiempo** de build | ✅ desde ADR‑202 (T41): GNU time alrededor del build y de `leanchecker` en la CI, contra un presupuesto versionado (`doc/control/presupuesto-ci.tsv`, rojo por encima), y `timeout-minutes` en los jobs |
| **P‑4** | **¿basta `ConsistentH`?** | 🏁 **SÍ, y resuelto el mismo día**: `goedel_first_prf` y `goedel_second_prf` toman hoy `ConsistentH := ¬ Prf ⊥`, la hipótesis **mínima**. ⭐ Y el footprint cayó a **`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]`** — **un solo axioma del proyecto**: las ω‑reglas y los dos esquemas de inducción entraban **por la hipótesis vieja** · ✏️ **2026‑10‑04 (ADR‑117)**: el ancla `prf_axiomsCodeT_eq` (un `axiom`, retirado) pasó después a ser la clase `[AnclaEq]` (ADR‑026), que daba `Prf ⊥` (F1, ADR‑114: los dos eran vacuos); hoy es un TEOREMA (`prf_ancla`), y los dos toman sólo `ConsistentH`, con footprint `[propext, Classical.choice, Quot.sound]`. ⚠️ Siguen siendo condicionales: la consistencia de los 142 axiomas no está probada (no hay modelo) *(✏️ 2026‑10‑14, [ADR‑134](DECISIONS.md): desde ADR‑120 lo está —`consistencia`, un modelo de los 142 y la solidez de `Prf`—, y es la de toda la teoría `T_Prf`)* |

---

**Véase también:** `AI-GUIDE.md` §27 (el control de sincronía y sus seis bloques),
`doc/AUDITORIA-2026-09-11.md` (de dónde sale este documento), `sondeos/README.md`.

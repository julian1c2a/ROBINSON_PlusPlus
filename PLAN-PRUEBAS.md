# PLAN DE PRUEBAS — ROBINSON_PlusPlus

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Las cifras de hoy, cada una con el control que la mide, en [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md).

**Creado:** 2026‑09‑11 (lo abrió la auditoría, `doc/AUDITORIA-2026-09-11.md` F‑4) · **Autor:** Julián Calderón Almendros
**Last updated:** 2026-11-04 — ADR‑254: V23, `check-indice.bash` (el índice de las constantes y lo que nadie usa de FOL). Antes, 2026-11-02 — ADR‑250 y ADR‑251: V10 con 35 titulares; V17, los 35 por los seis núcleos y nanoda con cuatro hilos. Antes, el mismo día — ADR‑237…243: V4 con los cinco bloques nuevos de `check-doc-sync.bash` ([G], [G.2], [P], [R] y [S]) y la consistencia en [I]; V21 (el `--check` de DEPENDENCIES, T30) y V22 (el informe del libro, T49). Antes, 2026-11-01 — [ADR‑235](DECISIONS.md) (T21): lo que dice de cada control, medido contra el código (la tabla V, el recuadro de la CI, §3, §4 y §5), y tres filas nuevas: V18 (los thaws de FOL, T14), V19 (la constructividad) y V20 (el presupuesto de la CI). Antes, 2026-10-30 — [ADR‑228](DECISIONS.md): V17, los 32 aceptados por los seis núcleos. Antes, el mismo día — [ADR‑222](DECISIONS.md) (T23): V13 cuenta lo que replaya, y V17, el segundo núcleo. Antes, 2026-10-28 — [ADR‑210](DECISIONS.md): V10, con los 32 titulares. Antes, el mismo día — [ADR‑209](DECISIONS.md) (T34): la cita del `.gitignore`, sin número de línea. Antes, el mismo día — [ADR‑202](DECISIONS.md) (T41): P‑3, el tiempo y la memoria de la CI, vigilados. Antes, 2026-10-27 — [ADR‑194](DECISIONS.md) (T46): V11, las once nociones. Antes, 2026-10-21 — [ADR‑185](DECISIONS.md) (T28): entra en AUTHORITATIVE (lo miran `[A]` y `[A2]`); el
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
| **V1** | `lake build` (y `lake build "@FOL/FOL" "@FOL/TheoryFramework"`, el paso «Build FOL» de la CI: FOL y TheoryFramework enteros, no sólo lo que RPP importa) | **todo el árbol activo typechequea** en el kernel de Lean. Es la prueba *fuerte* de base *(✏️ 2026‑10‑31 (T21, ADR‑235): decía «la única»; la repiten V13, con el mismo núcleo y declaración a declaración, y V17, sobre el cierre de los 32 titulares, con cuatro núcleos independientes del de Lean)*: una demostración que compila **es** una demostración | nada sobre si el **enunciado** es el que se quería *(✏️ 2026‑10‑18: el de los 24 titulares lo fija V10)* |
| **V2** | `bash check-sorry.bash` | **cero `sorry`/`sorryAx`/`admit`/`stop`** en RPP (con `sondeos/` y `scripts/`, sin Probe/), despojando comentarios y literales; **cero** de las ocho familias que sacan una prueba del núcleo (native_decide, decide +native, unsafe, opaque, implemented_by, extern, ofReduceBool/ofReduceNat/trustCompiler y skipKernelTC/addDeclWithoutChecking) en lo que compila el build de RPP, FOL y TheoryFramework; y ninguna orden #eval, #reduce, #guard, run_cmd, run_elab o run_meta que evalúe el ancla, ni en el build de RPP ni en `sondeos/` (ADR‑117). Cada censo lleva su autotest; los `sorry` de FOL los ven V11 y V12 | que no haya `axiom`s haciendo el papel de `sorry` — eso lo mira V3 |
| **V3** | `bash check-footprints.bash` (`#print axioms` de cada titular declarado, en los dos sentidos, y `[COBERTURA]`) | el **footprint exacto**: qué postulados sostienen cada teorema | que el postulado sea *razonable* (eso lo decide un ADR); ni los axiomas que habitan un inductivo (V11) |
| **V4** | `bash check-doc-sync.bash` | `[A]` cifras de cabecera · `[A2]` cifras del cuerpo (aviso hasta ADR‑169; hoy rompe, con trinquete por línea: `doc/control/a2-deuda.tsv`) · `[B]` citas muertas (rompe desde ADR‑084; desde ADR‑166, toda cita con forma de identificador o de ruta, con trinquete por cita: `doc/control/b-deuda.tsv`) · `[C]` proyección · `[D]` marcas de tiempo · `[E]` frescura del titular (aviso hasta ADR‑072; hoy rompe si la marca «Last updated» de un .md versionado —todos, salvo los de `doc/book/`— es anterior a su último commit, o a hoy si tiene cambios sin commitear; la deuda, en dos tablas del script —E_DEUDA, la de contenido: marca vieja; E_DEUDA_FORMATO, la de formato: sin marca, vacía desde ADR‑233—, cada documento por la razón de su tabla, en los dos sentidos y con TECHO en la base verificada, T24, ADR‑233) *(✏️ 2026‑10‑18: hoy rompen todos salvo `[A2]`, y hay más: `[F]`, `[H]`, `[M]`, `[T]` y `[L]`, la librería = el cierre de imports, ADR‑163)* *(✏️ 2026‑10‑31 (T21, ADR‑235): hoy rompen TODOS: la VERDAD DEL CÓDIGO (si no puede medir), `[L]`, `[EOL]` (finales de línea, ADR‑200), `[H]` del PATH higiénico (ADR‑201), `[A]`, `[A2]`, `[E]`, `[B]`, `[I]` (frases que un teorema vivo desmiente, ADR‑169), `[N]` (citas por número de línea, ADR‑209), `[C]`, `[D]`, `[F]`, `[H]` del catálogo de `sondeos/`, `[M]` y `[T]`)* *(✏️ 2026‑11‑02: y cinco más, rojos: `[G]` y `[G.2]` —las deudas enunciadas que ya tienen testigo, y el censo clasificado de los marcadores de deuda de los `.lean`; portados de FOL, T32, ADR‑237—, `[P]` —los footprints de la prosa de FOL y de RPP contra las filas de `check-footprints.bash`; T39, ADR‑240—, `[R]` —el registro de hallazgos, `doc/control/hallazgos.tsv`: cada ID de las auditorías con su estado; T37, ADR‑241— y `[S]` —las citas de sondeos del build: de CONTROL, archivadas con su etiqueta o de procedencia declarada; T10, ADR‑243—; y `[I]` vigila también la consistencia «sin probar», ADR‑237)* | **la verdad de las frases**. Ver §4 |
| **V5** | `sondeos/*.lean` | resultados **compilados** de preguntas cerradas antes de tocar producción. Los de CONTROL se recompilan en la CI (V14); los de registro, sólo a mano, con el modo informe de `check-sondeos.bash`, que sale con 0 aunque alguno no compile (el 2026‑10‑21, ADR‑181, de los 44 sondeos —los 11 de control incluidos— compilaban 43; `A3IsFCBTracked` no, y `sondeos/README.md` lo tiene por reparar) | que la pregunta fuese la correcta |
| **V6** | `doc/book/scripts/*.py` | lo COMPRUEBAN, sin bloquear nada (V7, P‑1): que todo `\ident{}`/`\modulo{}` del libro **exista** en el repo (`simbolos.py`), que el vocabulario se introduzca antes de usarse (`terminos.py`), que cada fragmento citado exista y se alcance desde el barril (`extraer.py`), y que el código **impreso** sea el del repo (`verificar_pdf.py`, que sólo avisa) | que lo impreso sea *verdad* — sólo que **cite bien** |
| **V7** | CI (`.github/workflows/build.yml`) | **job `build`**, en cada push a master, main o una rama ci/…, en cada PR a master o main, cada día (04:41 UTC) y tras cada push al master de FOL, que lo lanza con workflow_dispatch (ADR‑202, ADR‑216): ⛔ **todos sus pasos BLOQUEAN, salvo «El par registrado»**, que sólo avisa (ADR‑202) *(✏️ 2026‑10‑31 (T21, ADR‑235): eran V1, V13, V2, V11, V3, V4, V12, V14 y V15; hoy son, por orden: M‑3 —el mismo toolchain en RPP y en FOL—, V18, elan —fijado, con su sha256—, V1 —con V9, V10 y los `#pureza` de los módulos— y el build de FOL, V13 con su cobertura, V17, V20, V2, V11, V3, V19, V4, V12, V14 y V15; si uno sale en rojo, los siguientes no corren)*, y `master` está protegido: sólo entra un commit con ese job en verde (ADR‑136; en FOL, ADR‑168). **job `libro`**: cuatro controles de V6 —`simbolos.py`, `terminos.py`, `extraer.py` con la compilación del libro, y `verificar_pdf.py`; `ambito.py` y `extraer.py` con --axiomas sólo se corren en local—, **sólo en un push fuera de las ramas ci/… (ADR‑136) que toque `doc/book/`** (o sin commit base utilizable): en la práctica, el push a master, cuando master ya ha avanzado — el libro y el código son **dos tareas con commits separados** (PLAN‑LIBRO §0) | ⚠️ que un cambio en `.lean` rompa una cita del libro **no se ve hasta el siguiente push del libro** *(✏️ 2026‑10‑31 (T21, ADR‑235): y entonces tampoco bloquea, porque el job `libro` no es obligatorio en la protección de master; ver P‑1)*: el precio de las dos tareas, medido el 2026‑09‑11 al retirar `goedel_second'` (retirado) |

> 🔶 **Qué BLOQUEA y qué AVISA, exactamente.** ✏️ 2026‑10‑21 (ADR‑185): este recuadro decía que `check-sorry` sólo
> avisaba; es BLOQUEANTE desde ADR‑116 (2026‑10‑04), y desde entonces se añadieron los demás pasos *(✏️ 2026‑10‑31,
> T21, ADR‑235: no todos; `lake build`, el build de FOL, estratos, footprints, doc‑sync y warnings ya bloqueaban, y
> llegaron después leanchecker (el mismo ADR‑116), los sondeos de control (ADR‑141), `probar-controles` (ADR‑180) y,
> tras esta nota, `check-choice.bash` (ADR‑193), M‑3, el par registrado y el presupuesto (ADR‑202), la cobertura de
> leanchecker y el segundo núcleo (ADR‑222), y los thaws de FOL (ADR‑234))*. Hoy:
>
> | paso de CI | efecto |
> |---|---|
> | todo el job `build` salvo «El par registrado»: M‑3, los thaws de FOL (V18) y elan (con su sha256) antes de `lake build`, y de `lake build` a `probar-controles` | ⛔ **bloquea** |
> | «El par registrado» (el master de FOL frente a `doc/control/fol-sha.txt`; ADR‑202) | ⚠️ avisa: construir contra el master de FOL es a propósito (ADR‑073) |
> | los cuatro del job `libro` | ⛔ rompen el job, salvo §2.1 (`verificar_pdf.py`), que avisa; pero *(✏️ 2026‑10‑31 (T21, ADR‑235))* **no bloquean** master: el job no es obligatorio en la protección y sólo corre en un push fuera de las ramas ci/…, en la práctica el de master, que ya ha avanzado. El 2026‑10‑21 salió rojo en §2.6 y master siguió |
>
> ⭐ Y por más de un sitio: un `sorry` de la librería de RPP lo ven V2 (el texto), V11 (el entorno) y V12 (su aviso);
> uno de FOL o de TheoryFramework, V11 y V12 (la búsqueda de `sorry` de V2 sólo mira el árbol de RPP; su censo de
> agujeros de confianza, también FOL y TheoryFramework); uno de `sondeos/` o de `scripts/`, que el build no compila,
> sólo V2 (y V14, si es de control). Y `[A]` compara con los documentos la cifra de `sorry` de RPP.

| # | control | qué garantiza | qué **NO** garantiza |
|---|---|---|---|
| **V8** | 🆕 **`TEOREMAS-E-HIPOTESIS.md`** | por cada teorema cabecera, **quién descarga cada hipótesis**. Es la única defensa contra **F‑1** | es **a mano**: ningún script lo comprueba *(✏️ 2026‑10‑14, [ADR‑135](DECISIONS.md), T09: ya no del todo. Está en AUTHORITATIVE, y `[T]` de `check-doc-sync.bash` comprueba que cada titular de su universo declarado tenga fila y que ninguna fila sobre. Lo que sigue a mano es «quién descarga» y «qué usa la prueba»; la segunda la mide `#modelo`, `sondeos/InduccionTitulares.lean`, y la mecanizará T08 (✏️ 2026‑10‑31 (T21, ADR‑235): para los 12 de la clase (i) la comprueba cada build desde ADR‑143, V9; `#modelo` no corre en la CI))* |
| **V9** | 🆕 `#pureza_titulares` (`Meta/PurezaTitulares.lean`, ADR‑143, T08) | que el cierre de los 12 titulares de la clase (i) no nombra la semántica, con tres controles positivos que tienen que nombrarla; y `#pureza` (`Meta/PurezaComando.lean`; ADR‑147, ADR‑149), lo mismo sobre teoremas del propio módulo, al final de los de Rosser, Löb y los corolarios de Gödel, con su control positivo, `mutanteLocal`, que tiene que nombrarla | una prueba que use la verdad en ℕ sin pasar por `FOL.Metamath.Semantics` ni `SolidezPrf`; y el enunciado |
| **V10** | 🆕 `#contrato_titulares` (`Meta/PurezaTitulares.lean`, ADR‑165, T07) | el ENUNCIADO de los 35 titulares de `T_UNIVERSO` (24 en ADR‑165, 29 hasta ADR‑210, 32 hasta ADR‑250) y el valor de las definiciones de las que depende: el cierre de sus tipos, una huella por constante, contra `Meta/ContratoTabla.lean`, en los dos sentidos | las pruebas; lo de Lean; que el enunciado fijado sea el que se quería (F1 habría quedado fijado) |
| **V11** | 🆕 `bash check-estratos.bash` (ADR‑115/116; señuelo, ADR‑179) | POR ENTORNO: qué `axiom` habita cada una de las 12 nociones de derivabilidad (RPP y FOL), con su solidez, su completitud y su puente, y que §0bis de REFERENCE es esa tabla (T46, ADR‑194), y ninguna constante que use `sorryAx`, un axioma ajeno a los tres de Lean, implemented_by/extern o un `partial` no declarado; un señuelo permanente con una constante de cada clase prueba en cada ejecución que el censo las ve; y —sin señuelo que lo pruebe— ningún módulo cargado de una librería que no sea Init, Std, Lean, Lake, FOL, TheoryFramework o RPP (la marca «@AJENO»), y, por texto y con autotest, la escalera de binders de RPP («forall_», «pcc_thm_inst», «pcc_axiom_inst», «PSI_inst» y «psi_lift_form») en su peldaño máximo declarado | lo que no es un `axiom` ni nombra `sorryAx`: una declaración metida sin pasar por el núcleo (eso, V13) |
| **V12** | 🆕 `bash check-warnings.bash` (ADR‑065, por la cifra falsa de ADR‑060 §6) | los avisos de los dos builds (RPP; FOL y TheoryFramework) contra una tabla (fichero, clase, cuenta), con igualdad en los dos sentidos *(✏️ 2026‑10‑31 (T21, ADR‑235): la tabla está **vacía** desde ADR‑227, así que cualquier aviso es rojo)*; y las opciones que apagan un linter o suben un límite —desde ADR‑226 las de fichero; desde ADR‑229, también las «set_option … in», y de fichero no queda ninguna—, contra `doc/control/opciones.tsv`, también con igualdad y con autotest | que un aviso declarado sea inofensivo; ni un aviso que el `lake build` repetido no vuelva a imprimir: en la CI corre con el build ya hecho, y la parte de los avisos no tiene autotest |
| **V13** | 🆕 `leanchecker` (en la CI, ADR‑116) | re‑envía al núcleo cada declaración de RPP, FOL y TheoryFramework: caza la que entró sin pasar por él (`debug.skipKernelTC`, `addDeclWithoutChecking`). Desde ADR‑222 (T23), con `--verbose`, y `scripts/leanchecker-cobertura.bash` comprueba que lo replayado son los módulos de las fuentes y los `.olean` (193, los tres) | no es un núcleo independiente: es el mismo (eso, V17). En local, con `LEAN_NUM_THREADS=4` (ADR‑181) |
| **V14** | 🆕 `bash check-sondeos.bash --controles` (ADR‑141) | los 11 sondeos de control (`sondeos/CONTROLES.txt`) compilan con `lake lean` (con los leanOptions del build), cada uno en menos de 600 s y sin `sorry`; uno de ellos, `IteSimboloNucleo`, fija además con `#guard_msgs` los mensajes que mide (el de `AnclaEqInconsistente`, su control 3, quedó dentro de un comentario de registro: desde ADR‑117 el error que fijaba ya no sale) | los de registro, que no van a la CI |
| **V15** | 🆕 `make probar-controles` (ADR‑180) | que el despojador `strip-lean.awk` cuadre con su oráculo (en los `.lean` del árbol y los fixtures), que sus mutantes los mate el humo de `check-sorry`, y que `lineWFT` sea la traducción de sus axiomas (en la CI, el primero y el tercero; los mutantes, a mano) | que el oráculo siga al lexer de la versión de Lean en uso: se comprueba **a mano** al subir de versión (así en ADR‑181); ni `update-toolchain.bash` ni `toolchain.yml` lo comparan, ni pasan V15 |
| **V16** | 🆕 `update-toolchain.bash` y `.github/workflows/toolchain.yml` (ADR‑176) | cada lunes (y a mano), si hay una versión estable de Lean que el par no ha probado. La prueba, sin commit —en la CI, sobre los checkouts del runner (con --en-sitio); en local, en worktrees aparte—, pasa los dos builds, V13, V3, V12, V11, V2 y V14 (no V4, V15, V17, V18, V19 ni V20). El job queda ROJO, aunque compile, hasta que la versión se registra en `doc/control/toolchain-vigilado.txt` con un ADR | que subir sea buena idea: lo decide el propietario |
| **V17** | 🆕 `scripts/segundo-nucleo.bash` (en la CI, ADR‑222, T23) | el cierre de los 12 titulares de la clase (i), exportado con `leanexport`, lo aceptan seis núcleos —cuatro independientes del de Lean: lean4lean, nanoda, con‑leche y con‑ron—; ✏️ desde ADR‑228, también el de los 32, el modelo incluido (nanoda, con un hilo y la pila del proceso sin límite); ✏️ desde ADR‑250 y ADR‑251, el de los 35, con la completitud de FOL, y nanoda con cuatro hilos; lo medido, contra `doc/control/segundo-nucleo.tsv` en los dos sentidos; los `axiom` de la exportación son los de los footprints; un mutante lo rechaza todo núcleo que acepte | ~~que un núcleo independiente compruebe el modelo~~ ✅ ADR‑228: los cuatro lo comprueban |
| **V18** | 🆕 `bash scripts/thaws-fol.bash` (en la CI, «Los thaws de FOL, autorizados»; T14, ADR‑234) | que cada THAW de FOL —un commit que saca entradas de su `frozen_files.txt`, en toda su historia— se apoya en un ADR de RPP que existe y recoge una decisión del propietario: el que cita su mensaje («ADR‑NNN de RPP», lo que exigen desde ADR‑234 `.githooks/commit-msg` y `check-congelados.bash` de FOL) o, para los de antes de esa regla, el de `doc/control/thaws-fol.tsv`, que no crece; que el alcance que declara esa tabla (prosa o código) es el que vuelve a medir `scripts/prosa.py`; y que `git-lock.bash`, `.githooks/pre-commit` y `.githooks/commit-msg` son los mismos en RPP y en FOL | la VOLUNTAD del propietario: sólo que esté ESCRITA —el ADR existe y dice «propietario» (o «usuario»)—, no que ese ADR autorice ESE thaw |
| **V19** | 🆕 `bash check-choice.bash` (en la CI, T53, ADR‑193) | la CONSTRUCTIVIDAD de toda constante de RPP, FOL y TheoryFramework, sin las generadas: las que llevan `Classical.choice` en su cierre, las noncomputable y las que nombran String, contra `doc/control/choice.tsv`, en los dos sentidos; tres constantes de calibración tienen que salir con su marca | que el `Classical.choice` de una constante sea ESENCIAL (eso lo decide un ADR); ni los otros axiomas de Lean, que en los titulares mira V3 |
| **V20** | 🆕 `scripts/presupuesto-ci.bash` (en la CI, T41, ADR‑202: es P‑3) | el tiempo de reloj y la memoria residente máxima de `lake build` (RPP) y de leanchecker, medidos con GNU time, contra `doc/control/presupuesto-ci.tsv`: por encima, rojo | que el presupuesto sea el justo (se sube con un ADR que diga por qué); ni el tiempo de los demás pasos, que sólo acota el tope de cada job |
| **V21** | 🆕 `python3 gen-dependencies.py --check` (en la CI de RPP y en la de FOL, «DEPENDENCIES.md al día»; T30, ADR‑238) | que `DEPENDENCIES.md` es exactamente lo que se genera de las líneas `import` (módulos, aristas, niveles, grafo y barriles), salvo su marca; visto fallar con un `import` de más, un módulo nuevo, uno borrado y una cifra retocada | que el grafo sea BUENO (sólo que está al día); ni qué usa cada módulo de lo que importa |
| **V22** | 🆕 «El libro frente al código» (en la CI, en cada run; T49, ADR‑242) | el INFORME de `simbolos.py` y de `extraer.py` (cuántos `\ident{}`/`\modulo{}` sin respaldo y cuántos fragmentos rotos), al resumen del run | nada: **no bloquea** (`continue-on-error`); el libro está en espera, y lo que dice va a `doc/FEEDBACK-PARA-EL-LIBRO.md` |
| **V23** | 🆕 `bash check-indice.bash` (en la CI de RPP; el de FOL, en la suya; L5‑11 y B‑5, ADR‑254) | que `doc/indice.tsv` (y `../FOL/doc/indice.tsv`) es exactamente el ÍNDICE que se genera del entorno de Lean —cada constante declarada, sin las que genera Lean, con su clase, su módulo y su enunciado— y que `doc/control/fol-sin-uso.tsv` es exactamente lo que ninguna constante de RPP, FOL o TheoryFramework nombra de FOL, con su etiqueta; con calibración (seis constantes de prueba), vista fallar con tres mutantes | que el índice se CONSULTE (eso lo pide AI‑GUIDE §16c); ni que lo que nadie usa sobre: no mira los sondeos ni el libro, y simp puede usar un lema sin nombrarlo |

---

## 2 · La regla que estructura el trabajo: **el sondeo previo**

> ⭐ **Antes de tocar producción en un frente no trivial, se abre un `sondeos/*.lean` que conteste
> la pregunta que decide el diseño — y se compila.**

No es burocracia: está **medido** que paga. Tres casos, los tres del historial:

* `NegVerifierModE.lean` (archivado, etiqueta archivo/sondeos-2026-10) — el plan daba al módulo E riesgo **ALTO** y 300‑500 líneas; el sondeo midió
  que salía en **diez**, y que el riesgo estaba **en otro sitio** (C y D).
* `MedirF_Censo.lean` (archivado) — midió el censo de los 21 tags y **cazó un docstring falso de producción**.
* `CanonNeRefuta.lean` (archivado) — **refutó** un paso del plan (`canon_ne`, descartado) antes de que costara un frente.

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
> (como Probe/Fuerza.lean, fuera de git, → `Meta/OmegaStrength.lean`, retirado con la capa `⊢`, ADR‑115), la evidencia es el módulo y no hay nada
> que promover.

---

## 3 · Cuándo se ejecuta cada cosa

| momento | qué se ejecuta |
|---|---|
| durante el trabajo | `lake build` sobre el módulo, o `lake lean <fichero>` *(✏️ 2026‑10‑31 (T21, ADR‑235): decía `lake env lean`, que no pasa los leanOptions del lakefile —autoImplicit apagado, ADR‑128—; `lake lean` sí, ADR‑141)* |
| antes de commitear código | **V1 + V2**, y **V3** en el frente tocado |
| al commitear, si el clon los activó | los ganchos versionados *(T14, ADR‑234)*: `.githooks/pre-commit` rechaza un fichero congelado o bloqueado (y avisa, sin rechazar, de los `sorry`), y `.githooks/commit-msg`, un thaw cuyo mensaje no cite «ADR‑NNN de RPP». Los activa `bash git-lock.bash init` (core.hooksPath), una vez por clon. La CI no depende de ellos: en RPP, V18 comprueba que son los mismos que los de FOL; en FOL, `check-gancho.bash` los prueba y `check-congelados.bash` exige el ADR de cada thaw |
| antes de cerrar una pasada de documentación | **V4 en verde** (M‑6), con `[A2]`, `[B]` y `[E]` **adjudicados uno a uno** *(✏️ 2026‑10‑31 (T21, ADR‑235): los tres rompen —`[E]` desde ADR‑072, `[B]` desde ADR‑084, `[A2]` desde ADR‑169—; adjudicar es arreglar o marcar —un marcador de estado en `[B]`, uno de historia en `[A2]`—, y lo que ya estaba en su deuda —`doc/control/b-deuda.tsv`, `doc/control/a2-deuda.tsv`, E_DEUDA— puede seguir allí, pero la deuda no sube: tiene techo en la base verificada)* |
| antes de commitear el libro | **V6** + `doc/book/scripts/ambito.py` |
| en cada push a master, main o una rama ci/…, en cada PR, cada día y tras cada push al master de FOL | **V7** (el job `libro`, sólo en un push fuera de las ramas ci/… que toque `doc/book/`) |

⚠️ **Desde PowerShell**, no desde Git Bash: `lake` no está en el PATH de Bash, y sin él `check-doc-sync.bash` da
ROJO *(✏️ 2026‑10‑31 (T21, ADR‑235): decía que se saltaba la cifra de jobs avisando en una sola línea; desde el
2026‑09‑17, no poder medirla es rojo, y `[B]`, que vuelca el entorno de Lean, lo es también con --quick)*, igual que
V3, V11, V12, V14 y V19, que también lo necesitan. (V17 también lo necesita, pero fuera de la CI no corre: Windows bloquea leanexport y tres de los núcleos, y ADR‑228 los midió en WSL con los binarios Linux, sin el script.)

---

## 4 · ⛔ Lo que NINGÚN control garantiza — y es la parte útil

Sale de `doc/AUDITORIA-2026-09-11.md` §4. **Escribirlo es la única defensa que hay contra ello.**

| nadie comprueba | cómo se manifestó | mitigación |
|---|---|---|
| que **las hipótesis de un teorema cabecera sean descargables** | **F‑1**: `goedel_second'` (retirado) anunciado como Gödel II durante meses, con una hipótesis que ninguna pieza podía dar | ⬜ no mecanizable. **La pregunta**: *por cada teorema cabecera, ¿quién descarga cada hipótesis, y con qué?* |
| que el **cálculo del enunciado** sea el que el resultado necesita | **F‑1**: `⊢` resultó ser **sintácticamente completo** (`Meta/OmegaStrength.lean`, retirado con la capa ⊢) ⇒ no puede ser sujeto de incompletitud | ⬜ ninguna. Se decide al **enunciar** |
| que la **frase** de un banner siga siendo cierta | **F‑2**: seis documentos con el mismo titular falso **y las cifras al día** | 🔶 `[E]` mira la **fecha**, no la frase *(✏️ 2026‑10‑31 (T21, ADR‑235): y desde ADR‑169, `[I]` da rojo si un documento autoritativo o un .lean de la librería niega, con unas frases concretas, un teorema vivo: ⊬¬G (`goedel_I_neg`), `rosser` o `lob`; las demás frases no las mira nadie)* |
| que el **README** describa el proyecto que existe | **F‑3**, meses | ⬜ ninguna |
| que un **`sorry` de andamiaje** no falsee una medición | un `sorry` en el `simp set` **fabrica** el verde | 🔶 en lo versionado, sí: V2 da rojo con un `sorry` en `sondeos/` y V14 con uno en un sondeo de control, así que la evidencia de un ADR (M‑9) no puede llevarlo; en Probe/ y en el trabajo sin commitear, nada *(✏️ 2026‑10‑31 (T21, ADR‑235): decía «⬜ ninguna»; V2 bloquea desde ADR‑116)*. **Regla**: un `sorry` pospone una rama, nunca completa un `simp set` |
| que un **postulado** no esconda un **círculo** | `ax21` ⇄ `ax_mod2_alternation` (retirado), invisible mientras uno fue `axiom` | ⬜ ninguna. **Regla**: cada axioma retirado **audita** lo que se apoyaba en él |
| ⭐ que **el control mismo** no esté roto por un artefacto de la cadena de herramientas | **2026‑09‑11**: `check-doc-sync.bash` llevaba un **byte 0x01** donde iba la retro‑referencia de `sed`, y su patrón sólo cubría una de las **dos** salidas de `check-sorry.bash` ⇒ **la cifra de `sorry` no se midió nunca**: se comparaba contra una constante. ⚠️⚠️ **El byte se reprodujo solo al arreglarlo** ⇒ no era una errata, es lo que produce escribir esa secuencia a través de la cadena de herramientas | 🔶 **Regla nueva**: en un control, **ninguna retro‑referencia** — extraer con `grep -oE` *(✏️ 2026‑10‑31 (T21, ADR‑235): ningún control la vigila, y la incumplen líneas de controles de la CI —`check-footprints.bash`, `check-doc-sync.bash`, `check-estratos.bash`, `check-warnings.bash`, `scripts/leanchecker-cobertura.bash` y `scripts/lineWFT_generar.py` (dos sustituciones de re.sub, en el paso de V15)— y de las dos herramientas de V16, `update-toolchain.bash` y `toolchain.yml`; `scripts/pruebas/scan_mangle.py` busca, a mano, los bytes de control que deja un escape comido)*. Y **probar el control con el fallo puesto**: se verificó metiendo un `sorry` real y comprobando que `[A]` ROMPE *(✏️ 2026‑10‑31 (T21, ADR‑235): y, a mano, los mutantes de `scripts/pruebas/`: de `[A]`, `[A2]` e `[I]`, del trinquete de `[B]`, de `[E]` y `[C]`, y del censo por entorno)* |

---

## 5 · Lo que falta por montar

| | qué | estado |
|---|---|---|
| **P‑1** | `verificar_pdf.py` en CI | 🏁 **HECHO — y RE‑HECHO el mismo día**, porque la primera versión **no podía ejecutarse nunca**. Job **`libro`** (no `libro-pdf`: el nombre estaba mal aquí), con TeX Live y sólo cuando cambia `doc/book/`. ⛔⛔ **Medido el 2026‑09‑11**: el checkout era *shallow* ⇒ `github.event.before` no existía como objeto ⇒ el `git diff` de la puerta abortaba, su stderr iba a /dev/null y la puerta daba **siempre `run=false`**, con el job **en verde** y **cero controles ejecutados**. Corregido con `fetch-depth: 0`, una puerta que **falla hacia EJECUTAR** ante la duda, los checkouts hermanos de `FOL` y Peano que `simbolos.py` necesita para su cierre de imports, `poppler-utils` para §2.1 y `PYTHONIOENCODING`. ⚠️ **Sigue sin verificarse en el runner** hasta el primer push que toque el libro *(✏️ 2026‑10‑31 (T21, ADR‑235): fue el push de c861103 a master, el 2026‑10‑21. La puerta dio run=true y el job salió ROJO en §2.6, con 35 símbolos sin respaldo, sin llegar a §2.7, a la compilación ni a §2.1. El job no es obligatorio en la protección, y master siguió)* |
| **P‑2** | un control de **hipótesis descargadas** | 🏁 **HECHO**: **`TEOREMAS-E-HIPOTESIS.md`** — teorema → hipótesis → **quién la descarga**. ⚠️ Es **a mano**: se actualiza en el mismo commit que toca un teorema cabecera. Una fila «⬜ nadie» es información; una fila **ausente** es el fallo *(✏️ 2026‑10‑14, ADR‑135: la fila ausente de un titular de `T_UNIVERSO` la caza hoy `[T]`; uno nuevo que no se añada allí, no: ver V8)* |
| **P‑3** | medir el **tiempo** de build | ✅ desde ADR‑202 (T41; hoy V20): GNU time alrededor del build y de `leanchecker` en la CI, contra un presupuesto versionado (`doc/control/presupuesto-ci.tsv`, rojo por encima), y `timeout-minutes` en los jobs |
| **P‑4** | **¿basta `ConsistentH`?** | 🏁 **SÍ, y resuelto el mismo día**: `goedel_first_prf` y `goedel_second_prf` toman hoy `ConsistentH := ¬ Prf ⊥`, la hipótesis **mínima**. ⭐ Y el footprint cayó a **`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]`** (el último, retirado) — **un solo axioma del proyecto**: las ω‑reglas y los dos esquemas de inducción entraban **por la hipótesis vieja** · ✏️ **2026‑10‑04 (ADR‑117)**: el ancla `prf_axiomsCodeT_eq` (retirada; era un axiom) pasó después a ser la clase `[AnclaEq]` (retirada en ADR‑118; ADR‑026), que daba `Prf ⊥` (F1, ADR‑114: los dos eran vacuos); hoy es un TEOREMA (`prf_ancla`), y los dos toman sólo `ConsistentH`, con footprint `[propext, Classical.choice, Quot.sound]` *(✏️ 2026‑10‑31 (T21, ADR‑235): sin `Classical.choice` desde ADR‑189: `[propext, Quot.sound]`, igual que `prf_ancla`)*. ⚠️ Siguen siendo condicionales: la consistencia de los 142 axiomas no está probada (no hay modelo) *(✏️ 2026‑10‑14, [ADR‑134](DECISIONS.md): desde ADR‑120 lo está —`consistencia`, un modelo de los 142 y la solidez de `Prf`—, y es la de toda la teoría T_Prf)* |

---

**Véase también:** `AI-GUIDE.md` §27 (el control de sincronía; los bloques de hoy, en V4),
`doc/AUDITORIA-2026-09-11.md` (de dónde sale este documento), `sondeos/README.md`.

# Registro de afirmaciones falsas en docstrings de producción

**Abierto:** 2026-09-03 · **Mantiene:** la tarea del libro · **Corrige:** la tarea de desarrollo

## Por qué existe este fichero

El libro se escribe **leyendo el árbol que compila**, así que las cabeceras y docstrings de los
módulos de producción son **material fuente**. Y el compilador **no los verifica**: `lake build` en
verde garantiza los teoremas, no la prosa que los rodea.

Es un modo de fallo distinto del que cubre `check-doc-sync.bash`, que vigila los `.md` autoritativos
y **no mira dentro de los `.lean`**. Por eso hace falta este registro.

**Regla del libro** (`PLAN-LIBRO.md` §2.6): un docstring se puede **citar como testimonio** —lo que
el autor creía en ese momento, que a veces es justo lo interesante— pero **nunca usar como
evidencia** de lo que un módulo contiene. Toda afirmación del libro sobre qué hay en un módulo se
respalda con una **medición**: censo de `env.constants`, `#print axioms`, o `grep`.

⚠️ Corregir los docstrings **no** es competencia de esta tarea (`PLAN-LIBRO.md` §0). Aquí se
registran para que el libro no los cite, y para que la tarea de desarrollo los arregle.

---

## Casos detectados

| # | dónde | qué afirma | qué es verdad | estado |
|---|---|---|---|---|
| 1 | `Meta/CodeWitnessPrf.lean:78-82` | que el módulo aporta `DescMutua.DESCENSO_hasWit` y las secciones `S_Descenso`/`S_Paso2` | **no existe ningún `DescMutua`**; las secciones son `S_Clausura`/`S_Ens`/`S_HW` (censo de `env.constants`) | detectado |
| 2 | `Meta/CodeWitnessPrf.lean:1555` | cita `EvalSubsttc.prf_isTermCodeE1_of_In` como si estuviera en producción | el 09‑03: **no existía**, era un sondeo. ⚠️ **El 09‑04 dejó de ser falso sin que nadie tocara el docstring**: la promoción **B2** puso `prf_isTermCodeE1_of_In` en producción, en `CodeWitnessPrf.SinWTs`. El módulo que la cita **sigue sin existir** (`EvalSubsttc`), pero el hecho afirmado ya es cierto por otra vía | ⚠️ **mutado** — reescribir la cita, no borrarla |
| 3 | `Meta/LiftcCodePrf.lean` · `refl_isTermCodeE1_imp` | «EL RESULTADO CENTRAL DE ESTE MÓDULO» | **sobrevende**: toma como premisa justo lo que el descenso fabrica, luego nada aguas abajo puede usarlo; **cero usos** en B2 | detectado |
| 5 | `Minimal/Axioms.lean:908-917` | que `axiomsCodeT` es el código de **`coreAxioms`** (34) y que «se ancla por el axioma **`ax_axiomsCodeT`**» a `listFormCodeM coreAxioms` | **dos cosas falsas**: (a) `ax_axiomsCodeT` **no existe** —sólo aparece en comentarios, y `Meta/Hilbert.lean:69` dice «`ax_axiomsCodeT` eliminado»—; (b) el axioma vivo es `ax_axiomsCodeT_eq` (`:1376`) y ancla a **`axioms`** (141), no a `coreAxioms`. [ADR-015](../../DECISIONS.md) lo dice bien | ✅ **CORREGIDO en desarrollo 2026‑09‑05** — confirmadas las DOS mitades con `lake`, y medidas las listas con `#eval ·.length`: `coreAxioms` **34**, `codingAxioms` **107**, `axioms` **141** (34+107=141). El comentario reescrito dice ya el ancla real (`ax_axiomsCodeT_eq` → `axioms`) y **deja escrita la consecuencia**: la regla `thy` (`ax_lineWF_thy`, tag 15) admite las 141, no las 34. ⚠️ Sólo prosa: 0 declaraciones en el diff, 269 antes y 269 después |
| 4 | §9, marca «NO ES VACUO» | que el resultado no es vacuo | producción **ya probaba** esos enunciados por otra vía, sin descenso ninguno; lo que los controles miden es que **el descenso dispara**, que es otra cosa | corregido en desarrollo (2026-09-03) |

### Nota sobre el caso 5 — no es cosmético

Si `axiomsCodeT` codifica `axioms` (141) y no `coreAxioms` (34), entonces la regla `thy` del
verificador acepta como axioma de teoría los 141, no los 34. Eso cambia **qué significa
`provCodeC'`**, y por tanto **cuál es la sentencia G**. Es el mismo mecanismo que ADR-015 describe
para el caso contrario —añadir axiomas cambia el teorema—, y aquí lo que está desincronizado es
justo la descripción de dónde está esa frontera.

⚠️ No he podido comprobarlo en el entorno compilado (aquí no hay `lake`): lo seguro es la
**contradicción textual** entre el comentario y la declaración. Cuál de los dos refleja la intención
lo decide la tarea de desarrollo.

## Lección, y por qué es material del libro

Los cuatro son del tipo que se cita tal cual y queda mal. Y los cuatro están en **módulos del frente
vivo** — que es donde era de esperar: la cabecera se escribe cuando se planea el módulo y no se
vuelve a tocar cuando el módulo cambia de forma. Es **exactamente** el fallo que `AI-GUIDE.md` §27
describe para los documentos de estado —«se actualizan por su BANNER y no por su CUERPO»— pero una
capa más adentro, donde ningún control lo miraba.

Va al capítulo 26 («Método») como una trampa propia, y al 17 («Cómo se localiza el daño») como
recordatorio de que la única evidencia es la medición.

---

## Actualización 2026-09-04 (tarea de desarrollo)

**Un caso MUTÓ, y es material del libro por sí solo.** El #2 dejó de ser falso **sin que nadie
tocara el docstring**: la promoción B2 puso el lema en producción por otra vía. Un docstring no
sólo puede ser falso — **puede dejar de serlo solo**. Es testimonio fechado, no descripción, y eso
refuerza la regla de §2.6 en vez de debilitarla.

**Segunda tanda de auditoría, en curso.** Cinco categorías, cada una con **su propio método**
—mezclarlas es lo que deja huecos—:

| clase | qué falla | método OBLIGATORIO |
|---|---|---|
| existencia | cita un símbolo/sección que no existe, o existe en otro sitio | **censo de `env.constants`** con el barrel — **NO `grep`** |
| citas de línea | `fichero.lean:NNN` que ha derivado | mecánico: abrir el fichero por esa línea |
| footprint | «net‑0», «cero axiomas» | `#print axioms` real contra el texto |
| significado | «EL RESULTADO CENTRAL», «esto cierra X» | **censo de consumidores** + dirección de las hipótesis |
| cifras | «las ocho», listas declaradas cerradas | contar **la familia entera** |

Estado: **37 hallazgos en bruto** (21 falsas, 6 engañosas, 10 imprecisas), pendientes de pasar por
verificación adversarial — la cifra que valdrá es la que sobreviva. Trazado en la **rama G** de
`NEXT-STEPS.md`.

**Dato duro para el capítulo**: hay **72 números de línea en 60 sitios de cita** en los seis módulos
del frente. Son la parte más frágil del árbol: derivan en cuanto alguien inserta líneas más arriba
y **nadie se entera, porque el compilador no las mira**. Pregunta abierta del proyecto: ¿merece la
pena mantenerlos?

### Un caso de la propia comprobación, que ilustra el capítulo mejor que los otros cuatro

Verificando este registro se afirmó primero que **no existía** — por un chequeo de rutas que
resolvía los nombres desde la raíz del repo en vez de desde `doc/book/`. Existía. **Una medición
mal apuntada es indistinguible de una ausencia** hasta que se mira dos veces, y produce
exactamente el mismo error que no medir: una afirmación falsa dicha con confianza. La regla de
§2.6 —«respaldar con una medición»— es necesaria pero **no suficiente**: la medición tiene que
apuntar al sitio correcto, y eso también hay que comprobarlo.

---

## Cierre del caso #5 (2026‑09‑05)

Lo que el registro no podía comprobar —«aquí no hay `lake`»— lo cerró la tarea de desarrollo:

* **`ax_axiomsCodeT` no existe.** Cero declaraciones en el árbol; sus cinco menciones son
  comentarios, y `Meta/Hilbert.lean` lo da por **eliminado** explícitamente.
* **El axioma vivo ancla a `axioms`**, no a `coreAxioms`:
  `axiom ax_axiomsCodeT_eq : axioms ⊢ (axiomsCodeT =eq listFormCodeM axioms)`.
* **Y tu inferencia era correcta**: la regla `thy` del verificador (`ax_lineWF_thy`, tag 15) dice
  `lineWF ⇔ (lenc = 2) ∧ In (carc ·) axiomsCodeT`, o sea que admite **las 141**.

**Pero el diagnóstico final es más tranquilo que el temido**: no es un desajuste vivo del
sistema, sino **prosa fósil de un diseño anterior**. La nota de `Hilbert.lean` —«ya no hay ancla
gigante, `ax_axiomsCodeT` eliminado»— dice que el cambio fue **deliberado**: se pasó de anclar a
`coreAxioms` a anclar a `axioms`, y el párrafo se quedó describiendo el diseño viejo. El sistema
es coherente consigo mismo; lo que mentía era el párrafo que lo describe.

### Y por eso el caso #5 es el mejor del registro para el capítulo

Los otros cuatro son símbolos que no existen o énfasis mal puesto. **El #5 es un comentario que
fue verdad**, y dejó de serlo cuando el diseño cambió debajo — igual que el #2, pero al revés:
aquel se volvió verdadero solo, y éste se volvió falso solo. **Los dos sin que nadie los tocara.**

Es la prueba más limpia de la regla de §2.6: un docstring no describe un módulo, **da fe de lo
que su autor creía en una fecha**. Y aquí lo que estaba en juego no era una cita: era **dónde
está la frontera de la teoría**, que es lo que decide qué significa `provCodeC'` y por tanto
**cuál es la sentencia G**.

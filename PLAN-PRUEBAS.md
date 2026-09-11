# PLAN DE PRUEBAS — ROBINSON_PlusPlus

> ## ESTADO REAL — 2026‑09‑11 · **abierto por la auditoría** (`doc/AUDITORIA-2026-09-11.md` F‑4)
>
> **Build 145 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **131 módulos activos** · **5 `axiom` de Lean · 141 axiomas objeto** en `axioms`.

**Creado:** 2026‑09‑11 · **Autor:** Julián Calderón Almendros

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
| **V1** | `lake build` | **todo el árbol activo typechequea** en el kernel de Lean. Es la única prueba *fuerte* que hay: una demostración que compila **es** una demostración | nada sobre si el **enunciado** es el que se quería |
| **V2** | `bash check-sorry.bash` | **cero `sorry`/`admit`/`native_decide`** reales, despojando comentarios y literales | que no haya `axiom`s haciendo el papel de `sorry` — eso lo mira V3 |
| **V3** | `#print axioms` por frente | el **footprint exacto**: qué postulados sostienen cada teorema | que el postulado sea *razonable*. Eso lo decide un ADR |
| **V4** | `bash check-doc-sync.bash` | `[A]` cifras de cabecera · `[A2]` cifras del cuerpo (aviso) · `[B]` símbolos muertos (aviso) · `[C]` proyección · `[D]` marcas de tiempo · `[E]` frescura del titular (aviso) | **la verdad de las frases**. Ver §4 |
| **V5** | `sondeos/*.lean` | resultados **compilados** de preguntas cerradas antes de tocar producción | que la pregunta fuese la correcta |
| **V6** | `doc/book/scripts/*.py` | que todo `\ident{}` del libro **exista** en el repo, que el vocabulario se introduzca antes de usarse, y que el código **impreso** sea el del repo | que lo impreso sea *verdad* — sólo que **cite bien** |
| **V7** | CI (`.github/workflows/build.yml`) | **job `build`**: V1, V2 y V4 en cada push. **job `libro`**: V6 **entero** (símbolos, términos y el PDF) **sólo cuando el push toca `doc/book/`** — el libro y el código son **dos tareas con commits separados** (PLAN‑LIBRO §0) | ⚠️ que un cambio en `.lean` rompa una cita del libro **no se ve hasta el siguiente push del libro**. Es el precio de las dos tareas, y está medido: pasó el 2026‑09‑11 al retirar `goedel_second'` |
| **V8** | 🆕 **`TEOREMAS-E-HIPOTESIS.md`** | por cada teorema cabecera, **quién descarga cada hipótesis**. Es la única defensa contra **F‑1** | es **a mano**: ningún script lo comprueba |

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
| **`Probe/`** | **borrador**: medir si algo casa, tantear una táctica, leer un error | ❌ **no** (`.gitignore:30`) — es ruido, y correctamente |
| **`sondeos/`** | **resultado**: la pregunta que se contestó, con su respuesta compilada | ✅ **sí**, con su fila en `sondeos/README.md` |

> ⛔ **MANDATORY (M‑9)**: **un `Probe/` que decide un ADR se promueve a `sondeos/` antes de cerrar
> ese ADR**, o la decisión queda sin evidencia versionada. Si el probe pasó **a producción**
> (como `Probe/Fuerza.lean` → `Meta/OmegaStrength.lean`), la evidencia es el módulo y no hay nada
> que promover.

---

## 3 · Cuándo se ejecuta cada cosa

| momento | qué se ejecuta |
|---|---|
| durante el trabajo | `lake build` sobre el módulo (`lake env lean <fichero>`) |
| antes de commitear código | **V1 + V2**, y **V3** en el frente tocado |
| antes de cerrar una pasada de documentación | **V4 en verde** (M‑6), con `[A2]`, `[B]` y `[E]` **adjudicados uno a uno** |
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

---

## 5 · Lo que falta por montar

| | qué | estado |
|---|---|---|
| **P‑1** | `verificar_pdf.py` en CI | 🏁 **HECHO** (2026‑09‑11): job `libro-pdf`, con TeX Live y **sólo cuando cambia `doc/book/`** — instalar LaTeX cuesta minutos y no tiene sentido en cada push. ⚠️ **Sin verificar hasta el primer push que toque el libro** |
| **P‑2** | un control de **hipótesis descargadas** | 🏁 **HECHO**: **`TEOREMAS-E-HIPOTESIS.md`** — teorema → hipótesis → **quién la descarga**. ⚠️ Es **a mano**: se actualiza en el mismo commit que toca un teorema cabecera. Una fila «⬜ nadie» es información; una fila **ausente** es el fallo |
| **P‑3** | medir el **tiempo** de build | ⬜ hoy no se vigila; un frente puede degradarlo sin que nadie lo vea |
| **P‑4** | **¿basta `ConsistentH`?** | 🏁 **SÍ, y resuelto el mismo día**: `goedel_first_prf` y `goedel_second_prf` toman hoy `ConsistentH := ¬ Prf ⊥`, la hipótesis **mínima**. ⭐ Y el footprint cayó a **`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]`** — **un solo axioma del proyecto**: las ω‑reglas y los dos esquemas de inducción entraban **por la hipótesis vieja** |

---

**Véase también:** `AI-GUIDE.md` §27 (el control de sincronía y sus seis bloques),
`doc/AUDITORIA-2026-09-11.md` (de dónde sale este documento), `sondeos/README.md`.

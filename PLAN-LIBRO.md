# PLAN — Libro en LaTeX: *Incompletitud, formalizada*

**Creado:** 2026‑08‑19 · **Revisado:** 2026‑08‑22 23:55 · **Estado:** plan aprobado, **fase 0 sin
arrancar** · **Autor:** Julián Calderón Almendros

---

## 1 · Contexto y propósito

El proyecto `ROBINSON_PlusPlus` lleva **83 módulos Lean 4 activos** (+21 en cuarentena, +10 sondeos)
formalizando los teoremas de incompletitud de Gödel sobre un kernel FOL⁼ propio. Todo el
conocimiento acumulado vive hoy en **24 ficheros `.md`** que son **notas de trabajo**, no
exposición: `NEXT-STEPS.md` es un puntero de reanudación, `CHANGELOG.md` un diario, `DECISIONS.md`
un registro de ADRs.

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

---

## 2 · Principio editorial: sólo se publica lo que compila

**Regla dura:** todo bloque de código Lean del libro se **extrae del repo**, nunca se escribe a
mano en el `.tex`. Si un módulo no compila, su sección no entra.

Motivo: el proyecto acaba de descubrir que una inconsistencia latente sobrevivió meses de trabajo.
Un libro con código copiado a mano acumularía el mismo tipo de deriva silenciosa.

Mecanismo: cada fragmento se referencia por **fichero + nombre de declaración**, y un script de
extracción los vuelca a `.tex` antes de compilar. Nada de copiar‑pegar.

---

## 3 · Estructura propuesta

### Parte I — El terreno
1. **¿Qué dice Gödel, y qué hay que construir para decirlo?** — el enunciado informal, y por qué
   formalizarlo obliga a construir tres cosas: un lenguaje, una teoría, y una aritmetización.
2. **El kernel FOL⁼** — `Term`, `Formula`, De Bruijn, sustitución y *lifting*.
   *Material:* `doc/REFERENCE-Kernel.md`.
   *Lección:* por qué los índices de De Bruijn, y el precio que se paga por ellos.
3. **La teoría objeto: Robinson Q++** — los axiomas, y la frontera `Minimal` / `Full`.
   *Material:* `MINIMAL-AXIOMS.md`, `AXIOMS.md`.

### Parte II — Aritmetización
4. **Codificar sintaxis como números** — emparejamiento de Cantor, `cons`, códigos de términos y
   fórmulas. *Material:* `doc/REFERENCE-Godelization.md`, `TuplasFuncionesYListas.md`.
5. **El verificador de pruebas** — `lineWF`, `chainOk`, `runFn`, los 21 tags.
   *Material:* `doc/REFERENCE-Incompleteness.md`, `GODEL-D-ARITHMETIZATION.md`.
6. **Representabilidad y D1** — de `Prf φ` a `Prov(⌜φ⌝)`.

### Parte III — Los teoremas
7. **El lema diagonal y Gödel I** — punto fijo real, **`godelCN_fixedpoint`** → **`goedel_first_numeral`**.
   ⚠️ El código va escrito como **numeral** (capítulo 14 explica por qué); y el capítulo debe decir
   que sólo se tiene **`⊬G`**: la indecidibilidad (`⊬¬G`) sigue **abierta** — ver capítulo 9bis.
8. **Las condiciones de derivabilidad** — D1, D2 y el muro de D3.
9. **La inducción como precio** — por qué Q sola no basta y `Full` es imprescindible.
   *Material:* `AXIOMS.md` §1.1 (ya escrito).

9bis. **La mitad que falta: `⊬¬G`** ← **añadido 2026‑08‑22**. Casi todos los libros enuncian Gödel I
   como *«G es indecidible»* y despachan la segunda mitad en un párrafo. En la formalización **no es
   un párrafo**: `⊬G` sale de la consistencia, pero `⊬¬G` necesita **reflexión** — de
   `Prov(⌜φ⌝)` volver a `φ` —, y eso exige un **verificador negativo** que no se obtiene gratis.
   El capítulo cuenta: (a) que el proyecto llegó a «tenerlo» y era **falso** (`provFormula_repr`,
   retirado en F7a); (b) que el obstáculo de fondo es el **intuicionismo** del kernel FOL, no la
   ω‑consistencia; (c) que **Rosser sería peor**, no mejor, en este marco.
   *Material:* `PLAN-NEGVERIFIER.md`, memoria `project-godel-first-complete`, `GODEL-STATUS.md`.

### Parte IV — Lo que no sale en los libros ← **el núcleo original**

> **Reescrita el 2026‑08‑19.** La sesión de ese día produjo el material más valioso del libro: una
> inconsistencia real, su diagnóstico, **cuatro reparaciones que no funcionan**, la que sí, y el
> coste. Nada de esto aparece en los manuales, porque los manuales presentan el resultado ya limpio.

10. **El muro de `substfc`** — cuando una función objeto no se puede evaluar sobre un código
    abstracto. *Material:* memoria `project-substfc-wall`.

11. **Una inconsistencia latente.** La derivación en cinco pasos; `cons 0 nil = 2 = σσ0`; el error de
    categoría (`tcFn` es una operación sobre **sintaxis** declarada como función **objeto**, que sólo
    puede depender de **valores**). **La lección central:** la inconsistencia era **latente desde el
    principio**, y la hizo visible un teorema *net‑0* — `prf_cantor_mono`, que no añadía nada. El
    peligro no estaba en lo que se añadía, sino en lo que ya estaba.
    *Material:* memoria `project-inconsistencia-tcfn-cons`.

12. **Cómo se localiza el daño** — capítulo **metodológico**, y quizá el más útil para el lector.
    Por qué fallan las dos técnicas obvias: la alcanzabilidad por `import` da **falsos negativos**
    (me hizo afirmar en falso que Gödel I estaba limpio), y un crawler de dependencias **no funciona
    en Lean 4**, porque `value?` devuelve `NONE` para teoremas importados y sólo recorre tipos.
    La técnica que sí vale: **convertir el puente sospechoso en `axiom` de Lean y leer
    `#print axioms`**, con un **control positivo** que debe salir contaminado.
    Resultado: el daño entra a Gödel I **por un solo sitio**, el lema diagonal.
    *Material:* memoria `feedback-auditoria-footprint`, `sondeos/README.md`.

13. **Cuatro reparaciones que no funcionan** — el capítulo de **valor negativo**, el que ahorra meses:
    * **Partir el símbolo en dos** (`tcNum`/`tcCode`): insuficiente, porque las **hojas** de un
      árbol de código son numerales, luego `tcCode` necesitaría las dos recursiones y reproduce el
      mismo ⊥.
    * **Quitar el axioma sin más**: **decapita la diagonalización**. El «código del código» no es un
      accidente de la implementación — es lo que Gödel **exige** para construir `G = β(⌈β⌉)`.
    * **Relativizar por axiomas** en el lenguaje mono‑sortido: imposible; la tricotomía y el orden
      prueban `∀x. x=0 ∨ ∃k. x=σk` **sin inducción**, así que no hay sitio para un `cons` que no sea
      ni cero ni sucesor.
    * **Un paquete de buena‑formación** (`isFormCode`): no repara `tc`. **La razón es bonita y
      general**: `substfc` pide un reconocedor **extensional** (un subconjunto de ℕ); `tc` pide una
      distinción **intensional** (qué sintaxis escribimos para el número 9). Un predicado *es* un
      subconjunto: no separa lo que no está separado en los valores.

14. **La reparación: códigos como numerales.** Por qué el numeral **es** canónico y el árbol no.
    La aritmética **sin división** (números triangulares) que hace exacta la mitad del polinomio de
    Cantor. Y una lección de **método de ingeniería**: se **pilotó antes de ejecutar**, asumiendo el
    resultado costoso como axioma de Lean para comprobar que la cadena cerraba — evitando invertir
    ~20 lemas sin saber dónde enchufarlos. *Material:* `sondeos/PilotoDiagonal.lean`,
    `sondeos/DescargaHFN.lean`, memoria `project-reparacion-via-numeral`.

15. **Lo que se pierde, y por qué «perder» es la palabra equivocada.** 31 módulos a cuarentena: los
    14 tags, `hI_dot`, el chasis. Eran teoremas **correctos** sobre una teoría que probaba ⊥, o sea
    **vacuos**. El capítulo trata la pregunta incómoda: *¿qué significa haber demostrado algo sobre
    una teoría inconsistente?* Y cómo se recupera: **keystone** y **niveles** (argumentos concretos
    vs abstractos). *Material:* `cuarentena/README.md`, `PLAN-FRENTE-A.md`.

16. **La reconstrucción: internalizar en vez de reescribir** ← **añadido 2026‑08‑22**.
    El capítulo que cierra el arco de la Parte IV, y el que tiene **moraleja positiva**. Roto el
    puente `prf_tc_cons'`, había dos vías: reescribir los 21 módulos caídos uno a uno, o **reconstruir
    el puente dentro de `Prov`** con un solo teorema. Se eligió la segunda ([ADR‑014](DECISIONS.md)).
    * **Por qué se pudo:** `cons` **no tiene ecuaciones recursivas propias** — `ax_L0_cons_def` lo
      define por `div2 (cantor_poly h (σt))`, o sea `+`, `·` y `div2`, ya internalizados. Lo que
      parecía un quinto peldaño de inducción resultó ser **ensamblaje**. *Lección general: antes de
      inducir, mirar si el símbolo está definido o es primitivo.*
    * **Las dos técnicas que lo abarataron**, ambas exportables a cualquier formalización con una
      capa de códigos:
      1. **Dotar un teorema OBJETO es gratis.** `tcFn` es un símbolo de función ⇒ es congruente ⇒
         cualquier `⊢ a = b` sube a `⊢ ȧ = ḃ` **a nivel de código, sin entrar en `Prov`**. La mitad
         del trabajo que parecía «interno» no lo era.
      2. **La sustitución cubre todas las ocurrencias del hueco.** El polinomio de Cantor menciona
         `x+y` dos veces; con el contexto `Ac := C[v₀]` un **único** paso de Leibniz cierra las dos.
         Cinco pasos en vez de quince.
    * **Y el método:** el rédito se **verificó antes de celebrarlo** — `sondeos/CarcPayoff.lean`
      reconstruye `pcc_eval_carc` con el mismo enunciado y footprint. «Debería desbloquear» no es un
      resultado; «desbloquea, aquí está compilado» sí.
    *Material:* `Meta/DotConsPrf.lean`, `sondeos/CarcPayoff.lean`,
    `doc/REFERENCE-Incompleteness.md` §3.25, memoria `project-escalera-sigma1`.

17. **Método** — qué funcionó al formalizar: trocear y compilar entre pasos; **probar primero lo más
    arriesgado** (la fase A de `pcc_dot_cons` preguntaba si `substCodeF` computa por `rfl`: si no,
    todo lo demás sobraba); verificación adversarial; `#print axioms` como auditoría; y las
    **trampas caras**, todas reales: no lanzar sondeos contra un árbol que cambia; `lake build` puede
    dar **verde sin construir lo que crees** (la `lean_lib` sólo construye lo alcanzable desde el
    módulo raíz — señal de alarma: el número de jobs no cambia); filtrar **comentarios de bloque** al
    buscar usos, o una cuarentena de 31 se infla a 72; y el fallo de documentación que descubrió la
    auditoría del 2026‑08‑22: **los documentos de estado se actualizan por su banner y no por su
    cuerpo** — un ADR llevaba un mes diciendo «no implementado» sobre algo hecho.
    *Material:* memorias `feedback-*`.

### Apéndices
- A. Inventario de axiomas con su justificación (`AXIOMS.md`).
- B. Mapa de módulos (`REFERENCE.md`).
- C. Trampas de Lean 4 encontradas (memorias `feedback-lean-*`).

---

## 4 · Infraestructura

**No existe nada de LaTeX en el repo** (verificado: sin `.tex`, `.bib`, `.sty`). Se crea de cero:

```
libro/
  libro.tex            # documento maestro
  preamble.tex         # paquetes, entornos, estilo
  capitulos/*.tex      # un fichero por capítulo
  extraido/*.tex       # GENERADO — fragmentos Lean, nunca editar a mano
  bib/libro.bib        # Gödel, Rosser, Hilbert-Bernays, Paulson, O'Connor…
  scripts/extraer.py   # extrae declaraciones Lean del repo a extraido/
  Makefile             # extraer + latexmk
```

**Decisiones técnicas:**
- `\lstset` o `minted` para Lean 4 (evaluar cuál da mejor resaltado de Unicode: el proyecto usa
  `σ`, `⟹`, `⊢`, `≐` intensivamente).
- Entornos propios: `\begin{lean}` (código), `\begin{matematica}` (enunciado formal),
  `\begin{leccion}` (nota pedagógica), `\begin{muro}` (obstrucción encontrada).
- Idioma: **español**, coherente con toda la documentación del proyecto.
- `libro/` queda **fuera** del build de `lake` — no interfiere con la compilación Lean.

---

## 5 · Orden de ejecución

| fase | entregable | estado | por qué en este orden |
|---|---|---|---|
| **0** | esqueleto `libro/` + `Makefile` + un capítulo piloto | ⏳ **sin arrancar** | validar la cadena LaTeX **y** el extractor antes de escribir |
| **1** | `scripts/extraer.py` + capítulo 2 (kernel) | ⏳ | el kernel es estable y no está afectado por la inconsistencia |
| **2** | Parte IV, capítulos 11–13 y 16 | ⏳ | **escribir ahora, mientras el episodio está fresco** — es el material más valioso y el más fácil de perder |
| **3** | Partes I–III (+ 9bis) | ⏳ | exposición sistemática; se apoya en `doc/REFERENCE-*.md` ya escritos |
| **4** | Apéndices y bibliografía | ⏳ | mecánico |

⚠️ **La fase 2 va deliberadamente antes que la I–III.** El capítulo de la inconsistencia se escribe
mejor ahora que dentro de seis meses.

✅ **La Parte IV ya no depende de nada**: el arco completo — inconsistencia → diagnóstico → cuatro
reparaciones fallidas → la que funciona → la cuarentena → **la reconstrucción** (cap. 16) — está
cerrado y compilando. Era la única razón por la que la fase 2 podía quedarse a medias.

**Materia prima ya disponible, verificada y citable** (nada de esto hay que reconstruirlo):
`sondeos/` (10 experimentos compilados, con su `README.md`), `cuarentena/README.md` (grafo de
recuperación), `DECISIONS.md` ADR‑012/013/014, `doc/REFERENCE-Incompleteness.md` §3.24–§3.27, y las
memorias `project-inconsistencia-tcfn-cons`, `project-reparacion-via-numeral`,
`project-escalera-sigma1`, `feedback-auditoria-footprint`.

---

## 6 · Relación con la reparación en curso

El libro **no bloquea ni es bloqueado** por la reparación de la inconsistencia:

- Partes I–III describen lo que **ya está probado y compila** (kernel, Q++, verificador, Gödel I
  vía `goedel_first_numeral`).
- La Parte IV documenta el problema, su reparación (capítulos 11–15) **y la reconstrucción**
  (capítulo 16). El arco está **cerrado narrativamente**: se puede escribir entero hoy.

### ⚠️ Aviso editorial obligatorio — **reformulado 2026‑08‑22**

La versión anterior de este aviso decía *«mientras la reparación no esté hecha, el libro debe decir
que la teoría objeto es inconsistente»*. **La reparación está hecha** (2026‑08‑18/19), así que el
aviso cambia — y el nuevo es más delicado, no menos:

> El libro **debe decir explícitamente** que lo que se retiró fue la inconsistencia **conocida y
> localizada** (`ax_tc_cons`), y que **eso no es una prueba de consistencia** de Q++ extendido.
> Gödel I (`goedel_first_numeral`) es un teorema real sobre la teoría **reparada**; presentarlo como
> «Gödel I sobre una teoría consistente» sería engañoso, igual que lo habría sido publicarlo antes
> sin advertir del ⊥.

Y un segundo aviso, propio de la Parte III:

> Gödel I está **a medias**: sólo `⊬G`. La indecidibilidad (`⊬¬G`) **no está cerrada** en la cadena
> real — ver capítulo 9bis. El libro no puede enunciar «G es indecidible» sin esa salvedad.

---

## 7 · Verificación

- `make -C libro` compila el PDF sin errores ni referencias rotas.
- El extractor falla ruidosamente si una declaración citada **no existe** en el repo — así el libro
  no puede desincronizarse en silencio del código.
- `lake build` sigue verde: `libro/` no toca la compilación Lean.

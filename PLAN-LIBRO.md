# PLAN — Libro en LaTeX: *Incompletitud, formalizada*

**Creado:** 2026‑07‑27 · **Estado:** plan aprobado, sin ejecutar · **Autor:** Julián Calderón Almendros

---

## 1 · Contexto y propósito

El proyecto `ROBINSON_PlusPlus` lleva ~99 módulos Lean 4 formalizando los teoremas de
incompletitud de Gödel sobre un kernel FOL⁼ propio. Todo el conocimiento acumulado vive hoy en
**26 ficheros `.md`** que son **notas de trabajo**, no exposición: `NEXT-STEPS.md` es un puntero de
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
7. **El lema diagonal y Gödel I** — punto fijo real, `goedel_first_real'`.
8. **Las condiciones de derivabilidad** — D1, D2 y el muro de D3.
9. **La inducción como precio** — por qué Q sola no basta y `Full` es imprescindible.
   *Material:* `AXIOMS.md` §1.1 (ya escrito).

### Parte IV — Lo que no sale en los libros ← **el núcleo original**

> **Reescrita el 2026‑07‑27.** La sesión de ese día produjo el material más valioso del libro: una
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

16. **Método** — qué funcionó al formalizar: trocear y compilar entre pasos; verificación
    adversarial; `#print axioms` como auditoría; y las **trampas caras**, todas reales:
    no lanzar sondeos contra un árbol que cambia; `lake build` puede dar **verde sin construir lo
    que crees** (la `lean_lib` sólo construye lo alcanzable desde el módulo raíz — señal de alarma:
    el número de jobs no cambia); y filtrar **comentarios de bloque** al buscar usos, o una
    cuarentena de 31 se infla a 72. *Material:* memorias `feedback-*`.

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

| fase | entregable | por qué en este orden |
|---|---|---|
| **0** | esqueleto `libro/` + `Makefile` + un capítulo piloto | validar la cadena LaTeX **y** el extractor antes de escribir |
| **1** | `scripts/extraer.py` + capítulo 2 (kernel) | el kernel es estable y no está afectado por la inconsistencia |
| **2** | Parte IV, capítulos 11 y 12 | **escribir ahora, mientras el episodio está fresco** — es el material más valioso y el más fácil de perder |
| **3** | Partes I–III | exposición sistemática; se apoya en `doc/REFERENCE-*.md` ya escritos |
| **4** | Apéndices y bibliografía | mecánico |

⚠️ **La fase 2 va deliberadamente antes que la I–III.** El capítulo de la inconsistencia se escribe
mejor ahora que dentro de seis meses, y no depende de que la reparación esté terminada.

---

## 6 · Relación con la reparación en curso

El libro **no bloquea ni es bloqueado** por la reparación de la inconsistencia:

- Partes I–III describen lo que **ya está probado y compila** (kernel, Q++, verificador, Gödel I).
- La Parte IV documenta el problema **y** su reparación; el capítulo 12 se completa cuando la vía
  de tipos esté implementada.
- ⚠️ **Aviso editorial obligatorio:** mientras la reparación no esté hecha, el libro debe decir
  explícitamente que la teoría objeto **en su forma actual es inconsistente**, y que los resultados
  de la Parte III son formalmente correctos pero **vacuos** sobre ella. Publicar Gödel I sin esa
  advertencia sería engañoso.

---

## 7 · Verificación

- `make -C libro` compila el PDF sin errores ni referencias rotas.
- El extractor falla ruidosamente si una declaración citada **no existe** en el repo — así el libro
  no puede desincronizarse en silencio del código.
- `lake build` sigue verde: `libro/` no toca la compilación Lean.

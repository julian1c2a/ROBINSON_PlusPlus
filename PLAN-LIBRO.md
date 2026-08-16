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
10. **El muro de `substfc`** — cuando una función objeto no se puede evaluar sobre un código
    abstracto. *Material:* memoria `project-substfc-wall`.
11. **Una inconsistencia latente** — la historia completa: `tcFn` axiomatizado por recursión sobre
    **sintaxis** cuando sólo puede depender de **valores**; `cons 0 nil = 2 = σσ0`; la derivación de
    `⊥`; y el hecho de que un teorema *net‑0* la volviera visible.
    *Material:* memoria `project-inconsistencia-tcfn-cons` + este episodio.
12. **La reparación por tipos** — separar `Num` de `Code`, y por qué los tipos no *parchean* el
    error sino que lo hacen **inexpresable**.
13. **Método** — qué funcionó al formalizar: trocear y compilar entre pasos, verificación
    adversarial, `#print axioms` como auditoría, y por qué «lo verifiqué yo» no es opcional.
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

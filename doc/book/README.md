# `doc/book/` — el libro *Incompletitud, formalizada*

**Plan normativo:** [`PLAN-LIBRO.md`](../../PLAN-LIBRO.md) (raíz del repo). Este README sólo
explica **cómo se opera** el directorio; el qué y el porqué están allí.

## ⚠️ Ámbito: qué puede escribir esta tarea

Q++ está en desarrollo activo y esta tarea corre **en paralelo** a la de programación y prueba.
Sólo son escribibles **`PLAN-LIBRO.md`**, **`Sobre_el_libro.md`** y **todo `doc/book/**`**. El resto
del repositorio —los `.lean`, los `.md` de estado, los scripts de la raíz— es de **sólo lectura**
aquí. Ver `PLAN-LIBRO.md` §0.

Lo comprueba `scripts/ambito.py` sobre el área de staging: `make ambito`. Y `make subir MSG='...'`
prepara **sólo** el libro —nunca `git add -A`— antes de commitear.

Si al escribir un capítulo descubres que un documento de estado miente, **no lo corrijas desde
aquí**: anótalo en el capítulo y déjalo para la otra tarea.

## Licencia

**Prosa, figuras y maquetación: CC BY-SA 4.0. Código Lean 4 citado: MIT** (no cambia de licencia al
ser citado). Detalle en [`LICENSE`](LICENSE) y en el apéndice E del libro.

## Piezas

| pieza | qué es |
|---|---|
| `libro.tex` | documento maestro; el índice refleja `PLAN-LIBRO.md` §3 |
| `preamble.tex` | estilo y **los cinco entornos**: `lean`, `matematica`, `leccion`, `muro`, `refutado` |
| `capitulos/*.tex` | un fichero por capítulo — **prosa y enunciados, nunca código Lean a mano** |
| `fragmentos.json` | **el manifiesto**: qué declaración del repo se cita, desde qué módulo, con qué footprint esperado |
| `extraido/*.tex` | **GENERADO** por `scripts/extraer.py`. No editar. No commitear |
| `scripts/extraer.py` | extrae del repo y aplica los controles de `PLAN-LIBRO.md` §2.1–§2.3 |
| `bib/libro.bib` | bibliografía |
| `MATERIALES.md` | **la cantera**: hallazgos y razonamientos que deben acabar en el libro, cada uno con su capítulo de destino y su estatuto ([medido]/[citado]/[razonado]/[conjetura]) |
| `DOCSTRINGS-NO-FIABLES.md` | afirmaciones falsas encontradas en docstrings de producción (§2.6) |

## Uso

```bash
make            # extraer + compilar
make extraer    # sólo extraer los fragmentos del repo
make pdf        # sólo compilar (falla si falta algún fragmento)
make axiomas    # regenera los #print axioms reales (necesita lake/lean)
make ambito     # ¿hay algo preparado para subir fuera del libro?
make subir MSG='...'   # compila, verifica, prepara sólo el libro y commitea
make clean
```

⚠️ `make axiomas` **necesita `lake` y `lean` en el PATH** y se ejecuta desde la raíz del repo. Es el
control `PLAN-LIBRO.md` §2.2(c)-(d): compara el footprint real de cada declaración citada contra el
declarado en `fragmentos.json` y contra la base sancionada.

## Los cinco entornos, y cuándo se usa cada uno

- **`lean`** — código Lean 4 real. **No se teclea**: llega vía `\leanfrag{clave}`.
- **`matematica`** — el mismo enunciado en notación estándar, legible sin saber Lean.
- **`leccion`** — la nota pedagógica: qué se aprende de esto y dónde se reutiliza.
- **`muro`** — una obstrucción encontrada: *«aquí no sé pasar»*.
- **`refutado`** — un resultado **negativo compilado**: *«se ha probado que no se pasa»*.
  No es lo mismo que un muro, y confundirlos vacía de contenido la Parte IV.

## Regla que no se negocia

`doc/book/` **no entra en el build de `lake`** y **no toca** la compilación Lean. Si `lake build`
cambia de número de jobs por algo hecho aquí, es un error.

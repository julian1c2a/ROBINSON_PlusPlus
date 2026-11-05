# ROBINSON_PlusPlus

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Los banners que se apilaban aquí están, tal cual, en [doc/historia/BANNERS.md](doc/historia/BANNERS.md).

[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://leanprover.github.io/)
[![Build](https://github.com/julian1c2a/ROBINSON_PlusPlus/actions/workflows/build.yml/badge.svg)](https://github.com/julian1c2a/ROBINSON_PlusPlus/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

**Last updated:** 2026-11-05 — [ADR‑259](DECISIONS.md): 120 módulos (la admisibilidad de `listInd`, en el build). Antes, 2026-11-04 — [ADR‑256](DECISIONS.md): la memoria del presupuesto de la CI, rotulada (el pico del proceso más pesado), y su autotest. Antes, el mismo día — [ADR‑255](DECISIONS.md): la fila de `check-sondeos.bash`, con su control negativo. Antes, el mismo día — [ADR‑254](DECISIONS.md): la fila de `check-indice.bash` (el índice de las constantes y lo que nadie usa de FOL). Antes, 2026-11-02 — [ADR‑250 y ADR‑251](DECISIONS.md): 35 titulares (los tres semánticos del puente con FOL, con el choice de la completitud de FOL) y nanoda con cuatro hilos. Antes, 2026-11-01 — [ADR‑235](DECISIONS.md) (T21): los controles, contra el código: la tabla, con los que faltaban y sus filas al día, y la cifra del build, con su alcance. Antes, 2026-10-30 — [ADR‑228](DECISIONS.md): los 32, por los cuatro núcleos independientes. Antes, el mismo día — [ADR‑222](DECISIONS.md) (T23): el segundo núcleo, en «lo que se supone». Antes, 2026-10-28 — [ADR‑210](DECISIONS.md): los tres sintácticos del puente con FOL, titulares (32). Antes, el mismo día — [ADR‑195](DECISIONS.md) (T67): Gödel I en la lógica de primer orden, por el puente de FOL a `Prf`. Antes, 2026-10-27 — [ADR‑193](DECISIONS.md) (T53): el control nuevo, `check-choice.bash`. Antes, el mismo día — [ADR‑192](DECISIONS.md) (T68): 120 axiomas (el verificador antiguo, fuera de T). Antes, el mismo día — [ADR‑191](DECISIONS.md) (T61b): 118 módulos activos; los titulares, sin `Classical.choice`. Antes, 2026-10-21 — [ADR‑190](DECISIONS.md) (T76): 116 módulos activos. Antes, el mismo día — [ADR‑183](DECISIONS.md) (T25): reescrito contra el árbol (qué es, lo demostrado, las
capas, la instalación con el hermano FOL y el toolchain exacto, los controles, los documentos). Lo de antes, en la
historia de git.

Los **teoremas de incompletitud de Gödel**, y con ellos Tarski, Rosser y Löb, formalizados en Lean 4 **sin Mathlib**,
sobre una implementación propia de la lógica de primer orden con igualdad ([FOL](https://github.com/julian1c2a/FOL),
un repositorio hermano). La disciplina: cada paso se demuestra desde la base o se declara pendiente con nombre y firma,
y cada cifra que se publica la vuelve a medir un control o lleva su alcance: sobre qué, cuándo y dónde se midió (M‑13).

## Lo demostrado

Sobre el cálculo finitario `Prf` (`Meta/Hilbert.lean`), sin hipótesis dentro de Lean:

| teorema | dice | módulo |
|---|---|---|
| `goedel_I`, `goedel_I_neg` | ni `G` ni `¬G` son teoremas: Gödel I entero | `Meta/Consistencia.lean`, `Meta/SolidezVerificador.lean` |
| `goedel_II` | la teoría no demuestra su propia consistencia | `Meta/Consistencia.lean` |
| `goedel_second_formalizado` | Gödel II demostrado DENTRO de la teoría | `Meta/GodelCorolarios.lean` |
| `tarski`, `tarski_semantico_de` | la verdad no es definible: ni sintácticamente ni en ningún modelo estándar | `Meta/TarskiPrf.lean` |
| `rosser`, `rosser_ext` | la sentencia de Rosser es indecidible, también en toda extensión finita consistente | `Meta/Rosser.lean` |
| `lob` | de `Prf (Prov⌜φ⌝ ⇒ φ)` se sigue `Prf φ` | `Meta/Lob.lean` |
| `consistencia` | la teoría es consistente (un modelo de sus axiomas y la solidez de `Prf`) | `Meta/Consistencia.lean` |
| `goedel_I_fol`, `goedel_II_fol`; `goedel_I_semantico` | Gödel I y II también en la lógica de primer orden de FOL, para todo conjunto de teoremas de `Prf` (titulares desde ADR‑210); y un modelo de la teoría en que `G` es falsa (no titular: lleva el `Classical.choice` de la completitud de FOL) | `Meta/PuenteFOL.lean` |

Las condiciones de derivabilidad D1, D2 y D3 son teoremas (`repr_pos'_prf`, `d2_prf`, `d3_prf_real`). La tabla
completa —35 titulares, con la hipótesis de cada uno, quién la descarga y qué usa su prueba— es
[TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §1.

**La teoría** de esos teoremas, T_Prf ([AXIOMS.md](AXIOMS.md) §0), es lo que deriva `Prf`: los 120 axiomas de la
lista de `Minimal/`, los esquemas lógicos, y la inducción y la inducción de listas para toda fórmula. Contiene a PA
(no es Q). **Lo que se supone**: el núcleo de Lean y sus tres axiomas, y nada más: 0 `axiom` de Lean en el build, y
`leanchecker` re‑comprueba cada declaración en la CI, y cuatro núcleos independientes, el cierre de los 35 titulares,
el modelo y la completitud de FOL incluidos (ADR‑222, ADR‑228, ADR‑250). La consistencia que da `consistencia` es RELATIVA a Lean (PRA ⊢
Con(Lean) → Con(T_Prf)); absoluta no puede ser ([TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4).

## Las capas

**120** módulos activos (Minimal 2 + Meta 117 + Full 1); el catálogo, módulo a módulo, en [REFERENCE.md](REFERENCE.md)
§1, y las cifras de hoy, cada una con su control, en [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md).

| capa | qué hay |
|---|---|
| `Minimal/` | el lenguaje y la LISTA de axiomas, sin esquema de inducción: 120 sentencias, 34 matemáticas (`coreAxioms`) + 85 de codificación (`codingAxioms`) + el ancla diagonal |
| `Full/` | `primAxioms`, los lemas de sustitución y la fórmula de inducción (`Induction.lean`) |
| `Meta/` | la aritmetización de la sintaxis, el verificador de pruebas interno, D1–D3, el punto fijo, el modelo estándar y la solidez, y los titulares |

## Instalación

Hace falta [elan](https://github.com/leanprover/elan); la versión de Lean, **v4.35.0**, la fija `lean-toolchain` y
elan la instala sola. FOL es una dependencia LOCAL (`require FOL from "../FOL"` en el `lakefile.lean`): los dos
repositorios van uno al lado del otro.

```bash
git clone https://github.com/julian1c2a/FOL.git
git clone https://github.com/julian1c2a/ROBINSON_PlusPlus.git
cd ROBINSON_PlusPlus
lake build                                   # RPP y lo que importa de FOL
lake build "@FOL/FOL" "@FOL/TheoryFramework" # FOL entero, también desde aquí
```

`lake env lean --version` tiene que decir 4.35.0: si dice otra cosa, el `lake` del PATH no es el de elan. Sin Mathlib
y sin otras dependencias. En la CI (4 vCPU), el build de RPP tardó 185 s en su primera medida, en frío y sin caché
(ADR‑203); cada run lo vuelve a medir con GNU time, y `scripts/presupuesto-ci.bash` lo pone en rojo si pasa de su
presupuesto de tiempo o de memoria (`doc/control/presupuesto-ci.tsv`; la memoria es el PICO del proceso más pesado, no
la del build entero: ADR‑256).

## Los controles

Además del build, que ya comprueba los enunciados de los titulares (T07) y la pureza de la clase (i) (T08), la CI
(`.github/workflows/build.yml`), que corre con cada push a `master` o a una rama `ci/…`, cada día y con cada push al
master de FOL, pasa estos scripts, que también se lanzan a mano desde la raíz (`scripts/presupuesto-ci.bash`, sobre las salidas de
GNU time del build y de leanchecker; `scripts/segundo-nucleo.bash`, no donde Windows bloquea sus binarios, como en la
máquina del propietario, ni en WSL, porque llama a lake: allí sus núcleos de Linux se pasan a mano, como en
`doc/registro/2026-10-30-adr228/LEEME.txt`):

| script | qué comprueba |
|---|---|
| `bash check-sorry.bash` | por texto: ningún `sorry` (ni «admit», «stop» o «sorryAx») en los `.lean` de RPP, `sondeos/` incluidos (el de FOL y TheoryFramework lo mira `check-estratos.bash`, por entorno); ningún agujero de confianza («native_decide», «implemented_by»…) en lo que compila el build (RPP, FOL y TheoryFramework; `sondeos/` no); y ninguna orden («#eval», «#reduce», «#guard», «run_cmd»…) que evalúe el ancla, en RPP y `sondeos/` |
| `bash check-footprints.bash` | el `#print axioms` de cada declaración de su tabla (de RPP, FOL y TheoryFramework; los 35 titulares entre ellas), con igualdad; y que todo `#print axioms` que imprime el árbol tenga su fila |
| `bash check-choice.bash` | cada constante de RPP, FOL y TheoryFramework con `Classical.choice`, `noncomputable` o `String`, contra `doc/control/choice.tsv`, en los dos sentidos |
| `bash check-indice.bash` | el índice de las constantes declaradas de RPP (nombre, clase, módulo y enunciado), `doc/indice.tsv`, para buscar antes de construir, y lo que nadie usa de FOL, etiquetado (`doc/control/fol-sin-uso.tsv`): los dos, lo que se genera del entorno de Lean, con calibración |
| `bash check-estratos.bash` | por entorno: ningún `axiom` habita una noción de derivabilidad; `sorry`, confianza y `partial`, con señuelo |
| `bash check-warnings.bash` | los avisos de los dos builds (RPP; FOL y TheoryFramework), por fichero y clase, contra una tabla vacía: cualquier aviso es rojo; y los set_option que apagan un linter o suben un límite, de fichero (ninguno desde ADR‑229) o con … in, en las tres librerías, contra `doc/control/opciones.tsv`, con igualdad. ✏️ 2026‑10‑31 (T21, ADR‑235): decía «los avisos del build, declarados uno a uno»; la tabla está vacía desde ADR‑227 y las opciones se censan desde ADR‑226 |
| `bash check-doc-sync.bash` | que los documentos digan lo que hay —cifras (`[A]`, `[A2]`), citas muertas (`[B]`, `[M]`) y por número de línea (`[N]`), marcas de tiempo (`[D]`; `[E]`, con su deuda en dos tablas, de contenido y de formato, y un techo: ADR‑233), catálogos (`[C]`, `[H]`), titulares (`[T]`) y frases que un teorema desmiente (`[I]`)— y, del árbol, que la librería sea el cierre de imports (`[L]`), sin .olean huérfanos (`[F]`), sin CRLF en el índice (`[EOL]`) y con el PATH higiénico en cada script (`[H]`) |
| `bash check-sondeos.bash --controles` | los once sondeos de control (`sondeos/CONTROLES.txt`) compilan, y una variable implícita automática no (`autoImplicit` apagado, ADR‑255) |
| `bash scripts/leanchecker-cobertura.bash`, sobre el registro de `lake env leanchecker --verbose ROBINSON_PlusPlus FOL TheoryFramework` (en local, con LEAN_NUM_THREADS=4: ver debajo de la tabla) | el núcleo de Lean vuelve a pasar cada declaración de las tres librerías, y lo replayado son exactamente los módulos de sus fuentes, con un .olean por módulo |
| `bash scripts/segundo-nucleo.bash` | el cierre de los 35 titulares y el de los titulares de la clase (i), por seis núcleos (el de Lean, su versión paranoica y cuatro independientes), contra `doc/control/segundo-nucleo.tsv`: los seis aceptan los dos (ADR‑228, ADR‑250; nanoda, con cuatro hilos desde ADR‑251); sus `axiom`, los de los footprints; y un mutante que todo núcleo que acepta tiene que rechazar |
| `bash scripts/presupuesto-ci.bash` | el tiempo y la memoria (el pico del proceso más pesado) del build y de leanchecker (GNU time), contra `doc/control/presupuesto-ci.tsv`: por encima, rojo; `--autotest`, con medidas sintéticas (ADR‑256) |
| «bash scripts/thaws-fol.bash ../FOL» | cada thaw de FOL (toda la historia de su `frozen_files.txt`) se apoya en un ADR de RPP que existe y nombra al propietario (la palabra «propietario» o, en los antiguos, «usuario», en su sección): el que cita su mensaje o, si es de antes de la regla, el de doc/control/thaws-fol.tsv; su alcance declarado (prosa o código), re‑medido con scripts/prosa.py; y `git-lock.bash` y los ganchos de .githooks/, los mismos en RPP y en FOL (T14, ADR‑234) |
| `make probar-controles` | las herramientas que validan los controles: el despojador frente a su oráculo y `lineWFT` frente a su generador (en la CI, esas dos órdenes; los mutantes del despojador, que el objetivo también corre, sólo a mano) |

En el workflow, además, que RPP y FOL tengan el mismo `lean-toolchain` (M‑3; si no, rojo); que el master de FOL sea el
de `doc/control/fol-sha.txt` sólo avisa. ✏️ 2026‑10‑31 (T21, ADR‑235): la tabla no tenía `scripts/presupuesto-ci.bash`
(ADR‑202) ni `scripts/leanchecker-cobertura.bash` y `scripts/segundo-nucleo.bash` (ADR‑222); la fila de los thaws de
FOL es de hoy (T14, ADR‑234).

`leanchecker`, en local: `LEAN_NUM_THREADS=4 lake env leanchecker ROBINSON_PlusPlus FOL TheoryFramework` (con un hilo
por procesador replaya todos los módulos a la vez y necesita unos 25 GB; ADR‑181). En Windows, los `lake` y los
`bash check-*.bash`, desde PowerShell.

## Desarrollo

`master` está protegido (aquí y en FOL): se sube por una rama `ci/…`, y entra cuando la CI está en verde. Un módulo
nuevo se crea en `ROBINSON_PlusPlus/<capa>/` y se importa desde su barril (`ROBINSON_PlusPlus/Meta.lean` o
`ROBINSON_PlusPlus.lean`); `check-doc-sync.bash` `[L]` falla si uno no está importado o no está en git. El flujo
entero, en [WORKFLOW.md](WORKFLOW.md); las reglas para quien escribe código o documentos, en [AI-GUIDE.md](AI-GUIDE.md).

Los ganchos de git son los versionados en .githooks/ (pre-commit rechaza un commit que toque un fichero congelado o
bloqueado; commit-msg, un thaw que no cite «ADR-NNN de RPP»), y los activa `bash git-lock.bash init` (core.hooksPath),
una vez por clon (T14, ADR‑234).

## Documentos

| documento | para qué |
|---|---|
| [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) | ⭐ el estado: los titulares, sus hipótesis y qué usa cada prueba |
| [AXIOMS.md](AXIOMS.md) | la teoría de los titulares y lo que se supone |
| [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) | las cifras del árbol, cada una con su control |
| [REFERENCE.md](REFERENCE.md) | el catálogo de módulos y la referencia técnica (los nodos, en `doc/REFERENCE-*.md`) |
| [DEPENDENCIES.md](DEPENDENCIES.md) | los diagramas de dependencias |
| [DECISIONS.md](DECISIONS.md) | el registro de decisiones (ADR): lo que se hizo, cuándo y por qué |
| [NEXT-STEPS.md](NEXT-STEPS.md) | lo que queda y la cola del propietario |
| [doc/AUDITORIA-SUELO-2026-10-12.md](doc/AUDITORIA-SUELO-2026-10-12.md) | la auditoría del suelo: sus 81 trabajos y el estado de cada uno |
| [PLAN-PRUEBAS.md](PLAN-PRUEBAS.md) | el plan de pruebas que abrió la auditoría del 2026‑09‑11: qué tiene que comprobar cada control |
| [WORKFLOW.md](WORKFLOW.md) · [AI-GUIDE.md](AI-GUIDE.md) | el flujo de trabajo y las reglas |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | los nombres (Mathlib, con las reglas propias del proyecto) |
| [CHANGELOG.md](CHANGELOG.md) | la historia hasta ADR‑113, CONGELADA (ADR‑142); lo vigente es DECISIONS |

## Nombres

El proyecto sigue las [convenciones de Mathlib4](https://leanprover-community.github.io/contribute/naming.html), con
las reglas propias que recoge [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md). Ejemplos del árbol:

| entidad | convención | ejemplo |
|---|---|---|
| módulo | `UpperCamelCase` | `GodelTwoPrf.lean` |
| espacio de nombres | `UpperCamelCase` | `ROBINSON_PlusPlus.Meta.GodelTwoPrf` |
| tipo o predicado | `UpperCamelCase` | `ConsistentH`, `Estandar` |
| función o valor | `lowerCamelCase` | `codeNat`, `consN` |
| axioma OBJETO (una `Formula`) | prefijo `ax` | `ax_axiomsCodeT_def`, `ax6_add_comm` |
| teorema | sujeto_predicado | `goedel_first_prf`, `prf_sound` |

## Licencia y autor

MIT ([LICENSE](LICENSE)). Julián Calderón Almendros. Herramientas: Claude Code (Anthropic).

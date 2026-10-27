# ROBINSON_PlusPlus

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Los banners que se apilaban aquí están, tal cual, en [doc/historia/BANNERS.md](doc/historia/BANNERS.md).

[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://leanprover.github.io/)
[![Build](https://github.com/julian1c2a/ROBINSON_PlusPlus/actions/workflows/build.yml/badge.svg)](https://github.com/julian1c2a/ROBINSON_PlusPlus/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

**Last updated:** 2026-10-27 — [ADR‑193](DECISIONS.md) (T53): el control nuevo, `check-choice.bash`. Antes, el mismo día — [ADR‑192](DECISIONS.md) (T68): 120 axiomas (el verificador antiguo, fuera de T). Antes, el mismo día — [ADR‑191](DECISIONS.md) (T61b): 118 módulos activos; los titulares, sin `Classical.choice`. Antes, 2026-10-21 — [ADR‑190](DECISIONS.md) (T76): 116 módulos activos. Antes, el mismo día — [ADR‑183](DECISIONS.md) (T25): reescrito contra el árbol (qué es, lo demostrado, las
capas, la instalación con el hermano FOL y el toolchain exacto, los controles, los documentos). Lo de antes, en la
historia de git.

Los **teoremas de incompletitud de Gödel**, y con ellos Tarski, Rosser y Löb, formalizados en Lean 4 **sin Mathlib**,
sobre una implementación propia de la lógica de primer orden con igualdad ([FOL](https://github.com/julian1c2a/FOL),
un repositorio hermano). La disciplina: cada paso se demuestra desde la base o se declara pendiente con nombre y firma,
y cada cifra que se publica la vuelve a medir un control.

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

Las condiciones de derivabilidad D1, D2 y D3 son teoremas (`repr_pos'_prf`, `d2_prf`, `d3_prf_real`). La tabla
completa —29 titulares, con la hipótesis de cada uno, quién la descarga y qué usa su prueba— es
[TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §1.

**La teoría** de esos teoremas, T_Prf ([AXIOMS.md](AXIOMS.md) §0), es lo que deriva `Prf`: los 120 axiomas de la
lista de `Minimal/`, los esquemas lógicos, y la inducción y la inducción de listas para toda fórmula. Contiene a PA
(no es Q). **Lo que se supone**: el núcleo de Lean y sus tres axiomas, y nada más: 0 `axiom` de Lean en el build, y
`leanchecker` re‑comprueba cada declaración en la CI. La consistencia que da `consistencia` es RELATIVA a Lean (PRA ⊢
Con(Lean) → Con(T_Prf)); absoluta no puede ser ([TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4).

## Las capas

**118** módulos activos (Minimal 2 + Meta 115 + Full 1); el catálogo, módulo a módulo, en [REFERENCE.md](REFERENCE.md)
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
y sin otras dependencias. En la CI (4 vCPU) el build de RPP tarda unos cinco minutos.

## Los controles

Además del build, que ya comprueba los enunciados de los titulares (T07) y la pureza de la clase (i) (T08), cada push
pasa estos scripts (`.github/workflows/build.yml`), que también se lanzan a mano desde la raíz:

| script | qué comprueba |
|---|---|
| `bash check-sorry.bash` | ningún `sorry` ni agujero de confianza («native_decide», «implemented_by»…) en lo que compila el build |
| `bash check-footprints.bash` | el `#print axioms` de cada titular declarado, en los dos sentidos |
| `bash check-choice.bash` | cada constante de RPP, FOL y TheoryFramework con `Classical.choice`, `noncomputable` o `String`, contra `doc/control/choice.tsv`, en los dos sentidos |
| `bash check-estratos.bash` | por entorno: ningún `axiom` habita una noción de derivabilidad; `sorry`, confianza y `partial`, con señuelo |
| `bash check-warnings.bash` | los avisos del build, declarados uno a uno |
| `bash check-doc-sync.bash` | que los documentos digan lo que hay: cifras, citas muertas, marcas, catálogo |
| `bash check-sondeos.bash --controles` | los once sondeos de control (`sondeos/CONTROLES.txt`) compilan |
| `make probar-controles` | las herramientas que validan los controles (el despojador frente a su oráculo, `lineWFT`) |

`leanchecker`, en local: `LEAN_NUM_THREADS=4 lake env leanchecker ROBINSON_PlusPlus FOL TheoryFramework` (con un hilo
por procesador replaya todos los módulos a la vez y necesita unos 25 GB; ADR‑181). En Windows, los `lake` y los
`bash check-*.bash`, desde PowerShell.

## Desarrollo

`master` está protegido (aquí y en FOL): se sube por una rama `ci/…`, y entra cuando la CI está en verde. Un módulo
nuevo se crea en `ROBINSON_PlusPlus/<capa>/` y se importa desde su barril (`ROBINSON_PlusPlus/Meta.lean` o
`ROBINSON_PlusPlus.lean`); `check-doc-sync.bash` `[L]` falla si uno no está importado o no está en git. El flujo
entero, en [WORKFLOW.md](WORKFLOW.md); las reglas para quien escribe código o documentos, en [AI-GUIDE.md](AI-GUIDE.md).

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

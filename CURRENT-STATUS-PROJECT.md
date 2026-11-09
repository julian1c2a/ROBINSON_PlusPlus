# Current Project Status — ROBINSON_PlusPlus

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Este documento da las CIFRAS del árbol, cada una con el control que la mide, y la arquitectura por capas. Lo que se
> hizo y cuándo está en [DECISIONS.md](DECISIONS.md); lo que queda, en [NEXT-STEPS.md](NEXT-STEPS.md) («Lo que queda»).

**Last updated:** 2026-11-09 — [ADR‑262](DECISIONS.md): la deuda de documentación de [E], [B] y [A2], pagada en lote (las cifras de §1 no cambian), y la fila de `Meta/` de §4, que decía 116 (es 117 desde ADR‑259). Antes, 2026-11-05 — [ADR‑259](DECISIONS.md): `Meta/ListIndAdmisible.lean` (la admisibilidad de `listInd`, en el build): 150 jobs, 120 módulos, 652 footprints. Antes, el mismo día — [ADR‑258](DECISIONS.md): los seis pendientes, hechos (221 hechos, 0 pendientes); la constructividad y el índice, con sus cifras (4164 de RPP, 1633 de FOL). Antes, el mismo día — [ADR‑257](DECISIONS.md): los hallazgos (215 hechos, 6 pendientes: los textos, hechos). Antes, 2026-11-04 — [ADR‑256](DECISIONS.md): los hallazgos (207 hechos, 14 pendientes: la ronda 3, terminada). Antes, el mismo día — [ADR‑255](DECISIONS.md): la constructividad, con el filtro de las generadas de `check-indice.bash` (las mismas 200 marcas sobre 4169 constantes de RPP), y los hallazgos (198 hechos). Antes, el mismo día — [ADR‑254](DECISIONS.md): la fila del índice de las constantes y de lo que nadie usa de FOL (`check-indice.bash`); los titulares, 35 (decía 32), y los hallazgos, al día. Antes, 2026-11-03 — [ADR‑252 y ADR‑253](DECISIONS.md): las dos opciones de `simp` del congelado `Theorems/Eq.lean` de FOL, fuera (thaw); los tres semánticos en la forma de libro y la vuelta del puente sobre las clausuras; 648 footprints. Antes, 2026-11-02 — [ADR‑247, ADR‑250 y ADR‑251](DECISIONS.md): 48 sondeos (dos promovidos de `Probe/`, que se barre); los tres semánticos del puente, titulares (35); nanoda con cuatro hilos. Antes, el mismo día — [ADR‑238, ADR‑241 y ADR‑244](DECISIONS.md): dos filas nuevas (las dependencias, generadas, T30; el registro de hallazgos, T37), la forma de los axiomas (T69) y 46 sondeos. Antes, 2026-11-01 — [ADR‑235](DECISIONS.md) (T21): la columna «la mide», contra el código: los módulos, lo de fuera del build, los axiom de Lean y los axiomas objeto, con los controles que de verdad los miden. Antes, 2026-10-30 — [ADR‑227…231](DECISIONS.md): los avisos, a cero; el modelo, por los cuatro núcleos independientes; las opciones, a set_option … in. Antes, el mismo día — [ADR‑222](DECISIONS.md) (T23): el núcleo, con lo que replaya contado y un segundo núcleo; [ADR‑226](DECISIONS.md) (T44): los avisos, 19, y las opciones censadas. Antes, 2026-10-29 — [ADR‑221](DECISIONS.md) (T71, cerrada): los cinco semánticos de FOL, clasificados (sus enunciados implican WLEM o KSst, sin ningún axioma); 646 footprints. Antes, el mismo día — [ADR‑220](DECISIONS.md) (T71, la mitad de Markov): el enunciado de la completitud implica Markov, sin choice; 621 footprints. Antes, 2026-10-28 — [ADR‑218](DECISIONS.md) (T51): X1 en FOL —`Derivesᵢ`, el estrato duodécimo— y «sym!» a FOL; 149 jobs, 617 footprints. Antes, el mismo día — [ADR‑217](DECISIONS.md) (T58): `TheoryFramework` con contenido; las cifras de la tabla, re‑medidas (607 footprints, 24 avisos, la constructividad). Antes, el mismo día — [ADR‑210](DECISIONS.md): los tres sintácticos del puente con FOL, titulares (32). Antes, el mismo día — [ADR‑195](DECISIONS.md) (T67): el puente con FOL; 147 jobs, 119 módulos, 566 footprints. Antes, 2026-10-27 — [ADR‑194](DECISIONS.md) (T46): los once estratos, con su solidez, su completitud y su puente; 558 footprints. Antes, el mismo día — [ADR‑193](DECISIONS.md) (T53): la constructividad, vigilada constante a constante (`check-choice.bash`). Antes, el mismo día — [ADR‑192](DECISIONS.md) (T68): 120 axiomas objeto (los 22 «ax_vpf_*», fuera) y 514 constantes en el contrato. Antes, el mismo día — [ADR‑191](DECISIONS.md) (T61b): 134 jobs y 118 módulos (`SolidezDobleNegacion` y `ProvFiel`), 546 footprints, y `Classical.choice` sólo en `prf_sound`. Antes, 2026-10-21 — [ADR‑190](DECISIONS.md) (T76): las cifras del build, 132 jobs y 116 módulos («Full/Numerals.lean»
y «Meta/CodeArith.lean», fuera: un solo `numeral` fuera de `Minimal`). Antes, el mismo día — [ADR‑182](DECISIONS.md) (T26): reescrito entero. El cuerpo anterior —las tablas del
2026‑09‑10, con sus notas, y el diario de mayo a agosto— está, tal cual, en
[doc/historia/CURRENT-STATUS-hasta-2026-10-21.md](doc/historia/CURRENT-STATUS-hasta-2026-10-21.md).
**Author**: Julián Calderón Almendros

---

## 1 · Las cifras, y quién las mide

Ninguna cifra de esta tabla se copia a mano de otro documento: cada una la vuelve a medir el control de su fila, y las
que tienen forma de frase fija (los jobs, los módulos, `sorry`, `axiom`, `cuarentena/`, `sondeos/`) las compara además
`check-doc-sync.bash` `[A]` en cada push.

| cifra | hoy | la mide |
|---|---|---|
| Build | **150** jobs, 0 errores | `lake build` (la CI, en cada push) |
| Módulos | **120** módulos activos: Minimal 2 + Meta 117 + Full 1, más el barrel `Meta.lean` y la raíz `ROBINSON_PlusPlus.lean` | `check-doc-sync.bash` `[A]` y `[L]` (el cierre de imports del barril, el disco y git son el mismo conjunto: todo `.lean` de `ROBINSON_PlusPlus/`, en el disco o en git, está en el cierre, y todo módulo del cierre, en git) |
| Fuera del build | 0 en `cuarentena/` · **48** `sondeos/`, 11 de control | `check-doc-sync.bash` cuenta los `.lean` de `cuarentena/` y de `sondeos/`, sin sus subcarpetas (lo compara `[A]`), y exige una fila de `sondeos/README.md` por sondeo, en los dos sentidos (`[H]`); `check-sondeos.bash --controles` compila en la CI los 11 de `sondeos/CONTROLES.txt` (los demás, sólo en su informe local) |
| `sorry` | 0 `sorry` | `check-sorry.bash` (el texto) y `check-estratos.bash` (el entorno) |
| `axiom` de Lean | 0 `axiom` de Lean en el build, en RPP y en FOL | `check-estratos.bash`, por entorno y con señuelo (T13): un `axiom` de RPP, FOL o TheoryFramework es rojo; `check-doc-sync.bash`, el token en el código de RPP, con autotest (lo compara `[A]`); y, en la CI de FOL, `../FOL/check-axioms.bash`, por entorno y con señuelo |
| Axiomas objeto | **120**: 34 matemáticos (`coreAxioms`) + 85 de codificación (`codingAxioms`) + el ancla diagonal (142 hasta ADR‑192, que retiró los 22 del verificador antiguo) | `axioms_len` (120), `axiomsBase_len` (119), `coreAxioms_len` (34) y `codingAxioms_len` (85), en `Full/Induction.lean`, por `rfl`, en cada build. Su forma (T69, ADR‑244): 112 Π₁ o Δ₀ y 8 Π₂, medida a mano el 2026‑11‑02 con `sondeos/CensoFormaAxiomas.lean` (REGISTRO; no va a la CI) |
| Dependencias | **389** aristas `import` entre los módulos de RPP, profundidad **59** ([DEPENDENCIES.md](DEPENDENCIES.md), generado) | `gen-dependencies.py --check`, en la CI de RPP y en la de FOL (T30, ADR‑238): rojo si DEPENDENCIES.md no es lo que se generaría |
| Hallazgos de las auditorías | **426** IDs, cada uno con su estado: 221 hechos, 0 pendientes, 32 descartados, 173 sustituidos por un T (`doc/control/hallazgos.tsv`; ✏️ ADR‑254…258: decía 183 y 40, las de antes de ADR‑253; la ronda 3, terminada; los textos, ADR‑257; los seis últimos, ADR‑258) | `check-doc-sync.bash` `[R]` (T37, ADR‑241): los IDs, los de las fuentes en los dos sentidos, y cada estado con su ADR, commit o T existente |
| Titulares | **35**, cada uno con su fila en [TEOREMAS](TEOREMAS-E-HIPOTESIS.md) §1 o §3 (✏️ ADR‑254: decía 32, la cifra de antes de ADR‑250) | `[T]` (`T_UNIVERSO`); el contrato de sus enunciados (T07, `Meta/ContratoTitulares.lean`: 563 constantes en el cierre de sus tipos; decía 559) y la pureza de la clase (i) (T08, `Meta/PurezaTitulares.lean`), en cada build |
| Footprints | **652** filas (✏️ ADR‑259: cuatro de `Meta/ListIndAdmisible.lean`; ✏️ ADR‑253: dos de `Meta/PuenteFOL.lean`, la vuelta y `axiomasT_global`; ✏️ ADR‑221: veinticinco de `FOL/EsencialidadSem0.lean`; ✏️ ADR‑220: cuatro de `FOL/Markov0.lean`; ✏️ ADR‑217: decía 590; eran 597 desde ADR‑215; T58 añade diez, de `TheoryFramework`, y T51 diez, de X1 y «sym!», ADR‑218); en RPP, `Classical.choice` sólo en `prf_sound` (ADR‑191), en su corolario `prfH_sound` (ADR‑194) y en los tres de la completitud de FOL (`prf_completo`, `modelo_sin_G`, `goedel_I_semantico`, ADR‑195) | `check-footprints.bash` |
| Constructividad | sin las constantes generadas: en RPP, de **4192** (✏️ ADR‑259: 28 de `Meta/ListIndAdmisible.lean`; ✏️ ADR‑258: 4169 hasta quitar la copia de `DecidableEq` de `Meta/HilbertSeq.lean`; ✏️ ADR‑255: «generada», con las reglas de Lean y el rango de declaración, las de `check-indice.bash`, y no por nombre; decía 4325, y antes de ADR‑217, 4324: las 200 marcas, las mismas), 21 con `Classical.choice` (`prf_sound`, `prfH_sound`, los tres de la completitud de FOL y 16 de las herramientas de T07 y T08, que lo heredan del marco meta de Lean), 74 `noncomputable` sin choice y 16 con `String`, ninguna en la lógica; en FOL y TheoryFramework, de 1633 (1520 y 113; ✏️ ADR‑258: 1636 y 1523 hasta borrar los tres ejemplos de `FOL/FOL.lean`; ✏️ ADR‑255: decía 1976, 1853 y 123, con el filtro por nombre; ✏️ ADR‑221: 62 más, las de `FOL/EsencialidadSem0.lean`, ninguna con choice), 94 con choice (80 y 14; el control `markov_dioph_classical`, ADR‑220; 70 hasta los once corolarios de ruta de ADR‑194, 81 hasta los once de T58, ADR‑217, y `derivesI_soundness`, ADR‑218), 1 `noncomputable` (ADR‑193) y 1 con `String` (el código de «sym!», ADR‑218) | `check-choice.bash` (`doc/control/choice.tsv`, 200 líneas) |
| Índice de las constantes | declaradas, sin las que genera Lean: **4192** de RPP (`doc/indice.tsv`) y **1633** de FOL y TheoryFramework (`../FOL/doc/indice.tsv`), con su enunciado; de las 1399 declaraciones de FOL y TheoryFramework (sin constructores ni campos), **241** no las usa ninguna constante de las tres librerías, 101 de ellas titulares (`doc/control/fol-sin-uso.tsv`, etiquetadas, sin borrar) | `check-indice.bash`, en la CI de RPP y en la de FOL (L5‑11 y B‑5, ADR‑254): rojo si las tablas no son lo que se genera del entorno de Lean; con calibración |
| Avisos | **0**: la tabla, vacía (✏️ ADR‑227: fuera los 19 de seis módulos congelados de FOL, con un thaw del propietario; ADR‑226: fuera los cinco de RPP); ninguna opción de fichero que apague un linter o suba un límite (ADR‑229: pasadas a set_option … in delante de la declaración que las pide), y las … in, 336 (319 que apagan un linter y 17 que suben un límite), por fichero, opción y forma, con igualdad (`doc/control/opciones.tsv`) | `check-warnings.bash` |
| Estratos | **12** nociones de derivabilidad, ninguna habitada por un `axiom`; las doce con su solidez en el build, las ocho clásicas de FOL con su completitud (ADR‑194); la duodécima, `Derivesᵢ` (X1, ADR‑218), intuicionista: con la semántica de Tarski no la tiene | `check-estratos.bash` (y que §0bis de REFERENCE es su tabla) |
| Núcleo | `leanchecker` re‑comprueba en la CI cada declaración de RPP, FOL y TheoryFramework: 193 módulos, los de las fuentes (ADR‑222); y el cierre de los 35 titulares, el modelo y la completitud de FOL incluidos, lo aceptan cuatro núcleos independientes (lean4lean, nanoda —con cuatro hilos desde ADR‑251—, con‑leche, con‑ron; ✏️ ADR‑228: hasta entonces, sólo el de los 12 de la clase (i); ADR‑250: 35) | `.github/workflows/build.yml`, `scripts/leanchecker-cobertura.bash`, `scripts/segundo-nucleo.bash` |
| Lean | **v4.35.0** (ADR‑181) | `lean-toolchain`; la vigilancia semanal de versiones (`.github/workflows/toolchain.yml`) |

---

## 2 · Lo demostrado

Lo vigente, con la hipótesis de cada teorema, quién la descarga y qué usa su prueba, está en
[TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §1. En una línea: sobre el cálculo finitario `Prf`, cuya teoría
T_Prf contiene a PA ([AXIOMS.md](AXIOMS.md) §0), **Gödel I entero** (`goedel_I` y `goedel_I_neg`), **Gödel II**
(`goedel_II`, y dentro de la teoría `goedel_second_formalizado`), **Tarski** (sintáctico y semántico, este en todo modelo
estándar), **Rosser** (también para toda extensión finita consistente, `rosser_ext`) y **Löb** (`lob`), con D1, D2 y D3
demostradas y la consistencia de T_Prf como teorema (`consistencia`), sin hipótesis dentro de Lean. Y por el puente
con FOL (T67, ADR‑195): Gödel I y II en la lógica de primer orden (`goedel_I_fol`, `goedel_II_fol`; titulares desde ADR‑210), `Prf` completo para su teoría
(`prf_completo`) y un modelo de T_Prf en que G es falsa (`goedel_I_semantico`, que lo junta con la verdad de G en todo modelo estándar); estos tres, titulares desde ADR‑250, con el choice de la completitud de FOL; desde ADR‑253, en la forma de libro (en toda valuación). Y la vuelta, sin choice: `Prf f ↔ DerivesSet₀ ClausurasT f` (`prf_iff_derivesSet_clausuras`): T_Prf es la teoría de primer orden de las clausuras universales de `AxiomasT`.

## 3 · Lo que se supone

El núcleo de Lean v4.35.0 y sus tres axiomas (`propext`, `Classical.choice`, `Quot.sound`): ningún `axiom` del
proyecto en el build ([AXIOMS.md](AXIOMS.md) §0.2). La consistencia que da `consistencia` es RELATIVA a Lean (PRA ⊢
Con(Lean) → Con(T_Prf)) y no puede ser absoluta: [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4.

---

## 4 · La arquitectura, por capas

El catálogo módulo a módulo, con su rol y su estado, es [REFERENCE.md](REFERENCE.md) §1 (y `[C]` vigila que cada
módulo del árbol esté en él); las dependencias, [DEPENDENCIES.md](DEPENDENCIES.md). Aquí, sólo las capas.

| capa | qué hay | módulos |
|---|---|---|
| `Minimal/` | el lenguaje y la LISTA de axiomas (`Axioms.lean`: los 120, sin esquema de inducción) y la macro de los literales de símbolo (`SymLit.lean`) | 2 |
| `Full/` | `primAxioms` y las longitudes del censo, los lemas de sustitución y la fórmula `inductionFormula` (`Induction.lean`); el `numeral`, uno solo, en `Meta/Godel.lean` (ADR‑190) | 1 |
| `Meta/` | todo lo demás, en siete familias (abajo) | 117 (✏️ 2026‑11‑09, ADR‑262: decía 116, la cifra de antes de ADR‑259) |

Las familias de `Meta/` (los nombres, en REFERENCE §1.5):

* **La codificación y el cálculo**: `Godel`, `Provability`, `Hilbert` (`Prfᵢ`, `Prf` y `ConsistentH`),
  `HilbertDeduction` (`PrfH`), `HilbertSeq`, la aritmética de códigos y el verificador (`SubstArith`,
  `CheckArith`, `ProofChain`).
* **La aritmética dentro de `Prf`**: el orden, el producto, Cantor, la paridad, la inducción fuerte y las listas
  (`NatArithPrf`, `NatOrderPrf`, `NatMulPrf`, `CantorMonoPrf`, `Div2ParityPrf`, `StrongInductionPrf`, `NumListPrf`…).
* **D1, D2 y el punto fijo**: la representabilidad (`Representability`, `Representability2`, sus versiones `…Prf`),
  `DerivCondPrf`, la codificación por numerales (`CodeNumeralPrf`) y los lemas diagonales (`Diagonal`, `DiagonalTwo`,
  `DiagonalNumeral`).
* **D3** (la Σ₁‑completitud demostrable del verificador): la capa Δ₀, la evaluación dentro de Prov (`Eval…Prf`), los
  kits de reflexión (`CodeCtorKit`, `CodeTreeReflect`, `SubstTreeReflect`, `TrackedAtomsPrf`…), las guardas y los
  testigos (`HasWitTrackedPrf`, `SubstfcWitnessPrf`, `LiftfcWitnessPrf`…), la reflexión de `lineWF`
  (`LineWFTrackedPrf`, `LineWFAssemblePrf`…) y el ensamblaje (`D3ChainDotPrf`, `D3BodyPrf` y `PremsBdAllPrf`, con
  `d3_prf_real`).
* **El modelo, la solidez y la consistencia**: `ModeloCodigo`, `ModeloEstandar`, `ModeloCodificacion`, `SolidezPrf`,
  `SolidezDobleNegacion` (la solidez sin lógica clásica, ADR‑191), `Consistencia`, `SolidezVerificador` (W1),
  `RigidezEstandar` (W1 y E10 en todo modelo estándar), `ProvFiel` (Prov fiel, con el testigo) y `SegundoModelo`.
* **El puente con FOL**: `PuenteFOL` (T67, ADR‑195: lo que FOL deriva de teoremas de `Prf` es teorema; Gödel I en la
  lógica de primer orden, `Prf` completo y un modelo de T_Prf en que G es falsa).
* **Los titulares**: `GodelTwo`, `GodelTwoPrf`, `GodelCorolarios`, `TarskiPrf`, `Rosser` y sus etapas (`RosserW1`,
  `RosserPosNum`, `RosserNumerales`, `RosserNumEval`, `RosserGuardNeg`, `RosserNegLinea`, `RosserNegNum`) y `Lob`.
* **Los controles que viven en el build**: `PurezaComando` y `PurezaTitulares` (T08), `ContratoTitulares` y
  `ContratoTabla` (T07).

FOL (`../FOL`, un repositorio hermano) da la lógica de primer orden con igualdad, la semántica y la solidez que usan el
modelo y `consistencia`; RPP importa de él lo que necesita, y su build compila sus dos librerías enteras.

---

## 5 · Lo que queda

En [NEXT-STEPS.md](NEXT-STEPS.md), «Lo que queda»: los trabajos que abrió la auditoría del suelo
([doc/AUDITORIA-SUELO-2026-10-12.md](doc/AUDITORIA-SUELO-2026-10-12.md)), agrupados, y la cola que decide el propietario.

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

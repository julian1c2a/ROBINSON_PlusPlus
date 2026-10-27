# Current Project Status — ROBINSON_PlusPlus

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Este documento da las CIFRAS del árbol, cada una con el control que la mide, y la arquitectura por capas. Lo que se
> hizo y cuándo está en [DECISIONS.md](DECISIONS.md); lo que queda, en [NEXT-STEPS.md](NEXT-STEPS.md) («Lo que queda»).

**Last updated:** 2026-10-27 — [ADR‑193](DECISIONS.md) (T53): la constructividad, vigilada constante a constante (`check-choice.bash`). Antes, el mismo día — [ADR‑192](DECISIONS.md) (T68): 120 axiomas objeto (los 22 «ax_vpf_*», fuera) y 514 constantes en el contrato. Antes, el mismo día — [ADR‑191](DECISIONS.md) (T61b): 134 jobs y 118 módulos (`SolidezDobleNegacion` y `ProvFiel`), 546 footprints, y `Classical.choice` sólo en `prf_sound`. Antes, 2026-10-21 — [ADR‑190](DECISIONS.md) (T76): las cifras del build, 132 jobs y 116 módulos («Full/Numerals.lean»
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
| Build | **134** jobs, 0 errores | `lake build` (la CI, en cada push) |
| Módulos | **118** módulos activos: Minimal 2 + Meta 115 + Full 1, más el barrel `Meta.lean` y la raíz `ROBINSON_PlusPlus.lean` | `check-doc-sync.bash` `[A]` y `[L]` (la librería es el cierre de imports, y todo `.lean` del árbol está en ella) |
| Fuera del build | 0 en `cuarentena/` · **44** `sondeos/`, 11 de control | `check-sondeos.bash --controles` (los 11, en la CI); `sondeos/README.md` |
| `sorry` | 0 `sorry` | `check-sorry.bash` (el texto) y `check-estratos.bash` (el entorno) |
| `axiom` de Lean | 0 `axiom` de Lean en el build, en RPP y en FOL | `check-sorry.bash`, `check-estratos.bash` y `../FOL/check-axioms.bash`, por entorno y con señuelo (T13) |
| Axiomas objeto | **120**: 34 matemáticos (`coreAxioms`) + 85 de codificación (`codingAxioms`) + el ancla diagonal (142 hasta ADR‑192, que retiró los 22 del verificador antiguo) | `axioms_len` y `axiomsBase_len` (`Full/Induction.lean`), por `rfl`, en cada build |
| Titulares | **29**, cada uno con su fila en [TEOREMAS](TEOREMAS-E-HIPOTESIS.md) §1 o §3 | `[T]` (`T_UNIVERSO`); el contrato de sus enunciados (T07, `Meta/ContratoTitulares.lean`: 514 constantes en el cierre de sus tipos) y la pureza de la clase (i) (T08, `Meta/PurezaTitulares.lean`), en cada build |
| Footprints | **546** filas; en RPP, `Classical.choice` sólo en `prf_sound` (ADR‑191) | `check-footprints.bash` |
| Constructividad | sin las constantes generadas: en RPP, de **4306**, 17 con `Classical.choice` (`prf_sound` y 16 de las herramientas de T07 y T08, que lo heredan del marco meta de Lean), 74 `noncomputable` sin choice y 17 con `String`, ninguna en la lógica; en FOL y TheoryFramework, de 1498, 70 con choice y 1 `noncomputable` (ADR‑193) | `check-choice.bash` (`doc/control/choice.tsv`, 172 líneas) |
| Avisos | **28** declarados: los 9 de siempre y 19 nombres obsoletos en seis módulos congelados de FOL | `check-warnings.bash` |
| Estratos | **10** nociones de derivabilidad, ninguna habitada por un `axiom` | `check-estratos.bash` |
| Núcleo | `leanchecker` re‑comprueba en la CI cada declaración de RPP, FOL y TheoryFramework | `.github/workflows/build.yml` |
| Lean | **v4.35.0** (ADR‑181) | `lean-toolchain`; la vigilancia semanal de versiones (`.github/workflows/toolchain.yml`) |

---

## 2 · Lo demostrado

Lo vigente, con la hipótesis de cada teorema, quién la descarga y qué usa su prueba, está en
[TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §1. En una línea: sobre el cálculo finitario `Prf`, cuya teoría
T_Prf contiene a PA ([AXIOMS.md](AXIOMS.md) §0), **Gödel I entero** (`goedel_I` y `goedel_I_neg`), **Gödel II**
(`goedel_II`, y dentro de la teoría `goedel_second_formalizado`), **Tarski** (sintáctico y semántico, este en todo modelo
estándar), **Rosser** (también para toda extensión finita consistente, `rosser_ext`) y **Löb** (`lob`), con D1, D2 y D3
demostradas y la consistencia de T_Prf como teorema (`consistencia`), sin hipótesis dentro de Lean.

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
| `Meta/` | todo lo demás, en siete familias (abajo) | 115 |

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

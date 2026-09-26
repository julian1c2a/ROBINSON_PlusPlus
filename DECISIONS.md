# Decisiones de Diseño — ROBINSON_PlusPlus

**Last updated:** 2026-09-26 — hasta **ADR-101** (las decisiones D1-D7 del cierre de FOL y la condición para PeanoRF). ⚠️ Este fichero **no tenía** marca de tiempo y por eso el control `[E]` no podía comprobarlo (ADR-072 §2). Se añade aquí, y se actualiza **con cada ADR nueva**.

> ## ESTADO REAL — 2026‑09‑11 · `master` · 🏁🏁 **CADENA DE GÖDEL FINITARIA** (Gödel I y II sobre `Prf`, hipótesis **mínima** `ConsistentH`, **un solo axioma** en el footprint) · ⛔⛔ **`axioms ⊢` es COMPLETO** ([auditoría](doc/AUDITORIA-2026-09-11.md))
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 145 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **131 módulos activos** (Minimal 11 + Meta 109 + Full 11) **+ 0 en `cuarentena/` + 61 en `sondeos/`.**
> **3 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

**Última actualización:** 2026-09-10h — **ADR-022**: la clase de testigos de la ω‑consistencia se ESTRECHA a líneas estándar; el precio (una `OmegaConsistent` más fuerte) va escrito, y la garantía que lo hace admisible (`stdChain_proofCode'`) probada. — (previo 2026-09-05) **ADR-019 confirmado en vivo por B3**: el general mal colocado dejaba un corolario inalcanzable, y la duplicación por INSTANCIA que ningún censo ve. ADR-018 en producción.
**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> Este fichero adopta el esqueleto unificado de `lean4-project-template` (ADR-001–009,
> traducidos al español) y **preserva íntegros** los dos ADR reales y sustanciosos que
> ya existían aquí (renumerados a ADR-010/011) — son, junto con los de Peano, los ADR
> de mejor calidad entre los proyectos hermanos: documentan contraejemplos matemáticos
> concretos, no solo preferencias de estilo.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto — lectura obligatoria)

**Cada MANDATORY lleva su columna «Verificación»** — una MANDATORY sin verificación
mecánica es una intención, no una regla. Esta tabla recoge reglas **ya vigentes** en el
proyecto; no introduce ninguna nueva.

| # | MANDATORY | ADR | Verificación |
|---|---|---|---|
| **M-1** | ⛔ **Ningún `axiom` nuevo —de Lean o de la teoría objeto— sin sanción explícita del autor y su ADR.** Un axioma sin ADR ya hizo **inconsistente** la teoría objeto | ADR-010/011/012/013 | `AXIOMS.md` (inventario) · `check-doc-sync.bash` [A] contrasta la cifra «N `axiom` de Lean» con `grep '^axiom '` · `#print axioms` en cada frente |
| **M-2** | ⛔ **Las imágenes punteadas (`substfcT`, `substtcT`, `liftcT`, `liftfcT`, `predcT`) son DEFINICIONES, jamás axiomas.** Postular la ecuación de rastreo (`ax_tc_substfc`, `ax_tc_cons`) da `axioms ⊢ ⊥`; los puentes se escriben `:= rfl` y el salto sólo vale **dentro de `Prov`** | ADR-012/013/015 | `grep -rn '^axiom ax_tc_' ROBINSON_PlusPlus/` debe dar **0** |
| **M-3** | ⛔ **NUNCA `cd FOL && lake build`.** `FOL` es dependencia LOCAL (`require FOL from "../FOL"`) y compilarla desde su propio directorio usa **otro toolchain**. Todo se compila desde la raíz de `ROBINSON_PlusPlus` | — | `update-toolchain.bash` compila desde la raíz; el `lakefile.lean` es la única fuente del target |
| **M-4** | **Cero `sorry` en el árbol activo.** No se «aparca» una prueba con `sorry`: o entra probada, o se queda en `sondeos/` | — | `bash check-sorry.bash` → `✅ No sorry found.` (cuenta el TOKEN, fuera de comentarios y cadenas; AI-GUIDE §27.1) |
| **M-5** | **Todo módulo de producción aparece en el catálogo `REFERENCE.md` §1** y termina con su bloque `export` — puesto **por CONSUMO, no por existencia** | AI-GUIDE §1/§14/§17 | `check-doc-sync.bash` [C] (proyección). ⚠️ El «por consumo» del `export` **no** tiene verificación mecánica todavía: se audita a mano (así se detectaron B8b y el dedup de §3.52) |
| **M-6** | **`bash check-doc-sync.bash` en verde antes de cerrar cualquier pasada de documentación.** `[A]`, `[C]` y `[D]` rompen; `[B]` es aviso y **pide juicio**, no se ignora | AI-GUIDE §27 | el propio script (exit 0) |
| **M-7** | ⚠️ **El `PsiF` de un chasis inductivo (`pcc_bdAll_intro`) sólo es natural si el PARÁMETRO NO VIAJA DENTRO DE LA FÓRMULA que se codifica.** Si va dentro, `hPl` es **FALSA** y hace falta escribirlo con símbolos OBJETO y puentear dentro de `Prov`; si entra **sólo como testigo** (cuerpo cerrado), el `substCodeF`/`substCodeF2` **es** natural y no hace falta nada. ⚠️ **Afinada el 2026‑09‑10f** (§3.66.1): la forma vieja —«nunca un `substCodeF`»— sobre‑prohibía | ADR-021 | dos `rfl` (`substCodeT_hole_lhs`/`_rhs`, `Meta/D3ChainDotPrf.lean` §10.1) — y el propio `hPl` no compila |
| **M-11** | ⛔⛔ **Antes de demostrar algo por INDUCCIÓN sobre un tipo inductivo, comprobar que NINGÚN `axiom` lo habita.** Un `axiom` cuyo tipo es una aplicación de un `inductive` produce habitantes que **no son aplicaciones de constructor**; la inducción cubre los constructores, pero el teorema cuantifica sobre **todos** los habitantes ⇒ el teorema es **FALSO**. ⚠️ Es *eliminar* lo peligroso (`induction`/`cases`/`rec`), **no** *introducir*: usar los constructores para construir es seguro. ⛔⛔ **`Derives` NO ADMITIRÁ INDUCCIÓN NUNCA, y eso es PERMANENTE, no deuda** ([ADR‑029](#),
2026‑09‑13): los cuatro de `FOL/MetaRules.lean` (`imp_intro`, `raa`, `or_elim`, `ex_elim`) son
**irreducibles** —su premisa es una ocurrencia no positiva que el kernel rechaza—, así que siempre
habrá habitantes‑basura. ⇒ **No se persiga limpiarlo.** El cálculo del que **sí** se puede decir
algo por inducción es **`Prf₀`** (cero axiomas habitándolo), y es donde vive `prf0_soundness`.

⭐ **EL CRITERIO QUE DE VERDAD SEPARA NO ES «META‑REGLA» SINO *PREMISA‑FUNCIÓN*** (2026‑09‑12,
medido compilando): un `axiom` cuya premisa es `Γ ⊢ A → Γ ⊢ B` **tiene** que ser axioma —el kernel
rechaza el `inductive`: *«has a non positive occurrence of the datatypes being declared»*—; uno cuya
premisa sea un `Γ ⊢ …` directo o un `∀` sobre otro tipo **podría ser CONSTRUCTOR**.
⚠️ **Y RPP FABRICA uno de los malos**: `ax_list_induction` (`Full/Lists.lean:55`) tiene
`step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)` — **premisa‑FUNCIÓN**, la forma exacta de `raa`.
🔑 **Regla de diseño**: *una regla que se quiere añadir a una relación inductiva se añade como
**CONSTRUCTOR** (o con un inductivo que la envuelva), **nunca** como `axiom`. Un `axiom` **no
extiende el punto fijo: afirma una falsedad sobre él**.*
**LISTA NEGRA** (prohibido inducir): **`FOL.Derives` — DOCE** (8 en FOL: los 6 de `MetaRules` **más** un segundo `dne` en `Theorems/Neg.lean:57` y `forall_not_impl_exists_not` en `Theorems/Quantifiers.lean:115`; +4 en RPP: `ax_induction_prim`, `ax_list_induction`, `ax_axiomsCodeT_eq`, `ax_p_tfa`); **`Prf` — 1** (`prf_axiomsCodeT_eq`). **LISTA BLANCA** (seguro): **`Prf₀`** y **`PrfH`**, cero axiomas habitándolos. ⚠️ *Censo corregido el 2026‑09‑12: la primera versión contaba **nueve** y son **doce**; los dos que faltaban estaban **fuera** de `MetaRules`, que es justo donde nadie miró* | ADR-025 | `grep -rn "^axiom "` y mirar si el tipo **concluye** en el inductivo (ojo: puede concluir dentro de un `∃`, como `ax_p_tfa`). ⬜ No mecanizado |
| **M-10** | ⛔ **Ningún teorema cuyo enunciado hable de INDEMOSTRABILIDAD, indecidibilidad o consistencia puede formularse sobre `⊢`** — sólo sobre **`Prf`**. `axioms ⊢` es **sintácticamente COMPLETO** (`Meta/OmegaStrength.lean`), luego **no es r.e.** y `¬(axioms ⊢ X)` significa **«el cálculo REFUTA X»**, no «no lo demuestra» | ADR-024 | `derives_completo` + `hgi_es_refutar`; y a mano, al enunciar |
| **M-9** | ⛔ **Un `Probe/` que decide un ADR se PROMUEVE a `sondeos/` antes de cerrar ese ADR** — o la decisión queda **sin evidencia versionada**. `Probe/` está en `.gitignore` **a propósito** (es borrador); `sondeos/` es el **resultado**, y se versiona con su fila en `sondeos/README.md`. Si el probe pasó a **producción**, la evidencia es el módulo y no hay nada que promover | [auditoría F‑9](doc/AUDITORIA-2026-09-11.md) · `PLAN-PRUEBAS.md` §2.1 | a mano: todo ADR debe citar su sondeo o su módulo |
| **M-8** | ⚠️ **Subsumir la CLASE no es descargar la OBLIGACIÓN.** Antes de dar por resuelto un frente con «la clase X ya cubre la clase Y», leer **qué obligación queda después**: `numTree_of_isCodeShaped` es **cierto como teorema** y su conclusión —«no hay que cambiar `StdChain`»— **falsa**, porque la obligación que deja (`m ≠ n` con `codeNat` astronómico) **no es descargable** | ADR-022 | `stdChain_proofCode'` + `junk_line_not_stdLine` (`Meta/OmegaReflect.lean` §1ter/§1quater) |
| **M-12** | ⛔ **Empujar `FOL` ANTES que `ROBINSON_PlusPlus`.** La CI de RPP **clona FOL como hermana**; si se empuja RPP primero, la CI compila contra un FOL viejo y `check-footprints` falla con «NO MEDIDO» en los titulares nuevos. ⚠️ Es una **CARRERA**, no un fallo determinista: los cuatro pushes anteriores del mismo día pasaron con el orden malo, y el quinto no. 🔑 *Un fallo intermitente es peor que uno fijo: da verde el número de veces suficiente para que nadie mire el orden.* | — | MEDIDO el 2026‑09‑17, run `35214528037`: dos titulares de `FOL.Skolem0` «NO MEDIDO» con el repo local en verde. Verificación: `gh run list` tras cada pareja de pushes |
| **M-13** | ⚠️ **Una cifra de control se REEJECUTA o se marca con su ALCANCE.** Copiarla de una pasada a la siguiente la convierte en decoracion: «0 warnings» viajo por ADR-057/058/059 siendo la cifra de la `lean_lib FOL` **sola** (reales: 7 en RPP + 4 en FOL). Y su reciproca: **un control sin nada que contrastar no aprueba, se ABSTIENE** — `check_num` sin aparicion imprime «control VACIO» y sale con **0** | ADR-060 §6, ADR-061 §1 | ⬜ falta `check-warnings.bash`; el aviso «control VACIO» ya existe y hay que LEERLO |

> **Sobre `Classical.*`**: este proyecto **no** lo prohíbe (2 usos verificados el
> 2026-07-12). Lo que sí mantiene es la disciplina de **cero axiomas espurios** de M-1.
> El episodio «F7a» (retirada de 7 postulados legacy, en `CHANGELOG.md`) es su
> aplicación práctica. ⚠️ **No revertir F7a**: fue un arreglo de solidez.

---

## ADR-001: Sin dependencia de Mathlib

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: este proyecto no depende de Mathlib.

**Justificación**: objetivo educativo — construir la aritmética de Robinson y sus
extensiones hacia Gödel II desde cero, sobre `FOL` (proyecto hermano local).

**Consecuencias**: toda la infraestructura necesaria se construye desde cero o se
importa de `FOL` (dependencia local, `require FOL from "../FOL"`).

---

## ADR-002: `autoImplicit = false`

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: `moreServerArgs := #["-DautoImplicit=false"]` en `lakefile.lean`.

**Justificación**: las anotaciones de tipo explícitas evitan problemas accidentales de
polimorfismo de universos y hacen el código más legible y mantenible.

**Consecuencias**: todas las variables deben declararse o anotarse explícitamente.

---

## ADR-003: Sistema de bloqueo de archivos

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: usar `git-lock.bash` + `locked_files.txt`/`frozen_files.txt` + hook
`pre-commit` para prevenir ediciones accidentales de módulos terminados.

**Justificación**: las pruebas de Lean 4 son frágiles — cambios pequeños en módulos
terminados pueden romper pruebas dependientes.

**Consecuencias**: el flujo de trabajo exige bloquear/desbloquear ficheros (ver
`AI-GUIDE.md` §20-21). **Nota de auditoría (2026-07-12)**: `locked_files.txt`/
`frozen_files.txt` llevaban vacíos pese a haber 60+ módulos "✅ Completos" — se
corrige aquí también un bug real en `git-lock.bash` (`unlock`/`thaw` no vaciaban la
lista al quitar el último fichero, por el exit code 1 de `grep -Fv` cortocircuitando
el `&&` previo al `mv`).

---

## ADR-004: Convenciones de nombres Mathlib

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: todos los identificadores siguen las convenciones de nombres de
Mathlib4, documentadas en `NAMING-CONVENTIONS.md`.

**Justificación**: consistencia con el ecosistema Lean 4 más amplio.

**Consecuencias**: ver `NAMING-CONVENTIONS.md` para el diccionario completo y las 12
reglas de formación.

---

## ADR-005: Namespaces alineados con directorios

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: cada subdirectorio corresponde a un sub-namespace, reflejando la ruta
del fichero (`Minimal/Theorems/Block1.lean` → `ROBINSON_PlusPlus.Minimal.Theorems.Block1`).

**Justificación**: mapeo 1:1 claro entre sistema de ficheros y jerarquía de
namespaces.

**Consecuencias**: `new-module.bash` debe soportar creación en subdirectorios;
`gen-root.bash` debe escanear recursivamente.

### Addendum 2026-09-09 — medido, y por qué aquí NO se cambia la regla

Los proyectos hermanos **corrigieron ADR-005 a «namespace plano por fichero»** el
2026-07-12 (`lean4-project-template` 76eb5b8), tras auditar Peano y descubrir que
**ningún** fichero de producción seguía el mirroring que la regla mandaba: la práctica
real era `Project.<Concepto>`, un nivel. ⚠️ **Esa corrección NO se propaga a
ROBINSON_PlusPlus**, y la razón es una medición, no una preferencia:

    122 ficheros de `ROBINSON_PlusPlus/` · 109 con `namespace` = ruta exacta

Aquí el mirroring **sí se sigue**, así que la regla se queda como está. Las 13
excepciones, todas identificadas:

| excepción | veredicto |
|---|---|
| `ROBINSON_PlusPlus/Meta.lean` — sin `namespace` | ✅ legítima: es fichero **barril**, sólo `import`s |
| `Meta/LineWFDerives.lean` → `…Meta.ProofChain` | ✅ deliberada: reapertura de namespace para que las referencias cualificadas sigan resolviendo tras el dedup de ADR-019 |
| **los 11 módulos de `Full/`** — todos comparten `ROBINSON_PlusPlus.Full` | ⚠️ **deuda registrada** |

⚠️ **La deuda de `Full/` es exactamente la violación que la auditoría de Peano
encontró** (allí, 16 ficheros de `GroupTheory/` compartiendo namespace entre sí), y la
regla derivada que los hermanos adoptaron aplica igual aquí:

> **Un namespace, un fichero — nunca compartido.** Que dos ficheros «traten del mismo
> tema» no autoriza a fusionar sus declaraciones en un namespace común: oculta qué
> fichero define qué símbolo y arrastra colisiones de nombre.

No se toca ahora: renombrar el namespace de los 11 módulos de `Full/` es un refactor de
radio amplio sobre una capa estable y **fuera de la ruta crítica** (Gödel vive en
`Meta/`). Queda **anotada** para cuando se toque esa capa. El grano más fino dentro de
un fichero (sub-namespaces para sub-conceptos, como `CTree`, `ENS`, `HW` en `Meta/`)
sigue siendo legítimo si se documenta localmente.

---

## ADR-006: Subdirectorios temáticos para la organización de módulos

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: agrupar módulos por bloque temático (`Minimal/`, `Meta/`, `Full/`) en
vez de mantenerlos todos sueltos en la raíz.

**Justificación**: separa el núcleo mínimo de axiomas (`Minimal/`) del andamiaje
meta-teórico creciente (`Meta/`, que a 2026-07-12 tiene 53 módulos) y de la versión
completa (`Full/`).

**Consecuencias**: cada subdirectorio con 2+ módulos requiere un barrel
(`AI-GUIDE.md` §18).

---

## ADR-007: Árbol de documentación `doc/REFERENCE-{tema}.md`

**Fecha**: 2026-04-20 · **Estado**: ✅ **Aceptado e IMPLEMENTADO** (2026-07-12; revisado 2026-08-22)

**Decisión**: `REFERENCE.md` es solo el índice raíz, con el detalle de cada bloque temático en nodos
bajo `doc/REFERENCE-{tema}.md`.

**Justificación**: `REFERENCE.md` había llegado a 103 KB / 1531+ líneas — exactamente el síntoma que
`AI-GUIDE.md` §0.5 describe como señal de que hace falta partirlo.

**Consecuencias**: implementado. Existen **cinco nodos**: `doc/REFERENCE-Kernel.md`,
`-Arithmetic.md`, `-Godelization.md`, `-Full.md`, `-Incompleteness.md`. El índice raíz quedó en
~20 KB.

⚠️ **Corrección 2026-08-22**: este ADR llevaba desde julio marcado como «Propuesto (no implementado)
— no existe todavía directorio `doc/`», y llevaba **más de un mes siendo falso**. Es un ejemplo del
modo de fallo que esta auditoría corrige: *los documentos de estado se actualizan por su banner y no
por su cuerpo*.

**Lección aplicada en la misma auditoría:** la línea `Last updated` de `REFERENCE.md` había degenerado
en un volcado histórico acumulativo de **~20 KB en una sola línea**. Se sustituyó por una marca de
tiempo limpia; el historial es competencia de `CHANGELOG.md`.

---

## ADR-008: Sistema de anotaciones en REFERENCE.md

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: las entradas de REFERENCE.md incluyen anotaciones `@axiom_system` y
`@importance`.

**Justificación**: ayuda a los asistentes de IA a priorizar qué módulos/teoremas
cargar como contexto.

**Consecuencias**: las anotaciones deben mantenerse al actualizar módulos.

---

## ADR-009: `NAMING-CONVENTIONS.md` como fichero separado

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: las convenciones de nombres viven en un `NAMING-CONVENTIONS.md`
dedicado, con un resumen en `AI-GUIDE.md`.

**Justificación**: el diccionario completo con 12 reglas es demasiado extenso para
`AI-GUIDE.md` solo.

**Consecuencias**: si divergen, `NAMING-CONVENTIONS.md` es autoritativo.

---

## ADR-010: Meta-axiomas en `Minimal/Axioms.lean` son meta-teoremas de aritmética, no reglas FOL

**Fecha**: 2026-05-25
**Estado**: **Aceptado — pero su JUSTIFICACIÓN está SUPERSEDIDA por [ADR‑027](#adr-027-la-justificación-de-adr-010-está-refutada--gen-no-es-la-ω-regla-y-sí-podría-ser-constructor)** (2026‑09‑12)

> ⚠️⚠️ **LEER ANTES DE CITAR ESTE ADR.** Su **decisión** (mantener los cinco como `axiom`) sigue en
> pie para cuatro de ellos. Su **justificación** tiene **dos afirmaciones centrales refutadas**:
>
> 1. *«`gen` … es la **ω‑regla** (regla de Büchi)»* — **FALSO**: la ω‑regla toma como premisa
>    `A[n̄]` para cada **NUMERAL**; `gen` la toma para **todo `Term`**. Premisa **estrictamente
>    mayor** ⇒ regla **más débil**.
> 2. *«Su presencia como `axiom` es **correcta e inevitable**»* — **FALSO**: medido compilando,
>    `gen` **SÍ puede ser un constructor** (ocurrencia positiva).
>
> Y la «**soundness práctica**» de su §Justificación es **exactamente el detonador** de
> `../FOL/cuarentena/Inconsistencia.lean`: la premisa vacua no es una excepción rara, es lo que
> hace que `axioms ⊢` sea **completo** y por tanto **no r.e.** ([ADR‑024](#), `Meta/OmegaStrength.lean`).
>
> ⇒ Detalle en **ADR‑027**.

**Contexto**:
`Minimal/Axioms.lean` declara cinco entradas con `axiom`:

```lean
axiom imp_intro {Γ A B} (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)
axiom gen      {Γ A}   (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) : Γ ⊢ Formula.forall A
axiom raa      {Γ A}   (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A
axiom or_elim  {Γ A B C} (h : Γ ⊢ (A ∨ B))
                          (h1 : Γ ⊢ A → Γ ⊢ C) (h2 : Γ ⊢ B → Γ ⊢ C) : Γ ⊢ C
axiom ex_elim  {Γ A C} (h : Γ ⊢ Formula.ex A)
                        (cont : ∀ t, Γ ⊢ substFormula 0 t A → Γ ⊢ C) : Γ ⊢ C
```

Las hipótesis de `imp_intro`, `raa`, `or_elim` y `ex_elim` son funciones **meta-nivel**
en Lean (`Prop → Prop`), no derivaciones objeto. Esto hace que ninguno de los cuatro
sea derivable en general dentro de FOL:

**Contraejemplo** para `imp_intro`: sea `Γ = []`, `A = .atom "P" []`, `B = .atom "Q" []`.
En Lean clásico, `¬ Derives [] P` es verdad (P no es tautología), por lo que
`h : Derives [] P → Derives [] Q` es vacuosamente verdad. Pero `Derives [] (P ⇒ Q)` no
es derivable, así que `axiom imp_intro` sería una extensión *unsound* si se aceptara
como teorema FOL general. Análogamente para `raa`, `or_elim` y `ex_elim`.

**`gen`** tiene una naturaleza distinta: es la **ω-regla** (regla de Buchi). Es un
axioma matemático genuino —válido en el modelo estándar ℕ (aritmética Σ₁-completa)
pero no derivable en ningún sistema de deducción finito. Su presencia como `axiom` es
correcta e inevitable.

**Decisión**:
Mantener los cinco como `axiom` en Lean, con las siguientes clasificaciones:

| Axioma | Clasificación | Acción |
|---|---|---|
| `imp_intro` | Meta-teorema válido para aritmética | Mantener; documentar |
| `raa` | Meta-teorema válido para aritmética | Mantener; documentar |
| `or_elim` | Meta-teorema válido para aritmética | Mantener; documentar |
| `ex_elim` | Meta-teorema válido para aritmética | Mantener; documentar |
| `gen` | ω-regla; axioma matemático genuino | Mantener; no modificar |

**Justificación**:

1. **Soundness práctica**: en todos los usos en `Block1.lean`–`Block4.lean`, la
   hipótesis meta-nivel siempre recibe un argumento genuino (nunca vacuo):

   ```lean
   apply Axioms.imp_intro; intro h_neq   -- h_neq : Γ ⊢ A es una hipótesis real
   apply or_elim h_tric; · intro h_lt    -- h_lt viene de un caso real de la disyunción
   ```

2. **Validez aritmética**: el contexto `Γ` en ROBINSON_PlusPlus siempre es el
   conjunto fijo de axiomas de Robinson Q extendido. En esa teoría Σ₁-completa, las
   implicaciones meta-nivel reflejan derivabilidad real. Los cuatro meta-axiomas son
   **meta-teoremas correctos** para este `Γ` específico.

3. **No derivables en FOL puro**: derivar `imp_intro` desde las reglas objeto de
   `FOL.Derives` requeriría `Classical.em (Derives Γ A)` y luego construir
   `Γ, A ⊢ B` en el caso `¬ Derives Γ A` sin información sobre `B` — imposible.

4. **Alternativa correcta**: la forma demostrable de la introducción de implicación a
   nivel objeto es `Derives.intro_impl : (A :: Γ ⊢ B) → Γ ⊢ (A ⇒ B)`, ya presente en
   FOL — preferirla en código nuevo. La firma de `imp_intro` es distinta (meta-nivel
   vs. objeto).

**Consecuencias**:

- No intentar demostrar estos cuatro como teoremas Lean; solo `gen` podría estudiarse
  más.
- El código nuevo en ROBINSON++ debería preferir `Derives.intro_impl`,
  `Derives.elim_or`, `Derives.elim_ex` (reglas objeto de FOL) sobre los meta-axiomas
  cuando sea posible.
- Si en el futuro se quiere eliminar los meta-axiomas, habría que refactorizar
  Block1–Block4 para usar solo reglas objeto — tarea de alta carga, no prioritaria.
- Los tres axiomas matemáticos de Minimal (`mod2_range`, `mod2_of_even`,
  `add_left_cancel`) son teoremas en Peano y pueden eliminarse si se importa Peano
  directamente; decisión separada.

---

## ADR-011: `subst_lift_cancel_formula` — corrección del enunciado en FOL

**Fecha**: 2026-05-25
**Estado**: Aceptado

**Contexto**:
`FOL/Theorems/Quantifiers.lean` declaraba:

```lean
axiom subst_lift_cancel_formula (f : Formula) (v : Nat) (t : Term) :
    substFormula v t (liftFormula (v + 1) f) = f
```

Este enunciado es **falso** para `t` arbitrario. Contraejemplo:

- `f = .atom "P" [#0]`, `v = 0`, `t = .func "zero" []`
- `liftFormula 1 f = .atom "P" [#0]` (la variable 0 < 1 no se levanta)
- `substFormula 0 zero (.atom "P" [#0]) = .atom "P" [zero] ≠ .atom "P" [#0]`

**Decisión**:
El enunciado correcto y demostrable es:

```lean
theorem subst_lift_cancel_formula (f : Formula) (v : Nat) :
    substFormula v (.var v) (liftFormula (v + 1) f) = f
```

La clave es que `t` debe ser exactamente `.var v`. Con ese `t`:

- `liftFormula (v+1)` levanta variables ≥ v+1; la variable `v` no se toca.
- `substFormula v (.var v)` reemplaza `#v` con `.var v` (identidad) y decrementa
  variables > v.
- El resultado recupera la fórmula original exactamente.

La demostración procede por inducción estructural en `f`, usando:

- `FOL.substTerm_liftTerm_succ` y `FOL.substTerms_liftTerms_succ` (añadidos a
  `FOL/Theorems/Eq.lean`)
- En los casos `forall`/`ex`: `liftTerm 0 (.var v) = .var (v+1)` permite aplicar la IH
  con `v+1`

**Compatibilidad**: todos los usos en `Quantifiers.lean` reescriben hipótesis de la
forma `substFormula 0 (#0) (liftFormula 1 A)`. El nuevo LHS unifica con `v=0`, `f=A`
(ya que `#0 = .var 0`). Los `rw [subst_lift_cancel_formula] at h` existentes no
cambian.

**Consecuencias**:

- `subst_lift_cancel_formula` ya no es un axioma en FOL — es un teorema probado.
  **Verificado 2026-07-12**: el commit `d01f0f1` de FOL ("subst_lift_cancel_formula
  era un axiom FALSO — ahora teorema") aplicó este cambio en `FOL/Theorems/Quantifiers.lean`
  (la copia principal `FOL/`); `FOLPure/Theorems/Quantifiers.lean:18` **sigue
  declarándolo como `axiom`** — pendiente de aplicar el mismo fix ahí (fuera del
  alcance de esta sesión de propagación de plantilla; ver `FOL/DEPENDENCIES.md` sobre
  el estado de sincronización entre `FOL/` y sus variantes paralelas).
- `subst_distrib_and` y `lift_distrib_and` (también axiomas en `Quantifiers.lean`) se
  probaron simultáneamente como `rfl` (hold por definición).
- El build de FOL debe pasar sin axiomas espurios en `Quantifiers.lean`.

---

## Plantilla para nuevas decisiones

## ADR-012: Los códigos de Gödel se representan como NUMERALES, no como árboles `cons`

**Fecha:** 2026-08-18 · **Estado:** aceptada e implementada (`master`)

### Contexto

`axioms ⊢ ⊥`, verificado en el compilador. El símbolo objeto `tcFn` («código del código») tenía dos
ecuaciones que recurren sobre estructuras **incompatibles**: `ax_tc_zero`/`ax_tc_succ` sobre la
estructura **NUMERAL** y `ax_tc_cons` sobre la estructura de **CÓDIGO**. Como `ax_L0_cons_def`
identifica `cons h t = pair h (σt)`, en ℕ el mismo valor es ambas cosas (`cons 0 nil = 2 = σσ0`),
luego `tcFn` de ese valor debía ser dos códigos distintos a la vez.

**Diagnóstico de fondo:** `tcFn` pide a la teoría objeto ver información **intensional** que los
números no llevan — *qué término escribimos* para denotar N.

### Alternativas consideradas y descartadas (todas con evidencia)

| alternativa | por qué no |
|---|---|
| Partir `tcFn` en `tcNum`/`tcCode` | **Insuficiente**: las hojas de un árbol de código son numerales, luego `tcCode` necesitaría las dos recursiones y reproduce el mismo ⊥ |
| Retirar `ax_tc_cons` sin más | **Decapita la diagonalización**: el «código del código» es lo que Gödel exige para `G = β(⌈β⌉)` |
| Relativizar por axiomas (opción B) | **Imposible**: tricotomía + orden prueban `∀x. x=0 ∨ ∃k. x=σk` **sin inducción** |
| Paquete de buena‑formación (`isFormCode`) | **No repara `tc`**: `substfc` pide un reconocedor **extensional**, `tc` una distinción **intensional** |
| Sortes en el kernel FOL | **Cambia el teorema**: pasaría a ser la incompletitud de una teoría bi‑sortida, no de la aritmética |

### Decisión

Escribir `⌈φ⌉` como **numeral** (`numeral (codeNat φ)`) y dejar `tcFn` **sólo** con la lectura
numeral (`ax_tc_zero`/`ax_tc_succ`), que es consistente y tiene modelo explícito en ℕ
(`n ↦ ⌈σⁿ0⌉`). `ax_tc_cons` se retira de `axioms`.

**Coste en axiomas: −1. Ninguno nuevo.**

La pieza que lo hace posible es `prf_formCode_numeral : Prf (formCode φ =eq numeral (codeNat φ))`,
que se apoya en `prf_cons_eval` → `prf_div2_numeral`. La aritmética sale **sin división**: `consN`
se define con **números triangulares**, de modo que `2·consN a b = cpOf ā b̄` es una identidad `Nat`
directa, sin razonar sobre divisibilidad.

### Consecuencias

* **Gödel I sobrevive**: `goedel_first_numeral`, con la base sancionada de siempre **menos
  `tc_cons`**. D1 y el argumento modular **no se re‑demostraron**: son modulares.
* `provCode_transfer` puentea las dos representaciones en **un** paso de Leibniz.
* **D3 y Gödel II salen de la cadena activa** (ver ADR-013).
* ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.

---

## ADR-013: La capa rastreada se pone en CUARENTENA, no se borra

**Fecha:** 2026-08-18 · **Estado:** aceptada e implementada

### Contexto

La reparación de ADR-012 rompe 31 módulos: los 14 tags de `pcc_lineWF_tracked`, `hI_dot`, el chasis
`CTree`, el KIT. Todos dependen de `prf_tc_cons'` — y `pcc_eval_carc (h t)` lo usa sobre argumentos
**ABSTRACTOS**, donde la ecuación es **falsa** bajo la lectura numeral (medido en
`sondeos/PilotoRastreada.lean`: daría un código de cabeza `⌈σ⌉` igual a uno de cabeza `⌈::⌉`).

### Decisión

Mover esos módulos a **`cuarentena/`** (fuera del build, dentro del repo). **No borrarlos.**

### Justificación

Sus teoremas son **formalmente correctos** pero se demostraron sobre una teoría que probaba `⊥`:
eran **vacuos**. Apartarlos no pierde trabajo — reconoce que el suelo cedía. Y el análisis del grafo
mostró que la recuperación es **estructurada**, no un rescate ciego:

* hay un **keystone** (refundarlo desbloquea en cascada — `Sigma1CorePrf` devolvió **10 módulos**);
* la cuarentena se parte en **dos niveles**: argumentos **concretos** (la vía numeral los cubre) y
  argumentos **abstractos** (el muro real);
* los 13 sitios críticos embudan en **5 lemas**.

⚠️ Refundar **cambia enunciados**, no sólo pruebas: los códigos estáticos pasan de
`termCode (formCode φ)` a `termCode (numeral (codeNat φ))`.

Ver `cuarentena/README.md` y `PLAN-FRENTE-A.md`.

---

## ADR-014: La cuarentena se recupera INTERNALIZANDO la evaluación, no reescribiendo los tags

**Fecha:** 2026-08-22 · **Estado:** aceptada e implementada (`master`, HEAD `68fa43c`)

### Contexto

ADR-013 dejó 21 módulos en cuarentena y una pregunta abierta: **cómo se recuperan**. El punto
exacto de rotura está localizado: `pcc_eval_carc (h t)` cerraba con **`prf_tc_cons'`** — el puente
`tcFn (cons h t) = consT (tcFn h) (tcFn t)` a nivel de **código** —, que era consecuencia de
`ax_tc_cons` y **es falso** bajo la lectura numeral para argumentos abstractos.

Dos vías posibles:

| vía | qué exigiría |
|---|---|
| **(i)** reescribir cada consumidor a mano | los 14 tags + `hI_dot` + el chasis, caso por caso, sin garantía de que el patrón se repita |
| **(ii)** reconstruir el puente **dentro de `Prov`** | un solo teorema nuevo, si es que se puede probar |

### Decisión

**Vía (ii).** Construir la **escalera de Σ₁‑completitud internalizada** — `pcc_eval_add`,
`pcc_eval_mul`, el atajo de `div2`, y **`pcc_dot_cons`** — y usar ese último como sustituto de
`prf_tc_cons'` en cada sitio afectado.

```lean
pcc_dot_cons (h t : Term) :
    Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (tcFn (cons h t))))
```

### Justificación

1. **Se puede, y sale barato.** `cons` **no tiene ecuaciones recursivas propias**: `ax_L0_cons_def`
   lo define como `div2 (cantor_poly h (σt))`, o sea `+`, `·` y `div2`, los tres ya internalizados.
   El peldaño resultó ser **ensamblaje, no inducción** — tres fases, verdes a la primera.
2. **El rédito está verificado, no supuesto.** `sondeos/CarcPayoff.lean` reconstruye `pcc_eval_carc`
   con el **mismo enunciado y el mismo footprint**; los pasos 1‑3 del original quedan **intactos** y
   sólo cambia el cierre. ⇒ el keystone `EvalListPrf` es repatriable y **el patrón de arreglo es
   mecánico**: buscar cada `prf_tc_cons'` y sustituirlo por `pcc_rw` + `pcc_dot_cons`.
3. **Un solo teorema frente a 21 reescrituras.** La vía (i) habría exigido entender de nuevo cada
   tag; la (ii) concentra el trabajo en un punto y deja una herramienta (`pcc_rw`) reutilizable para
   toda evaluación futura dentro de `Prov`.

### Consecuencias

* ⚠️ **El transporte cambia de nivel.** Antes era **de código** (fuera de `Prov`, un
  `prf_provCode_congr`); ahora es **interno** (dentro de `Prov`, un `pcc_leibniz_apply`). Cada sitio
  debe aportar el contexto `G` y su ecuación de `substfc` — trivial con los `prf_substtc_*`, pero no
  es un reemplazo textual ciego.
* Se consolidan **dos técnicas** que abaratan todo trabajo futuro en esta capa:
  1. **Todo teorema OBJETO se «dota» gratis** con `prf_congr_tcFn`, **sin entrar en `Prov`** — `tcFn`
     es un símbolo de función, luego es congruente. *Antes de razonar dentro de `Prov`, comprobar si
     el paso es objeto.*
  2. **`substfc` sustituye TODAS las ocurrencias del hueco**, así que un único `pcc_leibniz_apply`
     con contexto `Ac := C[v₀]` cubre las repeticiones. Por eso la fase B fueron 5 pasos y no 15.
* `Meta/DotConsPrf.lean` queda como el módulo **más profundo** del proyecto (L24 de 25, ver
  `DEPENDENCIES.md` §0): depende en cadena de todo lo anterior.

---

## ADR-015: La buena‑formación de códigos se DEFINE en vocabulario existente, no se AXIOMATIZA

**Fecha**: 2026‑08‑24 (decidida) → 2026‑08‑26 (comparación cerrada con medición)
**Estado**: ✅ ACEPTADA · **Supersede** la «decisión pendiente» de ADR‑014 (`isFormCode`, <12 axiomas)

**Contexto**. Los 7 tags de `lineWF` necesitan `pcc_eval_substfc`, que exige un predicado de
buena‑formación sobre códigos. Dos opciones: **(1)** sancionarlo como axiomas objeto
(`isFormCode`/`isTermCode`/`isTermsCode` + inversión, ~15‑18 cláusulas); **(2)** definirlo por
**testigo de parseo** en vocabulario objeto **EXISTENTE**.

**Decisión**: **(2)**.

**Justificación — y la razón de peso NO es el ahorro de líneas.** `ax_axiomsCodeT_eq`
(`Minimal/Axioms.lean:1376`) ancla a **`axioms`** (los 141, `:1199`), **no** a `coreAxioms` (`:922`).
Luego los axiomas de (1) **tienen** que entrar en `axioms` para funcionar; `axiomsCodeT` los
absorbe; el verificador interno los cita; **`provCodeC'` cambia ⇒ G cambia** (141 → ~159).
**(1) no es más cara: es OTRO TEOREMA.** Además, el precedente que se citaba a favor de (1)
—`ax_allIn_nil/cons` y `ax_chainOk_nil/cons` ya sancionados en `codingAxioms`— resultó ser un
argumento a favor de (2): esos átomos **ya existen**, y usarlos cuesta **cero**.

**Consecuencias**.
* **Cero axiomas nuevos y cero símbolos nuevos** en todo el frente (verificado por censo de
  `Term.func` contra `Minimal/Axioms.lean`).
* Corolario registrado: **aunque algún día se sancionara (1), los sondeos de (2) son su certificado
  de conservatividad** — la prueba NO vacua que `ax_lineWF_inv` sólo afirma de palabra.
* El coste se paga en **trabajo de reflector**, no en sanción. Medido: ≈1,4‑1,6× de lo ya
  construido, no 3×.
* Proyección completa en `doc/REFERENCE-Incompleteness.md` §3.27.

---

## ADR-016: El predicado se PARTE en tres, y la partición es la CONDICIÓN de la inducción

**Fecha**: 2026‑08‑26 · **Estado**: ✅ ACEPTADA

**Contexto**. El primer diseño (`sondeos/ParseWitness.lean`) usó **un solo** predicado de 12
disyuntos que fusionaba las formas de código de FÓRMULA (tags 2‑9) con las de TÉRMINO (0‑1), `nil`
y el `cons` genérico. ⚠️ **Error trazable**: la restricción R‑6 ya decía «dos predicados mutuamente
recursivos», y se diseñó uno fusionado sin reconciliarlo.

**Decisión**: partir en `isFormCode` (8 disyuntos) / `isTermCode` (2) / `isTermsCode` (2).

**Justificación**. No es reparar un defecto: **es la condición para que la inducción exista**. El
cuadre es **8↔8 / 2↔2 / 2↔2** con las ecuaciones de `substfc`/`substtc`/`substtsc`;
`pcc_eval_substfc` se atasca **porque 12 ≠ 8**. Y el fusionado **no discriminaba**: `prf_isFC_junk`
compila — `implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ`, cuyas dos «subfórmulas» son códigos de TÉRMINO, **pasaba** el
reconocedor. El partido lo **REFUTA** (`crit_isFC_junk_REFUTED`, net‑0).

**Consecuencias**. El total de disyuntos **no crece** (12 = 8+2+2): es partición, no recubrimiento.
A1/A2 sobreviven al 100 % y ~527 líneas de A3 son byte‑idénticas. **Lección de método**: releer la
restricción de diseño ANTES de diseñar, no tras compilar.

---

## ADR-017: El testigo va ABIERTO — no se ancla en casilla, y no se acota

**Fecha**: 2026‑08‑27 (abierto) → 2026‑08‑29 (clausura) · **Estado**: ✅ ACEPTADA

**Contexto**. El descenso y la discriminación estaban probados sólo para testigo **CERRADO**, y el
que entrega un `∃` objeto es `#0`, que no lo es (`liftTerm 0 #0 = #1`). La salida propuesta era
meterlo en una **casilla** de la línea — pero `ind`/`listInd` tienen `lenc = 3` y no la tienen, así
que habría cambiado su **ARIDAD**, tocado `premsOf` y la construcción de D1, y **requerido sanción**.

**Decisión**: **no anclar el testigo en ninguna parte**, y **no acotar** el número de lifts.

**Justificación**. (a) La clausura era un **artefacto de la ruta de prueba**: `wfAllT` ya lleva el
lift explícito y `wfAllT_closed` sólo existía para quitarlo; llevándolo,
`FOL.substTerm_liftTerm` vale **para cualquier `p`** (`sondeos/TestigoAbierto.lean`,
`DiscriminaTestigoAbierto.lean`, con instancias en `#0`). (b) **Acotar es circular**: acotar y la
clausura de un paso son **inter‑construibles**, probado en las dos direcciones
(`AcotarEsLaMismaObligacion.lean`). (c) La clausura real sale **quitando `wTs`**: con una sola
lista, `liftsc 0` **es** el map posicional sobre lista arbitraria, vía `prf_list_induction`
(`ClausuraLiftSinWTs.lean`).

**Consecuencias**. **`ind`/`listInd` no cambian de aridad; no hace falta sanción.** ⚠️ Contrapartida
medida: sin `wTs` el reconocedor se **debilita** (la lista de argumentos ya no está obligada a ser
cadena `cons` terminada en `nil`). ⚠️ Y los **dos reconocedores** —el reflejado con `wTs` y el
plano sin él— están hoy **desconectados**: nada los relaciona.

---

## ADR-018: El descenso es UNA inducción con conclusión CONJUNTIVA, y la guarda va DENTRO de `Φ`

**Fecha**: 2026‑08‑30 · **Estado**: ✅ ACEPTADA

**Contexto**. `pcc_eval_liftc` (el `DESCENSO`) recorre a la vez **términos** y **listas de
argumentos**. La lectura natural —y la que estaba escrita— era que hacían falta **dos inducciones
mutuamente recursivas**, como en R‑6. Además, `prf_strong_induction` impone el gate
`liftFormula 1 Φ = Φ`, que prohíbe dejar libre nada por encima del índice de inducción, y el
`Φ` del consumidor (`Paso2Ind.PHI`) **no llevaba** la guarda `hasWit s` que el descenso necesita.

**Decisión**. (a) **Una sola** inducción fuerte, con la conclusión **conjuntiva**
`PHI := ∀w. (isTC1 w #0 ⇒ targetLift #0) ∧ (isTsC1 w #0 ⇒ targetLiftsc #0)`, y `w` cuantificado
**dentro** de `Φ`. (b) La guarda se mete **dentro** de `Φ` (`PHI_guarded`), no se pasa por fuera.

**Justificación**. (a) Tres estrategias independientes convergieron **por separado** en este mismo
motivo, y las tres cerraron: el término y su lista de argumentos viajan juntos, de modo que la
conjunción hace de par mutuo sin necesidad de recursión mutua. (b) La guarda `hasWit c` es un `∃`
**interno**, así que meterla en `Φ` **no añade binder exterior** y el gate sigue pasando —
verificado compilando `PHI_guarded_lift`. La alternativa (pasarla como hipótesis externa) habría
exigido un lema de lifting de **derivaciones**, que **no existe** en el proyecto (ya medido en
ADR‑017). Y no había atajo por el consumidor: se **probó** que el `s` que ve `paso2_caso_forall`
es `#0`, luego pedir `hLift` sólo para él es pedirlo para todo `s`.

**Consecuencias**. `pcc_eval_liftc` existe con `w`/`s` **abstractos** y footprint net‑0, y
desde **2026‑09‑04 está EN PRODUCCIÓN**: `Meta/EvalLiftcPrf.lean` (rama B2, §3.34).
⚠️ Contrapartida: `Φ` es ahora **guardado**, luego **todo consumidor aguas abajo tiene que
suministrar `hasWit`** — barato, porque `CRIT_hasWit_real` da testigo para todo término y
`CRIT_hasWit_lift` lo propaga al subcódigo, pero **no es gratis** y hay que declararlo en cada
composición. ⚠️ Y el patrón **no se extiende sin más** a `pcc_eval_substtc`: allí la guarda es
**abierta** (tricotomía con `v` abstracto, a reflejar dentro de `Prov`) y aparece `varc (pred n)`,
que pide un `pred` dotado inexistente. Ver `doc/REFERENCE-Incompleteness.md` §3.28.

---

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]

---

## ADR-019: Cuando el sondeo SUBSUME a producción, baja el GENERAL — no subas el corolario

**Fecha**: 2026‑09‑04 · **Estado**: ✅ ACEPTADA · **Descubierta al promover B2** (§3.34.2)

**Contexto**. Al promover un sondeo aparece un patrón recurrente: un lema del sondeo resulta ser
**más general** que uno que producción ya tenía. En B2 pasó dos veces:

| general (del sondeo) | particular (ya en producción) |
|---|---|
| `substF_targetLift` | `LiftcCodePrf.substF_targetLift_hole` (su caso `v:=0`, `s:=#0`) |
| `prf_isTermCodeE1_of_boundedIn` | `SinWTs.prf_crit_In_rejects_open1` |

La reacción natural —y la que estaba escrita en el plan— es **dejar el general en el módulo
nuevo y reescribir el de producción como corolario suyo**.

**⛔ Eso es IMPOSIBLE, y no por estilo: por el grafo.** El módulo nuevo **importa** a aquel en
que vive el particular. Un corolario allí que dependa del general de aquí es un **ciclo de
imports**. Y el particular no puede simplemente irse: tiene consumidores **dentro de su propio
módulo** (`substF_targetLift_hole` en tres sitios de `LiftcCodePrf`, incluido un simp‑set).

**Decisión**. **Baja el GENERAL** al módulo donde vive el particular, y deja el particular como
corolario **allí mismo**. La dirección del grafo manda: lo genérico vive arriba, lo específico
abajo — nunca al revés.

**Cómo se comprueba antes de mover** (no se supone):
1. Inventario de las constantes que usan enunciado y prueba del general — mejor con `#deps`
   sobre el término de prueba, no leyendo los `import`.
2. Cada una, ¿está disponible **antes** del punto de destino? La más tardía fija el sitio.
3. Prueba compilada en un `Probe/` que importe **sólo lo que importa el módulo de destino** —
   ⚠️ **ni el módulo nuevo ni el barrel**, o la prueba no demuestra nada.

**Consecuencias**.
* ⚠️ **Al bajar hay que quitar el nombre del `export` y del bloque `#print axioms` del módulo
  de origen.** Exportar o imprimir una constante que el módulo ya no declara es **error duro de
  elaboración**, y **no lo salva ningún `open`**. Es el fallo que más veces se coló en B2.
* La cualificación se simplifica sola: `prf_isTermCodeE1_of_In` necesitaba `SinWTs.impT`
  cualificado a mano en el módulo del descenso (que abre los dos namespaces); dentro de
  `SinWTs` el nombre a secas ya es el correcto.
* ⚠️ **B3 lo confirmó en vivo, y el error casi se cuela.** El plan de `SubstfcPlanos` ponía el
  general `prf_substtc_binK_at` en `LiftcCodePrf` prometiendo **tres** corolarios — pero
  `LiftcCodePrf` **importa** `CodeCtorKit`, así que el tercero era **inalcanzable por
  construcción**. Contabilidad medida: **un** lema de ahorro, no tres. Con el general en
  `CodeCtorKit`, los tres. **Tarifa pagada**: subir los tres `prf_substtc_termCode_*`, quitarlos
  del bloque `export` de `LiftcCodePrf` y **reapuntar una referencia cualificada** que se rompía
  sin avisar hasta el build.
* 🔑 **Y B3 destapó la forma más escurridiza del problema**: `psi_substtc_l1` **no era una
  copia de `psi_lift_form`: era una INSTANCIA** (`Φ := PHIsubsttc`). Invisible al índice **por
  nombre** (el nombre difiere) y al comparador de **enunciados normalizados** (el enunciado
  también). Sólo se ve preguntando *«¿existe ya un genérico del que esto sea instancia?»* — que
  **no es una pregunta que un censo conteste**. Contramedida: cuando aparezca una escalera
  (`_l1`/`_l2`/`_l3`), mirar si el escalón 1 ya está arriba **antes** de promover los otros.
* El mismo criterio decidió las **seis piezas genéricas** que subieron aguas arriba en B2:
  si un lema no menciona el vocabulario del frente, no es del frente, y escondido en el módulo
  del descenso queda **invisible** para los sondeos que lo tienen copiado a mano — `PSI_inst`
  estaba duplicado en **siete**.

---

## ADR-020: Los 7 esquemas de sustitución llevan la guarda DENTRO — y para eso las guardas BAJAN a `Minimal`

**Fecha:** 2026-09-05 · **Estado:** aceptado · **Sanción del autor:** explícita (vía C)
**Corrige el argumento de coste de:** §3.27.1 y la parte correspondiente de ADR-015

### Contexto

Los 7 tags de `lineWF` que faltan para cerrar `pcc_lineWF_tracked` —`q1` (9), `q2` (10), `q3` (11),
`leibniz` (13), `ind` (18), `qconf` (19), `listInd` (20)— son los que reconstruyen su conclusión
con `substfc`/`liftfc`. Reflejarlos exige evaluar esos operadores, y la evaluación
(`pcc_eval_substfc`, `pcc_eval_liftc`) **pide una guarda de buena formación** del código:
`hasWitF` en la ranura de fórmula, `hasWit` en la de término.

De dónde sale esa guarda se midió en tres vías (§3.32.2), y **dos están REFUTADAS con prueba
compilada**, no «no conseguidas»:

* **(A) derivarla del antecedente `lineWF t`** — REFUTADA. Se construyó una línea basura que
  satisface `lineWF` (con el `prf_lineWF_q1` de **producción**), tag 9, `lenc = 4̄`, que cumple
  **la condición estructural entera**, y cuya casilla 2 es un **código de variable**. De ahí sale
  `⊥`. La causa: la condición entera del tag 9 es **una sola ecuación de `carc`**, no menciona
  buena formación, y `ax_lineWF_inv` sólo habla de la **etiqueta**.
* **(B) cargarla colgante por la cadena** — REFUTADA, y peor:
  `M5_LA_GUARDA_COLGANTE_IMPLICA_BOT` demuestra que la hipótesis es refutable, luego la D3
  resultante sería **vacua**, no condicionada.

### Decisión

**Se enmiendan los 7 esquemas metiendo la guarda dentro del bicondicional**, en su versión
**MÍNIMA**: se guarda **sólo las ranuras que aparecen bajo `substfc` o `liftfc`** — las únicas
cuya evaluación la necesita. Las que sólo aparecen bajo constructores (`implc`, `forallc`, `exc`,
`eqc`) no llevan nada, para dejar el verificador lo más completo posible.

| tag | guarda añadida | conjuntos |
|---|---|---|
| `q1` (9) | `hasWitF (nthc · 2̄)` y `hasWit (nthc · 3̄)` | 2 |
| `q2` (10) | `hasWitF (nthc · 2̄)` y `hasWit (nthc · 3̄)` | 2 |
| `q3` (11) | `hasWitF (nthc · 3̄)` — sólo la que va bajo `liftfc` | 1 |
| `leibniz` (13) | `hasWitF (nthc · 2̄)`, `hasWit (nthc · 3̄)`, `hasWit (nthc · 4̄)` | 3 |
| `ind` (18) | `hasWitF (nthc · 2̄)` — los args de término son **cerrados** | 1 |
| `qconf` (19) | `hasWitF (nthc · 2̄)` | 1 |
| `listInd` (20) | `hasWitF (nthc · 2̄)` | 1 |

**11 conjuntos nuevos**, 7 de sorte fórmula y 4 de sorte término, anidados a la derecha
(`G₁ ∧ (G₂ ∧ ecuación)`) para que `hcond_absorbe_extra` se aplique en cascada.

### El precio estructural: el CICLO DE IMPORTS (ADR-019) en DOS capas

**Capa 1.** `hasWitF` y su cono se escribieron en `Meta/CodeWitnessPrf.lean`. Los esquemas viven en
`Minimal/Axioms.lean`, que **sólo importa `FOL.*`**. Mencionarlos desde allí es un ciclo.

Luego **las 21 definiciones del cono bajan a `Minimal/Axioms.lean`**: `shapeNul` `shapeUn`
`shapeBin` `argsInBody` `argsIn` `isTermCodeE1` `wfAll1Body` `wfAll1` `isTC1` `hasWit` `lorAll`
`clBot` `clAtom` `clEq` `clBin` `clUn` `isFormCodeE2` `wfAllFBody` `wfAllF` `isFC1` `hasWitF`.
Todas sus hojas (`In` `lt` `land` `lor` `numeralM` `cons` `nil` `lenc` `nthc` `carc` `liftTerm`)
ya estaban allí o en `FOL`, así que el descenso es mecánico y **no cambia ni un enunciado**.

🔑 **Y NO se duplican**: `CodeWitnessPrf` las recupera con `export ROBINSON_PlusPlus.Minimal.Axioms
(…)` dentro de `SinWTs` y de `ENS`. Son **la misma constante**, no una copia con puente `rfl`
—verificado: `#print axioms CodeWitnessPrf.ENS.hasWitF` imprime `Minimal.Axioms.hasWitF`, y los
`example … := rfl` pasan el kernel—, así que las **5 310 referencias** medidas (4 749 en
`sondeos/`, 428 en el propio módulo, 133 en otros módulos de `Meta/`) siguen resolviendo **sin
tocar ninguna**. Duplicarlas habría sido la enfermedad que ADR-019 describe.

**Capa 2 — la que la medición previa no vio.** Los siete `prf_lineWF_*` —el codificador de D1, la
dirección de vuelta del bicondicional— viven en `Meta/ReprPrf.lean`, que está **estrictamente
aguas arriba** de `CodeWitnessPrf`. No pueden **pagar** la guarda (`prf_hasWitF_real` está abajo);
sólo pueden **arrastrarla como hipótesis**. Eso obliga a bajar también **nueve lemas de
fontanería** `substF_*` (`argsIn`, `isTermCodeE1`, `wfAll1`, `isTC1`, `hasWit`, `isFormCodeE2`,
`wfAllF`, `isFC1`, `hasWitF`): son los que hacen a `substFormula` atravesar las guardas, y sin
ellos la congruencia Leibniz no se puede enunciar arriba. Los `liftF_*` **no** bajan: su cadena es
independiente. ⚠️ `substF_hasWitF` **no existía en producción** — estaba duplicada en
`sondeos/MedirC_Carga.lean` y `sondeos/MedirC_Enmienda.lean`. Ahora es una sola constante.

**La capa cierra**, y es lo que hace viable la vía: sólo `ReprPrf` y `ForallElimCodePrf` están
aguas arriba de `CodeWitnessPrf`. Los otros cuatro consumidores —`PropCodePrf`, `LineWFCases`,
`LineWFDerives`, `Representability2Prf`— son **incomparables** con él (ni lo importan ni son
importados), así que pueden importarlo y **descargar** la guarda. La obligación viaja hacia abajo
hasta donde hay códigos reales.

Firma resultante, por ejemplo `q1`:

```lean
theorem prf_lineWF_q1 (concl A t : Term) (hwA : Prf (hasWitF A)) (hwt : Prf (hasWit t)) :
    Prf (lineWF (cons concl (cons (numeralM 9) (cons A (cons t nil)))) ⇔
      (concl =eq implc (forallc A) (substfc zero t A)))
```

🔑 **El enunciado viejo era FALSO tras la enmienda, no sólo incompleto**: afirmaba el bicondicional
para `A` y `t` **arbitrarios**, que es exactamente lo que la línea basura de la vía (A) explotaba.
Que rompa es la señal de que la enmienda hace lo que promete.

### Qué cambia, y qué NO

**NO cambia el enunciado de nada.** Ni D1, ni D2, ni D3, ni Gödel I, ni Gödel II: los cinco están
escritos sobre `Prf`, `provCodeC'` y `lineWF`, que son los mismos símbolos. **Ni la sentencia G**:
`godelCN` tiene 483 dependencias transitivas y **ninguna es `axioms`** (§3.32.1), porque
`axiomsCodeT`, `lineWF`, `chainOk` y `runFn` son átomos **opacos**. Y las listas **no cambian de
longitud**: se sustituyen 7 de las 141, no se añade ninguna (`coreAxioms` 34, `codingAxioms` 107,
`axioms` 141). El inventario de `axiom` de Lean sigue en **7**.

**Cambia qué demuestra `Prov`**, en una sola dirección: `lineWF` se vuelve **estrictamente más
exigente** en esos 7 tags, luego el verificador acepta **menos** líneas.

* **Solidez**: mejora o queda igual. Nada sólido se vuelve insólido.
* **Completitud (D1)**: aquí va la factura. El **enunciado** de D1 no cambia, pero su **prueba**
  debe descargar los 11 conjuntos para cada línea que el codificador emite con esos tags. Son
  líneas **concretas**, así que la obligación es sobre códigos concretos — y **las dos piezas ya
  estaban en producción**: `prf_hasWitF_real (φ) : Prf (hasWitF (formCodeM φ))` y
  `CRIT_hasWit_real (t) : Prf (hasWit (termCodeM t))`. Es la **rama A**, cerrada en agosto,
  pagando una factura que entonces no existía. `sondeos/MedirC_Enmienda.lean` ya lo había
  demostrado para la línea q1 real (`guardQ1_se_paga`) y no se sabía.
* **El chasis NO se rehace**, contra lo que decía §3.32.2: `pcc_lineWF_tracked_of_schema` ya es
  **genérico en `C`**, y `hcond_absorbe_extra` (`sondeos/SegundoMuro.lean`) es **genérico en `P`**,
  compilado y net-0. Encajan tal cual. `pcc_lineWF_tracked_modulo_7` tampoco se toca: sus 7
  hipótesis conservan la firma exacta.
* **Trabajo genuinamente nuevo**: el reflector del conjunto extra —la reflexión Σ₁ de `hasWitF`
  sobre un código **abstracto**—, que necesita el lema previo **`∀t. hasWit (tcFn t)`**, medido e
  **inexistente** en producción y en los 57 sondeos. Receta precedentada (`pcc_eval_lenc` más
  `prf_strong_induction`), no técnica nueva.
* **De propina, la rama F se abarata**: `derives_lineWF_neg_thy_of_not_prf` y compañía demuestran
  hechos **negativos** sobre `lineWF`, y un `lineWF` más fuerte es más fácil de refutar.

### Por qué esto no debilita el teorema

Lo único que la enmienda le quita a `Prov` son **líneas basura** — del tipo que la vía (A)
construyó y compiló, con la ranura 2 ocupada por un código de variable. Un verificador de verdad
comprueba que su carga sean códigos; el nuestro no lo comprobaba. **La enmienda no recorta la
aritmetización: le quita una generosidad que no debería tener.** Y que D1 sobreviva es
precisamente la garantía de que no recorta: `Prov` sigue reconociendo **todas** las demostraciones
reales.

⚠️ **Con precisión**: la refutación de (A) prueba que el verificador acepta líneas cuya carga no
codifica nada. **No** prueba que la teoría actual sea insólida — de eso no hay medición. Son cosas
distintas y no conviene confundirlas.

### Consecuencia documental

**El argumento de coste que se venía repitiendo para descartar esta vía era FALSO** y hay que
dejar de repetirlo: «enmendar un esquema cambia G» es incorrecto, medido sobre el `Environment` de
Lean y no por lectura. Queda corregido en §3.32.1, y esta ADR lo hereda.

### Addendum (2026-09-05, al ejecutar): lo que la ejecución CORRIGIÓ de esta ADR

Esta ADR se redactó antes de aplicar la enmienda. Tres cosas cambiaron al hacerlo:

**1. El ciclo de imports tenía TRES capas, no una.** Además de bajar las 21 guardas (capa 1), hubo
que bajar **9 lemas de fontanería `substF_*`** porque los 7 `prf_lineWF_*` viven en `ReprPrf`,
**aguas arriba** de `CodeWitnessPrf`: no pueden PAGAR la guarda, sólo arrastrarla (capa 2).
⚠️ `substF_hasWitF` **no existía en producción**, sólo duplicada en dos sondeos.

**2. 🔑 La tercera capa se resolvió BORRANDO, no moviendo.** `CodeWitnessPrf` estaba en el FONDO
del DAG (veía 62 módulos, sólo 3 lo veían), lo que hacía inalcanzables `prf_hasWitF_real` y
`CRIT_hasWit_real` desde D1 y parecía obligar a mover **148 de sus 178 declaraciones**. Medido de
verdad: el módulo **entero** necesita **10 de sus 36 imports**; **26 eran lastre**. Y el único que
lo hundía por debajo de `Representability2` era `Sigma1CorePrf`, **por un solo nombre**: `objList`,
tres líneas. Bajada `objList` a `Minimal` y podados 27 imports, el módulo pasa a ver 20, sube por
encima de `Representability2`, y **no se movió ni una declaración**.
⇒ **Regla**: cuando un módulo parezca estar en el sitio equivocado del DAG, medir **qué imports
usa de verdad** antes de mover código. La posición suele ser HISTÓRICA, no necesaria.

**3. El criterio que decide la viabilidad: PAGAR vs ARRASTRAR.** Cada sitio tocado por la enmienda
o **descarga** la guarda (tiene códigos reales) o la **arrastra** como hipótesis. Arrastrar hasta
arriba es exactamente la «guarda colgante» de la vía (B), refutada porque la D3 resultante sería
**vacua**. ⇒ una guarda sólo se arrastra si algún consumidor concreto puede pagarla.

**Y una pieza nueva que la ADR daba por lejana ya está**: `∀t. hasWit (tcFn t)`
(`Meta/HasWitTcFnPrf.lean`, net-0 puro), probada por **inducción OBJETO** — la única ruta posible,
porque `tcFn` es un átomo opaco con sólo `ax_tc_zero`/`ax_tc_succ` vivos. Paga las guardas de
término en todos los sitios donde el testigo es un código punteado.

**Estado al cierre: parada CONOCIDA en `Meta/MpCodePrf.lean`.** De sus 10 sitios, **4 son gratis**
(piden `hasWitF` de códigos que ya son `formCode` de algo, incluido `forallc (formCode φ)`, que
**es** `formCode (∀φ)`), y **6 piden una sola pieza que no existe**:
`prf_hasWitF_substfc : Prf (hasWitF c) → Prf (hasWit s) → Prf (hasWitF (substfc v s c))`.
Las guardas de TÉRMINO ya están resueltas: los 11 módulos consumidores pasan `tcFn …`.
⚠️ El build se detiene ahí, así que los módulos de aguas abajo aún no se han evaluado: aparecerán
más sitios, pero **ésos pagan** en vez de arrastrar.

### Addendum 2026‑09‑06b · 🏁 la pieza existe, y el camino al verde está MEDIDO

`prf_hasWitF_substfc` **está probada** (`sondeos/ClausuraSubsttc.lean`, 1 911 l., 0 sorrys, net‑0
puro), junto con la mitad TÉRMINO `prf_hasWit_substtc` que sus casos `atom`/`eq` consumen.
**Ya no queda ninguna pieza matemática por demostrar para cerrar la vía C.** Detalle en §3.38 de
`doc/REFERENCE-Incompleteness.md`.

**La ADR se cumple, y esto lo confirma el compilador**: la parada son **10 errores**, todos en
`Meta/MpCodePrf.lean`, todos la misma aplicación. La familia `pcc_thm_inst*`/`pcc_axiom_inst*`
**arrastra** la guarda de testigo (`wᵢ` es un `Term` arbitrario: ahí no se puede pagar), y los
**~40 sitios** de la zona bloqueada **pagan** casi todos con `prf_hasWit_tcFn`, porque el testigo
que pasan es `tcFn …`. Es exactamente el criterio *pagar vs arrastrar* funcionando: se arrastra
sólo donde hay un consumidor concreto que descarga.

⚠️ **Y una deuda que la ADR genera y hay que saldar al promover**: el árbol rojo ha obligado a
**reproducir tres piezas** que existen en producción pero son inalcanzables
(`prf_nil_or_cons` en `EvalLiftcPrf`, la fusión de testigos en un sondeo, y `PrfH_congr_substfc3`
en `BdAllIntroPrf`). Al promover, la copia buena es la que baja, y las de aguas abajo se borran
(⛔ ADR‑019).

### Addendum 2026‑09‑06c · ① y ② ejecutados — y la ADR confirmada por el compilador

`Meta/SubstfcWitnessPrf.lean` en producción y **`MpCodePrf` VERDE**. Detalle en §3.39.

**La mitad CÓDIGO se paga ENTERA en `MpCodePrf`**, con tres lemas: `prf_hasWitF_fc_lift`
(`⌜φ⌝` y `forallc ⌜φ⌝`, que **es** `⌜∀φ⌝`), `prf_hasWit_liftc_lift` (`CRIT_hasWit_lift`, que
existía desde B1) y `prf_hasWitF_substfc_lift` (la clausura nueva). **La mitad TESTIGO se
arrastra**, porque `wᵢ` es un `Term` arbitrario — y el primer módulo que la recibe,
`Meta/EvalArithPrf.lean`, la **paga** en dos de sus cuatro sitios con `tcFn`. El criterio
*pagar vs arrastrar* funcionando en vivo.

⛔ **ADR‑019 tres veces en la misma pasada**: al promover no se dejan duplicados de lo que el árbol
rojo había obligado a reproducir. `psi_lift_form4`/`PSI_inst4` **suben** a `StrongInductionPrf`
(son maquinaria genérica de la inducción fuerte); `PrfH_congr_substfc3`/`prf_congr_substfc3`
**bajan** de `BdAllIntroPrf` a `NumCodeClosedPrf`; `nilOrCons`/`prf_nil_or_cons` **bajan** de
`EvalLiftcPrf`. ⚠️ Los dos donantes están aguas abajo y no compilan: esos borrados —incluido
quitar el nombre del `export` y del `#print axioms`, que si no es error duro— quedan como **deuda
anotada, no verificada**.

⚠️ **Y un frente que la medición anterior no había contado**: `pcc_leibniz_code`, **6 sitios**.
Pide `hasWitF Ac` con `Ac` abstracto, así que arrastra salvo donde el `Ac` sea un código real.

### Addendum 2026‑09‑07 · 🏁 ADR‑020 CERRADA — el árbol compila con la enmienda

```
Build completed successfully (132 jobs) · 112 módulos · 0 sorrys · 7 `axiom` de Lean
```

Los **29 módulos** que bloqueaba `MpCodePrf` están cerrados. Detalle en §3.38–§3.40 de
`doc/REFERENCE-Incompleteness.md`.

**✅✅ LA CONDICIÓN QUE SOSTENÍA LA DECISIÓN, COMPROBADA — y la razón es ESTRUCTURAL.**
La ADR se aceptó sobre el criterio *«una guarda sólo se arrastra si algún consumidor concreto puede
pagarla»*, y con el riesgo explícito de que si llegaba colgando hasta D3 la D3 resultante sería
**vacua** (que es por lo que la vía (B) está refutada). Medido con el compilador:

* `d3_prf_of_chainOkDot` conserva su firma **exacta**.
* `pcc_lineWF_tracked_modulo_7` y `pcc_lineWF_tracked_of_branches` también, y sus 7 hipótesis
  pendientes siguen siendo las 7 formas **sin guarda**.

🔑 El motivo no es suerte: la enmienda mete la guarda **DENTRO del `⇔` OBJETO**, así que al
reflector le llega como **conjunto objeto** extraído de `lineWF t`, no como hipótesis Lean — y por
tanto **no puede** aparecer en su firma. Esa es exactamente la propiedad que hacía viable la vía C
frente a la (B), y hasta hoy era un argumento; desde hoy es una comprobación.

⇒ **Corolario**: la garantía de `pcc_lineWF_tracked_modulo_7` («cerrar esos 7 reflectores cierra
`pcc_lineWF_tracked`, y no hay nada más aguas abajo») **sigue valiendo bajo la enmienda**, sin
cambiar una línea del ensamblaje.

✅ **Y las dos deudas que la ADR generó vía ADR‑019 quedan saldadas**: los borrados en
`BdAllIntroPrf` (`PrfH_congr_substfc3` + su `export`) y en `EvalLiftcPrf` (`nilOrCons`/
`prf_nil_or_cons` + su `export` + su `#print axioms`), que se habían hecho sin poder compilar,
compilan sin un solo `unknown identifier`.

**Lo que NO cambió, y conviene repetirlo**: 7 `axiom` de Lean (la cifra **de entonces**; hoy **6**), 141 axiomas objeto (se **sustituyen**
7 de los 141, no se añade ninguno), y ni D1, ni D2, ni D3, ni Gödel I/II, ni la sentencia `G`
cambian de enunciado.

### Addendum 2026‑09‑07b · el CHASIS de la deuda, en producción — y la forma real de la enmienda

`Meta/LineWFGuardPrf.lean` (nuevo, net‑0 **puro**: `[propext, Classical.choice, Quot.sound]`).
Detalle completo en `doc/REFERENCE-Incompleteness.md` §3.41.3–§3.41.5.

**`hcond_absorbe_extra` entra en el build.** Es el lema sobre el que se **aceptó esta ADR** —el
que garantiza que el chasis absorbe el conjunto extra— y hasta hoy vivía en **cinco copias fuera
del build**: `sondeos/SegundoMuro.lean`, `sondeos/MedirC_Carga.lean`,
`sondeos/MedirC_Enmienda.lean` y dos de `Probe/`. Una decisión no debería descansar sobre una
pieza que el árbol no compila; ya no lo hace.

⭐ **La deuda queda reducida a DOS lemas genéricos, no siete.** `hcond_absorbe_cascade` absorbe
la cascada entera por inducción sobre la lista de casillas, así que el índice de casilla es un
parámetro y los 7 tags se cierran a la vez. Las dos obligaciones —`DEUDA_hGuardT` y
`DEUDA_hGuardF`— quedan **enunciadas y no postuladas** (`abbrev` de `Prop`, idioma de
`Meta/Sigma1BoundedPrf.lean`): **cero `axiom` nuevos**, el inventario sigue en 7.

⚠️ **Corrección a cómo se venía describiendo la enmienda en este ADR.** No añade «la guarda» ni
«un par de guardas»: añade entre **una y tres**, **anidadas a la derecha** delante de la
condición estructural, y el orden es `hasWitF` antes que `hasWit`:

| tag | `lenc` | guardas, en orden |
|---|---|---|
| `q1` (9), `q2` (10) | 4 | `hasWitF`@2, `hasWit`@3 |
| `q3` (11) | 4 | `hasWitF`@3 |
| `leibniz` (13) | 5 | `hasWitF`@2, `hasWit`@3, `hasWit`@4 |
| `ind` (18), `qconf` (19), `listInd` (20) | 3 / 4 / 3 | `hasWitF`@2 |

7 `hasWitF` + 4 `hasWit` = los **11 conjuntos nuevos** que declara esta ADR. ✔ El recuento era
correcto; la **forma** estaba mal descrita, y modelarla como un par habría producido un lema
correcto sobre la fórmula equivocada — que además habría compilado. §2.1 del módulo lo
**comprueba** con siete `rfl` contra `Minimal/Axioms.lean`: si la ADR cambiara el orden de las
guardas, un índice de casilla o el anidamiento, esos siete dejan de compilar.

**Lo que sigue abierto** (y no lo cierra este addendum): el recorrido de `isTC1`/`isFC1` bajo el
`∃`. Los átomos ya están (`pcc_lt_tracked`, `pcc_eq_tracked`, con términos **abstractos**), el
`∀` acotado también (`pcc_bdAll_intro`) y el `∃` sin cota también
(`pcc_exIntro_code_open`); falta la disyunción de formas y el `argsIn` interno. Es un
ensamblaje, no una inducción nueva.

### Addendum 2026‑09‑08c · 🏁 media cascada DESCARGADA — `DEUDA_hGuardT` probada

`pcc_hGuardT (i n : Nat) (t : Term) (hin : i < n) : DEUDA_hGuardT i n t`
(`Meta/HasWitTrackedPrf.lean`). Footprint = la base sancionada; **net‑0 puro**. Árbol verde a
132 jobs. Detalle en `doc/REFERENCE-Incompleteness.md` §3.44.

De las **dos** obligaciones que este ADR dejó abiertas (addendum 2026‑09‑07b) **queda una**:
`DEUDA_hGuardF`. `hGuard_of_deudaF` es `hGuard_of_deudas` con la mitad `wit` ya descargada.

**⚠️ Una condición NUEVA, y hay que dejarla escrita: la cota de casilla `i < n`.**

`condD` escribe la casilla como accesor dotado `nthcT ṫ ı̄`; el reflector del átomo `In`
entrega `(nthc t ı̇)˙`. El puente entre los dos es `pcc_eval_nthc`, **que exige**
`ı̇ < lenc t`. No es un artefacto de esta prueba: `nthc` fuera de rango no está determinado,
así que ningún reflector de la casilla `i` puede existir sin la cota.

`Hcond` ya trae `lenc t = ṅ` entre sus tres hipótesis, luego lo único que se añade es
**aritmético**. Y las **cuatro** casillas `wit` que la enmienda declara lo cumplen todas:

| tag | `lenc` (`n`) | casillas `wit` | `i < n` |
|---|---|---|---|
| `q1` (9), `q2` (10) | 4 | 3 | ✔ |
| `leibniz` (13) | 5 | 3, 4 | ✔ |
| `q3` (11), `ind` (18), `qconf` (19), `listInd` (20) | — | ninguna | — |

Comprobado con un `decide` sobre los pares `(i,n)`. `hGuard_of_deudas` (con su `∀ i` sin
restricción) se conserva para quien tenga las deudas sin cota; el consumidor real usa
`hGuard_of_deudaF`, que pide la cota **sólo de las casillas que su lista usa**.

**⚠️ Y una corrección a cómo este ADR describía su propia obligación.** El addendum
2026‑09‑07b decía que lo que faltaba era «el recorrido de `isTC1`/`isFC1` bajo el `∃`», dando
por hecho que la imagen punteada era una elección del que refleja. **No lo es.**

> `condD C t = substfc 0 ṫ (formCode C)`: la imagen la impone `formCode`. Y
> `formCode (shapeUn X k)` es la **ecuación posicional** `Ẋ = ⟨k̄, nthcT Ẋ 1̄⟩`, no la
> conjunción de accesores `carc X = k̇ ∧ lenc X = ṅ` que el kit genérico sabía producir.

Las dos son equivalentes en la teoría objeto y **son códigos distintos**; el chasis recompone
el `⇔` con el código. Reflejar la equivocada habría dado un teorema correcto sobre la fórmula
equivocada —y habría compilado—, exactamente el mismo modo de fallo que el addendum
2026‑09‑07b registró para la **forma** de la cascada. La cura fue la misma: **`rfl` contra el
original**, aquí dos, casando `shapeFCun`/`shapeFCbin` con `formCode`.

⭐ El coste de la corrección resultó ser **cero teoremas objeto nuevos**: la ecuación posicional
la reflejan `pcc_tc_objAt` + `PrfH_dotVN` de `Meta/CodeTreeReflect.lean`, ya probadas por
inducción sobre el árbol para los 14 tags estructurales. `pcc_shape_tree` sólo las compone, y
es genérica en el `CTree` — luego C3‑F la hereda tal cual.

**Lo que NO cambia**: 7 `axiom` de Lean (la cifra **de entonces**; hoy **6**, `d3` retirado), 141 axiomas objeto, y ninguna firma de D1/D2/D3 ni de
Gödel I/II.


### Addendum 2026‑09‑08d · C3‑F a medias, y limpio

`Meta/HasWitFTrackedPrf.lean` (nuevo, 828 l., **net‑0 puro**). Detalle en §3.45 de
`doc/REFERENCE-Incompleteness.md`. Cierra **la mitad cara** de `DEUDA_hGuardF`:

```
pcc_wfAllF_trackedC (wF wT) : wfAllF wF wT ⇒ Prov(⌜wfAllFDotC ẇF ẇT⌝)
pcc_isFormCodeE2_trackedC   -- el recorrido de las OCHO cláusulas
```

⭐ **La corrección del addendum anterior se aplicó como método, y funcionó.** Lo primero del
módulo —antes de una sola prueba— son **siete `example … := rfl`** casando la imagen propuesta
con la que `substCodeF` produce de verdad. Acertaron todos a la primera; C3‑T había costado una
sesión por hacerlo al revés.

Queda: `isFC1` (dos `PrfH_and_intro_code`, trivial), el `∃∃` —⚠️ el `∃` **exterior** liga `wF`
y el **interior** `wT`, luego los huecos se rellenan en **dos pasadas a niveles distintos**, y
eso pide generalizar el descenso `prf_substfc_wfAll1DotAtC` a nivel arbitrario— y la fontanería
`condD`, que es el `rfl` ya comprobado. **Ninguna de las tres es contenido nuevo.**

**Lo que NO cambia**: 7 `axiom` de Lean (la cifra **de entonces**; hoy **6**, `d3` retirado), 141 axiomas objeto, ninguna firma aguas abajo.


### Addendum 2026‑09‑08e · 🏁🏁 ADR‑020 NO DEBE NADA — `DEUDA_hGuardF` probada

`pcc_hGuardF (i n : Nat) (t : Term) (hin : i < n)` y `hGuard_of_slots`
(`Meta/HasWitFTrackedPrf.lean`). Footprint = la base sancionada; **net‑0 puro**. Árbol verde a
135 jobs. Detalle en `doc/REFERENCE-Incompleteness.md` §3.46.

**Las DOS obligaciones que este ADR generó están saldadas.** `hGuard_of_deudas` (addendum
2026‑09‑07b) pedía `DEUDA_hGuardT` y `DEUDA_hGuardF`; `hGuard_of_slots` no pide ninguna. Lo
único que se añade sobre el chasis original es la cota de casilla `i < n`, que **no es un
artefacto** (addendum 2026‑09‑08c) y que cumplen las **once** casillas que la enmienda declara:

| casillas | pares `(i, n)` |
|---|---|
| las **cuatro** `hasWit` | (3,4) (3,4) (3,5) (4,5) |
| las **siete** `hasWitF` | (2,4) (2,4) (3,4) (2,5) (2,3) (2,4) (2,3) |

Comprobado con un `decide` sobre la lista. 11 = el recuento que este ADR declara.

**⚠️ Y lo que esto NO cierra, dicho antes de que alguien lo lea al revés.** C3 sigue abierto:
`pcc_lineWF_tracked_modulo_7` pide un reflector por tag y en el árbol hay **14**, ninguno de los
7 de sustitución. Pero lo que les falta es ahora **sólo su condición ESTRUCTURAL** —el RHS del
esquema, con `substfcT`/`substtcT`—, que es exactamente lo que `pcc_eval_substtc` (B3.2) y
`pcc_eval_substfc` (B3.4) compraron. **El conjunto extra que este ADR añadió ya no estorba.**

⇒ El enunciado correcto es: *«ADR‑020 ya no debe nada; C3 sigue abierto, pero por la mitad que
B3.2/B3.4 compraron, no por la que la enmienda añadió.»* Que es justo lo que la línea roja de
la decisión prometía.

**Lo que NO cambia**: 7 `axiom` de Lean (la cifra **de entonces**; hoy **6**, `d3` retirado), 141 axiomas objeto, ninguna firma aguas abajo.


---

## ADR-021: El `PsiF` de un chasis inductivo se escribe con símbolos OBJETO — y por eso hacen falta DOS cuerpos

> ⭐⭐ **PRECISADO el 2026‑09‑10f** (`doc/REFERENCE-Incompleteness.md` §3.66.1). El chasis
> **INTERIOR** de D3 (`boundedPremsIn`, `Meta/PremsBdAllPrf.lean`) tiene un `PsiF` que **SÍ** es un
> `substCodeF2` y cuya `hPl` **es cierta**. La diferencia con el exterior no es el `substCodeF`:
>
> | chasis | `PsiF` | ¿natural? | por qué |
> |---|---|---|---|
> | exterior (`chainOkB`) | `substCodeF 1 (liftc 0 q̇) (lineOkB nil ↑q #0)` | ❌ | `q` va **dentro de la fórmula** |
> | interior (`boundedPremsIn`) | `substCodeF2 1 (liftc 0 i̇) (liftc 0 (liftc 0 q̇)) premsBodyF` | ✅ | cuerpo **CERRADO**; `q`,`i` son **sólo testigos** |
>
> 🔑 **La regla, bien enunciada**: lo que rompe la naturalidad **no es «ser un `substCodeF`»** — es
> que el **PARÁMETRO VIAJE DENTRO DE LA FÓRMULA**. `substCodeF` manda cada variable **al hueco o a
> un `varc` cerrado según su nivel**; si el parámetro está dentro, `liftTerm` lo cambia de nivel y
> por tanto de destino. Si es sólo testigo, `substCodeF` lo copia tal cual y `liftTerm` lo
> atraviesa.
>
> ⚠️ **La forma vieja no era falsa, era demasiado gruesa**, y una regla que sobre‑prohíbe cuesta
> trabajo inventado: enunciada así, en el chasis interior `hPl`/`hPs` salen con dos inducciones
> mecánicas (`liftTerm_substCodeF2`, `substTerm_substCodeF2`) y **no hace falta ningún par
> dotado/computable**.


**Fecha**: 2026-09-10
**Estado**: Aceptado — ⚠️ **forzado por una medición, no elegido**. La alternativa está
**refutada por el compilador**, no descartada por conveniencia.

### Contexto

`pcc_bdAll_intro` (`Meta/BdAllIntroPrf.lean`) es el chasis que produce
`Prf (CF p ⇒ Prov(⌜∀i<bndF p. Ψ⌝))` por inducción sobre el parámetro `p`. Entre sus nueve
obligaciones hay dos de **naturalidad del cuerpo**:

    hPl : ∀ k q, liftTerm k (PsiF q) = PsiF (liftTerm k q)
    hPs : ∀ v t q, substTerm v t (PsiF q) = PsiF (substTerm v t q)

Al aplicarlo a D3 (§3.56) se descubrió que el `PsiF` natural —el que **casa el destino por
`rfl`**, `chainOkBPsi W p = substCodeF 1 (liftc 0 W) (lineOkB nil (liftTerm 0 p) #0)`— **no
cumple `hPl`**.

### La medición (certificada por el compilador, dos `rfl`)

    substCodeT 1 w #1                            = w                    -- el HUECO entrega el testigo
    substCodeT 1 (liftTerm 0 w) (liftTerm 0 #1)  = varc (numeral 1)     -- …y tras el lift, un varc CERRADO

`substCodeF`/`substCodeT` mandan cada variable del argumento **al hueco del testigo o a un `varc`
cerrado, según su nivel**. Un `liftTerm` en el parámetro la mueve **fuera del hueco**: donde antes
salía el testigo, ahora sale un `varc`. Los dos lados dejan de ser el mismo término. ⇒ `hPl` es
**FALSA**, no «difícil».

### Decisión

> **El `PsiF` de `pcc_bdAll_intro` —y de cualquier chasis que induzca sobre el parámetro— se
> escribe con SÍMBOLOS DE FUNCIÓN OBJETO** (`substfc`, `liftc`, `tcFn`, `nthcT`, `funcc`…),
> **NUNCA con un `substCodeF`/`substCodeT` aplicado a una fórmula o término que contenga el
> parámetro.**
>
> El parámetro entra **sólo** por dentro de un símbolo objeto (`tcFn q`), y el código de la
> fórmula queda **CERRADO**.

**Razón**: los símbolos objeto son `Term.func`, y `liftTerm`/`substTerm` los **atraviesan** — la
naturalidad es un `simp only`. `substCodeF` es una función de **Lean** que **recursa sobre la
fórmula**, y ahí la naturalidad es falsa.

⭐ La regla ya se cumplía sin estar escrita: `argsInPsi` (`Meta/HasWitTrackedPrf.lean` §4) está
construido enteramente con `inFormCodeFn`/`nthcT`/`tcFn`, y por eso sus `liftT_`/`substT_` eran
dos `simp only`. **No estaba documentada, y por eso no se vio venir.**

### Consecuencia: hacen falta DOS cuerpos, y un puente DENTRO de `Prov`

| cuerpo | quién lo pide | forma | ¿natural? |
|---|---|---|---|
| `chainOkBPsi` | el **destino** (`hmatch`, casa por `rfl`) | `substCodeF` — computa | ⛔ **no** |
| `chainOkBPsiDot` | el **chasis** (`pcc_bdAll_intro`) | símbolos objeto | ✅ sí |

El puente es **`prf_substfc_arith_open`**, dentro de la teoría objeto. ⚠️ Y no es un peaje: es
**la infraestructura por la que cruza todo**. A 2026‑09‑10 han cruzado **tres cosas distintas**:

| qué cruza | con qué | dónde |
|---|---|---|
| la **FORMA** | `rfl` + `prf_eq_symm` | `hmatch_chainOkB` (§3.55.5) |
| la **PRUEBA** | `prf_provCode_congr` + `prf_congr_bdAllCode` | `hbdAll_of_dotted` (§3.56.5) |
| el **TESTIGO** | `prf_congr_hasWitF` (Leibniz objeto) | `hwP_chainOkBPsi` (§3.58.2) |

Con **un solo** cuerpo, ninguna de las tres tenía por dónde pasar.

### Regla derivada: el ÍNDICE del nivel no es cosmético

De la misma familia salen **tres** variantes de la invariancia del cuerpo, y **no son
intercambiables** (`Meta/BdAllIntroPrf.lean`, `Meta/SubstCodeOpenPrf.lean` §5):

| variante | nivel actuante | código a | testigo | condición sobre `φ` |
|---|---|---|---|---|
| `substfc_inv_substCodeF` | `v+1` | `v` | libre | `liftFormula (v+2) φ = φ` |
| `substfc_inv_substCodeF_at` | `v` | `v` | libre | `liftFormula (v+1) φ = φ` |
| **`substfc_id_substCodeF`** | `v` | **`v+1`** | ⚠️ **atado**: `u ≐ varc v̄` | `liftFormula (v+2) φ = φ` |

⚠️ **Por debajo del hueco el testigo deja de ser libre**: la casilla `n = v` es una `varc v̄`
corriente y `substtc` la sustituye **por el testigo**. ⭐⭐ Y el salto es **exactamente de uno**:
con el código a `v+2` o más quedarían variables que `substtc` **decrementaría**, y el enunciado
sería **FALSO**.

📖 **El testigo va como PARÁMETRO con su ecuación, no clavado.** Existe `prf_congr_substfc_arg2`
(`Meta/ArithPrf.lean:59`) y se podría clavar transportando; **no se hace**, por la regla que §3.50
ya había registrado: *cuando un cuerpo bajo binder necesita el mismo parámetro a dos niveles, no
lo escribas con `liftc` — parametrízalo por los dos*. Bajo el binder aparece `liftc 0 u`, que no
es sintácticamente la variable de arriba, y el puente hay que darlo igualmente.

### Consecuencias operativas

* Al abrir un frente con `pcc_bdAll_intro`, **medir `hPl` ANTES de escribir `hbody`**. Cuesta dos
  `rfl` y evita atacar el cuerpo contra un chasis que no puede consumirlo.
* Si el destino impone un `substCodeF`, **no intentar hacerlo natural**: construir el gemelo
  dotado y puentear dentro de `Prov`.
* ⚠️ **El número de obligaciones abiertas no mide el progreso.** Aplicar este ADR **subió** el
  contador de D3 de 2 a 3 (§3.56) y fue el paso más importante del frente: lo que el «2» medía era
  una cadena que **no cerraba**.

**Lo que NO cambia**: 7 `axiom` de Lean (la cifra **de entonces**; hoy **6**, `d3` retirado), 141 axiomas objeto, ninguna firma aguas abajo.
Footprint de todas las piezas nuevas: los tres axiomas de Lean, o la base sancionada.

---

## ADR-022: La clase de testigos de la ω‑consistencia se ESTRECHA a LÍNEAS ESTÁNDAR — y se paga el precio por escrito

**Fecha**: 2026-09-10
**Estado**: Aceptado — **sancionado por el propietario** el 2026‑09‑10h.
⚠️ **Encarece una hipótesis META.** No es una refactorización: cambia lo que `OmegaConsistent`
afirma. Por eso va a ADR y no a un commit de limpieza.

### Contexto

`Meta/OmegaReflect.lean` reduce la mitad **`⊬¬G`** de Gödel I a dos piezas:

    reflects_of_omega : OmegaConsistent → NegVerifier → Reflects φ

y ambas cuantifican sobre la **misma** clase de testigos, `StdChain`. Hasta hoy:

```lean
def StdChain (l : List Term) : Prop := ∀ x ∈ l, IsCodeShaped x
```

con `IsCodeShaped` generada por `numeralM`, `strCodeM`, `nil` y `cons`.

### El problema, MEDIDO (no argumentado)

El docstring de `IsCodeShaped` justificaba la clase diciendo que las comparaciones de
`NegVerifier` son *«PARALELAS POR TIPO — `formCode φ` contra `formCode ψ`, **nunca `cons` contra
`numeral` en la misma ranura**»*.

⛔ **Es FALSO sobre la clase que él mismo define**, y el contraejemplo está **compilado** desde
antes, en `sondeos/MedirF_Censo.lean` §4:

```lean
theorem isCodeShaped_linea_mala :
    IsCodeShaped ⟨formCode (⊥⇒⊥), 8̄, 3̄⟩          -- ✅ testigo StdChain LEGÍTIMO
```

Refutar esa línea obliga a comparar **`formCode ⊥` (un `cons`) contra `numeralM 3` (un numeral)**
en la misma ranura. Y ahí:

* `formCode_ne` / `cons_ne_head` / `cons_ne_tail` (`Meta/CodeDistinct.lean`) **no pueden**: son
  estructurales y los dos lados tienen constructores distintos sin que eso implique desigualdad —
  `cons nil nil ≐ numeralM 2` es **provable** (`ax_L0_cons_def` + Cantor). Es la misma raíz que
  tumbó `canon_ne`.
* La **única** vía es por **VALOR**: `numTree_ne` (mismo sondeo), que pide `m ≠ n` **a nivel META**
  entre los valores de Cantor.

### ⚠️ Y aquí es donde la medición anterior se queda corta — la parte que hay que corregir

`sondeos/MedirF_Censo.lean` §4 concluía: *«¿hay que cambiar `StdChain`? **NO**: `NumTree` ya la
subsume»*, con `numTree_of_isCodeShaped` probado. **Ese teorema es cierto y su conclusión no.**

🔑 **Subsumir la CLASE no es descargar la OBLIGACIÓN.** `NumTree` da que *todo* término
`IsCodeShaped` **tiene** un valor; lo que `numTree_ne` necesita es **decidir `m ≠ n` en META**, y
eso exige **calcular** el valor. El propio sondeo lo mide y lo dice:

    codeNat (⊥⇒⊥) = 583 734        -- y `triN` es recursión unaria

para una sentencia real —la `G` del punto fijo— es **astronómico**. El truco de aritmética acotada
que el mismo sondeo aporta (`consN_ge`, `codeNat_ge : 3 ≤ codeNat φ`) resuelve los choques contra
numerales **pequeños** y **sólo** ésos. ⇒ con la clase ancha, `NegVerifier` tiene obligaciones
**existentes pero no descargables**.

### Decisión

Estrechar la clase a la **forma exacta de `lineCode'`**:

```lean
inductive StdArgs : Term → Prop
  | nil                          : StdArgs nil
  | form {t} (A : Formula)       : StdArgs t → StdArgs (cons (formCode A) t)
  | term {t} (u : Term)          : StdArgs t → StdArgs (cons (termCode u) t)

def StdLine (x : Term) : Prop :=
  ∃ f k as, And (x = cons (formCode f) (cons (numeralM k) as)) (StdArgs as)

def StdChain (l : List Term) : Prop := ∀ x ∈ l, StdLine x
```

Ahora la disciplina de tipos **es verdadera por construcción**: cabeza `formCode`, casilla del tag
`numeralM`, argumentos `formCode`/`termCode`. Todas las comparaciones que `NegVerifier` necesita
son paralelas y las deciden `formCode_ne`/`termCode_ne` **sin evaluar Cantor**.

### La GARANTÍA — sin ella el estrechamiento sería una trampa

Estrechar la clase **debilita** `NegVerifier` y **refuerza** `OmegaConsistent`. Llevado al límite
—clase vacía— `NegVerifier` sería trivial y `OmegaConsistent` **falsa**. Lo que impide ese abuso
está probado en el propio módulo:

```lean
theorem stdLine_lineCode' (acc f r) : StdLine (lineCode' acc f r)          -- los 21 tags
theorem stdChain_proofCode' (rs acc) :
    ∃ l, And (StdChain l) (objList l = proofCode' rs acc)                  -- 🏁 LA GARANTÍA
```

⇒ **el código de cualquier demostración‑secuencia real es un testigo estándar**. No se deja fuera
ningún testigo que la teoría pueda producir honestamente; sólo la basura.

Y en la otra dirección, el payoff, también probado:

```lean
theorem junk_line_not_stdLine :
    ¬ StdLine ⟨formCode (⊥⇒⊥), 8̄, 3̄⟩          -- la línea de MedirF_Censo §4, FUERA
```

### El PRECIO, escrito y no escondido

1. **`OmegaConsistent` es estrictamente más fuerte.** Cuantifica sobre menos `l`, luego la premisa
   interna `∀ l, StdChain l → ⊢ ¬A[objList l]` es más fácil de cumplir y su negación más difícil.
2. ⚠️ **El argumento «toda teoría SÓLIDA es ω‑consistente» ya NO la cubre en general.** Con la
   clase ancha, solidez ⇒ ω‑consistencia sin más. Con la estrecha, la solidez da un testigo **en
   ℕ** que podría no tener forma de línea estándar.
3. ⭐ **Pero sí la cubre en el ÚNICO `∃` al que se aplica.** `reflects_of_omega` la usa sobre
   `A = provBody (formCode φ)`, cuyos testigos honestos son **códigos de prueba**, y ésos son
   estándar por `stdChain_proofCode'`. El hueco del punto 2 es **genérico, no operativo**.
4. Atenuante ya medido antes: **no era la ω‑consistencia clásica pura** ni siquiera antes —
   cuantifica sobre `objList l`, no sobre numerales arbitrarios. Es **estrechar lo ya estrecho**.

### Alternativas consideradas

| alternativa | por qué no |
|---|---|
| **Dejar `StdChain` y usar `NumTree`** (`MedirF_Censo` §4) | subsume la **clase**, no la **obligación**: pide `m ≠ n` en META con `codeNat` **astronómico**. Sirve para los choques contra numerales **pequeños**, y ahí se conserva |
| **Restringir el `∃` en vez de la clase** (una `OmegaConsistent` sólo para `provBody`) | más honesto en el papel, pero rompe la forma genérica de la hipótesis y no cambia nada operativo: el punto 3 ya lo da |
| **Rosser** | consigue ambas mitades desde consistencia simple, pero **cambia de sentencia**. Es un frente distinto, no una variante de éste |

### Consecuencias operativas

* `NegVerifier` y las dos deudas de `Meta/VerifierSound.lean` (`DEUDA_chainNeg`, `DEUDA_inNeg`)
  quedan **enunciadas sobre la clase estrecha** ⇒ los módulos **C** y **D** pueden atacarse ya.
* `IsCodeShaped` **se conserva** (su `isClosed` sigue valiendo y los sondeos la citan), pero
  **deja de definir `StdChain`**, y su docstring lleva la corrección de que su afirmación central
  era falsa.
* ⚠️ **Regla de método que este ADR deja**: *subsumir la clase no es descargar la obligación*. Una
  medición puede ser **correcta como teorema** y **equivocada como conclusión**; hay que leer qué
  obligación queda **después** de aplicarla.

**Lo que NO cambia**: 6 `axiom` de Lean (**la cifra de entonces**; hoy **5**, `ax_mod2_alternation` derivado), 141 axiomas objeto, `reflects_of_omega` y
`goedel_first_undecidable_omega` **sin tocar** (son paramétricos en `StdChain`).

---

## ADR-023: El censo de `coreAxioms` se CERTIFICA con `primAxioms` — y eso NO mueve la frontera de la teoría

**Fecha**: 2026-09-10
**Estado**: 🏁 **ACEPTADO, RATIFICADO Y EJECUTADO** el 2026‑09‑10h. **9 de los 11 certificados.**
Los 2 restantes (ax21, ax24) piden una **segunda** sanción, distinta y **no pedida** — ver el final.

### Contexto

El censo (`doc/REFERENCE-Full.md` §3.14.1) parte `coreAxioms` en **23 primitivos/definitorios** y
**11 derivables con inducción**, y los 11 **están demostrados** en `Full`. Pero se enuncian:

```lean
theorem add_comm_thm : axioms ⊢ ax6_add_comm         -- y ax6_add_comm ∈ axioms
```

⇒ **trivialmente ciertos por `ax`**. El **tipo no certifica** la redundancia; sólo la prueba lo
hace, y nada impide que una edición futura la cortocircuite.

### ⚠️ CORRECCIÓN de lo que este mismo proyecto escribió esta misma sesión

Al levantar el censo se anotó que certificarlo *«pide `primAxioms`, y eso **mueve la frontera de la
teoría** (ADR‑015) ⇒ ADR, no limpieza»*. **Eso confunde dos cosas distintas**, y sólo una es cierta:

| | qué se hace | ¿mueve la frontera? |
|---|---|---|
| **(A) CERTIFICAR** | añadir `primAxioms ⊆ axioms` y demostrar `primAxioms ⊢ axN` | ⛔ **NO.** `axioms` queda **intacta**; `axiomsCodeT`, `provCodeC'` y la sentencia `G` no se enteran |
| **(B) ESTRECHAR** | **quitar** los 11 de `axioms` | ✅ SÍ, y por eso **no se hace** |

Este ADR decide **(A)**. **(B)** queda descartada.

### La medición que lo hace barato

1. ⭐ **`Derives.weakening` es un CONSTRUCTOR de `Derives`** (`FOL/FOL.lean`), no un lema por
   probar. ⇒ el puente `primAxioms ⊢ f → axioms ⊢ f` es **una línea** y **ninguna firma aguas
   abajo cambia**.
2. ⭐ **Ninguna de las 46 citaciones `∈ axioms`** de `Full/{Induction,Mod2,Lists}.lean` cita **uno
   de los 11 derivables**. Las distintas que se citan son, todas, **primitivas**:

       Full/Lists.lean      : ax_C1, ax_C2, ax_L1, ax_L2                    (4)
       Full/Induction.lean  : ax2, ax3, ax4, ax5, ax8, ax9, ax13            (7)

   ⇒ **no hay circularidad que romper**: la migración es **mecánica**.
3. ⭐ **`ax_list_induction` YA es genérico en `Γ`** (`Full/Lists.lean`). ⇒ `ax_C3` y `ax_L3` se
   certifican **sin tocar ningún axioma**.

### Lo EJECUTADO hoy

```lean
def primAxioms : List Formula := [ … los 23 … ]        -- Full/Induction.lean §0bis
theorem primAxioms_len    : primAxioms.length = 23 := rfl
theorem primAxioms_subset : ∀ f ∈ primAxioms, f ∈ axioms
theorem prim_to_axioms    : primAxioms ⊢ f → axioms ⊢ f     -- Derives.weakening
theorem axp               : f ∈ primAxioms → primAxioms ⊢ f -- Derives.hyp

theorem concat_assoc_prim : primAxioms ⊢ ax_C3_concat_assoc   -- 🏁 CERTIFICADO
theorem in_concat_prim    : primAxioms ⊢ ax_L3_in_concat      -- 🏁 CERTIFICADO
```

`concat_assoc_thm`/`in_concat_thm` **conservan su firma** `axioms ⊢ …` (vía `prim_to_axioms`), y
los *pointwise* también, porque `Meta/ProofChain.lean` los consume. ⚠️ Los cuatro helpers de
congruencia de `Full/Lists.lean` pasan a ser **genéricos en `Γ`** —no citan ningún axioma— para
servir a los dos contextos a la vez.

### ⛔ LO QUE FALTA, Y POR QUÉ NO LO DECIDO YO

Los otros **9** (ax6, ax7, ax10, ax11, ax12, ax18, ax19 en `Induction.lean`; ax21, ax24 en
`Mod2.lean`) pasan por `induction_object`, y con él por

```lean
axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ
```

que está **especializado a `axioms`**. Para certificar sobre `primAxioms` hace falta el mismo
axioma sobre `primAxioms` — y eso es **restatar un axioma** ⇒ **M‑1: sanción explícita**.

⚠️⚠️ **Y la salida fácil está CERRADA**: generalizarlo a `∀ {Γ}, Γ ⊢ inductionFormula φ` —la forma
que `ax_list_induction` sí tiene— sería **FALSO**, porque con `Γ = []` diría que el esquema de
inducción es **lógicamente válido**. `ax_list_induction` puede ser genérico porque es una **regla**
(lleva `base` y `step` sobre el mismo `Γ`); `ax_induction` es un **axioma**, y un axioma tiene que
**nombrar su contexto**.

⇒ 🏁 **RATIFICADO por el propietario el 2026‑09‑10h**, y ejecutado tal cual:

```lean
axiom ax_induction_prim (φ : Formula) : primAxioms ⊢ inductionFormula φ

theorem ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ :=
  prim_to_axioms (ax_induction_prim φ)          -- ⇒ `ax_induction` deja de ser axioma
```

**No añade un axioma: lo MUEVE**, y el recuento queda igual — `ax_induction` pasa a teorema, y los
`axiom` de Lean **siguen siendo 6**. Dice exactamente lo que `Full` significa: *«los 23 primitivos
**más** el esquema de inducción»*.

### 🏁 Lo ejecutado con la ratificación: **9 de 11** → 🏁🏁 **10 de 10 desde el 2026‑09‑12**

`Full/Induction.lean` migrado entero a `primAxioms` — **35 declaraciones**, con `induction_object_prim`
y `axp` —, y las **firmas `axioms ⊢` de siempre re‑expuestas por debilitamiento** para los diez
lemas que consumen otros módulos (`zero_add`, `succ_add`, `add_comm_ax`, `zero_mul`, `succ_mul`,
`mul_comm_ax`, `lt_succ_self`, `not_lt_zero`, `lt_succ_of_lt`, `zero_lt_succ`, `zero_or_succ_ax`).
⇒ **ax6, ax7, ax10, ax11, ax12, ax18, ax19 CERTIFICADOS** (`*_thm_prim`), más ax_C3 y ax_L3.

⚠️ **Un caso no salió por debilitamiento y enseña algo**: `lt_succ_of_lt` toma la hipótesis **en el
contexto** (`axioms ⊢ lt b a → …`), y ahí el debilitamiento va **en la dirección contraria**. Se
cierra el ángulo internando la implicación sobre `primAxioms`, **debilitando la implicación**, y
aplicando `mp`. Regla: *un lema que consume el contexto no se debilita; se internaliza primero.*

**Footprint de los certificados**: los tres de Lean + las ω‑reglas + **`ax_induction_prim`**. Nada
de `ax_axiomsCodeT_eq` ni `prf_axiomsCodeT_eq`.

### ⬜ Los 2 que faltan piden una SEGUNDA sanción — que **no** se ha pedido

ax21 y ax24 se derivan en `Full/Mod2.lean`, y ahí:

1. ⛔ **`ax_mod2_alternation`** es otro `axiom` **sobre `axioms`** — exactamente la situación que
   tenía `ax_induction`. Certificar ax21/ax24 exige moverlo igual, y eso es **otra decisión M‑1**.
2. Además usa dos teoremas de `Block1` (`teo_1_3`, `teo_2_9`) enunciados sobre `axioms`.

### 🏁 Addendum 2026‑09‑10h — la pregunta previa se contestó, y el inventario bajó a **5**

`ax_mod2_alternation` **era derivable**, y no hubo que moverlo: **se retiró**. De `ax21` (rango) +
`ax16` (el bicondicional) + `ax4` + `zero_add` + `teo_1_11` (`0 ≠ 1`). ⇒ **6 → 5 `axiom` de Lean.**

⚠️⚠️ **Y al retirarlo se hizo visible una CIRCULARIDAD que el censo no había visto.** El diseño de
2026‑06‑11 («Opción C.2») afirmaba las dos cosas a la vez:

* *«de `ax_mod2_alternation` salen `ax21` y `ax24` por inducción»* — y así estaba escrito
  `mod2_range_ax`;
* *«en `Minimal`, `ax_mod2_alternation` es derivable de `ax21 + ax16`»*.

Juntas dan un **círculo**. Mientras uno de los dos fue **`axiom`**, el círculo no se veía: Lean lo
aceptaba porque pasaba por un postulado.

🔑 **Cuál es el primitivo, medido y no argumentado**: `ax16 + ax17` **no** fijan el rango de `mod2`.
Un modelo con `mod2 2̄ = 2̄` los satisface — `ax17` sólo pide `div2(2̄)·2̄ + mod2(2̄) = 2̄`, que con
`div2(2̄) = 0̄` encaja, y `ax16` en `2̄` se cumple vacuamente. ⇒ **`ax21` carga información
independiente y es PRIMITIVO**; la alternancia es el **teorema**.

⇒ **El censo se corrige: `coreAxioms` = 24 primitivos + 10 derivables** (era 23 + 11), `ax21` entra
en `primAxioms`, y `mod2_range_ax` deja de fingir que deriva algo: cita el axioma.

🏁🏁 **CENSO CERRADO: 10 DE 10** (2026‑09‑12). `ax24` **certificado** sobre los primitivos:
`mod2_of_even_prim : primAxioms ⊢ ax24_mod2_of_even`, footprint
`[propext, Classical.choice, Quot.sound, FOL.MetaRules.{ex_elim, gen, imp_intro, or_elim},
ax_induction_prim]` — **sin `ax_list_induction`, sin anclas, sin nada de `axioms`**.

⭐ **Salió más barato de lo previsto, y por una pieza**: la versión `axioms` usaba `teo_2_9` de
`Block1` —que vive sobre `axioms` porque allí `Γ := axioms`— y portarlo habría arrastrado medio
bloque. Se **evita** con **`add_eq_zero_right_prim`** (≈20 líneas) sobre `zero_or_succ_ax_prim`,
que **ya existía**. ⚠️ Y `teo_1_3`, que tres documentos daban como dependencia, era **prosa
obsoleta**: no se usaba.

⭐ Y la cadena entera (`teo_1_11_prim`, `mod2_zero_prim`, `ax_mod2_alternation_prim`,
`a_plus_one_eq_one_prim`, `mod2_two_k_eq_zero_prim`) quedó **sobre los primitivos**, con las firmas
`axioms ⊢` como **envoltorios** por `prim_to_axioms` ⇒ **ninguna prueba duplicada**.

🔑🔑 **La lección, y va a la lista de reglas**: *un postulado puede estar ocultando un círculo, y el
círculo sólo se ve al retirarlo.* Es la recíproca de M‑1 (ningún axioma sin ADR): **cada axioma que
se retira audita lo que se apoyaba en él.**

### Consecuencias operativas

* **Certificar es barato y no cambia nada**: cuando un frente de `Full` derive un axioma de
  `Minimal`, enunciarlo sobre `primAxioms` y recuperar `axioms ⊢` con `prim_to_axioms`.
* `primAxioms` vive en `Full/Induction.lean`, no en `Minimal/Axioms.lean`, para **no tocar el
  fichero con verja**. ⭐ Su sitio natural es junto a `coreAxioms`; moverlo es del propietario.
* ⚠️ **Regla que este ADR deja**: *«mueve la frontera de la teoría» no es un comodín*. Antes de
  aplazar algo por eso, comprobar si de verdad **cambia `axioms`** o sólo **añade un enunciado
  sobre un subconjunto**.

**Lo que NO cambia**: 6 `axiom` de Lean (**la cifra de entonces**; hoy **5**, `ax_mod2_alternation` derivado), 141 axiomas objeto, `axioms`, `coreAxioms`,
`axiomsCodeT`, `provCodeC'`, `G`, y todas las firmas aguas abajo.

---

## ADR-024: `⊢` es herramienta, `Prf` es enunciado — y qué significa exactamente `ConsistentOmega`

**Fecha**: 2026-09-11
**Estado**: **Aceptado** — decisión del propietario tras la medición de `Meta/OmegaStrength.lean`.
Incluye la **retirada** de `goedel_second'` y `con_imp_godel'` (opción (b)).

### El hecho que lo fuerza, medido

```lean
theorem derives_completo (A) : (axioms ⊢ A) ∨ (axioms ⊢ neg A)          -- sin hipótesis
theorem derives_decide_exactamente_una (hcon : ConsistentOmega) (A) :
    ((axioms ⊢ A) ∧ ¬(axioms ⊢ ¬A)) ∨ (¬(axioms ⊢ A) ∧ (axioms ⊢ ¬A))   -- con consistencia
```

**`axioms ⊢` es sintácticamente COMPLETO**, y con consistencia decide **exactamente una** de cada
par. La causa **no es aritmética**: `raa` e `imp_intro` toman como premisa una **función de Lean**,
así que de `axioms ⊬ A` sale `axioms ⊢ ¬A` **vacuamente**.

⚠️ **Es un metateorema CLÁSICO**: `derives_completo` usa excluido medio en la metateoría. Sin él no
saldría. Lo que **sí** sale sin EM es `refuta_lo_que_no_prueba`, y basta para la conclusión.

### La lectura correcta, y no es que el proyecto esté roto

Gödel I exige **tres** hipótesis: consistente + suficientemente fuerte + **efectivamente
axiomatizada (r.e.)**. Lo medido dice que `axioms ⊢` **incumple la tercera**:

    completa  ⟹  no r.e.

`{A | axioms ⊢ A}` es una **compleción consistente** de `axioms` —tipo Lindenbaum—, no un sistema
formal. ⇒ **no puede ser sujeto de un teorema de incompletitud**, y `Prf` **sí** puede, porque está
definido por derivaciones **finitas** que `checkProof` verifica — que es exactamente lo que el
verificador aritmetizado internaliza.

### Decisión

| | |
|---|---|
| **`axioms ⊢`** | ✅ **herramienta de trabajo**. `imp_intro`/`raa` ahorran el teorema de deducción, y toda la capa `Minimal`/`Full` vive ahí legítimamente |
| **`Prf`** | ✅ **el único cálculo admisible en el ENUNCIADO** de un resultado de incompletitud |

⛔ **MANDATORY (M‑10)**: *ningún teorema cuyo enunciado hable de indemostrabilidad, indecidibilidad
o consistencia puede formularse sobre `⊢`.* Si aparece `¬(axioms ⊢ …)` en la **conclusión o en una
hipótesis** de un resultado así, está mal enunciado: por `derives_completo` eso significa «el cálculo
**refuta**», no «no demuestra».

### Lo ejecutado

* 🗑️ **Retirados** `goedel_second'` y `con_imp_godel'` (`Meta/GodelTwo.lean`), con la nota de por qué.
  **Se conservan** `d3` —que fue `axiom` hasta el 10g y hoy es teorema— y `consistencyFormula'`.
* 🏁 **`Meta/GodelTwoPrf.lean`**: `goedel_second_prf (hcon : ConsistentOmega) : ¬ Prf Con'`.
* 📄 `FOL/MetaRules.lean`: corregido el docstring de `gen`, que llamaba «ω‑regla» a algo que **no lo
  es** — su premisa recorre **todo `Term`**, no los numerales, luego como regla es **más débil**.

### ⚠️ Y ahora lo que hay que mirar de frente: qué es `ConsistentOmega`

`ConsistentOmega := ¬ (axioms ⊢ ⊥)`. Con lo anterior, eso **no es** «la teoría `axioms` es
consistente» en el sentido habitual. Es:

> *el conjunto `{A | axioms ⊢ A}` —que es una compleción **completa** de `axioms`— es **consistente***

es decir: **existe una asignación de verdad total a las sentencias que extiende `axioms`**. Es, en
fuerza, muy cercano a suponer la **solidez** de `axioms` respecto de algún modelo.

**Dónde se usa**: es la hipótesis de **los dos** teoremas de Gödel del proyecto —
`goedel_first_numeral` y `goedel_second_prf`.

| | |
|---|---|
| ✅ **Lo que NO invalida** | las conclusiones son sobre **`Prf`**, que es r.e. y no completo. Los teoremas **dicen lo que parecen decir** |
| ⚠️ **Lo que sí hay que escribir** | la hipótesis es **más fuerte** que «Q++ es consistente». Presentarla como «consistencia simple» a secas sería un **sobreclaim** |
| ⬜ **Lo que queda por medir** | si `ConsistentH := ¬ Prf ⊥` bastaría. `consistentH_of_omega` da `ConsistentOmega → ConsistentH`; la **vuelta no existe**, y **ésa es la pregunta**: ¿se puede reformular Gödel I/II sobre `ConsistentH`? Sería **estrictamente mejor** |

### 🏁🏁 Addendum 2026‑09‑11 — **P‑4 RESUELTO: sí bastaba `ConsistentH`**

Con el punto fijo ya sobre `Prf` (`prf_godelCN_fixedpoint`, net‑0 puro), los dos teoremas salen en
**cuatro líneas**:

```lean
goedel_first_prf  (hcon : ConsistentH) : ¬ Prf godelCN
goedel_second_prf (hcon : ConsistentH) : ¬ Prf consistencyFormula'
```

⇒ **la hipótesis de la cadena de Gödel es hoy la MÍNIMA honesta**: *el cálculo finitario no
demuestra `⊥`*. `ConsistentOmega` **desaparece de los enunciados cabecera**;
`consistentH_of_omega` la transfiere para quien la tenga a mano (corolarios `_of_omega`).

⭐⭐ **Y el footprint lo certifica** — cae de

    [3 de Lean] + dne + gen + imp_intro + ax_induction_prim + ax_list_induction
              + ax_axiomsCodeT_eq + prf_axiomsCodeT_eq

a

    [propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]

**un solo axioma del proyecto.** Las ω‑reglas y los dos esquemas de inducción entraban **por la
hipótesis vieja**, que hablaba de `⊢`. ⇒ **la cadena de Gödel es ENTERAMENTE FINITARIA**, y lo único
que la separa de los tres axiomas de Lean es **`prf_axiomsCodeT_eq`**, el ancla de codificación.

🔑 **La lección**: *una hipótesis mal elegida no sólo debilita el enunciado — arrastra al footprint
todo lo que ella necesita.* Cambiarla por la mínima limpió **seis** dependencias de golpe.

**Lo que NO cambia**: 5 `axiom` de Lean, 141 axiomas objeto, `Prf`, `Derives`, y ningún enunciado
sobre `Prf`.

---

## ADR-025: Un `axiom` que HABITA un inductivo prohíbe la inducción — y `FOL.soundness` era FALSO

**Fecha:** 2026‑09‑11 · **Estado:** ✅ SANCIONADO (contención ejecutada; la reparación de fondo, abierta)

### El hecho, medido y compilado

`FOL/Soundness.lean` probaba `soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f` por `induction h`. Eso es
**falso**, y no por un descuido en la prueba: **el enunciado no es demostrable porque no es verdad**.

    theorem inconsistencia_de_cualquier_solidez
        (solidez : ∀ {Γ f}, (Γ ⊢ f) → satisfies Γ f) : False
    footprint: [propext, FOL.MetaRules.raa]          ← compilado, EXIT 0

⇒ **cualquier** testigo del enunciado de solidez para `Derives` demuestra `False`. Sin hipótesis.

### La causa

`Derives` (`FOL/FOL/FOL.lean:165`) es un `inductive` de **18 constructores**, todos semánticamente
válidos. Pero hay **DOCE `axiom`s que lo HABITAN** — ⚠️ *la primera redacción de este ADR decía
«cinco», mirando sólo `MetaRules`; el censo se corrigió el **2026‑09‑12**, y los que faltaban
estaban **fuera** de `MetaRules`, que es justo donde nadie miró*:

| dónde | cuáles | n |
|---|---|---|
| `FOL/MetaRules.lean` | `imp_intro`, `gen`, `raa`, `dne`, `or_elim`, `ex_elim` | 6 |
| `FOL/Theorems/Neg.lean:57` | **un SEGUNDO `dne`** (forma de esquema `Γ ⊢ (¬¬A ⇒ A)`, distinto del de `MetaRules`, que es regla). Lo consume `Completeness.lean` | 1 |
| `FOL/Theorems/Quantifiers.lean:115` | `forall_not_impl_exists_not` | 1 |
| RPP | `ax_induction_prim`, `ax_list_induction`, `ax_axiomsCodeT_eq`, `ax_p_tfa` ⚠️ (este último **concluye dentro de un `∃`** — por eso un `grep` ingenuo no lo ve) | 4 |
| | | **12** |

Los seis de `MetaRules` **tienen que ser axiomas**: sus premisas son **funciones de Lean**, o sea
ocurrencias negativas de `Derives` en su propio constructor, que Lean rechaza en un `inductive`. No
hay alternativa dentro del tipo. Los otros seis **no** tienen esa excusa.

⇒ `Derives` tiene habitantes que **no son aplicaciones de constructor**. Un teorema probado por
`induction` cubre los 18 casos, pero **se aplica a todos los habitantes**. Es el fallo clásico de
`axiom foo : UnInductivo`: rompe la garantía de «no hay basura» del tipo.

El detonador concreto: con `Γ = []` y dos modelos triviales sobre `Unit`, `raa` —cuya premisa
`[] ⊢ P → [] ⊢ ⊥` existe **vacuamente** cuando `P` no es derivable— da `[] ⊢ ¬P`; la solidez obliga
a `[] ⊨ ¬P`; y `P` es verdadera en el otro modelo.

### La decisión

1. **Contener, no reparar.** `Soundness.lean`, `Compacity.lean` (su `compactness_theorem` era
   **vacuo**) y `Theorems/Soundness.lean` → `FOL/cuarentena/`, fuera del glob de `lean_lib «FOL»`.
   `FOL.lean` deja de importarlos: importaba `MetaRules` **y** `Soundness` ⇒ **`import FOL` era un
   módulo inconsistente**.
2. **La regla, escrita**: [M‑11](#), con su LISTA NEGRA y su LISTA BLANCA.
3. **Retirar el sobreclaim**: el docstring de `MetaRules` afirmaba que el sistema resultante es
   «**sólido** y completo relativo a ℕ». La solidez es precisamente lo que **no** se tiene.

### Qué NO dice

* ⚠️ **RPP no está afectado** [medido]: no importa `FOL.Soundness` ni el barrel raíz `FOL`. Árbol
  reconstruido: **145 jobs verdes**, footprints de Gödel intactos.
* ⚠️ **`FOL/Semantics.lean` está BIEN** y se queda. Es lo que permitió probar `prf0_soundness`.
* ⚠️ **Las meta‑reglas no están «mal»**: dicen lo que dicen. `⊢` es una noción metateórica de
  verdad, no una relación de derivabilidad — [ADR‑024](#) y `Meta/OmegaStrength.lean`. Lo nuevo es
  que eso **también impide la solidez**, y las dos caras son la misma.

### La salida buena, ya ejecutada

`sondeos/AnclaSoundness.lean`: **`prf0_soundness {φ} (h : Prf₀ φ) : satisfies axioms φ`**, por
inducción sobre los 17 constructores de `Prf₀` —el único cálculo del árbol **sin axiomas
habitándolo**—, footprint `[propext, Classical.choice, Quot.sound]`, **net‑0 puro**.

⭐ **Y el hallazgo de método**: `FOL/Semantics.lean` existe **desde mayo** con 0 `sorry`, y este
proyecto **no lo había importado nunca**. Cuatro agentes independientes midiendo el frente
afirmaron que el árbol no tenía semántica. *Antes de construir, buscar* — van tres veces.

### ⬜ Lo que queda ABIERTO (decisión del propietario)

**La reparación de fondo**: que las meta‑reglas **no habiten `Derives`** — declararlas sobre una
relación aparte `DerivesW` con `Derives Γ f → DerivesW Γ f`, dejando `Derives` limpio para que su
solidez sea un teorema de verdad. ⚠️ **Coste medido**: RPP usa constructores `Derives.*` **164
veces** (`Derives.subst` 58, `Derives.refl` 40, `Derives.hyp` 18, `weakening` 13, `intro_impl` 13…),
más toda la notación `⊢`. **No es una tarde.**

⛔⛔ **Y con el censo corregido, esa reparación NO BASTARÍA** (2026‑09‑12): mover sólo `MetaRules`
dejaría **seis** habitantes en `Derives` — los dos de `FOL/Theorems/` y los cuatro de RPP.

⚠️ **Y hay uno que RPP FABRICA, y es de los malos**: `ax_list_induction`
(`Full/Lists.lean:55`) tiene `step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)` — **premisa‑FUNCIÓN de
Lean**, la forma exacta que hace patológico a `raa`, con conclusión `∀ L : Term`. ⇒ **mover
`FOL/MetaRules` no limpia `Derives` mientras esa línea siga ahí**: el problema no es de quién es el
fichero, es de la FORMA de la premisa.

Una reparación que deja habitantes **no repara nada**: la prohibición de inducir seguiría en pie.
Quien acometa (f) tiene que mover **los doce**, empezando por casa.

🔑 **Y la regla de diseño que se deduce** (R‑1(c)): *una regla que se quiere añadir a una relación
inductiva se añade como **CONSTRUCTOR**, o con un inductivo que la envuelva — **nunca** como
`axiom`. Un `axiom` no extiende el punto fijo: **afirma una falsedad sobre él**.*
⭐ Nota: `ax_p_tfa` se retira por decisión del propietario (NEXT‑STEPS (a)) ⇒ quedarían once.

### 📌 POSDATA 2026‑09‑12 — **la cuarentena NO fue efectiva el primer día**

Se movió el fuente, se quitó del barrel, se reconstruyó el árbol y dio **verde**. Pero `lake` **no
recoge la basura**: el `.olean` compilado se quedó, `import FOL.Soundness` **seguía resolviendo**
desde él, y `False` se demostraba al día siguiente exactamente igual (verificado compilando).

🔑 **La lección: retirar el FUENTE no retira el MÓDULO.** Un `.olean` sin `.lean` es un **módulo
fantasma** — importable, invisible al build, y sin fuente que auditar.

⭐ Al añadir el control que lo detecta (**bloque `[F]`** de `check-doc-sync.bash`) aparecieron
**cuatro fantasmas más, en RPP**: `Meta/ZZAdv2`, `Meta/ZZAdvTest`, `Meta/ZZTestCantorReview` y
—el serio— **`Meta/Incompleteness`**, la capa Gödel **LEGACY** retirada en `f03eacf`, que reexponía
**`axiom D2` y `axiom D3`**: las dos condiciones de derivabilidad que el proyecto se pasó meses
**demostrando**. Los cinco borrados y los dos imports verificados como **fallidos**.

**Véase también:** `FOL/cuarentena/README.md` (el detalle entero),
`FOL/cuarentena/Inconsistencia.lean` (la evidencia), `sondeos/AnclaSoundness.lean`.

---

---

## ADR-026: El ancla de codificación deja de ser `axiom` y pasa a ser la CLASE `AnclaEq`

**Fecha:** 2026‑09‑12 · **Estado:** ✅ EJECUTADO (decisión del propietario: *«elegimos (A) parametrizar
con la IGUALDAD»*) · **Consecuencia de:** [ADR‑025](#) / **M‑11**

### El problema, medido

`axiom prf_axiomsCodeT_eq : Prf (axiomsCodeT =eq listFormCodeM axioms)` **HABITA el inductivo `Prf`**.
Por **M‑11** eso prohíbe demostrar nada sobre `Prf` por inducción — y el árbol lo hacía **tres veces**:

| teorema | dónde |
|---|---|
| `prf_to_derives` | `Meta/Hilbert.lean:256` |
| `prf_to_prfH` | `Meta/HilbertDeduction.lean:143` |
| `prf_to_derivation` | `Meta/HilbertSeq.lean:379` |

⛔ **Y no era latente**: `prf_to_prfH prf_axiomsCodeT_eq` está escrito literalmente en
`Meta/InAxiomsCodePrf.lean:308`, y en `:317` **D1 se aplica al propio postulado**
(`repr_pos'_prf (prf_eq_symm prf_axiomsCodeT_eq)`), pasando por `prf_iff_derivation` → la inducción.

⚠️⚠️ **Y `#print axioms` NO DETECTA esta clase**: los tres teoremas tienen footprint limpio y eran
**injustificados**. La regla del proyecto decía que el footprint se audita «sólo con `#print axioms`»;
esta clase de fallo **es invisible ahí**.

### 🔑 El fondo, que es lo que decide el diseño

Postular `Prf (ancla)` afirma que el ancla **tiene una derivación finita de Hilbert**, y
`prf_to_derivation` **cobra esa afirmación**. Lo que queremos es que el ancla sea **VERDADERA**.
La hipótesis dice exactamente eso y nada más.

### Lo medido antes de elegir: el ancla tiene TRES usos, y no piden lo mismo

| # | dónde | qué necesita |
|---|---|---|
| 1 | `Representability2Prf.lean` (`prf_inAxC`) | sólo **pertenencia positiva** |
| 2 | `InAxiomsCodePrf.lean:308` | **la IGUALDAD**, transportada a `PrfH` |
| 3 | `InAxiomsCodePrf.lean:317` | **la IGUALDAD**, metida **dentro de `Prov`** por D1 |

⇒ ⛔ **`AnclaPos` (sólo pertenencia) NO basta** — cubre (1) y deja (2) y (3) fuera. El panel del
2026‑09‑11 sólo había trazado el camino de Gödel I y por eso le pareció suficiente.

### La decisión

    class AnclaEq : Prop where
      eq : Prf (axiomsCodeT =eq listFormCodeM axioms)

**CLASE y no argumento explícito**, y la razón es de coste medido: el ancla alcanza **16 módulos**.
Como argumento habría que tocar **las ~40 llamadas**; como clase, **la resolución de instancias la hila
sola** y **ninguna llamada cambia** — sólo las firmas. Se anotaron **~440 firmas** con `[AnclaEq]`, de
forma automática, en **54 rondas de `build → anotar → build`**.

### El resultado

| | antes | después |
|---|---|---|
| `axiom` de Lean en RPP | 5 | **4** |
| axiomas habitando `Prf` | 1 | **0** ⇒ las tres inducciones son **legítimas** |
| footprint de `goedel_first_prf` / `goedel_second_prf` | `[…, prf_axiomsCodeT_eq]` | **`[propext, Classical.choice, Quot.sound]`** |
| firma | `ConsistentH → ¬Prf godelCN` | **`∀ [AnclaEq], ConsistentH → ¬Prf godelCN`** |

### ⛔⛔ Lo que hay que decir SIEMPRE junto al footprint

**El postulado NO desapareció: se movió del footprint a la FIRMA.** Y **no hay ninguna
`instance : AnclaEq` en el árbol** [medido] ⇒ la hipótesis está **abierta**.

⇒ Anunciar «Gödel I y II con cero axiomas del proyecto» **sin esa frase sería M‑8 con otro nombre**.
La fila correspondiente está en `TEOREMAS-E-HIPOTESIS.md` §1, que es exactamente el control que
existe para esto (**P‑2**).

### ⚠️ Un error de método cometido al ejecutarlo, que conviene no repetir

Para estimar el alcance calculé un **cierre transitivo por NOMBRES** sobre el fuente: dio **2983 de
3527 declaraciones (85 % del árbol)**. Absurdo, y es la trampa ya documentada
(*«el cierre por nombres sobreestimó por dos órdenes; el compilador es la única medida»*). Se
descartó y se midió con el compilador: **~440 firmas, 54 rondas**.

**Véase también:** [ADR‑025](#) (M‑11), `TEOREMAS-E-HIPOTESIS.md`,
`Meta/Representability2Prf.lean` (la clase y su docstring), `doc/AUDITORIA-FOL-2026-09-12.md`.

---

## ADR-027: La justificación de ADR-010 está REFUTADA — `gen` no es la ω‑regla, y sí podría ser constructor

**Fecha:** 2026‑09‑12 · **Estado:** ✅ ACEPTADO · **Supersede:** la **§Justificación** de
[ADR‑010](#adr-010-meta-axiomas-en-minimalaxiomslean-son-meta-teoremas-de-aritmética-no-reglas-fol)
(su **decisión** queda en pie) · **Relacionado:** ADR‑024, ADR‑025 (M‑11), ADR‑026

### Qué dice ADR-010 y qué está medido

| ADR‑010 (2026‑05‑25) | medido |
|---|---|
| *«`gen` … es la **ω‑regla** (regla de Büchi)»* | ⛔ **FALSO.** La ω‑regla toma `A[n̄]` para cada **NUMERAL**; `gen` la toma para **todo `Term`** — variables libres y aplicaciones incluidas. **Premisa estrictamente mayor ⇒ regla más DÉBIL.** La fuerza del cálculo no viene de `gen`: viene de `raa` e `imp_intro` (`Meta/OmegaStrength.lean`) |
| *«Su presencia como `axiom` es correcta e **inevitable**»* | ⛔ **FALSO, y compilado.** Un `inductive` que incluye `gen` como constructor **typechequea** (`EXIT 0`, recursor sin axiomas): su premisa `∀ n : Term, D Γ A[n]` es una **ocurrencia POSITIVA** |
| *«**Soundness práctica**: la hipótesis meta‑nivel siempre recibe un argumento genuino»* | ⛔ **Es exactamente el detonador.** La premisa **vacua** no es un caso raro: es lo que hace que `axioms ⊢` sea **sintácticamente COMPLETO** (lo que no prueba, lo **refuta**) y por tanto **NO r.e.** — ADR‑024. Y con un teorema de solidez da **`False` sin hipótesis** (`../FOL/cuarentena/Inconsistencia.lean`) |

⭐ **Lo que ADR‑010 SÍ acertó, y conviene decirlo**: separó correctamente los **cuatro** con
hipótesis meta‑nivel (`imp_intro`, `raa`, `or_elim`, `ex_elim`) del resto, y su contraejemplo para
`imp_intro` es **el mismo** que hoy detona `soundness`. Su análisis era **mejor** que el docstring
de `FOL/MetaRules.lean`, que decía que los seis eran inevitables.

### La decisión

1. **Se mantiene la DECISIÓN de ADR‑010**: los cuatro con premisa‑función siguen como `axiom` —
   ahora por la razón correcta (**ocurrencia no positiva**, medida), no por «soundness práctica».
2. **Se retira la clasificación de `gen` como «ω‑regla / axioma matemático genuino»**. Es una regla
   de generalización sobre todo `Term`, **más débil** que la ω‑regla, y **podría ser constructor**.
3. **El criterio escrito pasa a ser PREMISA‑FUNCIÓN** (M‑11), no «meta‑regla».
4. ⬜ **Queda abierto (D‑2 de la auditoría)**: mover a constructores los cuatro evitables de FOL
   (`gen`, los dos `dne`, `forall_not_impl_exists_not`) ⇒ **13 → 9** axiomas en FOL y lista negra de
   `Derives` de 8 a 4, **sin tocar la fuerza del cálculo** y con **cero pruebas tocadas en `FOL/`**.

### ⬜ Lo que falta corregir aguas abajo

El error «`gen` = ω‑regla» sobrevive en **8 documentos** de RPP:
`GODEL-D-ARITHMETIZATION.md` (:13, :16, :25, :41, :52, :136), `GODEL-STATUS.md:188`,
`MINIMAL-AXIOMS.md:266`, `doc/REFERENCE-Incompleteness.md:9`.

**Véase también:** `Meta/OmegaStrength.lean` (la medición de la fuerza de `⊢`),
`../FOL/AXIOMS.md` §2 (la doctrina corregida y D‑2),
`doc/AUDITORIA-FOL-2026-09-12.md` R‑3.

---

## ADR-028: FOL pasa de 13 a 4 axiomas — y los cuatro son EXACTAMENTE los que el kernel obliga

**Fecha:** 2026‑09‑12 · **Estado:** ✅ EJECUTADO · **Decisiones del propietario:** D‑2, D‑3, D‑4, D‑5
de `doc/AUDITORIA-FOL-2026-09-12.md` · **Relacionado:** ADR‑025 (M‑11), ADR‑027

### El resultado

    FOL:  34 → 28 → 13 → 4 axiomas,  en un día

Y los cuatro que quedan —`imp_intro`, `raa`, `or_elim`, `ex_elim`— son **exactamente** aquellos cuya
premisa es `Γ ⊢ A → Γ ⊢ B`, es decir una **ocurrencia NO POSITIVA** que el kernel rechaza:

    (kernel) arg #3 of 'D.raa' has a non positive occurrence of the datatypes being declared

⇒ **no hay alternativa dentro del tipo.** El censo de FOL es hoy **irreducible**.

### D‑2 · Cuatro axiomas pasan a ser CONSTRUCTORES (13 → 9)

`gen`, `dne` (regla), `dne` (esquema) y `forall_not_impl_exists_not` **no tenían por qué ser
axiomas** — ADR‑027 ya había refutado que `gen` fuese «inevitable». Hoy son
`Derives.gen_rule`, `Derives.dne_rule`, `Derives.dne_schema` y `Derives.forall_not_ex_not`.

* ⭐ **Los nombres y las firmas se conservan** (como `theorem`): las **336 citas** de RPP —`gen`
  sola, **323**— no cambiaron ni una.
* ⭐ **Coste medido: CERO.** No hay ni una inducción sobre `Derives` en ninguno de los dos repos.
* 🔑 **Y no es contabilidad**: un `axiom` que habita un inductivo **afirma una falsedad sobre el
  punto fijo**; un constructor **lo extiende**. La lista negra de M‑11 baja de **8 a 4** en FOL.

### D‑3 · `Completeness.lean` a cuarentena (9 → 4)

702 líneas y **cinco axiomas** en un módulo con **cero consumidores reales**. Dos de los cinco son
**construibles** (`Formula` es numerable) y se postularon en un commit titulado «100 % sorry‑free».

⇒ ⚠️ **No hay Teorema de Completitud demostrado** en el sentido en que `README.md` lo publicaba.

⭐ El riesgo que la auditoría señalaba —retirarlo rompería 20 módulos de RPP vía `Theorems.Eq`, que
**no estaba en el barrel**— se había resuelto horas antes metiéndolo.

### D‑4 · El barrel se parte: `FOL.Core` + `FOL`

**Medido**: RPP importa **nueve** módulos de FOL, y **nunca** el barrel. `FOL.Core` es exactamente
esos nueve; `FOL` = `FOL.Core` + `Semantics`. Antes `import FOL` arrastraba `Completeness` y con él
cinco postulados que el consumidor no usaba.

### D‑5 · El git‑lock, apuntado

⚠️ **Corrección a la auditoría**: decía que el mecanismo estaba **inerte**. **No lo estaba** — el
hook está instalado y salta en cada commit (avisó de `sorry` en los de hoy). Lo que fallaba era
otra cosa: `locked_files.txt` contenía la cadena literal **`an`** —basura, no una ruta— y
`frozen_files.txt` estaba vacío. Es decir: **armado y apuntando a nada**, que es peor que inerte
porque `make status` lo presentaba como una salvaguarda activa.

### ⬜ Lo que NO cambia

* **`Derives` sigue prohibido para inducción** (M‑11): quedan los 4 de FOL **más** los tres de RPP
  (`ax_induction_prim`, `ax_list_induction`, `ax_axiomsCodeT_eq`). ⚠️ Y `ax_list_induction` es de
  los malos: **premisa‑FUNCIÓN** fabricada por nosotros (ADR‑027, R‑1).
* **La fuerza del cálculo es la misma.** `⊢` sigue siendo sintácticamente completo y **no r.e.**:
  eso lo causan las cuatro premisas‑función, que son justo las que no se han podido tocar.

**Véase también:** `../FOL/AXIOMS.md` (el censo, reescrito), `../FOL/cuarentena/README.md`,
`doc/AUDITORIA-FOL-2026-09-12.md` §5.

---

## ADR-029: `ax_list_induction` pierde su premisa‑función — y M‑11 sobre `Derives` se declara PERMANENTE

**Fecha:** 2026‑09‑13 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑023, ADR‑025 (M‑11), ADR‑027, ADR‑028

### 1 · El cambio de forma

`ax_list_induction` (`Full/Lists.lean`) era **el único habitante de `Derives` fabricado por
nosotros con premisa‑FUNCIÓN**:

    (step : ∀ h t : Term, Γ ⊢ φ t → Γ ⊢ φ (cons h t))      ← función de Lean

Misma forma que `raa`, y **misma patología**: si `Γ ⊬ φ t`, esa función existe **vacuamente** y el
axioma regalaba `∀L, Γ ⊢ φ L`. Ahora la premisa es una **implicación OBJETO**:

    (step : ∀ h t : Term, Γ ⊢ (φ t ⇒ φ (cons h t)))        ← familia indexada por Term

| | antes | ahora |
|---|---|---|
| forma de `step` | `Derives → Derives` | `∀ h t : Term, Derives …` |
| ocurrencia | **NO POSITIVA** | **POSITIVA**, como `gen` |
| vacuidad explotable | ⛔ **sí** | ✅ **no** |
| ¿shape legal de constructor? | ❌ | ✅ **verificado compilando** (recursor sin axiomas) |

**Coste medido: 11 sitios**, todos con el mismo cambio de dos líneas
(`intro h t IH` → `intro h t; apply imp_intro; intro IH`). ⭐ Y uno **se simplificó**:
`list_induction_derives` ya tenía la implicación objeto a mano y consumía `mp e2 IH` sólo para
readaptarla; ahora pasa `e2` directamente.

⚠️ **Error de medición propio, registrado**: al planificarlo dije «3 sitios de uso real». Eran
**11**. La cifra salió de un `grep | head -10` **truncado**, y el `head` se comió los 8 de
`Meta/ProofChain.lean`. *Un grep truncado no es una medición.*

⬜ **Por qué NO se hace constructor**, ahora que la forma lo permitiría: porque **no es una regla
lógica, es un axioma de TEORÍA**. Como constructor de `Derives` valdría en **todo** contexto,
incluido `Γ = []`, diciendo que la inducción de listas es **lógicamente válida** — falso. Es el
mismo argumento de [ADR‑023](#) para `ax_induction`.

### 2 · ⛔⛔ M‑11 sobre `Derives` es PERMANENTE

Conviene decirlo como conclusión y no dejarlo como tarea abierta:

> **`Derives` no admitirá inducción nunca.**

Porque los cuatro de `FOL/MetaRules.lean` **no pueden dejar de ser axiomas**: su premisa
`Γ ⊢ A → Γ ⊢ B` es una **ocurrencia no positiva**, y el kernel rechaza el `inductive` con todas las
letras — *«has a non positive occurrence of the datatypes being declared»*. No es una limitación de
nuestro diseño: es del tipo.

⇒ Aunque se hicieran hipótesis los tres de RPP (como [ADR‑026](#) hizo con el ancla `Prf`),
quedarían los cuatro. **La lista negra de `Derives` tiene un suelo de cuatro.**

🔑 **Y la lectura correcta no es «hay que limpiar `Derives`»**, sino la que [ADR‑024](#) ya daba en
otro plano: **`⊢` es la herramienta de trabajo; el cálculo del que se puede DECIR algo es `Prf₀`**,
que tiene **cero** axiomas habitándolo y sobre el que está probado `prf0_soundness`.

### Estado del censo tras esto

| inductivo | habitantes‑axioma | ¿inducible? |
|---|---|---|
| `FOL.Derives` | **7** (4 FOL irreducibles + 3 RPP) | ⛔ **NUNCA** — suelo de 4 |
| `Prf` | 0 desde [ADR‑026](#) | ✅ sí |
| **`Prf₀`**, **`PrfH`** | **0** | ✅ sí |

**Véase también:** `Full/Lists.lean` (el axioma y su docstring), `../FOL/AXIOMS.md` §1,
`sondeos/AnclaSoundness.lean` (`prf0_soundness`).

---

## ADR-030: La enumerabilidad de `Formula` deja de ser un postulado — `FOL/Enumeration.lean`

**Fecha:** 2026‑09‑13 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑028 (D‑3), ADR‑029

### 1 · Qué se retira

`cuarentena/Completeness.lean` decía *«asumimos la enumerabilidad de las fórmulas»* y postulaba dos
axiomas:

    axiom formula_enum      : Nat → Formula
    axiom formula_enum_surj : ∀ f : Formula, ∃ n, formula_enum n = f

No hacía falta asumirla. **`FOL/Enumeration.lean`** (nuevo, ~330 líneas) la construye en cinco
capas —`unpair` · `natToList` · `natToString` · `natToTerm`/`natToTerms` · `natToFormula`—, cada
una con su sobreyectividad. `Completeness.lean` conserva los **nombres** (ahora `def` y `theorem`),
así que **ninguno de sus ocho sitios de uso cambió**.

| medida | valor |
|---|---|
| axiomas de `cuarentena/Completeness.lean` | **5 → 3** |
| footprint de `natToFormula_surj` | `[propext, Classical.choice, Quot.sound]` |
| ⭐ footprint de `lindenbaum_lemma` | `[propext, Classical.choice, Quot.sound]` — **net‑0 puro** |
| axiomas de `FOL/` + `TheoryFramework/` | **4**, sin cambio |
| build | RPP **145 jobs** · `lake build "@FOL/FOL" "@FOL/TheoryFramework"` **22 jobs** |

⭐ **El Lema de Lindenbaum queda INCONDICIONAL.** No era el objetivo, pero era el único consumidor
de los dos postulados. Recíproca de M‑1 otra vez: *cada axioma que se retira audita lo que se
apoyaba en él.*

⚠️ **Y el veredicto sobre la completitud NO cambia.** Quedan `termEqv_func_congr`,
`termEqv_rel_congr` y —el caro— `henkin_extension_lemma`. **La cifra baja; el titular no.**

### 2 · Las tres decisiones técnicas que lo hicieron barato

1. ⭐ **El par de Cantor sin números triangulares.** La inversa habitual exige
   `n = (a+b)(a+b+1)/2 + b` y con ella identidades de división entera, caras sin Mathlib. `unpair`
   **camina la diagonal** con un paso estructural, y la sobreyectividad sale por inducción doble
   sin una sola división. 🔑 *La recursión se pone donde la PRUEBA la quiere, no donde la fórmula
   la sugiere.*
2. ⚠️ **`String` se midió ANTES de construir**, porque era el único punto que podía bloquearlo
   todo (`Formula.atom : String → List Term → …`). El núcleo da `Char.ofNat_toNat` y
   `String.ofList_toList`, que basta. ⚠️ En v4.31 `String` ya **no** es `structure String where
   data : List Char` sino UTF‑8 opaco: `String.mk s.data = s` **no** vale por `rfl`.
3. ⚠️ **Las sobreyectividades de `Term` y `Formula` no son inducción sobre el inductivo**, sino
   sobre una COTA de tamaño (`∀ N, ∀ t, size t < N → …`), el patrón de `truth_lemma_lt`. `Term` es
   un inductivo **anidado** y así se esquiva escribir su recursor mutuo a mano.

### 3 · Dónde vive, y por qué NO en `cuarentena/`

`FOL/Enumeration.lean` entra por el barrel `FOL.lean`, que es `@[default_target]`.

🔑 **Una construcción que retira un axioma y vive fuera del build no retira nada**: nadie la
verifica. Es exactamente la enfermedad que este repo lleva tres días pagando (el `.olean`
fantasma, `TheoryFramework` roto durante meses, los 15 axiomas de las librerías sin compilar).

⚠️ Y se midió un **agujero de CI que nadie había visto**: `lake build` desde RPP compila **sólo los
nueve módulos de FOL que RPP importa**. `FOL.Semantics`, `FOL.Enumeration` y `TheoryFramework`
entera **no los compilaba nadie en CI**. Añadido el paso
`lake build "@FOL/FOL" "@FOL/TheoryFramework"` a `.github/workflows/build.yml`.

⚠️ Y `check-axioms.bash` de FOL ahora **también cuenta la cuarentena** (`ESPERADO_CUAR=3`),
porque la cifra «3» quedó escrita en seis documentos y **no la comprobaba nada**. Probado en los
dos sentidos.

### 4 · ⚠️⚠️ El error de método, registrado

**La prueba YA EXISTÍA y la volví a escribir.** La auditoría del 2026‑09‑12 la había compilado
(**M‑2**, *«derivable — COMPILADO en 94 líneas»*) y dejó el fichero en
`…/scratchpad/ProbeEnum.lean`. Al ir a construir busqué en los dos repos, no encontré nada, y
construí de nuevo.

🔑 **Dos reglas salen de aquí:**

* *Antes de construir, buscar* — **y buscar incluye el scratchpad de la propia sesión**, no sólo
  el árbol. (Van seis veces que esta regla paga o cobra.)
* **Una medición cuyo artefacto vive en un directorio efímero es una medición que se evapora.** La
  auditoría escribió la conclusión en el informe y dejó la prueba fuera del árbol; tres semanas
  más y no habría existido.

**Reparado**: el fichero está rescatado en `sondeos/EnumFormulaPorInyeccion.lean`, recompilado hoy.

⚠️ Y las dos rutas **no son la misma**, así que la duplicación no fue del todo estéril:

| | `FOL/Enumeration.lean` (adoptada) | `sondeos/EnumFormulaPorInyeccion.lean` |
|---|---|---|
| dirección | `Nat → Formula`, **computable** | `Formula → Nat` **inyectiva** + `Classical.choose` |
| `#eval` | ✅ funciona | ❌ `noncomputable` |
| líneas | ~330 | **102** |
| footprint | `[propext, Classical.choice, Quot.sound]` | **idéntico** |

Se adoptó la computable: en un proyecto sobre **representabilidad** y conjuntos **r.e.**, una
enumeración obtenida por elección es una sobreyección *semántica* y nada más. El precio son 230
líneas. ⬜ Cambiar de una a otra es **una línea** en `cuarentena/Completeness.lean`.

**Véase también:** `../FOL/FOL/Enumeration.lean`, `../FOL/AXIOMS.md` §2.4,
`../FOL/cuarentena/README.md` §9, `doc/AUDITORIA-FOL-2026-09-12.md` M‑2.

---

## ADR-031: Las dos congruencias de la igualdad, DEMOSTRADAS — la Completitud queda a UN postulado

**Fecha:** 2026‑09‑13 · **Estado:** ✅ EJECUTADO · **Relacionado:** ADR‑028 (D‑3), ADR‑030

### 1 · Qué se retira

`cuarentena/Completeness.lean` postulaba la congruencia de la igualdad bajo los dos constructores
que llevan **lista** de argumentos:

    axiom termEqv_func_congr … : PointwiseEqv S ts1 ts2 → termEqv S (func f ts1) (func f ts2)
    axiom termEqv_rel_congr  … : PointwiseEqv S ts1 ts2 → (S (atom p ts1) ↔ S (atom p ts2))

Los dos son **teoremas**. La medición pedida por el propietario (*«mide `termEqv_func_congr` y
`termEqv_rel_congr`»*) se hizo compilando, y salió cerrada.

| medida | valor |
|---|---|
| axiomas de `cuarentena/Completeness.lean` | **3 → 1** (y **5 → 1** en el día) |
| `termEqv_func_congr` / `termEqv_rel_congr` | `[propext, Classical.choice, Quot.sound]` |
| ⭐ `evalTerm_canonical` (modelo canónico) | **net‑0 puro** |
| ⭐⭐ `truth_lemma` (Lema de la Verdad) | **net‑0 puro** |
| `model_existence_lemma` / `completeness` | `henkin_extension_lemma`, **y nada más** |
| coste | ~45 líneas en `FOL/Theorems/Eq.lean` + ~55 en `Completeness.lean` |
| build | FOL **22 jobs** · RPP **145 jobs** · `check-axioms.bash` EXIT=0 (`ESPERADO_CUAR=1`) |

⚠️ **Y el veredicto NO se mueve.** Con `henkin_extension_lemma` postulado, `completeness` no está
demostrado. 🔑 Lo que cambia es **dónde está la deuda**: ya no repartida en cinco sitios, sino
concentrada en uno, con nombre, y con su dificultad bien identificada (amplía el lenguaje con
constantes nuevas y hay que probar la conservatividad).

### 2 · 🔑 Lo que faltaba no era de LÓGICA, era de LISTAS

`Derives.subst` es Leibniz **con índice 0**: `Γ ⊢ t₁ ≐ t₂ → Γ ⊢ φ[t₁] → Γ ⊢ φ[t₂]`. Sustituye **un**
término. Pero `Term.func` y `Formula.atom` llevan una **lista** de argumentos, y la congruencia hay
que hacerla posición a posición.

La técnica de la fórmula‑contexto ya existía en el repo desde siempre —`derive_eq_symm` y
`derive_eq_trans` la usan: se pone `Term.var 0` en el hueco, `liftTerm 0` en todo lo demás, y
`substTerm_liftTerm` la vuelve a cerrar—. Lo único que **no** existía era **abrir el hueco dentro
de la lista**: partirla en `pre ++ x :: post` y saber que `substTerms` distribuye sobre `++`.

⇒ **`substTerms_append`, cuatro líneas, era toda la pieza que faltaba.** Con ella salen seguidos
`substTerms_lift_hole`, `derive_eq_func_congr` y `derive_atom_congr`.

🔑 *Un axioma que lleva meses en pie puede estar esperando un lema de fontanería, no un teorema.*
Es el mismo patrón que ADR‑030 (allí el bloqueo aparente era `String` y bastaba un lema del núcleo).

### 3 · Dónde va cada mitad

| pieza | dónde | por qué |
|---|---|---|
| `substTerms_append`, `substTerms_lift_hole`, `derive_eq_func_congr`, `derive_atom_congr` | **`FOL/Theorems/Eq.lean`** — en el build | son lemas **generales de igualdad** que a la librería le faltaban, no andamiaje de la cuarentena |
| `DerivesSet_map`/`_map2`, `pointwiseEqv_symm`, los dos teoremas | `cuarentena/Completeness.lean` | traslado a conjuntos e inducción sobre `PointwiseEqv` |

⚠️ **La inducción sobre `PointwiseEqv` es legítima**: es un `inductive` **sin ningún `axiom`
habitándolo** ⇒ **M‑11 no aplica**. Conviene comprobarlo explícitamente cada vez que se induce.

### 4 · ⭐ La estimación de la mañana se comprobó la misma tarde

`AXIOMS.md` §2.4 decía de estos dos: *«derivable en principio, **no medido**»*. Estaba **bien
etiquetado**, y al medirlo resultó cierto.

🔑 *Una estimación declarada como estimación no hace daño; la que se publica como medición, sí.*
Es la cara buena de «medir una obstrucción no es probarla»: también
vale al revés — **declarar que algo no está medido es lo que permite volver y medirlo**.

**Véase también:** `../FOL/FOL/Theorems/Eq.lean` (las cuatro piezas nuevas),
`../FOL/AXIOMS.md` §2.5, `../FOL/cuarentena/README.md` §9.

---

## ADR-032: `henkin_extension_lemma` SE MIDIÓ — sale, y por eso se QUEDA

**Fecha:** 2026‑09‑13 · **Estado:** ✅ **DECIDIDO — opción (A), sanción del propietario**:
*el axioma se queda*. El árbol no se toca; lo que se guarda es la medición y el porqué. ·
**Relacionado:** ADR‑024 (M‑10), ADR‑025 (M‑11), ADR‑030, ADR‑031

### 1 · El encargo y el resultado

El último axioma de `cuarentena/Completeness.lean`. El juicio publicado —mío, esa misma mañana—
era: *«el caro de verdad: su prueba clásica amplía el lenguaje con constantes nuevas»*.

⚠️⚠️ **Ese juicio era FALSO, y lo dice el compilador.** `sondeos/HenkinSaleDeRaa.lean`:

    IsMaximalConsistent S → IsHenkin S        ← teorema, compilado
    henkin_extension_lemma                     ← `lindenbaum_lemma` + tres líneas

⇒ `cuarentena/Completeness.lean` llegaría a **CERO axiomas propios**.

### 2 · ⚠️⚠️ Y el precio, que es el verdadero hallazgo

| | axiomas propios | footprint de `completeness` |
|---|---|---|
| hoy | **1** | `[propext, Classical.choice, Quot.sound, henkin_extension_lemma]` |
| pagándolo | **0** | `[propext, Classical.choice, Quot.sound, `**`FOL.MetaRules.raa`**`]` |

**No es «1 → 0».** Es cambiar un postulado **propio, honesto y con nombre** por **el axioma que
hace el cálculo completo y NO sólido** — el mismo que en `cuarentena/Inconsistencia.lean` da
`False` en cuanto se le junta cualquier teorema de solidez.

⚠️ Y hay un coste estructural aparte: obliga a que `Completeness.lean` **importe `FOL.MetaRules`**,
cosa que hoy **no hace** (medido: siete imports, ninguno es `MetaRules`). `cuarentena/README.md` §4
presentaba justamente ese hecho como la razón de que este módulo **no** estuviera en el radio de la
inconsistencia. Pagarlo lo mete dentro.

### 3 · Por qué sale — y por qué eso es la mala noticia

`raa : (Γ ⊢ A → Γ ⊢ ⊥) → Γ ⊢ ¬A` toma una **función de Lean**: si `Γ ⊬ A` existe **vacuamente**
⇒ `Γ ⊢ ¬A`. De ahí, en tres líneas:

    derives_complete (Γ A) : (Γ ⊢ A) ∨ (Γ ⊢ ¬A)

**Todo contexto decide toda fórmula.** Con eso, el obstáculo clásico —constantes frescas y
conservatividad— **ni se plantea**: el testigo del existencial sale de la completitud sintáctica.

La cadena, sin una sola constante nueva:

1. `S` maximal consistente, `S (∃A)` ⇒ hay `Γ0 ⊆ S` finito con `Γ0 ⊢ ∃A`.
2. Si ninguna instancia está en `S`, **ninguna es derivable desde `Γ0`** (si lo fuera,
   `max_cons_contains` la metería). ⭐ **Y el contexto es UNIFORME**: `Γ0` para todas a la vez —
   que era exactamente el punto donde el argumento parecía romperse.
3. `no_instance_no_body`: ninguna instancia derivable ⇒ el **cuerpo** no lo es desde el contexto
   **levantado**, por `intro_forall` seguido de `elim_forall`. ⭐ Footprint **`[propext]`**: esta
   pieza **no usa `raa`** y es la que sustituye a la generalización sobre constante fresca.
4. `raa` en el contexto levantado da `¬A`, y `elim_ex` cierra con `⊥`.

⚠️ **M‑11 NO se viola**: no hay ni una inducción sobre `Derives` — sólo constructores, `raa` como
**introducción**, y tercio excluido sobre la `Prop` `Γ ⊢ A`. Las pruebas son legítimas.
⚠️ Pero **no valdrían para un cálculo sólido**, donde `derives_complete` es falso.
🔑 **Esta Henkin sale de la patología, no de la lógica.**

### 4 · Lo que NO se sigue

**No** se sigue `False`. El detonador de `Inconsistencia.lean` es `raa` **más solidez**, y
`Completeness.lean` no demuestra solidez y va en la dirección contraria. El módulo quedaría
consistente; lo que quedaría comprometido es **lo que su teorema significa**.

### 5 · ✅ La decisión: **(A)**, el axioma se queda

Sancionada por el propietario el **2026‑09‑13**. Las tres opciones que había sobre la mesa:

| | opción | qué publica | |
|---|---|---|---|
| **A** | **dejar el axioma** y guardar la medición | `AXIOMS.md`: **1 axioma**, con nombre y con su dificultad **real** escrita. El lector ve dónde está la deuda | ✅ **ELEGIDA** |
| **B** | **pagarlo** | `AXIOMS.md`: **0 axiomas**. ⚠️ Y un cero se lee como «Completitud demostrada», cuando lo que habría detrás es «completitud de un cálculo que, cuando no deriva `A`, deriva `¬A`» | ❌ |
| **C** | pagarlo **y** escribir el aviso al lado | el cero, con el veredicto explícito. Depende de que **nadie cite la cifra sin el párrafo** | ❌ |

🔑 **Lo que (A) compra**: que la cifra del censo siga significando lo que dice. `AXIOMS.md`
existe porque *«un `sorry` es visible y un `axiom` no»*; un censo que baja a cero **comprando el
cero con `raa`** deja de ser un censo y pasa a ser publicidad.

#### Cómo queda protegida la decisión

⚠️ Una decisión de **no** hacer algo es la más fácil de deshacer por accidente: el que llegue
después ve un axioma, ve que es demostrable, y lo «arregla». Tres guardas:

| dónde | qué |
|---|---|
| `cuarentena/Completeness.lean`, junto al `axiom` | el aviso completo **en el punto de uso**, con el footprint de las dos opciones y la orden de **reabrir ADR‑032** antes de tocarlo. ⚠️ Y sustituye al comentario que decía «requiere expandir el lenguaje con constantes», **medido FALSO** |
| `check-axioms.bash` | `ESPERADO_CUAR=1` **rompe también si baja a 0**. El control ya protege la decisión **en los dos sentidos**, sin tocar nada |
| `AXIOMS.md` §2.6 · `cuarentena/README.md` §9.2 | la medición, con el precio en footprints |

⭐ **El control no hubo que cambiarlo**: `check-axioms.bash` compara con una cifra **exacta**, no
con una cota. Un contador exacto convierte *«no pagar este axioma»* en algo que el build vigila.

🔑 **El argumento de fondo es ADR‑024 otra vez**: `⊢` es la **herramienta**, no el **sujeto**. El
proyecto ya retiró `goedel_second'` por esto mismo (M‑10). Comprar un cero con `raa` sería la misma
operación en la dirección contraria.

⚠️ Y una lección de método, que es la tercera del día: *«el caro de verdad»* era una **estimación
mía publicada en un documento de censo sin la etiqueta de estimación**. Las dos anteriores
(ADR‑031 §4) estaban bien etiquetadas y por eso volvimos a medirlas. Ésta no lo estaba, y se
publicó tres veces (`AXIOMS.md`, `cuarentena/README.md`, `NEXT-STEPS.md`) antes de medirse.
🔑 **Una estimación sin etiqueta es una medición falsa.**

**Véase también:** `sondeos/HenkinSaleDeRaa.lean`, `../FOL/AXIOMS.md` §2.6,
`../FOL/cuarentena/README.md` §9.2, `../FOL/cuarentena/Inconsistencia.lean`.

---

## ADR-033: `Derives₀` — el cálculo sobre el que la metateoría SÍ significa algo (Paso 0)

**Fecha:** 2026‑09‑14 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑024 (M‑10), ADR‑025/ADR‑029 (M‑11), ADR‑032 ·
**Plan:** `doc/PLAN-COMPLETITUD-FINITISTA.md` §3

### 1 · El problema que resuelve

`Derives` **no puede ser el sujeto** de ningún teorema metateórico, y las tres razones están
medidas:

1. ⛔ es **sintácticamente completo** (`raa` toma una función de Lean ⇒ lo que no prueba, lo
   refuta) ⇒ **no es r.e.**;
2. ⛔ **no es sólido** — `cuarentena/Inconsistencia.lean` compila `False` a partir de cualquier
   teorema de solidez suyo;
3. ⛔ **no admite inducción** (M‑11), y eso es **permanente**: suelo de cuatro axiomas.

### 2 · La solución, y por qué es barata

    inductive Derives₀ : List Formula → Formula → Prop     -- 21 constructores
    derives0_to_derives : Γ ⊢₀ f → Γ ⊢ f

Los **22** constructores de `Derives` **menos `gen_rule`**, y **sin** los cuatro axiomas de
`MetaRules`. `FOL/Derives0.lean`, dentro del barrel `FOL` (`@[default_target]`).

| medida | valor |
|---|---|
| `Derives₀.rec` | **`[propext]`** — cero axiomas del proyecto |
| `derives0_to_derives` | `[propext]` |
| habitantes‑axioma | **0** ⇒ **M‑11 no aplica** |
| build FOL | 22 → **23 jobs** |
| ⭐ build RPP | **145 jobs, SIN CAMBIO** |

⭐ **No se pierde ninguna REGLA, sólo la fuerza META** — medido en
`sondeos/DerivesSinMetaReglas.lean`: el inductivo pelado ya tiene `intro_impl` (que hace de
`imp_intro` y de `raa` con `B := ⊥`), `elim_or`, `elim_ex`, `dne_rule` y `dne_schema`, las seis con
footprint `[propext]`.

⚠️ **`gen_rule` se queda fuera a propósito**: su premisa `∀ n : Term, …` es **infinitaria** (la
ω‑regla sobre términos). Un cálculo finitario no la lleva, y la introducción de `∀` la da
`intro_forall`, la regla de la eigenvariable con De Bruijn. ⭐ Coste cero para lo que ya hay:
`cuarentena/Completeness.lean` usa **14** constructores distintos y **`gen_rule` no está entre
ellos** (medido).

### 3 · ⭐ Por qué NO toca ROBINSON_PlusPlus — y por qué eso importa

`Derives₀` es un objeto **NUEVO**, no un reemplazo, y el puente va en **una** dirección. RPP sigue
con `Derives`: `gen` 323 usos, los cuatro axiomas 320, los constructores 164. **Ni una cita
cambia**, y el módulo entra por el barrel `FOL`, que RPP **no importa**.

🔑 **Es mucho más barato que la «reparación de fondo»** de `../FOL/cuarentena/README.md` §8
—partir `Derives`/`DerivesW`, priced allí como «no es una tarde»— y **da exactamente lo mismo para
el objetivo**: un cálculo sobre el que se puede inducir.

⇒ *Cuando un tipo está contaminado, a veces no hay que limpiarlo: hay que declarar al lado el que
sí sirve, y quedarse con el viejo como herramienta.* Es ADR‑024 llevado al tipo.

### 4 · ⭐ La prueba de que el paso funciona es el propio encaje

`derives0_to_derives` se demuestra **por inducción sobre `Derives₀`** — veintiún casos, cada uno
su constructor homónimo—, que sobre `Derives` sería **ilegítima**. El fichero compiló a la primera.

⚠️ **La recíproca no vale, y a propósito.** La metateoría vive del lado de `Derives₀`.

### 5 · ⬜ Lo que viene, en orden

1. ⚠️⚠️ **`derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`** — *el agujero de verdad del repo*. Hoy hay un
   cálculo cuya solidez es **falsa**, y eso pesa más que no tener la completitud. Plantilla:
   `prf0_soundness` (`sondeos/AnclaSoundness.lean`), net‑0 puro.
2. El **lema de renombrado** sobre derivaciones — desbloqueado por este ADR — que es lo que hace
   falta para la extensión de Henkin de verdad.
3. Portar `cuarentena/Completeness.lean` a `Derives₀` y medir qué se rompe.

**Véase también:** `../FOL/FOL/Derives0.lean`, `sondeos/DerivesSinMetaReglas.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §3 y §9.

---

## ADR-034: `derives0_soundness` — el repo tiene por fin un cálculo de FOL⁼ SÓLIDO (Paso 1)

**Fecha:** 2026‑09‑14 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑024 (M‑10), ADR‑025 (M‑11), ADR‑033 ·
**Plan:** `doc/PLAN-COMPLETITUD-FINITISTA.md` §4

### 1 · Lo que se demuestra

    derives0_soundness : Γ ⊢₀ f → Γ ⊨ f          -- `../FOL/FOL/Soundness0.lean`

| medida | valor |
|---|---|
| `derives0_soundness` | `[propext, Classical.choice, Quot.sound]` — **cero axiomas del proyecto** |
| 🏁 `derives0_consistent : ¬ ([] ⊢₀ ⊥)` | ídem |
| 🏁🏁 `derives0_not_complete` | ídem |
| build | FOL 23 → **24 jobs** · RPP **145, sin cambio** |

⛔ **Para `Derives` esto es IMPOSIBLE**: su solidez es **falsa** y con `raa` da `False` sin
hipótesis (`../FOL/cuarentena/Inconsistencia.lean`). Es M‑11: los cuatro axiomas **habitan** el
tipo. `Derives₀` tiene **cero habitantes‑axioma** (ADR‑033) ⇒ la inducción es legítima ⇒ el
teorema es de verdad.

### 2 · 🏁 Los dos corolarios, que son lo que importa

* **`derives0_consistent`** — la **primera prueba de consistencia de un cálculo de FOL⁼** en el
  proyecto. Cinco líneas, con el modelo trivial sobre `Unit`.
* ⭐⭐ **`derives0_not_complete`** — hay `A` con `[] ⊬₀ A` **y** `[] ⊬₀ ¬A`.
  **Éste certifica que el Paso 0 sirvió para lo que tenía que servir**: `Derives` **sí** decide
  toda fórmula (`raa` toma una función de Lean ⇒ lo que no prueba, lo refuta), y ésa es justamente
  la patología que lo inhabilita como sujeto — completo ⇒ **no r.e.** ⇒ incumple la tercera
  hipótesis de Gödel I (ADR‑024, **M‑10**). `Derives₀` **no** la padece, y la prueba son dos
  modelos sobre `Unit`: todas las relaciones verdaderas / todas falsas.

⇒ 🔑 **`Derives₀` es sólido, consistente y no decide todo.** Un cálculo del que se puede decir
algo.

### 3 · ⭐ Costó mucho menos de lo estimado, y la razón vale más que el ahorro

Los **18 casos originales se rescataron de `../FOL/cuarentena/Soundness.lean`**. Aquella prueba
**era correcta caso por caso** —deducción natural intuicionista, cada regla semánticamente
válida—; lo que la invalidaba era **el tipo sobre el que inducía**, no su contenido.

🔑 **Cuando un teorema cae por M‑11, su demostración suele estar bien: lo que hay que cambiar es el
SUJETO, no la prueba.** Es el complemento exacto de M‑11, y conviene tenerlo escrito al lado:
*un módulo en cuarentena no es un módulo equivocado; puede ser un módulo bien escrito sobre el
objeto equivocado.*

Sólo hubo que añadir **tres** casos: `dne_rule`, `dne_schema` y `forall_not_ex_not` —los
constructores que D‑2 introdujo (ADR‑028) y que la prueba vieja no cubría—, y son los únicos que
piden lógica clásica en el metanivel. De ahí el `Classical.choice`: legítimo, la semántica es
clásica. ⚠️ Sin Mathlib **no hay `by_contra`**: `Classical.byContradiction` a mano.

⚠️ **Y volvió a morder la trampa §12** de `feedback_lean_notation_traps`: en el enunciado de
`derives0_not_complete`, `∧` se parsea como **`Formula.and`** y `¬` como **`neg`**. Hay que
escribir `And` y `Not` explícitos cuando el enunciado es META y el fichero tiene la notación de
FOL⁼ abierta.

### 4 · ⬜ Lo que sigue

1. 🏁 **HECHO el mismo día**: `check-footprints.bash` (raíz de RPP, `make footprints`, y en CI).
   Compara **13 titulares** de los dos repos con su footprint publicado y **rompe** si no cuadra.
   Probado con el fallo puesto en los dos modos —footprint distinto y declaración ausente—, los
   dos con `EXIT=1`. 🔑 *Un `info:` en medio de 145 jobs no es un control.*
2. El **lema de renombrado** sobre derivaciones de `Derives₀`, que desbloquea la extensión de
   Henkin de verdad (plan §6.2).
3. Portar `cuarentena/Completeness.lean` a `Derives₀` y medir qué se rompe (plan, orden 3).

**Véase también:** `../FOL/FOL/Soundness0.lean`, `../FOL/cuarentena/Soundness.lean` (de donde
salen los 18 casos), `doc/PLAN-COMPLETITUD-FINITISTA.md` §4.

---

## ADR-035: `derives0_rename` — la pieza que Henkin necesitaba, y es CONSTRUCTIVA

**Fecha:** 2026‑09‑14 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑033, ADR‑034 · **Plan:** `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2

### 1 · Qué se demuestra

    derives0_rename (ρ : String → String) :
        Γ ⊢₀ f  →  Γ.map (renameFormula ρ) ⊢₀ renameFormula ρ f

`../FOL/FOL/Rename.lean`, en el build. Footprint **`[propext, Quot.sound]`** — ⭐ **ni siquiera
`Classical.choice`**: el renombrado es **puramente constructivo**.

### 2 · Por qué hacía falta

Es **la pieza que la extensión de Henkin necesita**. La construcción clásica añade testigos
`(∃A) → A[c]` con `c` fresca, y la consistencia de cada paso se prueba por contraposición: de una
derivación que usa `c` hay que fabricar otra que no la use. Eso es **transformar una derivación**.

⛔ Sobre `Derives` es **ilegítimo** (M‑11). ✅ Sobre `Derives₀` (ADR‑033) es trabajo ordinario.
🔑 **Es el primer rendimiento concreto del Paso 0**, y confirma que la inversión estaba bien hecha.

### 3 · ⭐ Por qué salió barato

| | |
|---|---|
| **el renombrado no toca las variables** | conmuta con `liftTerm`/`substTerm` sin capturas — es mucho más barato que una sustitución |
| `LocalRule` tiene **un solo constructor** | el caso `rewrite_at`, que parecía el caro, son tres líneas |
| `ρ` **no** necesita ser inyectiva | para esta dirección, un renombrado cualquiera transporta derivaciones |

Lemas previos: `rename_liftTerm`/`_liftTerms`/`_liftFormula`, `rename_substTerm`/`_substTerms`/
`_substFormula`, `rename_getAt?`, `rename_replaceAt`, `rename_localRule`, `map_rename_lift`.
Y `rename_neg` sale por **`rfl`**.

### 4 · ⚠️ Una decisión de diseño que conviene tener escrita

**Sólo se renombran símbolos de FUNCIÓN**; los de relación (`Formula.atom p ts`) quedan intactos.
En esta firma los dos son `String`, pero son **dos espacios de nombres distintos** (`Model.func` y
`Model.rel`), y lo que Henkin mueve son **constantes**, que son funciones de aridad cero.
Renombrar también los relacionales confundiría los dos espacios.

### 5 · 🏁 La RECÍPROCA, el mismo día — y sale sin inducción nueva

    derives0_rename_inv (hσ : ∀ s, σ (ρ s) = s) :
        Γ.map (renameFormula ρ) ⊢₀ renameFormula ρ f  →  Γ ⊢₀ f

Es `derives0_rename σ` **aplicado a la inversa**, más la cancelación de las dos capas: **cuatro
líneas, cero casos**.

🔑 **Cuando una operación es funtorial y tiene inversa por un lado, su «conservatividad» es el
mismo teorema aplicado a la inversa.** No hay que volver a inducir sobre el cálculo. ⚠️ Yo había
anunciado la recíproca como «otra pieza» que «pedirá `ρ` inyectiva»; las dos mitades de esa frase
resultaron equivocadas.

| teorema | footprint |
|---|---|
| `derives0_rename` | `[propext, Quot.sound]` |
| `derives0_rename_inv` | `[propext, Quot.sound]` ⭐ **constructivo** |
| `derives0_rename_iff` (las dos direcciones) | `[propext, Quot.sound]` |
| `derives0_rename_conservative` (hipótesis: **inyectividad**) | `[propext, Classical.choice, Quot.sound]` |

⭐⭐ **La separación es exacta**: la conservatividad **no** necesita elección; la necesita **sólo**
el paso *«inyectiva ⇒ tiene inversa»*, que se aísla en `invOf` dentro de una sección con
`open Classical`. Por eso la forma buena del teorema pide **la inversa**, no la inyectividad — y en
la construcción de Henkin la inversa **se tiene escrita**, porque el renombrado es explícito.

### 6 · ⬜ Lo que sigue abierto, con nombre

⚠️ **Con esto AÚN NO está la extensión de Henkin**, y conviene no confundirlo. Falta el paso de
**eigenvariable**: de `Γ ⊢₀ φ(c)` con `c` fresca, concluir `Γ ⊢₀ ∀x φ(x)`.

Eso **no es un renombrado**: manda una **constante** a una **variable**, con corrimiento de índices
de De Bruijn bajo los binders. Es otra operación —llamémosla `abstractConst`— y otra inducción
sobre los 21 constructores. ⚠️ Y será **más cara** que ésta, precisamente porque **sí toca las
variables**, que es lo que hacía barato el renombrado.

⇒ Lo entregado es la **mitad de extensión de lenguaje** (meter la teoría en un sublenguaje y
traerse la contradicción de vuelta). La mitad del **testigo fresco** sigue abierta.

⚠️ Y un aviso medido ayer que caerá sobre la próxima pieza: el renombrado concreto que Henkin use
—del tipo `s ↦ "0" ++ s`— necesitará **descomponer cadenas** para su inversa, y en Lean v4.31 eso
trae `Classical.choice` (`sondeos/ClassicalChoiceCenso.lean`). Un argumento más para la firma con
`Nat` en vez de `String`.

**Véase también:** `../FOL/FOL/Rename.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2,
`check-footprints.bash` (que ya lo vigila).

---

## ADR-036: `derives0_gen_fresh` — el paso de EIGENVARIABLE, y con él las tres piezas de Henkin

**Fecha:** 2026‑09‑14 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑033, ADR‑034, ADR‑035 · **Plan:** `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2

### 1 · Qué se demuestra

    derives0_gen_fresh (c) (hfresh : ∀ g ∈ Γ, ¬ occursFormula c g) :
        Γ ⊢₀ φ  →  Γ ⊢₀ ∀ (absFormula c 0 φ)

`../FOL/FOL/Eigenvariable.lean`. Footprint **`[propext, Quot.sound]`** — net‑0 puro, **sin
`Classical.choice`**. Igual `absDerives` (el transporte, 21 casos) y `derives0_inst_fresh`.

⚠️ **No se pide** que `c` no aparezca en `φ`: al revés, la gracia es que `φ` **la usa**, y
`absFormula c 0 φ` es «`φ` con `c` convertida en la variable ligada».

### 2 · ⚠️ Por qué costó más que el renombrado

`FOL.Rename` manda símbolos a símbolos y **no toca las variables**; por eso conmutaba con todo
gratis. Aquí la operación manda una **constante** a una **variable**, así que **sí** toca los
índices de De Bruijn: al entrar en un binder, el índice sube.

⇒ Las conmutaciones llevan **hipótesis de nivel**: `absTerm_lift`/`absFormula_lift` piden `j ≤ k`;
`absTerm_subst`/`absFormula_subst` piden `v ≤ k`. Se usan con `j = 0` y `v = 0`, donde son
triviales, **pero la inducción bajo binders las necesita generales**.

⚠️ Y el `∀ k` tiene que estar **dentro** del enunciado de `absDerives`, en el motivo de la
inducción: en `intro_forall` y `elim_ex` la hipótesis inductiva se usa a nivel `k + 1`. Con el `k`
fijado fuera, la inducción **no cierra**.

### 3 · ⚠️⚠️ El error de enunciado que cazó el compilador

Escribí `abs_getAt?` y `abs_replaceAt` **a nivel constante**, copiando los de `FOL.Rename`. Son
**FALSOS**: `getAt?`/`replaceAt` **atraviesan binders** (`Pos.body`), y `absFormula` **cambia de
nivel** al entrar en uno. Hubo que introducir `posDepth : Pos → Nat` —cuántos `body` tiene el
camino— y enunciarlos como

    getAt? (absFormula c k f) p = (getAt? f p).map (absFormula c (k + posDepth p))

🔑 **Cuando una operación depende de la profundidad, todo lo que navegue el árbol tiene que
llevarla en el enunciado.** Es la trampa de copiar un lema de una operación que *no* dependía de
ella.

### 4 · ⭐ Por qué encaja tan bien en este cálculo

`Derives₀.intro_forall` **ya es** la regla de la eigenvariable en forma de De Bruijn
(`Γ.map (liftFormula 0) ⊢₀ A → Γ ⊢₀ ∀A`), y es un **constructor**. Lo único que faltaba era llevar
la derivación desde «constante fresca» hasta «contexto levantado», y eso es exactamente
`absFormula_eq_lift`: **si `c` no aparece, abstraerla ES levantar**.

⇒ El teorema final son cuatro líneas sobre `absDerives`.

### 5 · Estado de las tres piezas de Henkin

| pieza | estado | footprint |
|---|---|---|
| transporte por renombrado | 🏁 ADR‑035 | `[propext, Quot.sound]` |
| conservatividad (inversa) | 🏁 ADR‑035 | `[propext, Quot.sound]` |
| **eigenvariable** | 🏁 **este ADR** | `[propext, Quot.sound]` |

⬜ **Lo que queda es el ENSAMBLAJE, no más piezas**: construir la extensión de Henkin iterada
—suministro de constantes frescas vía el renombrado a un sublenguaje, `S₁ := S ∪ {(∃A) → A[c_A]}`,
iteración ω, y la consistencia de cada paso por contraposición con `derives0_gen_fresh`—, y con
ella `henkin_extension_lemma` sobre `Derives₀`.

⚠️ **Y ahí reaparecerá `String`**: el renombrado concreto («mete todo en un sublenguaje») necesita
**descomponer cadenas** para su inversa, y en Lean v4.31 eso trae `Classical.choice`
(`sondeos/ClassicalChoiceCenso.lean`). Las tres piezas son constructivas; el ensamblaje no lo será
mientras los símbolos sean `String`.

**Véase también:** `../FOL/FOL/Eigenvariable.lean`, `../FOL/FOL/Rename.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2, `check-footprints.bash` (20 titulares).

---

## ADR-037: `henkin_step_consistent` — el corazón de Henkin, probado; el ensamblaje, NO

**Fecha:** 2026‑09‑14 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑033..036 · **Plan:** `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2

### 1 · Qué se demuestra, y qué NO

    henkin_step_consistent : IsConsistent₀ S → (c fresca en S y en A) →
        IsConsistent₀ (S ∪ { (∃A) → A[c] })

`../FOL/FOL/Henkin0.lean`. Footprint `[propext, Classical.choice, Quot.sound]` — **cero axiomas
del proyecto**; el `Classical.choice` viene sólo del `filter` (necesita `DecidableEq Formula`).

⚠️⚠️ **Y digo lo que NO está, antes que lo que sí**: esto **no** es `henkin_extension_lemma`. Es
**el paso**. Falta la **iteración ω** y, sobre todo, el **suministro de constantes frescas** para
un `S` arbitrario.

🔑 La parte **matemática** del ensamblaje está hecha y es finitaria. Lo que falta es
**combinatoria de nombres**.

⚠️⚠️ **CORREGIDO el mismo día, y por medición**: aquí dije que eso sería el trozo **caro** y que
«pasa por `String`». `sondeos/NombresFrescosMedicion.lean` lo refuta: `String.append_right_inj`
**existe** (⇒ `ρ` inyectiva, y su prueba sale **limpia**), y `"g" ++ t ≠ "f" ++ s` **compila por
`rfl` sobre `beq`**, así que la familia infinita de constantes frescas son **tres líneas**.
⇒ **coste estimado ~80 líneas, riesgo bajo.** Lo que sí se sostiene: mete `Classical.choice`, pero
por la **implementación** de `String`, no por la matemática. Ver el plan §6.4 para la tabla
completa de lo que queda, medido y estimado por separado.

### 2 · ⭐ El punto fino que hace que esto funcione

`derives0_gen_fresh` pide `c` fresca **en el contexto finito**, no en todo `S`. Y `DerivesSet₀`
—«existe un `Γ` FINITO dentro de `S` que deriva»— **entrega exactamente eso**.

⇒ 🔑 **La compacidad sintáctica metida en la definición de `⊢₀*` es lo que hace barato el paso.**
Es la misma observación que explicaba por qué `IsConsistent` es Π⁰₁ y no peor.

### 3 · La pieza que el ensamblaje descubrió: `derives0_lift`

Al escribir el paso 6 —`∃A` y `∀¬A` se contradicen— apareció un agujero estructural. En un cálculo
**finitario** esa contradicción pasa obligatoriamente por `elim_ex`, cuya premisa lateral vive en
el contexto **levantado** `A :: Γ.map (liftFormula 0)`. Había que llevar allí el `∀(¬A)`.

⇒ `FOL/Lift0.lean`: **`derives0_lift : Γ ⊢₀ φ → ∀ k, Γ.map (liftFormula k) ⊢₀ liftFormula k φ`**,
footprint `[propext, Quot.sound]`, más `substFormula_lift_var` (el lift se deshace sustituyendo la
variable por sí misma) y `derives0_ex_forall_neg_absurd`.

⚠️ **Nota de ingeniería, escrita a propósito**: `Lift0` es casi una copia de `Eigenvariable`
—`absTerm c k` coincide con `liftTerm k` salvo en `c`—. Un `absTerm'` parametrizado por un
**predicado** de símbolos daría los dos con una sola inducción. ⬜ **No se hizo, y por riesgo, no
por gusto**: `Eigenvariable` ya está compilado y vigilado por `check-footprints.bash`; el refactor
va **después** de cerrar el ensamblaje, no en medio.

### 4 · Estado del Paso 2 del plan

| pieza | ADR | footprint |
|---|---|---|
| transporte por renombrado | 035 | `[propext, Quot.sound]` |
| conservatividad | 035 | `[propext, Quot.sound]` |
| eigenvariable | 036 | `[propext, Quot.sound]` |
| debilitamiento bajo lift | **037** | `[propext, Quot.sound]` |
| **paso de Henkin** | **037** | `[propext, Classical.choice, Quot.sound]` |

⬜ **Lo que queda, con nombre:**

1. **Suministro de constantes frescas** — para `S` arbitrario hace falta meterlo en un sublenguaje
   con `FOL.Rename` y quedarse con los símbolos del complemento. ⚠️ Combinatoria de `String`.
2. **Iteración ω** — `S₀ := S`, `S_{n+1} := S_n ∪ {henkinAx cₙ φₙ}` con `cₙ` fresca, y la
   consistencia del límite por el argumento del `max` (como `lindenbaum_limit_bound`).
3. **`IsHenkin` del límite** y el empalme con Lindenbaum.

**Véase también:** `../FOL/FOL/Henkin0.lean`, `../FOL/FOL/Lift0.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2.

---

## ADR-038: Los ESTRATOS, declarados y vigilados — y la escalera de binders, cerrada a medias

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO (sanción del propietario) ·
**Relacionado:** ADR‑024 (M‑10), ADR‑025/029 (M‑11), ADR‑033

### 1 · El diagnóstico que lo motiva

La pregunta del propietario era si el proyecto **se había quedado corto en estratificación**. La
respuesta medida es **no en el número de capas, sino en el ROL**: hay **cinco** nociones de
derivabilidad y, hasta el 2026‑09‑14, nadie podía decir mirando el árbol cuál era **herramienta**
y cuál **sujeto**. Ése es el agujero que se cobró `FOL.soundness`.

### 2 · La tabla, medida por el TIPO

`REFERENCE.md` §0bis. Los habitantes se cuentan por la **cabeza de la conclusión** del tipo de cada
`axiom`, no por grep sobre nombres:

| noción | ctors | axiomas que la **habitan** | ¿inducción? |
|---|---:|---:|---|
| `Derives` | 22 | ⛔ **7** | ⛔ nunca (permanente) |
| `Derives₀` | 21 | 0 | ✅ |
| `Prf` | 7 | 0 | ✅ |
| `Prf₀` | 17 | 0 | ✅ |
| `PrfH` | 8 | 0 | ✅ |

⭐ **Y el dato que ordena todo el proyecto**: **los siete axiomas habitan `Derives`**. Ninguna otra
noción tiene ninguno.

### 3 · `check-estratos.bash`, y por qué NO lo cubría `check-footprints`

⛔⛔ **`#print axioms` es CIEGO a esta clase.** Un teorema probado por inducción sobre un inductivo
habitado tiene footprint **limpio** y es **injustificado**.

⇒ Son **dos controles distintos y ninguno sustituye al otro**: `check-footprints` mide **de qué
depende** un teorema; `check-estratos` mide si **la inducción que lo probó era legítima**.

Rompe en los dos sentidos, y probado con el fallo puesto en **cuatro** modos (los cuatro `EXIT=1`):
más axiomas de los declarados —con el mensaje *«si era inducible, HA DEJADO DE SERLO»*—,
constructores que no cuadran, estrato habitado no declarado, y peldaño de escalera no declarado.

🔑 **La regla de rol, en una línea**: *si un cálculo está habitado por axiomas, es HERRAMIENTA; el
SUJETO tiene que ser otro.* Explica `goedel_second'` retirado, Gödel reenunciado sobre `Prf`, y
`Derives₀` declarado **al lado** de `Derives` en vez de intentar limpiarlo.

### 4 · La escalera de binders: cerrada la mitad barata, medida la cara

🏁 **Cerrado genéricamente el nivel de las DEFINICIONES**: `forallN : Nat → Formula → Formula` con
los cinco puentes `forallN k f = forall_k f` **por `rfl`** y `forallN_succ`. ⭐ **Ninguno de los
188 usos cambia** (build 145 jobs, verde).

⚠️⚠️ **Y aquí corrijo mi propia estimación.** Dije *«medio día, riesgo cero… y cerrar la escalera
`forall_n` genéricamente»*, metiendo las dos cosas en el mismo paquete. **La segunda no es de ese
tamaño, y está medido**: la maquinaria crece **superlinealmente** —**6 → 13 → 34 → 64** líneas para
`pcc_thm_inst`/`inst2`/`inst3`/`inst4`—, son cadenas de `prf_mp`/`prf_provCode_congr` con torres de
`liftc`/`substfc`, y ⛔ **los símbolos objeto no reducen**. Una versión genérica en `n` es trabajo
del orden del frente `substfc`.

⚠️ **Y el desfase es real**: hay **tres axiomas de aridad 5** (`validProofFn`) sin instanciador de
código. Queda **declarado y vigilado**, no escondido: el control lo imprime y rompe si cambia.

**Véase también:** `check-estratos.bash`, `REFERENCE.md` §0bis y §0bis.2,
`ROBINSON_PlusPlus/Minimal/Axioms.lean` (`forallN` y los puentes).

---

## ADR-039: La extensión de Henkin, CONSTRUIDA — y el riesgo que el plan marcaba en rojo, disuelto

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑030 (enumeración), ADR‑033 (`Derives₀`), ADR‑035 (renombrado), ADR‑036
(eigenvariable), ADR‑037 (el paso de Henkin), ADR‑032 (el axioma que NO se paga)

### 1 · Qué queda demostrado

`doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4 pedía tres piezas. **Las dos primeras están**, en dos
módulos nuevos de FOL:

| | módulo | titular |
|---|---|---|
| (1) | `FOL/Fresh0.lean` | `exists_fresh` — hay constante fresca para la teoría desplazada **más** cualquier lista finita de axiomas ya añadidos **más** la fórmula del turno |
| (2) | `FOL/HenkinLimit0.lean` | ⭐⭐ `henLimit_consistent` y `henLimit_witness` — **toda teoría consistente se extiende a una consistente con testigo para cada fórmula** |

⇒ La **extensión de Henkin está construida**, no postulada. Footprint
`[propext, Classical.choice, Quot.sound]` y **cero axiomas del proyecto**.

⛔ **Y esto NO toca `cuarentena/Completeness.lean`**: `henkin_extension_lemma` sigue siendo un
`axiom` sobre `Derives`, y ADR‑032 sigue vigente. Lo de aquí es sobre **`Derives₀`**, que es otro
sujeto. `check-axioms.bash` no se mueve.

### 2 · ⚠️ La estimación que el plan publicaba, y lo medido

§6.4 daba a la iteración ω **riesgo medio**, con la causa localizada y bien localizada: `cₙ` tiene
que ser fresca también para `φₙ`, y `φₙ` recorre **todas** las fórmulas ⇒ no vale `cₙ := cst n`.
De ahí concluía que hacía falta una función `Formula → Nat` («mayor índice de `cst` usado») **con
su lema, ~40 líneas**, y lo marcaba *«identificado, no medido»*.

**Medido: la función no hace falta, y el diagnóstico seguía siendo correcto.** Lo que falla no es
la causa sino el **enunciado elegido para resolverla**:

| enunciado | qué obliga a hacer |
|---|---|
| ⬜ «el mayor índice usado en `φ`» | **leer los nombres** — invertir `cst`, o `String.length` |
| ⭐ «a partir de cierto índice, **todas** son frescas» | inducción estructural con `max`, y **nada más** |

    cst_bound_formula : ∀ f, ∃ N, ∀ m ≥ N, ¬ occursFormula (cst m) f

El único paso clásico queda en el **símbolo**: `∃ N, ∀ m ≥ N, cst m ≠ s` sale de
`Classical.em (∃ k, cst k = s)` más `cst_inj`. Y `Exists.choose` convierte el `∃` en la función
`bnd` que el índice del turno necesita.

🔑 **La lección, y es de método**: el riesgo estaba bien identificado y mal **cotizado**, porque el
plan cotizó *la solución que se le había ocurrido*, no *el problema*. Un `∃` bien elegido puede
sustituir a una función y a su lema.

### 3 · Las cifras

| pieza | estimado ⬜ | fichero 📏 | de ello CÓDIGO 📏 |
|---|---:|---:|---:|
| (1) suministro de frescas | ~80 l. | 295 l. | **150 l.** |
| (2) iteración ω | ~190 l. | 313 l. | **168 l.** |

(«código» = líneas no vacías que no son comentario ni docstring.)

⚠️ (1) salió **casi al doble** de lo estimado: la estimación contaba las dos piezas que el sondeo
`NombresFrescosMedicion.lean` ya había medido y **no contaba la transferencia de la teoría**
(`shiftTheory` y su conservatividad en las dos direcciones), que es la mitad del módulo. (2) salió
**por debajo**, y por la razón del §2.

⭐ **Ninguna de las dos piezas necesitó un intento fallido**: los cuatro sondeos y los dos módulos
compilaron a la primera; el único error de toda la sesión fue un `/-- -/` delante de un `mutual`.

### 4 · Lo que la construcción usa, y de dónde salió

* ⭐ **`ρ s := "f" ++ s` mete la teoría en un sublenguaje**, y las constantes `cst n` quedan fuera
  de la imagen. La conservatividad **no elige preimágenes**: **mapea con la inversa**
  (`invOf`, ADR‑035).
* ⭐ **La consistencia del límite sale de `DerivesSet₀`**: una derivación usa contexto **finito**,
  luego vive en una etapa. *La compacidad sintáctica metida en la definición paga por tercera vez.*
* ⭐ **`natToFormula_surj`** (ADR‑030) es lo que hace que el testigo exista para **toda** fórmula.
  La enumeración se construyó para otra cosa y sirve aquí sin tocarla.
* ⭐ **`not_occurs_henkinAx` es net‑0 puro**: las dos conmutaciones que faltaban (el lift no cambia
  símbolos; la sustitución sólo mete los del término sustituido) no dependen de ningún axioma.

### 5 · Lo que queda

(3) **Lindenbaum sobre `Derives₀` + maximalidad**, ~200 l. ⬜ (calco medido de
`cuarentena/Completeness.lean`), y después el modelo canónico y `truth_lemma`, ~470 l. ⬜
⚠️ **Y es ahí donde entra el `Classical.choice` de verdad** —el `if IsConsistent (Sₙ ∪ {φₙ})`, que
es Π⁰₁—: el que hay hoy en el footprint es de `Exists.choose` y de `String`, no el del teorema.

**Véase también:** `FOL/Fresh0.lean`, `FOL/HenkinLimit0.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4, `check-footprints.bash` (29 titulares).

---

## ADR-040: El ensamblaje de Henkin, CERRADO — y la no‑finitud, localizada en una línea

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑039 (piezas 1 y 2), ADR‑033 (`Derives₀`), ADR‑030 (enumeración),
ADR‑032 (el `axiom` que NO se paga)

### 1 · Qué queda demostrado

La pieza (3) de `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4, en `FOL/Lindenbaum0.lean` (126 l. de
código frente a las ~200 estimadas). Y con ella **el ensamblaje entero**, en un solo enunciado:

    henkin_completion : IsConsistent₀ S →
      ∃ T, IsMaximalConsistent₀ T ∧ IsHenkin₀ T ∧ (∀ f, shiftTheory S f → T f)

*Toda teoría consistente se extiende a una **maximal consistente** con **testigo para cada
existencial**.* Footprint `[propext, Classical.choice, Quot.sound]`, **cero axiomas del proyecto**.

⇒ Las **tres** piezas del §6.4 están. ⬜ Queda el **modelo canónico** y `truth_lemma` (~470 l.),
que es calco de lo que sobra de las 801 de `cuarentena/Completeness.lean`.

### 2 · ⛔ Y la decisión de fondo: **dónde se declara la no‑finitud**

Está en **una línea**, y va señalada en el docstring del módulo, en el de la `def` y aquí:

    if IsConsistent₀ (Sₙ ∪ {φₙ}) then … else …

Esa condición es **Π⁰₁** y se decide con `Classical.propDecidable`. **Ahí cabe toda la no‑finitud
del teorema de completitud.**

⚠️ **Y esto obliga a re‑leer los footprints de ADR‑039**: los `Classical.choice` de `Fresh0` y
`HenkinLimit0` **no eran** éste —eran `Exists.choose` y la implementación de `String`—. El de aquí
sí. Tres apariciones del mismo nombre en `#print axioms`, **tres causas distintas**, y sólo una es
matemática.

🔑 Es el corolario exacto de [[feedback-footprint-no-es-constructividad]]: **el footprint no
distingue las causas, así que hay que distinguirlas por escrito.** Un `Classical.choice`
explicado vale más que uno escondido.

### 3 · Lo que salió gratis, y por qué

⭐ **`derivesSet0_intro_impl` es el teorema de deducción, y no hay que demostrarlo**: sobre
`Derives₀`, `intro_impl` es un **constructor**. La versión de `cuarentena/Completeness.lean`
invocaba `FOL.Metamath.Deduction.deduction_theorem`; aquí todo el trabajo es sacar `A` del contexto
finito con un `filter`.

⭐ **El paso de `henLimit` a `IsHenkin₀` son dos líneas**: el axioma `(∃A) → A[c]` está en `T`
porque `T ⊇ henLimit S`, y un maximal consistente está cerrado por modus ponens. *El trabajo estaba
en construir `henLimit`, no en usarlo.*

⭐ **Tercera vez que paga la compacidad metida en `DerivesSet₀`**: consistencia del paso de Henkin
(ADR‑037), consistencia del límite ω (ADR‑039) y consistencia del límite de Lindenbaum (aquí).

### 4 · ⚠️ Lo que este ADR **no** dice

* ⛔ **No hay completitud todavía.** Falta el modelo canónico. `henkin_completion` es la
  **hipótesis** que ese modelo consume, no el teorema.
* ⛔ **No toca `cuarentena/Completeness.lean`.** `henkin_extension_lemma` sigue siendo un `axiom`
  sobre `Derives`, **ADR‑032 sigue vigente**, y `check-axioms.bash` no se mueve.
* ⚠️ La conclusión es sobre `shiftTheory S`, no sobre `S`: la extensión vive en el **sublenguaje**.
  Es conservativa (`derivesSet0_shift_inv`), pero **el enunciado tiene que decirlo**, y lo dice.

**Véase también:** `FOL/Lindenbaum0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.3 y §6.4,
`check-footprints.bash` (31 titulares).

---

## ADR-041: **COMPLETITUD** — `completeness₀`, y las dos direcciones sobre un mismo cálculo

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑033 (`Derives₀`), ADR‑034 (solidez), ADR‑030 (enumeración), ADR‑031
(congruencias), ADR‑039/040 (el ensamblaje de Henkin), ADR‑024 (M‑10), ADR‑032

### 1 · Qué queda demostrado

    completeness₀        : Γ ⊨ f → Γ ⊢₀ f
    derives0_complete_iff : (Γ ⊢₀ f) ↔ (Γ ⊨ f)

en `FOL/Canonical0.lean`, footprint `[propext, Classical.choice, Quot.sound]` y **cero axiomas del
proyecto**. Con `FOL/Eq0.lean` (las cuatro piezas de la igualdad sobre `Derives₀`), **510 líneas de
código** frente a las ~470 estimadas.

⭐⭐ **Es la primera vez que el proyecto tiene las DOS direcciones sobre un mismo cálculo de FOL⁼.**
La ida es `derives0_soundness` (ADR‑034).

⛔ **Y sobre `Derives` no puede haberlas, ni ahora ni nunca**: su solidez es FALSA
(`cuarentena/Inconsistencia.lean`) y `axioms ⊢` es **sintácticamente completo** ⇒ no r.e. (M‑10,
ADR‑024). Esto **no cambia nada** de la arquitectura: `⊢` sigue siendo la herramienta y `Prf` el
sujeto. Lo que cambia es que ahora hay **un tercer objeto** del que sí se puede decir la verdad.

### 2 · ⚠️ Qué NO significa, dicho antes de que alguien lo lea de más

| lectura tentadora | lo que de verdad hay |
|---|---|
| «Gödel I queda afectado» | ⛔ **No.** Gödel I es sobre `Prf`, y `Derives₀` **no es** `Prf`. La completitud **semántica** no es la **sintáctica**: `derives0_not_complete` (ADR‑034) sigue siendo cierto |
| «se puede retirar `henkin_extension_lemma`» | ⛔ **No.** Ése es un `axiom` sobre **`Derives`**, y **ADR‑032 sigue vigente**. `check-axioms.bash` no se mueve |
| «el proyecto ya es constructivo» | ⛔ **No.** El `Classical.choice` es el **WKL** — ver §4 |
| «`cuarentena/Completeness.lean` puede salir de cuarentena» | ⛔ **No.** Aquello es sobre `Derives`. Lo de aquí es un objeto **nuevo**, escrito al lado |

### 3 · ⚠️ El agujero que el calco NO cubría, y hubo que escribir

`henkin_completion` (ADR‑040) entrega un maximal consistente que extiende **`shiftTheory S`**, no
`S`: la extensión de Henkin vive en el **sublenguaje**. El modelo canónico da entonces un modelo de
`shiftTheory S`, y hacía falta **volver**.

⇒ `pullback M ρ` —reinterpretar cada símbolo `f` como `ρ f`— y

    eval_pullback_formula : evalFormula (pullback M ρ) v f ↔ evalFormula M v (renameFormula ρ f)

⭐ **Net‑0 puro: no depende de NINGÚN axioma.** *Renombrar símbolos de función no cambia la
satisfacibilidad*, y eso es constructivo. ⚠️ Es la única pieza de este tramo que no estaba en
`cuarentena/Completeness.lean`: aquel fichero **postulaba** la extensión de Henkin, así que nunca
tuvo que volver del sublenguaje. 🔑 *Pagar un axioma esconde también el trabajo que el axioma
evitaba.*

### 4 · ⛔ El entregable es un `Classical.choice` EXPLICADO

Como el plan §6.3 dijo desde el principio. El `Classical.choice` de `completeness₀` es el
`if IsConsistent₀ (Sₙ ∪ {φₙ})` de `FOL.Lindenbaum0`, que es **Π⁰₁**:

* la completitud para lenguajes numerables es **≡ WKL₀** sobre RCA₀ (Simpson, *SOSOA* IV.3.3);
* **WKL₀ es Π⁰₂‑conservativo sobre PRA** (Friedman, *SOSOA* IX.3) ⇒ **finitistamente reducible**;
* ⛔ **no es constructiva**: WKL falla en realizabilidad recursiva (Kleene).

⇒ La frase exacta que este repo puede publicar: *«la completitud de FOL⁼ para teorías numerables
está **demostrada** en Lean sobre `Derives₀`, con cero axiomas propios, y su contenido no finitario
está **localizado** en una línea Π⁰₁ que es exactamente el WKL».*

### 5 · ⭐ Control de NO VACUIDAD, porque un teorema puede ser cierto y no servir

Un enunciado de completitud puede ser trivial si el consecuente lo es. Dos líneas lo descartan, y
**producen derivaciones reales** pasando por el modelo canónico:

    derives0_em     (A)   : [] ⊢₀ A ∨ ¬A
    derives0_peirce (A B) : [] ⊢₀ ((A → B) → A) → A

Peirce es el ejemplo canónico de tautología **clásica** que la lógica intuicionista no demuestra.
Si `completeness₀` fuera vacua, esto no compilaría.

### 6 · Lo que salió gratis, y por qué — otra vez el SUJETO

* ⭐ `FOL/Eq0.lean` es un **traslado literal** de `Theorems/Eq.lean`: `refl` y `subst` son
  constructores de los dos cálculos, y la parte difícil (`substTerms_append`, `substTerms_lift_hole`)
  es **sintaxis pura** y se importa tal cual. *Las listas no distinguen `Derives` de `Derives₀`.*
* ⭐ `max_cons_forall` necesitaba `forall_not_impl_exists_not`, que en `Derives` es un teorema de
  `Theorems/Quantifiers`; en `Derives₀` es un **constructor**. Igual `dne_schema` en `completeness₀`.
* ⭐ `derivesSet0_map`/`map2`: *la regla viaja con su contexto finito.* Cuarta vez que paga la
  compacidad metida en `DerivesSet₀`.

**Véase también:** `FOL/Canonical0.lean`, `FOL/Eq0.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §6, `check-footprints.bash` (39 titulares).

---

## ADR-042: Vía H · **H1 y H2** — la completitud proposicional, y es FINITARIA de verdad

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑033 (`Derives₀`), ADR‑041 (completitud semántica), plan §5

### 1 · Qué queda demostrado

    derives0_of_ptaut     : PTaut φ → [] ⊢₀ φ
    derives0_of_ptaut_ctx : (∀ v, (∀ g ∈ Γ, peval v g) → peval v φ) → Γ ⊢₀ φ

`FOL/Propositional0.lean` (244 l. de código) sobre `FOL/DecEq.lean` (31 l.). Footprint
**`[propext, Quot.sound]`** — ⭐⭐ **ni un `Classical.choice`** —, y `derives0_em_ctx` **no depende
de ningún axioma**.

🔑 **Ésa es toda la diferencia con la vía W, y es la razón de ser de la vía H**: aquí no hay
König, porque `Γ` es **finito** y la valuación recorre una lista **finita** de átomos. La vía W es
*finitistamente reducible*; ésta es **finitaria**.

### 2 · ⭐ La desviación del plan, y por qué mejora el resultado

§5.2 pedía «semántica proposicional para fórmulas **sin cuantificadores**». Lo implementado trata
`∀` y `∃` **como átomos** — el *esqueleto proposicional*.

| | alcance | coste |
|---|---|---|
| ⬜ como pedía el plan | sólo fórmulas sin cuantificadores | + un predicado `QF` y su propagación |
| ⭐ como está | **toda** fórmula | **ninguno** |

⇒ `derives0_of_ptaut` descarga **cualquier** tautología proposicional, con subfórmulas
cuantificadas dentro, en una línea. La restricción no habría hecho el teorema más fuerte, sólo
menos aplicable.

### 3 · ⭐ El control que mide PARA QUÉ sirve la vía H

`derives0_em` y `derives0_peirce` **ya estaban demostrados** (ADR‑041 §5), pero **por completitud
semántica**, y por eso arrastran `Classical.choice`. Los mismos dos teoremas por la vía H:

| teorema | vía W (`FOL.Canonical0`) | vía H (`FOL.Propositional0`) |
|---|---|---|
| `A ∨ ¬A` | `[propext, Classical.choice, Quot.sound]` | **`[propext, Quot.sound]`** |
| Peirce | `[propext, Classical.choice, Quot.sound]` | **`[propext, Quot.sound]`** |

🔑 *La vía H da los mismos teoremas con footprint **estrictamente menor**.* Es la demostración
práctica, dentro del repo, de que las dos vías no son redundantes.

### 4 · ⚠️ Dos cosas MEDIDAS que conviene no volver a descubrir

* ⛔ **`deriving instance DecidableEq for Term` NO funciona.** `Term.func : String → List Term →
  Term` es un inductivo **anidado** y ningún *deriving handler* de v4.31 se le aplica. Hay que
  escribir la recursión mutua `Term`/`List Term` a mano — 25 líneas, **net‑0**.
  ⭐ En cambio **`Formula` sí se deriva**, una vez existe la de `Term`.
* ⚠️⚠️ **CORREGIDO el mismo día (ADR‑043 §5).** Aquí decía:
  > ⚠️ La instancia **no reduce en el kernel** (recursión bien fundada): `by decide` sobre una
  > igualdad concreta de fórmulas **se atasca**.

  **Es FALSO.** Re‑medido: los tres controles compilan **por `rfl`**, la instancia **sí reduce**,
  y gracias a eso `ptautCheck` se evalúa en el kernel. 🔑 El fallo era **del control**: probé
  `decide (X = Y) = true` con `by decide` —un `decide` envolviendo a otro— y lo que se atascaba
  era el de fuera. *Un control mal montado mide su propio montaje.*

### 5 · ⛔ Lo que NO se ha hecho, y NO se retrofita

* **No hay recíproca**, y no puede haberla: `⊢₀ φ` no implica `PTaut φ` — `(∀x P(x)) → P(t)` es
  derivable y su esqueleto es `p → q`. *El cálculo sabe más que su esqueleto.*
* ⛔ **`FOL.DecEq` NO se retrofita** a `FOL.Henkin0` ni a `FOL.Lindenbaum0`: no lo importan, así
  que su elaboración no cambia. Retrofitarlo movería footprints ya publicados y medidos, y el
  `Classical.choice` de `Lindenbaum0` **tiene que seguir ahí** por otra razón —el
  `if IsConsistent₀ …`, Π⁰₁ (ADR‑040 §2)—, así que no se ganaría nada y se perdería trazabilidad.
* ⬜ **Falta H3** —normalización / eliminación de cortes—, que sigue siendo **la pieza grande** de
  la vía H, y H4 detrás. H1+H2 son la **base**, no el teorema de Herbrand.

### 6 · ⭐ El detalle técnico que vale la pena recordar

En la eliminación de átomos, `v[a↦true]` y `v[a↦false]` **no coinciden con `v`** en el resto de la
lista si `a` está repetido. No hace falta pedir la lista sin repeticiones: basta **debilitar**,
porque el literal que discrepa es exactamente `a` (o `¬a`), que es la **cabeza** del contexto
objetivo. *Debilitar sale más barato que una hipótesis de no‑repetición.*

**Véase también:** `FOL/Propositional0.lean`, `FOL/DecEq.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §5, `check-footprints.bash` (47 titulares).

---

## ADR-043: Vía H · **H4 hecho** (la mitad ⟸) y **H3 enunciada** — el certificado de Herbrand

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO (H4 ⟸) · ⬜ ABIERTO (H3) ·
**Relacionado:** ADR‑042 (H1/H2), ADR‑031 y `FOL.Eq0` (igualdad), plan §5

### 1 · Qué queda demostrado

    derives0_ex_of_cert : HerbrandCert φ ts E → [] ⊢₀ ∃x φ(x)

`FOL/Herbrand0.lean`, **154 l. de código**, footprint `[propext, Quot.sound]` —
⭐ **ni un `Classical.choice` en todo el módulo**, y `derives0_discharge` **no depende de ningún
axioma**.

⭐⭐ **El certificado es DATO SINTÁCTICO y se verifica por CÓMPUTO.** `HerbrandCert φ ts E` es:
una lista de términos, una lista de instancias de la igualdad, y la constancia de que la
disyunción `φ(t₁) ∨ … ∨ φ(tₙ)` se sigue **proposicionalmente** de ellas — comprobable con
`ptautCheck`, que **reduce**, así que sale **`by rfl`**.

🔑 Eso es exactamente lo que §0 del plan pedía del objetivo **H**: *un certificado finito y
verificable*. No un teorema sobre certificados: **un certificado**.

### 2 · ⭐ Cómo se resuelve §5.3 (la igualdad) sin implementar clausura de congruencia

§5.3 decía que con `=` la disyunción termina en tautología **ecuacional**, y que eso pide
«clausura de congruencia (Ackermann / Nelson–Oppen): decidible y finitaria, pero una **capa entera
más**».

⭐ **No hace falta implementarla**: se convierte en un **dato del certificado**. `E` es una lista
de `EqInstance` —refl, simetría, transitividad, congruencia de función, congruencia de relación—,
un inductivo **cerrado**, y `derives0_of_eqInstance` prueba que **todas son derivables**. ⇒ el
certificado **no añade fuerza**: sólo la organiza.

Ejemplo compilado, y es el que justifica toda la lista: `∃x (x ≐ c)` con `ts = [c]` y
`E = [c ≐ c]`. Su disyunción de Herbrand es `c ≐ c`, que **no** es tautología proposicional —es un
átomo— pero **sí** es un axioma de la igualdad.

🔑 *Lo que hacía falta decidir no era la teoría ecuacional, sino la tautología proposicional — y
eso ya estaba (ADR‑042).*

### 3 · ⬜ H3, ENUNCIADA con su consumidor — y por qué no se ha empezado `LK₀`

    HerbrandExtraction : ∀ φ, QuantFree φ → ([] ⊢₀ ∃x φ) → ∃ ts E, HerbrandCert φ ts E
    herbrand_iff (h3)  : ([] ⊢₀ ∃x φ) ↔ ∃ ts E, HerbrandCert φ ts E

*Una deuda se **enuncia** como `Prop`, nunca se postula*, y **el consumidor va delante**. La mitad
`←` es **incondicional**; `h3` sólo paga la `→`.

⚠️ **Por qué no cae por inducción** (⬜ análisis sobre la lista de constructores, **no** medición
compilada — y va etiquetado): el enunciado **no es inductivo**. Ya `intro_ex Γ φ t` pide que
`φ(t)` se siga *proposicionalmente* de instancias ecuacionales, y la hipótesis de inducción sólo
da que es *derivable*. Hay que subir a un enunciado **sobre secuentes arbitrarios** —el
mid‑sequent—, que es la eliminación de cortes.

Y el obstáculo es **contable**: de los 21 constructores de `Derives₀`, **siete** son «de corte»
(una premisa menciona una fórmula ausente de la conclusión): `elim_impl`, `elim_and_l`,
`elim_and_r`, `elim_or`, `elim_ex`, ⛔ `subst` y ⛔ `rewrite_at`; más `weakening`, estructural.
Los dos marcados son los que impiden que sea un Hauptsatz de libro: `subst` es **Leibniz** —la
igualdad no se elimina, se vuelve teoría— y `rewrite_at` **no tiene análogo en LK**.

⛔ **Y `LK₀` no se ha empezado a propósito.** Diseñar un cálculo de secuentes sin poder validarlo
contra la mitad difícil es fabricar una obligación que puede salir **inconsumible**, y el
escarmiento está escrito: *la guarda se copia del CONSUMIDOR, no del molde*
([[feedback-enunciar-una-deuda]]). Primero el consumidor —que ya está—, después el molde.

### 4 · ⚠️ Ámbito, dicho para que no se lea de más

* **Un solo cuantificador**: `∃x φ(x)`, no `∃x̄`. ⬜ La versión n‑aria es iteración rutinaria pero
  la aritmética de De Bruijn bajo binders anidados pide su propia capa de lemas.
* ⚠️ `QuantFree φ` **no es decoración**: para `φ` con cuantificadores el enunciado de H3 es
  **falso**.
* ⚠️ `derives0_discharge` **es un corte, y es admisible gratis** porque `intro_impl` es un
  **constructor**. ⛔ **Esto NO es H3**: eliminar el corte es transformar la *derivación* para que
  no lo use; esto sólo lo **contrae**.

### 5 · ⚠️⚠️ Y una corrección: ADR‑042 §4 publicaba algo FALSO

Decía que la instancia `DecidableEq Formula` **no reduce en el kernel** y que `by decide` sobre
una igualdad de fórmulas **se atasca**. **Re‑medido: es falso.** Los tres controles compilan por
`rfl`, la instancia **sí reduce**, y gracias a eso `ptautCheck` se evalúa y el certificado se
comprueba a máquina.

🔑 **El fallo era del CONTROL, no del código**: probé `decide (X = Y) = true` con `by decide` —un
`decide` envolviendo a otro— y lo que se atascaba era el de fuera. *Un control mal montado mide su
propio montaje.* Corregido en su sitio (ADR‑042 §4 y el docstring de `FOL/DecEq.lean`), con el
texto viejo a la vista.

**Véase también:** `FOL/Herbrand0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.4,
`check-footprints.bash`.

---

## ADR-044: H3, primera pieza — **`rewrite_at` es ADMISIBLE**, y el frente pasa de dos obstáculos a uno

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑043 §3 (el conteo de obstáculos), ADR‑033 (`Derives₀`), ADR‑036
(`substFormula_lift_var`), plan §5.5

### 1 · Qué queda demostrado

    Derives₁               -- los 20 constructores de `Derives₀` MENOS `rewrite_at`
    rewrite_at_admissible  -- y no hace falta como regla
    derives0_iff_derives1  -- los dos cálculos derivan EXACTAMENTE lo mismo

`FOL/Derives1.lean`, **214 l. de código**, footprint `[propext, Quot.sound]` — **ni un
`Classical.choice`**. ⭐ Y `Derives₁.rec` **no depende de ningún axioma** (el de `Derives₀` lleva
`propext`).

⇒ **`Derives₁` es deducción natural clásica de libro más igualdad**: hipótesis, los conectivos,
los cuantificadores, `bot_elim`, debilitamiento, doble negación, `refl` y `subst`. Nada más.

🔑 **Y eso es lo que importa para H3.** ADR‑043 §3 dejó el obstáculo contado: siete constructores
«de corte», de los cuales **dos** impedían que la eliminación de cortes fuera un Hauptsatz de
libro. **Uno de los dos ya no está.**

### 2 · Cómo se retira, y el punto fino

`LocalRule` tiene **un solo constructor**, `commuteImpl A B C : A→(B→C) ⟹ B→(A→C)`, así que
eliminar `rewrite_at` es una **congruencia por posiciones**:

    rewrite_equiv : getAt? f p = some sub → LocalRule sub sub' →
        ∀ Γ, (Γ ⊢₁ f → replaceAt f p sub') ∧ (Γ ⊢₁ replaceAt f p sub' → f)

⚠️ **Tiene que ser biconditional aunque `rewrite_at` sólo pida una dirección.** Al bajar por el
**antecedente** de una implicación la congruencia se **invierte** (`impl_congr_l` es
contravariante), de modo que la inducción necesita las dos mitades a la vez. *Una inducción puede
necesitar más de lo que el consumidor pide.*

⭐ **Los dos casos caros son los de `Pos.body`**, bajo el binder: `⊢₁ (∀X) → (∀Y)` desde
`⊢₁ X → Y` sale por `intro_forall` —que **levanta el contexto**— y `elim_forall` con `Term.var 0`,
cerrando con **`substFormula_lift_var`**. 🔑 *Es el mismo lema que sostenía el paso de
eigenvariable de Henkin* (ADR‑036): **deshacer un lift sustituyendo la variable cero**. Salió
gratis porque ya estaba — van varias.

⭐ Y el detalle que lo hace funcionar: la hipótesis de las congruencias va cuantificada sobre
**todos** los contextos (`∀ Δ`), no sobre uno. Es lo que permite instanciarla en el contexto
**levantado** que `intro_forall` fabrica, **sin tener que levantar `X` ni `Y`**.

### 3 · ⚠️ Una medición nueva, y de las que cuestan una tarde si no se sabe

**`getAt?` y `replaceAt` NO REDUCEN.** Sus llamadas recursivas cambian **los dos** argumentos
(`getAt? f1 p` desde `getAt? f p`), así que Lean las compila por recursión **bien fundada**, y

    getAt? f Pos.root = some f      -- ⛔ NO es `rfl`

Hay que ir por las **ecuaciones** (`simp only [getAt?]`). Es primo de ⛔ *los símbolos OBJETO no
reducen*, pero por otra causa: aquí el símbolo es **de Lean** y lo que falla es el **esquema de
recursión**, no la aritmetización.

### 4 · ⬜ El obstáculo que queda — con lo MEDIDO de él

`subst`, Leibniz. La vía estándar: reducirlo a **instancias de congruencia**, dejando ND puro +
axiomas de igualdad, que es como la literatura enuncia Herbrand con `=`.

⚠️⚠️ **Y aquí hay un dato medido que fija el orden**: las cuatro piezas de `FOL/Eq0.lean`
—simetría, transitividad y las dos congruencias de una posición— están **derivadas DE `subst`**
(`Derives₀.subst` aparece en las cuatro; `FOL/Theorems/Eq.lean` igual). ⇒ **no se puede quitar
`subst` y conservar las congruencias como teoremas**: hay que **subirlas a constructores
primitivos** y después probar que `subst` es admisible a partir de ellas.

⬜ **Estimación, etiquetada**: `Derives₂` ~60 l. de andamiaje · Leibniz de **términos** ~100 l. ·
Leibniz de **fórmulas** ~150 l. · las dos traducciones ~80 l. **Riesgo medio‑alto**, concentrado
en el caso del binder, donde la sustitución **cambia de índice y levanta el término**:
`substFormula 0 t (∀a) = ∀ (substFormula 1 (liftTerm 0 t) a)`.

### 5 · ⛔ Lo que este ADR NO dice

* **H3 NO está.** Esto retira **un obstáculo**, no el teorema. `HerbrandExtraction` sigue abierta.
* ⛔ **Nada se retrofita.** `Derives₀` se queda como está y todo lo probado sobre él sigue en pie;
  `derives0_iff_derives1` transporta lo que haga falta cuando haga falta. Reescribir los diez
  módulos que hablan de `Derives₀` para que hablen de `Derives₁` no compra nada hoy y movería
  footprints medidos.
* ⚠️ `check-estratos.bash` pasa de **5** a **6** estratos declarados. `Derives₁`: 20 ctors,
  **0 habitantes‑axioma** ⇒ inducción legítima.

**Véase también:** `FOL/Derives1.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.5,
`check-estratos.bash`, `check-footprints.bash` (58 titulares).

---

## ADR-045: H3, segunda pieza — **`subst` es ADMISIBLE**, y el cálculo queda en forma de libro

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑044 (primera pieza), ADR‑043 §3 (el conteo), ADR‑031 (las congruencias),
plan §5.3 y §5.6

### 1 · Qué queda demostrado

    Derives₂               -- `Derives₁` SIN `subst`, con TRES congruencias primitivas
    eq_substFormula        -- ⭐⭐ Leibniz, DEMOSTRADO a partir de ellas
    derives0_iff_derives2  -- y deriva EXACTAMENTE lo mismo que el cálculo original

`FOL/Derives2.lean`, **347 l. de código**, footprint `[propext, Quot.sound]` — **ni un
`Classical.choice`**. ⭐ `Derives₂.rec` **no depende de ningún axioma**.

⇒ 🏁🏁 **Los DOS obstáculos que ADR‑043 §3 había contado ya no están.** `Derives₂` es **deducción
natural clásica de libro más los axiomas de la igualdad**, que es exactamente la forma en que la
literatura enuncia Herbrand con `=`. Lo que queda «de corte» son los **cinco estándar**
—`elim_impl`, `elim_and_l/r`, `elim_or`, `elim_ex`—, que es de lo que trata Gentzen.

### 2 · Qué sustituye a `subst`, y por qué justo eso

| constructor | qué dice |
|---|---|
| `eq_func_congr` | `a ≐ b ⟹ f(…a…) ≐ f(…b…)`, en **UNA** posición |
| `eq_atom_congr` | `a ≐ b ⟹ P(…a…) ⟹ P(…b…)`, en **UNA** posición |
| `eq_eq_congr` | `a ≐ b ⟹ a ≐ c ⟹ b ≐ c` |

⭐ **Simetría y transitividad NO son primitivas**: salen de `eq_eq_congr` + `refl` en una línea
cada una. ⚠️ Pero `eq_eq_congr` **sí hace falta**, porque `Formula.eq` es un **constructor propio**
de `Formula` y no un `atom`, así que `eq_atom_congr` no lo alcanza. *Una igualdad que es un
conectivo y no un predicado necesita su propia congruencia.*

### 3 · ⭐ Esto cierra §5.3 del plan, y la cierra hacia abajo

§5.3 decía que la igualdad obligaba a **«una capa entera más»** de clausura de congruencia
(Ackermann / Nelson–Oppen). **Medido: son tres constructores**, y con ellos Leibniz **se
demuestra**. La igualdad deja de ser una **regla de inferencia** y pasa a ser **teoría** — que es
justo lo que hacía falta para que el Hauptsatz se pueda plantear.

🔑 Y encaja con ADR‑043 §2: allí la clausura de congruencia se volvió **un dato del certificado**
(`EqInstance`); aquí se vuelve **tres axiomas del cálculo**. Es la misma reducción vista desde los
dos lados, y las dos veces sale más barata de lo que §5.3 estimaba.

### 4 · Dónde está el trabajo, en dos escalones

1. **Leibniz de TÉRMINOS** (`eq_substTerm`, recursión mutua con `eq_substTerms`): en el caso `func`
   hay que subir de igualdades **punto a punto** de la lista de argumentos a la igualdad de los dos
   términos, iterando la congruencia de una posición **con un prefijo que crece** (`eq_func_pw`).
   🔑 *Lo que faltaba no era lógica sino LISTAS*, por tercera vez (ADR‑031, ADR‑041, aquí).
2. **Leibniz de FÓRMULAS** (`eq_substFormula`), por inducción estructural. ⛔ Los casos `∀`/`∃`
   obligan a que **la ecuación viaje al contexto levantado**, porque
   `substFormula v t (∀A) = ∀ (substFormula (v+1) (liftTerm 0 t) A)` — **cambia el índice y levanta
   el término**. De ahí `derives2_lift`, una inducción entera sobre los 22 constructores y **la
   mitad del coste del módulo**. Cierra otra vez con `substFormula_lift_var`.

⭐ **Un contraste con ADR‑044 que vale la pena guardar**: allí `impl` obligó a un enunciado
**bicondicional**, porque la congruencia se invierte en el antecedente. **Aquí no hace falta**: el
enunciado ya es **simétrico en `t₁`/`t₂`**, así que basta aplicar la hipótesis de inducción con los
términos intercambiados y la ecuación simétrica. 🔑 *Cuando la simetría está en los datos, no hay
que meterla en el enunciado.*

### 5 · Y se paga la deuda en la otra dirección

ADR‑044 §4 midió que las cuatro piezas de `FOL/Eq0.lean` están **derivadas de `subst`**, de modo
que no podían conservarse como teoremas al quitarlo. `derives2_to_derives1` paga eso: demuestra que
las **tres nuevas son derivables** en `Derives₁` (usando `subst`), así que **`Derives₂` no es más
fuerte**. Sin ese lado, «quitar una regla» sería sólo «cambiarla de sitio».

### 6 · ⛔ Lo que NO dice

* **H3 NO está.** Esto no elimina cortes: pone el cálculo en la forma en que el Hauptsatz **se
  puede plantear**. `HerbrandExtraction` sigue abierta.
* ⛔ **Nada se retrofita.** `Derives₀` se queda; `derives0_iff_derives2` transporta lo que haga
  falta cuando haga falta.
* ⚠️ `check-estratos.bash` pasa de **6** a **7** estratos. `Derives₂`: **22** ctors —más que
  `Derives₁`, porque una regla se cambió por tres axiomas—, **0 habitantes‑axioma**.

**Véase también:** `FOL/Derives2.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.6,
`check-estratos.bash`, `check-footprints.bash` (64 titulares).

---

## ADR-046: H3, tercera pieza — el CÁLCULO DE SECUENTES, y la deuda reducida a DOS `Prop`

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑043 (el consumidor y la decisión de no construir el molde), ADR‑044/045 (los
dos obstáculos), plan §5.7

### 1 · Qué queda demostrado

    LK₀                    -- secuentes clásicos de dos lados, SIN corte (13 ctors)
    LKc                    -- lo mismo MÁS el corte (14)
    lk0_herbrand           -- ⭐⭐ la EXTRACCIÓN: de `LK₀ E ⟹ ∃xφ` salen los términos
    herbrandExtraction_of  -- ⭐⭐⭐ CutElim + NDtoLK ⇒ HerbrandExtraction

`FOL/Sequent0.lean`, **348 l. de código**. `lk0_herbrand` mide **`[propext]`**, `lk0_to_lkc`
**ningún axioma**, la cadena `[propext, Quot.sound]` — **ni un `Classical.choice`**.

⇒ **H3 queda reducida a DOS `Prop` enunciadas**, y el consumidor está escrito.

### 2 · ⭐ El orden, que es el que ADR‑043 §3 había decidido

Aquel ADR decidió **no** construir `LK₀` mientras no hubiera consumidor: *la guarda se copia del
CONSUMIDOR, no del molde*. El consumidor apareció allí mismo (`HerbrandCert`) y el cálculo quedó en
forma estándar en ADR‑045. **Sólo entonces** tiene sentido el molde — y **lo primero que se hace
con él es probar el consumidor**, `lk0_herbrand`.

🔑 Si esa prueba no hubiera salido, `LK₀` estaría mal diseñado **y no se sabría hasta el
Hauptsatz**, es decir, después de pagar la pieza cara. La disciplina se cobró aquí.

### 3 · ⭐⭐ Qué enseña `lk0_herbrand`, además de servir

De sus **13** casos:

| grupo | casos | qué pasa |
|---|---|---|
| produce el testigo | `exR` | ⭐ `∃A` en el sucedente sólo puede ser `∃φ`, y el término de la regla **es** un testigo |
| ⛔ imposibles | `allR`, `allL`, `exL` | meten un cuantificador donde la hipótesis dice que no lo hay |
| proposicionales | los **nueve** restantes | bookkeeping sobre `peval` |

🔑 **Y ahí se ve, en una frase, para qué sirve el Hauptsatz**: la regla de **corte** tendría una
fórmula `A` **arbitraria** —posiblemente cuantificada— que **no aparece en la conclusión**, así que
las hipótesis de la inducción **no se heredan**. *El corte es exactamente lo que rompe esta
lectura.*

### 4 · ⬜ Lo que queda — dos `Prop`, y nada más

    CutElim : ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ                      -- el HAUPTSATZ
    NDtoLK  : ∀ Γ f, Derives₂ Γ f →
                ∃ E, (∀ g ∈ E, EqInstance g) ∧ LKc (E ++ Γ) [f]

⚠️ **`NDtoLK` no es rutina, y su dificultad está localizada** (⬜ medida como **problema**, no como
coste): el caso `intro_forall` **levanta el contexto**, de modo que la lista `E` de instancias que
devuelve la hipótesis de inducción vive en el contexto **levantado** y hay que producirla desde el
de abajo — pero una instancia con `Term.var 0` **no es el levantamiento de ninguna**. Es el mismo
tipo de obstáculo que ADR‑045 resolvió con `derives2_lift`, en la dirección contraria.

### 5 · ⚠️ Y una comprobación que NO está hecha, dicha

`LK₀ Γ Δ → Derives₂ Γ (disjOf Δ)` —que `LK₀` **no sea demasiado fuerte**— ⬜ **no está**. El
obstáculo está identificado: el caso `allR` exige sacar una disyunción de dentro de un
cuantificador (`∀x(A ∨ C) → (∀x A) ∨ C` con `C` sin `x`), clásico pero con su propia capa de lemas
sobre el levantamiento.

⇒ **No está en el camino crítico** —las dos obligaciones del §4 no pasan por ella—, pero es lo que
certificaría que el molde no prueba de más. Queda dicho, no escondido.

### 6 · ⭐ El control cazó un error mío de conteo

Declaré `LK₀|14` y `LKc|15` en `check-estratos.bash`. **Son 13 y 14.** El control rompió en el
acto y la cifra se corrigió en los **dos** sitios (la tabla y el docstring, que también decía «14
casos» y «los diez restantes»).

🔑 *Un contador exacto rompe también hacia abajo* — es la misma propiedad que protege ADR‑032, y
esta vez me protegió de publicar una cifra falsa en un docstring.

**Véase también:** `FOL/Sequent0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.7,
`check-estratos.bash` (9 estratos), `check-footprints.bash` (69 titulares).

---

## ADR-047: La corrección de PeanoRF, ACEPTADA y BLINDADA — y su conjetura sobre `Theorems.Eq`, REFUTADA

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Origen:** `../Peano-from-ROB-n-FOL/doc/HANDOFF-FOL-2026-09-16.md` (proyecto PeanoRF)

### 1 · Lo aceptado, tras medirlo

En `FOL/Semantics.lean`, `shift_updateEnv_comm`, un caso **imposible** se cerraba con `omega`:

    -  | zero => omega
    +  | zero => exact absurd (Nat.le_zero.mp (Nat.not_lt.mp h1)).symm h2

**Medido aquí, no aceptado de palabra** — cinco declaraciones pasan a `[propext, Quot.sound]`:
`shift_updateEnv_comm`, `eval_liftFormula_ext`, `eval_substFormula_ext`,
`contextSatisfies_lift_zero`, `eval_substFormula_zero`. Era el **único `Classical.choice` de toda
la semántica de fórmulas**.

⭐ **Y queda BLINDADO**: los cuatro primeros entran en `check-footprints.bash` (69 → **73**). Sin
eso, la ganancia se pierde en el primer refactor y nadie se entera. *Una mejora sin control es una
mejora prestada.*

### 2 · 🔑 La regla, que es lo reutilizable

> **`omega` sobre metas ARITMÉTICAS es limpio. Sobre metas FUERA de su lenguaje, descargadas por
> CONTRADICCIÓN, mete `Classical.choice`.**

⇒ Cuando `omega` cierre un caso imposible cuya meta **no** sea aritmética, sustituirlo por
`absurd` / `False.elim` explícito. Es una instancia **nueva** de la familia «Classical oculto», y
encaja con lo que este repo ya tenía medido: *el footprint de una táctica no es propiedad del
enunciado ni de la táctica* ([[feedback-footprint-no-es-constructividad]] §2).

### 3 · ⚠️ Lo NO aceptado: su conjetura sobre los tres de `FOL.Theorems.Eq`

El handoff marca como «SOSPECHOSOS, muy probable que sea el mismo patrón del `omega`»
a `substTerm_subst_comm_succ`, `substTerms_subst_comm_succ` y `subst_subst_comm_succ`.

**Medido: la conjetura NO explica esos tres.** Sus `omega` están **todos** dentro de
`show ¬ k = j from by omega` — es decir, sobre metas **aritméticas**, que es el lado **limpio** de
su propia regla. Y en el entorno de imports de `FOL/Theorems/Eq.lean` (`import FOL.FOL`) salen
limpios, uno a uno:

| pieza | footprint |
|---|---|
| `Nat.lt_trichotomy` | **ningún axioma** |
| `rcases Nat.lt_trichotomy …` | **ningún axioma** |
| `by omega` sobre `¬ k = j` | `[propext, Quot.sound]` |
| `simp [substTerm, show ¬ k = j from by omega]` | `[propext, Quot.sound]` |
| `congr 1` sobre `Term.func` | **ningún axioma** |

⇒ ⬜ **La causa está en una rama concreta del lema y NO está localizada.** Hace falta bisección por
ramas del propio lema, como ellos mismos hicieron para la semántica. ⚠️ Y su propio aviso de método
aplica aquí: *refutar con la cadena sucia es refutar ruido* — por eso esto se declara como
**conjetura refutada**, no como diagnóstico alternativo.

⬜ `FOL.Tactics.tryMem`: **no medido** por este lado.

### 4 · ⚠️ Nota de proceso, para el próximo handoff

El arreglo llegó **aplicado y sin commitear en el árbol de trabajo compartido**. Ese día yo hice
varios `git add -A`, así que **pudo haberse colado en un commit mío con un mensaje que no lo
menciona** — de hecho comprobé si había pasado, y por poco. 🔑 *Un cambio ajeno sin commitear en un
árbol compartido es indistinguible de uno propio.* ⇒ pedir parche o rama, o avisar antes.

**Véase también:** `FOL/Semantics.lean`, `check-footprints.bash`,
`../Peano-from-ROB-n-FOL/doc/HANDOFF-FOL-2026-09-16.md`.

---

## ADR-048: `LK₀` no prueba de más — y el dividendo de tener las DOS direcciones

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO ·
**Relacionado:** ADR‑046 §5 (la comprobación que quedaba), ADR‑041 (completitud), ADR‑047 (la
corrección de la semántica), plan §5.7

### 1 · Qué queda demostrado

    lkc_sound       : LKc Γ Δ → ∀ M v, (todo Γ vale) → algún elemento de Δ vale
    lk0_sound       : ídem para `LK₀`, por el encaje
    lk0_to_derives0 : LK₀ Γ Δ → Γ ⊢₀ disjOf Δ
    lk0_not_empty   : ¬ LK₀ [] []

`FOL/SequentSound0.lean`, **173 l. de código**, `[propext, Classical.choice, Quot.sound]`.

⚠️ **No es adorno.** `LK₀` es el cálculo sobre el que se va a enunciar y demostrar el Hauptsatz. Si
fuera **demasiado fuerte**, `CutElim` podría ser cierto y no servir —o se perseguiría un teorema
falso durante las mil líneas del Hauptsatz—. Esto lo cierra **antes** de pagar esa pieza.

### 2 · ⭐ El dividendo: comprar un resultado sintáctico por la semántica

ADR‑046 §5 estimó `LK₀ Γ Δ → Derives₂ Γ (disjOf Δ)` en **~250 l. con riesgo en `allR`**, que por la
vía sintáctica exige sacar una disyunción de dentro de un cuantificador. **Por la semántica ese
caso es rutina**, y el resultado sintáctico cae **como corolario** vía `completeness₀` (ADR‑041) y
`derives0_iff_derives2` (ADR‑045).

🔑 **La regla nueva**: *cuando las dos direcciones están demostradas, un resultado sintáctico se
puede comprar por la semántica* — a cambio de `Classical.choice`, que aquí no cuesta nada porque el
enunciado ya es clásico. **Es la primera vez que este repo cobra ese dividendo**, y sólo se puede
desde ADR‑041. ⚠️ Con su condición: el precio es un footprint clásico, así que **no** sirve para
resultados que quieran ser net‑0.

### 3 · ⭐⭐ Lo que enseña el caso `cut`

Se probó sobre **`LKc`** —el que **tiene** corte— y `lk0_sound` salió por `lk0_to_lkc`: **una sola
inducción** en vez de dos. Y el caso `cut` es **semánticamente trivial**, tres líneas: si algo de
`A :: Δ` vale y, suponiendo `A`, algo de `Δ` vale, entonces algo de `Δ` vale.

🔑 **Ahí está, en una frase, todo el frente H3**: *el corte es **gratis para la verdad** y
**carísimo para la demostración***. `lk0_herbrand` (ADR‑046) no puede con él —su fórmula de corte
no aparece en la conclusión, así que las hipótesis de la inducción no se heredan— y eliminarlo es
el Hauptsatz. **La semántica no distingue lo que la sintaxis paga.**

### 4 · ⭐ Y ADR‑047 pagó aquí, inmediatamente

Los dos casos caros (`allR`, `exL`) pasan por `contextSatisfies_lift_zero` y
`eval_liftFormula_zero`. **Las dos acababan de quedar limpias** con la corrección de PeanoRF. Sin
ella, este módulo habría heredado un `Classical.choice` **indistinguible del legítimo** — y el
footprint habría dicho lo mismo por dos razones distintas, que es exactamente lo que
[[feedback-footprint-no-es-constructividad]] §4 advierte.

### 5 · ⚠️ El `Classical.choice` de aquí ES matemático

La solidez de un cálculo de secuentes **multiconclusión** es clásica de raíz: `implR` decide si `A`
vale, `allR` decide si `∀A` vale. Sin tercio excluso no hay teorema.

⭐ Y por eso vive en **otro módulo**: `FOL.Sequent0` —la **extracción**— mide `[propext]` y es
constructiva. *La extracción es constructiva; la solidez, no.* Separarlos es lo que deja verlo.

**Véase también:** `FOL/SequentSound0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.7,
`check-footprints.bash` (76 titulares).

---

## ADR-049: `NDtoLK` demostrada — y la regla que faltaba, `eqAx`

**Fecha:** 2026‑09‑16 · **Estado:** ✅ EJECUTADO · **Revisa:** ADR‑046 (diseño de `LK₀`) ·
**Relacionado:** ADR‑045 (`Derives₂`), ADR‑048 (solidez), plan §5.8

### 1 · Qué queda demostrado

    ndToLK : Derives₂ Γ f → LKc Γ [f]                          -- los 22 casos
    herbrandExtraction_of_cutElim : CutElim → HerbrandExtraction

`FOL/NDtoLK0.lean`, **118 l. de código**, `[propext, Quot.sound]` — **ni un `Classical.choice`**;
`mpLK` y `viaEqImpl` **no dependen de ningún axioma**.

⇒ 🏁 **De las dos obligaciones de ADR‑046 queda UNA: el Hauptsatz.** Toda la vía H —y con ella lo
único que faltaba del plan— cabe en una línea.

### 2 · ⭐⭐ Lo que desbloqueó: una REGLA, no más esfuerzo

ADR‑046 §4 midió el bloqueo, y lo midió bien: con las instancias de igualdad **en el antecedente**,
el caso `intro_forall` **levanta el contexto**; la `E` que devuelve la hipótesis de inducción vive
arriba y hay que producirla abajo, pero **una instancia con `Term.var 0` no es el levantamiento de
ninguna**. No hay manera de arreglarlo con más bookkeeping.

⭐ La salida fue **añadir la regla que faltaba**: `eqAx`, el **corte contra un axioma de la
teoría** (*theory‑cut*), que mete el axioma **localmente, donde se usa**:

    eqAx : EqInstance g → LK (g :: Γ) Δ → LK Γ Δ

| | antes | ahora |
|---|---|---|
| `NDtoLK` | ⛔ bloqueada por el levantamiento | ✅ **demostrada**, traducción **estructural** sin `E` |
| `lk0_herbrand` | devolvía sólo `ts` | ⭐ devuelve `ts` **y** la `E` que la derivación usa |
| `CutElim` | estándar | **sigue siendo estándar**: los axiomas son **sin cuantificadores** y permutan como cualquier regla izquierda |

🔑 **La lección**: *cuando una obligación se bloquea por bookkeeping, a veces lo que falta no es
esfuerzo sino una regla.* ⚠️ Y el aviso recíproco: sólo vale si la regla nueva **no encarece** lo
que venía detrás — aquí `CutElim` no se encarece, y eso hay que comprobarlo **antes** de añadirla,
no después.

### 3 · ⚠️ El diseño está FORZADO, no elegido

`eqAx` **no puede** ser una regla **derecha** de igualdad (`⟹ t ≐ t`). `peval` trata `t ≐ t` como
un **átomo**, así que bajo una valuación arbitraria es **falso**: el certificado sólo puede decir
*«la disyunción se sigue de `E`»*, y por tanto la `E` **tiene que existir**.

🔑 **La forma de `HerbrandCert` fija la forma del cálculo.** Es el mismo principio que ADR‑043 §3
—*la guarda se copia del consumidor*— aplicado ahora al molde entero.

### 4 · Qué se tocó, y qué no

* `FOL/Sequent0.lean`: `eqAx` en `LK₀` (13 → **14** ctors) y `LKc` (14 → **15**);
  `lk0_herbrand` **generalizada** para devolver `E`; `NDtoLK` cambia de forma (ya no lleva `E`).
* `FOL/SequentSound0.lean`: caso `eqAx` + ⭐ **`eqInstance_valid`** —los axiomas de la igualdad son
  **válidos en todo modelo**—, que es lo que hace sólido el theory‑cut. **Net‑0.**
* ⛔ **`Derives₀`…`Derives₂` no se tocan.** Nada aguas arriba se movió.

### 5 · Lo que salió gratis, y lo que costó

⭐ **`intro_forall` es literalmente `allR`** y **`elim_ex` es `exL`** — directos, sin corte. *Los
dos cálculos tienen la misma regla de eigenvariable, escrita de dos maneras.*

⚠️ El caso con más trabajo fue `forall_not_ex_not` (`¬∀A ⟹ ∃¬A`): bajar por `allR`, subir el `∃`
con testigo `Term.var 0` y cerrar con **`substFormula_lift_var`** — el lema del paso de
eigenvariable de Henkin (ADR‑036), **por tercera vez**.

**Véase también:** `FOL/NDtoLK0.lean`, `FOL/Sequent0.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.8, `check-estratos.bash` (LK₀ 14, LKc 15),
`check-footprints.bash` (80 titulares).

---

## ADR-050: El andamiaje del Hauptsatz — H3 sobre el CORTE ÚNICO, y dos conmutaciones que faltaban

**Fecha:** 2026‑09‑17 · **Estado:** 🔶 PARCIAL (el Hauptsatz **NO** está) ·
**Relacionado:** ADR‑046/049 (`LK₀`, `NDtoLK`), ADR‑048 (solidez), plan §5.9

### 1 · Qué queda demostrado, y qué NO

`FOL/Hauptsatz0.lean`, **218 l. de código**. ⛔ **`CutAdm` no está**: esto es lo que hay que tener
**antes** de intentarlo.

    CutAdm               -- el corte ÚNICO
    cutElim_of           -- ⭐ CutAdm ⇒ CutElim, DEMOSTRADO
    LKh                  -- el cálculo INDEXADO POR ALTURA (14 ctors)
    lkh_mono · lkh_to_lk0 · lk0_to_lkh
    liftFormula_subst_le -- ⭐ la conmutación De Bruijn que FALTABA

`cutElim_of`, `lkh_mono` y `lkh_to_lk0` **no dependen de ningún axioma**; el resto,
`[propext, Quot.sound]`. **Ni un `Classical.choice`.**

### 2 · ⭐ Separar el corte ÚNICO de su clausura

`CutElim` es la clausura sobre derivaciones; lo que un Hauptsatz demuestra es el **corte único**,
`CutAdm`. La conversión es una inducción de quince líneas. ⇒ **H3 se enuncia ahora sobre el objeto
sobre el que la literatura razona**, no sobre su envoltorio.

🔑 Es el mismo movimiento que ADR‑043 (enunciar la deuda con su consumidor) una vuelta más adentro:
*una deuda bien enunciada se parece a lo que la literatura demuestra, no a lo que uno necesita.*

### 3 · ⚠️⚠️ Por qué hace falta indexar por ALTURA — y es una limitación del sistema, no del diseño

La prueba de Gentzen es una **inducción doble**: grado de la fórmula de corte × **suma de las
alturas** de las subderivaciones.

⛔ **La altura no se puede definir sobre `LK₀`**: vive en `Prop`, así que **no hay eliminación
grande** y no existe `altura : LK₀ Γ Δ → Nat`. ⇒ hay que indexarla **en el propio inductivo**, y
mantener los dos encajes.

🔑 Es de la familia de M‑11 (ADR‑025): **el universo en el que vive un inductivo decide qué se
puede decir de sus habitantes.** Allí era la inducción; aquí es la medida.

### 4 · ⭐ Una decisión de diseño que se come una complicación clásica entera

`LKh.struct` se declara **preservando la altura**. Eso da **debilitamiento, contracción e
intercambio gratis dentro de la inducción** — y la contracción es exactamente lo que en la
presentación clásica obliga a pasar por la regla **MIX** en vez del corte.

🔑 *Una decisión sobre la forma del inductivo puede eliminar una complicación entera de la prueba.*
⚠️ Con su contrapartida, que hay que vigilar: `struct` sin coste de altura es una regla **fuerte**;
si la inducción doble no cierra, el primer sospechoso es ella.

### 5 · ⛔ Dos conmutaciones De Bruijn que el repo NO tenía — MEDIDO

| lema | condición | dónde |
|---|---|---|
| `substFormula_lift_comm` | `k = v` | `Theorems/Eq.lean` |
| `liftFormula_subst` | `v ≤ k` | `Lift0.lean` |
| ⭐ `liftFormula_subst_le` | **`k ≤ v`** | **hecho aquí** |
| ⬜ Barendregt general | `substFormula v s (substFormula 0 u f) = …` | **falta** |

⚠️ La segunda falta de verdad: `subst_subst_comm_succ` sólo cubre índices **adyacentes**
(`j+1`/`j`), y el caso `allL` del lema de sustitución necesita `v` **arbitrario**.

🔑 *Una familia de lemas De Bruijn casi nunca está completa: hay que mirar qué mitad falta antes de
planificar, no a mitad de la prueba.*

### 6 · ⚠️ Y no hay atajo semántico — dejado escrito para que no se intente

`CutAdm` **no** sale de `lkc_sound` (ADR‑048) + `completeness₀` (ADR‑041): `completeness₀` devuelve
una derivación de **`Derives₀`**, no de `LK₀`, y convertirla exigiría `Derives₀ → LK₀` **sin
corte** — que **es** el Hauptsatz. **El círculo se cierra.**

⚠️ Esto **no contradice** ADR‑048 §2 (*un resultado sintáctico se puede comprar por la semántica*):
allí el destino era `Derives₂`, que la completitud sí produce. Aquí el destino es `LK₀` **cut‑free**,
que ninguna completitud de este repo produce. 🔑 *El dividendo semántico sólo paga hacia el cálculo
del que se tiene completitud.*

### 7 · ⬜ Lo que falta, con su riesgo

1. ⬜ Barendregt general, ~90 l., **riesgo bajo** (gemela de la hecha);
2. ⬜ `lkh_subst` — cerrado por sustitución, preservando altura, ~150 l.;
3. ⬜ **la inducción doble**, ~400–600 l., **riesgo alto**.

**Véase también:** `FOL/Hauptsatz0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.9,
`check-estratos.bash` (10 estratos), `check-footprints.bash` (85 titulares).

---

## ADR-051: Las dos conmutaciones y `lkh_subst` — H3 a UNA pieza, y un control que absolvía a 27 módulos

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: ADR-050 dejó `CutAdm` con **tres** piezas abiertas. Se pagan las dos primeras.
⚠️ Y al ir a proyectar, se descubre que el catálogo de FOL llevaba meses mintiendo.

### 1 · ⭐ Barendregt GENERAL — y generalizar salió MÁS BARATO

    substFormula v s (substFormula w u f)
      = substFormula w (substTerm v s u) (substFormula (v+1) (liftTerm w s) f)     -- con `w ≤ v`

⚠️ **El enunciado de ADR-050 §7.1 era el caso `w = 0`**, que es el único que `lkh_subst` consume.
Hubo que **generalizar a `w` arbitrario** para que la recursión bajo el binder (`w+1 ≤ v+1`)
cerrara sobre sí misma. 🔑 *Y por eso salió barato*: es el **quinto corolario de «medir la
forma»** — generalizar puede abaratar, porque los pasos caros suelen ser artefactos de la
instancia. Estimado ~90 l.; **medido 99 l.**, riesgo bajo confirmado.

El único caso con trabajo real es `.var n` con `n = v+1`, donde hay que **deshacer** un
levantamiento: `(substTerm_liftTerm s w (substTerm v s u)).symm`. Los otros seis caen por
tricotomía de `n` contra `w` y `v`, y `omega` sobre las guardas.

### 2 · ⭐⭐ `lkh_subst` — cerrado por sustitución, PRESERVANDO la altura

    lkh_subst : LKh n Γ Δ → ∀ v t, LKh n (Γ.map (substFormula v t)) (Δ.map (substFormula v t))

**La altura de salida es la misma `n`.** Eso es lo que la inducción doble necesitará: *sustituir
no puede encarecer una derivación*, o el orden de la inducción interna no estaría bien fundado.

| casos | qué hacen | qué paga |
|---|---|---|
| `allR`, `exL` | **cambian el entorno** (bajo el binder: `v+1`, `liftTerm 0 t`) | `liftFormula_subst_le` (ADR-050), vía `map_lift_subst` |
| `allL`, `exR` | **instancian** (el testigo viaja a `substTerm v t s`) | **Barendregt general**, §1 |
| `eqAx` | nada: `eqInstance_subst` — cinco casos, **sin ningún axioma** | — |
| los otros nueve | `simp only [List.map_cons, substFormula]` | — |

⭐ Y aquí **se cobra la decisión de diseño de ADR-050**: como `LKh.struct` preserva la altura,
debilitamiento, contracción e intercambio son **un caso más de la inducción** y no una
complicación aparte. Estimado ~150 l.; **medido 133 l.**

📏 **Footprint**: `eqInstance_subst` **sin ningún axioma**; `substFormula_subst_le` y `lkh_subst`,
`[propext, Quot.sound]`. Ni un `Classical.choice` en todo `Hauptsatz0.lean`.

⇒ **H3 queda con UNA sola pieza**: la inducción doble (~400–600 l., riesgo alto).

### 3 · ⛔⛔ Y el hallazgo caro: `[C] PROYECCIÓN` no miraba FOL, y luego absolvía por SUBCADENA

Al ir a proyectar (AI-GUIDE §14) se midió que `FOL/REFERENCE.md` §3 y §6 tenían **12 entradas**,
**cuatro de ellas fantasma** (`Prelim.lean`, `Soundness.lean`, `Completeness.lean`,
`Compacity.lean` — módulos que ya no existen). ⇒ de los **34** módulos que el control comprueba
(todo `FOL/*.lean` y `FOL/Theorems/*.lean` menos el barril), había **7** proyectados y **27 NO**.

⛔ **La causa no es el olvido, es el control.** El bloque `[C]` de `check-doc-sync.bash` iteraba
**sólo** sobre `ROBINSON_PlusPlus/Meta/*`, `Minimal/*` y `Full/*` contra el REFERENCE.md **de
RPP**: *los módulos de FOL no los miraba nadie*. Van **siete** causas medidas de «control que da
verde sin comprobar».

⚠️⚠️ Y la octava, que es mía y de hoy: la **primera versión** del control nuevo casaba con
`grep -F "$m.lean"`, y eso **absuelve por subcadena y por basename**:

| módulo | lo absolvía | por qué |
|---|---|---|
| `Theorems/Eq.lean` | `DecEq.lean` | `"Eq.lean"` es subcadena de `"DecEq.lean"` |
| `Theorems/Deduction.lean` | `Deduction.lean` (§6.8) | el `basename` de los dos es el mismo |

⇒ el control se endureció a la **ruta** (no el basename) con **frontera de palabra**, y entonces
cazó los dos. 🔑 *Un control que casa por subcadena no comprueba: absuelve.*

### 4 · Lo que la proyección destapó, que no era sólo documentación

* ⭐ **`Theorems/Eq.lean` es el módulo de conmutaciones De Bruijn del repo** (24 nombres), y
  estaba **sin proyectar**. Por eso `Hauptsatz0` tuvo que **medir dos veces** qué mitad de la
  familia faltaba: el catálogo no podía decírselo a nadie. *Un módulo sin proyectar se vuelve a
  construir* — y van **seis** con ésta.
* ⚠️ **`Theorems/Deduction.lean` es un duplicado literal** de `FOL/Deduction.lean`: el mismo
  teorema, la misma prueba, otro `namespace`. **No lo importa nadie.**
* ⚠️ **Tres huérfanos medidos**: `Classical.lean`, `Tactics2.lean` y `Theorems/Deduction.lean`
  no los importa ningún módulo del árbol. ⬜ **No se retiran aquí**: retirar es una decisión con
  ADR, no una pasada de documentación. Quedan **escritos** en `FOL/REFERENCE.md` §6.14.
* ⭐ **`MetaRules.lean` proyectado por fin**, y con ello el dato que más se re-aprende: de sus
  16 nombres, **cuatro son `axiom`** (`imp_intro`, `raa`, `or_elim`, `ex_elim`) — los **cuatro
  habitantes-axioma de `Derives`**, el suelo de M-11 (ADR-029).

### 5 · Decisión

1. ✅ `substFormula_subst_le` y `lkh_subst` entran en `FOL/Hauptsatz0.lean` (§5 y §6).
2. ✅ `FOL/REFERENCE.md` gana §3.13 (tabla de descripciones de los 21 módulos del plan), §6.13
   (338 nombres públicos **generados del árbol**) y §6.14 (los seis antiguos).
3. ✅ `check-doc-sync.bash` `[C]` comprueba **FOL contra `../FOL/REFERENCE.md` §6**, por ruta y
   con frontera de palabra.
4. ⬜ Las cuatro entradas fantasma de §3/§6 llevan **banner de aviso** en vez de borrarse: lo que
   dicen es historia del repo, y borrarlas perdería la traza. ⬜ Retirar los tres huérfanos queda
   **abierto**, con ADR propio.

**Controles tras el cambio:** RPP **145 jobs** · `lake build "@FOL/FOL" "@FOL/TheoryFramework"`
**42 jobs** · `check-footprints` **88** (⚠️ eran 85: los tres teoremas nuevos **no estaban**
vigilados — un titular que no se declara no lo comprueba nadie) · `check-estratos` **10** ·
`check-doc-sync` ✅ · `check-axioms` ✅ (`ESPERADO_CUAR=1`, intacto).

**Véase también:** `FOL/Hauptsatz0.lean` §5-§6, `FOL/REFERENCE.md` §6.13-§6.14,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.10, ADR-050, ADR-029.

---

## ADR-052: 🏁🏁🏁 EL HAUPTSATZ — H3 cerrada, y la inducción doble que no hizo falta

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: ADR-051 dejó `CutAdm` como la única pieza viva de H3, estimada en ~400–600 l. y
**riesgo alto**. Se paga. `FOL/Hauptsatz0.lean` §7-§8, **605 l. de código nuevas**.

    hauptsatz          : CutAdm              -- ⭐⭐⭐ el corte es ADMISIBLE en LK₀
    cut_elimination    : CutElim
    herbrand_extraction: HerbrandExtraction  -- H3, que era la deuda
    herbrand           : ([] ⊢₀ ∃φ) ↔ ∃ ts E, HerbrandCert φ ts E   -- ⭐ ya INCONDICIONAL

📏 **Footprint**: `[propext, Quot.sound]` en todo. **Ni un `Classical.choice`, ni un axioma del
proyecto.** (`eqInstance_lift` y `eqInstance_subst`, sin ningún axioma.)

### 1 · ⛔⛔ La corrección de diseño: `struct` TIENE que subir la altura

ADR-050 declaró `LKh.struct` **preservando** la altura y anotó, en `NEXT-STEPS.md`, que *«si la
inducción doble no cierra, el primer sospechoso es `struct`»*. **Lo era.** Con la altura
preservada, el caso `struct` de la inducción recurre sobre una premisa de la **misma** altura: la
medida no decrece. Y no hay escapatoria por inducción estructural, porque la prueba también recurre
sobre el lado **derecho**, que no es subderivación del izquierdo.

⭐ **Y no se perdió nada.** El debilitamiento/contracción/intercambio «gratis» que evita la regla
**MIX** de Gentzen no venía de la altura de `struct`: viene de que el enunciado del corte pide
**PERTENENCIA** —`Or (x = A) (x ∈ Δ)`— en vez de la forma `A :: Δ`. Con eso, que `A` aparezca
muchas veces en el contexto es el caso normal y no hace falta contraer.
🔑 *Lo que mata a MIX es el ENUNCIADO, no el constructor.*

⚠️ Medido: el cambio costó **tres ediciones** (el constructor, `lkh_mono`, `lk0_to_lkh`) y
`lkh_subst` **no se movió**. Una sospecha anotada un día antes se cobró en cinco minutos.

### 2 · ⭐⭐⭐ `LeftPrin`, y por qué la inducción DOBLE no hizo falta

La presentación clásica induce sobre el **grado** × la **suma de alturas**, con un análisis cruzado
de las dos últimas reglas: por cada una de las 5 conectivas, los 14 casos de la otra derivación.
Eso es ~5×14 bloques de permutación casi idénticos.

Aquí se hace en **dos pasadas independientes de 14 casos**:

| pasada | induce sobre | qué hace |
|---|---|---|
| `cutPrinAux` (§8.5) | la altura `n` de `D2` | analiza `D2` **una sola vez**; los 5 casos principales son las reducciones de grado |
| `cutLeftAux` (§8.6) | la altura `m` de `D1` | analiza `D1`; sus casos principales **delegan** en `cutPrinAux` |

Lo que las desacopla es un **dato uniforme**:

    LeftPrin (b ⇒ c)  Γ Δ = LK₀ (b :: Γ) (c :: Δ)
    LeftPrin (b ∧ c)  Γ Δ = LK₀ Γ (b :: Δ)  ∧  LK₀ Γ (c :: Δ)
    LeftPrin (b ∨ c)  Γ Δ = LK₀ Γ (b :: c :: Δ)
    LeftPrin (∀ b)    Γ Δ = LK₀ (Γ.map lift) (b :: Δ.map lift)
    LeftPrin (∃ b)    Γ Δ = ∃ t, LK₀ Γ (substFormula 0 t b :: Δ)
    LeftPrin _        _ _ = False

— las premisas de la regla derecha principal de `A`, empaquetadas. Con `leftPrin_mono` y
`leftPrin_lift` ese dato **viaja** a los contextos nuevos que cada permutación de `D2` crea.
⇒ **la medida `m + n` no aparece en ningún sitio**: basta `m` por fuera y `n` por dentro.

🔑 *Cuando dos análisis de casos se cruzan, lo que los desacopla es encontrar el DATO que uno le
pasa al otro.* Y es el mismo patrón que ADR-049 (`eqAx`): **el desbloqueo no fue esfuerzo, fue una
definición**.

⭐ **Dividendo inesperado**: en cada regla derecha de `D1` la **misma llamada recursiva** sirve para
las dos ramas del `by_cases` — es `LeftPrin A Γ Δ` si la principal es `A`, y la premisa de la regla
si no lo es. Cinco casos que parecían dobles son uno.

⛔ Y `LeftPrin` es **`False`** para `⊥`, átomos e igualdades —no hay regla derecha que las
introduzca—, lo que **cierra gratis** el caso `botL` de `D2` con `A = ⊥`, que en las presentaciones
de libro hay que argumentar aparte.

### 3 · `lkh_lift`: la otra clausura, que sí hizo falta y no estaba

Cuando `D2` termina en `allR` (o `exL`), permutar el corte obliga a **levantar la derivación
entera del otro lado y la propia fórmula de corte**. ⇒ hizo falta
`lkh_lift : LKh n Γ Δ → ∀ k, LKh n (Γ.map (liftFormula k)) (Δ.map (liftFormula k))`, gemela de
`lkh_subst` (ADR-051) y con la misma propiedad crítica: **preserva la altura**.

⭐ Los tres lemas que consume **ya existían** (`liftFormula_lift`, `liftFormula_subst`,
`substFormula_liftFormula`): esta vez el catálogo sí los decía, porque `Theorems/Eq.lean` y
`Lift0.lean` se proyectaron en ADR-051. *Antes de construir, buscar* — y esta vez salió bien.

⚠️ El índice tiene que ser **general** (`k` arbitrario, no sólo 0): el caso `allR` recurre con
`k+1`. Es la misma lección que el Barendregt de ADR-051 — **generalizar es lo que cierra**.

### 4 · Lo que queda dicho, y lo que NO cambia

* ⭐ **El atajo semántico seguía sin existir**, como ADR-050 §6 dejó escrito: `completeness₀`
  devuelve `Derives₀`, no `LK₀` sin corte. Esto se ha pagado **sintácticamente**, que era la única
  vía. La advertencia era correcta y ahorró el intento.
* ⚠️ **Esto NO toca `Derives`**: `hauptsatz` es sobre `LK₀`, y el puente a la deducción natural es
  `ndToLK` sobre `Derives₂` (ADR-049). **M-11 y ADR-032, intactos.**
* ⚠️ `herbrand` es sobre `Derives₀`, no sobre `⊢`. Sigue valiendo ADR-024: *ningún resultado sobre
  `axioms ⊢` dice nada*, porque ese cálculo es sintácticamente completo.

### 5 · Decisión

1. ✅ `LKh.struct` **sube la altura**; el comentario de §2 que decía lo contrario queda corregido
   **en su sitio**, con la razón escrita.
2. ✅ `FOL/Hauptsatz0.lean` gana §7 (`deg`, `lkh_lift`) y §8 (el Hauptsatz). 1 023 l. de código.
3. ✅ `Hauptsatz0.lean` pasa a importar `FOL.NDtoLK0` (sin ciclo: `NDtoLK0` sólo importa
   `FOL.Sequent0`).
4. ✅ `check-footprints.bash`: **88 → 96** titulares, los ocho nuevos.
5. ⬜ **No se retira nada**: `HerbrandExtraction` sigue siendo un `Prop` y `herbrand_iff` sigue
   tomándolo por hipótesis. El teorema incondicional es **`herbrand`**, al lado. *Cuando una deuda
   se salda, el enunciado condicional se queda: documenta de qué dependía.*

**Controles tras el cambio:** RPP **145 jobs** · FOL **42 jobs** · `check-footprints` **96** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

**Véase también:** `FOL/Hauptsatz0.lean` §7-§8, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.11,
ADR-050, ADR-051, ADR-049, ADR-043.

---

## ADR-053: La consistencia de `Derives₀` SIN `Classical.choice` — y la no-constructividad estaba en el TIPO DE LLEGADA

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: el Hauptsatz (ADR-052) se pagó por su valor logico. Esta ADR cobra el **dividendo
finitista**, que es la razon por la que un plan finitista lo queria. `FOL/Finitary0.lean`, 190 l.

| teorema | ruta | footprint |
|---|---|---|
| `derives0_consistent` (ADR-034) | semantica: `derives0_soundness` + el modelo `Mtrue` | `[propext, **Classical.choice**, Quot.sound]` |
| ⭐⭐ `derives0_consistent_fin` | **sintactica**: `ndToLK` + `cut_elimination` + `lk0_tval` | **`[propext, Quot.sound]`** |

**Mismo enunciado, footprint estrictamente menor.** Es el patron de ADR-042 (`A ∨ ¬A` y Peirce,
demostrados por completitud y por Kalmar): *la via H da lo mismo con menos supuestos*.

### 1 · ⚠️ De donde venia el `Classical.choice`, MEDIDO — y NO era del modelo

La sospecha natural (y la que un agente lateral formulo) es que el coste viene de «la semantica».
**Falso, y se mide en dos minutos**: `derives0_consistent` **ya** usaba un modelo de UN PUNTO
(`Mtrue : Model Unit`, `FOL/Soundness0.lean:204`). El `Classical.choice` sale de **cuatro
`Classical.byContradiction`** en la prueba de `derives0_soundness` (`FOL/Soundness0.lean:172-182`),
y estan ahi porque `eval` devuelve **`Prop`** y la semantica de Tarski es clasica.

🔑 *El modelo era finitario; la SOLIDEZ no.* ⚠️ Y el docstring del propio modulo ya lo decia
(«los unicos que necesitan logica clasica en el metanivel»): estaba escrito y nadie lo habia leido
como una **oportunidad**.

### 2 · ⭐ La salida: evaluar a `Bool`, no a `Prop`

    tval (a : Bool) : Formula → Bool
      | ⊥ => false | atom => a | eq => true
      | impl f g => (!tval a f) || tval a g | and => && | or => ||
      | forall f => tval a f | ex f => tval a f

Es el modelo de un punto **calculado**: dominio de un elemento ⇒ los cuantificadores desaparecen, y
`tval` no mira los terminos ⇒ ignora `lift` y `subst` (`tval_lift`, `tval_subst`, dos inducciones de
diez lineas).

⭐⭐ **Y por eso no hace falta el tercio excluido.** El caso `implR` de la solidez dice «o vale
`A ⇒ B`, o vale algo de `Δ`». Sobre `Prop` eso exige `em`. Sobre `Bool` es `cases h : tval a A`.
🔑 **La no-constructividad no estaba en la matematica: estaba en el TIPO DE LLEGADA del evaluador.**
Es una leccion generalizable: antes de aceptar un `Classical.choice` «porque la semantica es
clasica», mirar si el modelo concreto que se usa admite una version decidible.

### 3 · ⭐ La regla `eqAx` no cuesta nada aqui

`tval_eqInstance` **no depende de ningun axioma**: los cinco axiomas de la igualdad
(`eqReflAx`, `eqSymmAx`, `eqTransAx`, `eqFuncAx`, `eqAtomAx`) son `eq`- o `impl`-shaped y salen por
`rfl`. ⚠️ Salvo `eqAtomAx`, que da `!a || a` y necesita `cases a` — no es `rfl` con `a` variable, y
fue el UNICO error de compilacion del modulo.

⇒ el theory-cut de ADR-049, que fue lo que desbloqueo `NDtoLK`, **sigue sin encarecer nada**, que
era la condicion que ADR-049 §aviso se impuso a si misma. *Una regla nueva solo vale si no encarece
lo de detras — y se comprueba cada vez que se usa, no una sola vez.*

### 4 · ⛔ Donde paga el Hauptsatz — ⚠️⚠️ ESTA SECCION ESTA RECTIFICADA, ver §6

⚠️ **NO en `lk0_tval`**: `LK₀` ya era cut-free (el calculo con corte es `LKc`), asi que la solidez
booleana no necesita el Hauptsatz para nada. Corrige una afirmacion que circulaba.

Paga en **un solo sitio**: el puente desde la deduccion natural. `ndToLK` produce `LKc` —**con**
corte— y `cut_elimination` es lo unico que lleva de ahi a `LK₀`:

    Derives₀ [] ⊥  →  Derives₂ [] ⊥  →  LKc [] [⊥]  →  LK₀ [] [⊥]  →  False
                (derives0_iff_derives2)  (ndToLK)  (cut_elimination)  (lk0_tval)

### 5 · Decision

1. ✅ Modulo nuevo `FOL/Finitary0.lean` (no dentro de `Hauptsatz0.lean`: es otro teorema, y aquel ya
   tiene 1 023 l. y un solo trabajo). Entra en el barril `FOL.lean`.
2. ✅ `check-footprints.bash`: **96 → 100** titulares.
3. ⬜ **No se retira `derives0_consistent`**: se queda, y documenta la otra ruta y su precio.
   *Cuando un enunciado se re-demuestra mas barato, el caro no estorba: mide el precio de la via.*
4. ⬜ Queda abierto si `lk0_not_empty` (`FOL/SequentSound0.lean`, hoy con `Classical.choice`) debe
   re-enunciarse sobre `lk0_empty`. No se toca aqui para no mover un modulo ya medido.

**Controles:** RPP **145 jobs** · FOL **43 jobs** · `check-footprints` **100** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

### 6 · ⛔⛔ RECTIFICACION (mismo dia): el Hauptsatz NO hacia falta

⚠️ **§4 de esta misma ADR era FALSA como afirmacion de necesidad.** Decia que el Hauptsatz pagaba
«en un solo sitio», el paso de `LKc` a `LK₀`, porque `ndToLK` produce una derivacion **con** corte.
Lo destapo una **medicion externa** (barrido de metateoremas candidatos, 18 agentes) y lo confirmo
el compilador a la primera:

⭐ **El caso `cut` de la solidez booleana son CINCO LINEAS.** Si la formula cortada vale, la premisa
derecha da el resultado; si no, el testigo ya esta en Δ. Es, literalmente, lo que el propio repo
tenia escrito en `FOL/SequentSound0.lean:51-53`: *«el caso `cut` es semanticamente TRIVIAL … Tres
lineas»* — **escrito, y no leido como una oportunidad.** Luego la inducción se hace directamente
sobre `LKc` (15 casos) y se para ahi:

    Derives₀ [] ⊥  →  Derives₂ [] ⊥  →  LKc [] [⊥]  →  False
                (derives0_iff_derives2)  (ndToLK)   (lkc_tval)

⇒ `FOL/Finitary0.lean` **ha dejado de importar `FOL.Hauptsatz0`**, y ese es el control: si lo
necesitara, no compilaria. `lkc_tval`, `lkc_empty`, `lkc_no_bot` anadidos.

🔑 **La leccion, y es la segunda vez en dos dias**: *un dividendo atribuido a la pieza equivocada
sobrevive hasta que alguien mide.* ADR-052 §1 ya corrigio que el debilitamiento gratis no venia de
`struct` sino del ENUNCIADO; aqui, que la consistencia finitaria no venia del Hauptsatz sino de que
el corte es gratis para la verdad.
⇒ **la consistencia finitaria estaba disponible ANTES del Hauptsatz**, desde ADR-049 (`ndToLK`).
El Hauptsatz vale por **Herbrand (H3)**, que es lo que ADR-052 dice; no por esto.

### 7 · ⭐⭐ Y lo que este modulo SI mejora, que es mas de lo que se creia

`lk0_not_empty` (`FOL/SequentSound0.lean:300`) demuestra hoy `¬ LK₀ [] []` pasando por
`lk0_to_derives0`, **que es `completeness₀`** (`SequentSound0.lean:290`). Es decir: **la
consistencia del calculo de secuentes se compra hoy con el TEOREMA DE COMPLETITUD**, y arrastra con
el el `Classical.choice` que ADR-041 identifico como el **WKL**.

⇒ `lk0_empty` / `lkc_empty` lo sustituyen con `[propext, Quot.sound]`. Y son **estrictamente mas
fuertes**: `¬ LK₀ [] [⊥]` implica `¬ LK₀ [] []` por `struct`, no al reves.
⬜ Queda abierto re-enunciar `lk0_not_empty` sobre `lk0_empty`; no se toca aqui para no mover un
modulo ya medido, pero **es deuda escrita**.

**Vease tambien:** `FOL/Finitary0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.12, ADR-052,
ADR-042, ADR-034, ADR-049.

---

## ADR-054: COMPACIDAD y LOEWENHEIM-SKOLEM DESCENDENTE — el patron del SUJETO, cobrado dos veces

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: cerradas las dos vias del plan (ADR-041 y ADR-052), se ataca el catalogo clasico.
Los dos candidatos que un barrido de 18 agentes midio como SIN OBSTRUCCION.
`FOL/Compacity0.lean`, 60 l. de codigo.

    compactness₀           : IsSatisfiable S ↔ (todo subconjunto FINITO de S es satisfacible)
    loewenheim_skolem_down : IsSatisfiable S → IsSatisfiableCountable S

📏 `[propext, Classical.choice, Quot.sound]`. ⚠️ El `Classical.choice` es el de siempre y **esta
explicado**: viene de `completeness₀` via `model_existence_lemma₀`, y es el `if IsConsistent₀`
Π⁰₁ de `FOL.Lindenbaum0` — el **WKL** (ADR-041, plan §6.3). **No se anade fuerza nueva.**
⛔ Esto es via W, no via H: al reves que `FOL.Finitary0` (ADR-053), NO es finitario, y hay que
decirlo cada vez.

### 1 · ⭐ Lo que esto REPARA, y no es adorno

`cuarentena/Compacity.lean` esta apartado desde el 2026-09-11 y su `compactness_theorem` esta
declarado **VACUO** —con esa palabra— en `cuarentena/README.md:90` y en `FOL.lean:89`: *«su prueba
pasaba por `soundness`»*, y la solidez de `Derives` es FALSA (M-11).
⇒ `compactness₀` es **el mismo teorema con el SUJETO cambiado**: la prueba de la cuarentena
(13 lineas) se transplanta verbatim cambiando `soundness`→`derives0_soundness` y
`model_existence_lemma`→`model_existence_lemma₀`.

⭐ De los TRES modulos apartados, este es el **unico** cuyo defecto queda reparado fuera: el de
`Soundness.lean` es un enunciado **FALSO**, no una prueba mala. Anotado en `cuarentena/README.md`.
🔑 *Cuando un teorema cae, su prueba suele estar bien — lo que cambia es el SUJETO.* Van **tres**
(los 18 casos de solidez rescatados en ADR-034, `Derives₀` entero, y esto).

### 2 · ⭐⭐ La compacidad SINTACTICA ya estaba metida en la definicion

`DerivesSet₀ S f := ∃ Γ : List Formula, (∀ g ∈ Γ, S g) ∧ (Γ ⊢₀ f)` (`FOL/Henkin0.lean:82`): la
derivabilidad desde un CONJUNTO pide un contexto **finito por construccion**.
⇒ la mitad que en los libros es el trabajo —«toda derivacion usa finitas hipotesis»— **no hay que
demostrarla: esta en el tipo**. Lo unico que queda es cruzar solidez con existencia de modelo, y
son dos `obtain`.

⚠️ Esto ya estaba escrito en el repo y ya habia pagado cuatro veces; lo que faltaba era **usarlo
aqui**. Es la misma clase de hallazgo que ADR-053 §6: *estaba escrito y no se leyo como una
oportunidad.*

### 3 · ⭐ Loewenheim-Skolem descendente: la obstruccion era el ENUNCIADO

Sin Mathlib no hay `Cardinal` ni `Countable`, y el barrido midio **cero** predicados de
numerabilidad en el arbol. Aqui se dice con lo unico que hay:

    CountableDom D := ∃ e : Nat → D, ∀ d, ∃ n, e n = d

Y entonces la prueba es **componer dos cosas que ya existian**: el dominio del modelo canonico es
`QuotientDomain T hMax = Quotient (termSetoid T hMax)` (`FOL/Canonical0.lean:247`) y
`natToTerm_surj` enumera los terminos ⇒ `Quotient.mk ∘ natToTerm` enumera el dominio.
🔑 **El modelo que la completitud construye YA ERA numerable; lo que faltaba era poder decirlo.**

⚠️ Con un detalle que NO es gratis y que conviene registrar: `IsSatisfiable` esconde el dominio bajo
un `∃`, luego la numerabilidad **no se puede anadir a posteriori**. Hay que rehacer
`model_existence_lemma₀` llevandola dentro (`model_existence_countable₀`) y con ella
`satisfiable_of_shift` (`countable_of_shift`). Ocho lineas, pero el ENUNCIADO las obliga.
🔑 *Un `∃` que oculta un dato impide anadirle propiedades despues: o viaja dentro, o se rehace.*

### 4 · ⬜ Lo que NO se hace, y por que

Del barrido de candidatos quedan fuera tres, y por razones medidas, no por opinion:

| | por que |
|---|---|
| **D** propiedad de la subformula | ⛔ el enunciado LITERAL es **falso**: `LK₀.eqAx` (`Sequent0.lean:125`) mete `g` en la premisa sin que aparezca abajo. La version correcta lleva «o subformula de una `EqInstance`», y choca ademas con el muro de `Prop` (haria falta un `LK` indexado por el conjunto de formulas, como `LKh` lo esta por la altura) |
| **G** conservatividad de los 107 | ⛔ **falso**: el arbol tiene su propio contraejemplo COMPILADO — `ax_tc_cons` vivia en `codingAxioms` y daba `axioms ⊢ falso` (M-2). Un metateorema general que los descargase «de golpe» habria demostrado algo falso |
| **I** teorema de Church | ⛔ **no enunciable**: `Not (DecidablePred …)` ni siquiera tipa, y escrito bien es **refutable** por `Classical.propDecidable`. ⬜ Queda un sustituto honesto (~15 l.) via Godel II, sin decidir |

**Controles:** RPP **145 jobs** · FOL **44 jobs** · `check-footprints` **104** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

**Vease tambien:** `FOL/Compacity0.lean`, `FOL/cuarentena/README.md`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §6.5, ADR-041, ADR-034, ADR-053.

---

## ADR-055: Herbrand para un BLOQUE de existenciales — la mitad ⟸ pagada, la ⟹ enunciada; y lo MEDIDO sobre LS ascendente

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: el enunciado-titular de la via H (plan §5.1) lleva **barras de tupla**:
`⊢₀ ∃x̄ φ(x̄) ⟺ ∃ t̄₁…t̄ₙ : ⊢ᵖʳᵒᵖ φ(t̄₁) ∨ … ∨ φ(t̄ₙ)`. Lo que ADR-052 entrego es el caso **n = 1**.
`FOL/HerbrandBlock0.lean`, 120 l. de codigo.

    derives0_exBlock_of_cert : HerbrandCertBlock n φ tss E → [] ⊢₀ exBlock n φ   -- ⟸, PAGADA
    HerbrandExtractionBlock  : Prop                                              -- ⟹, ENUNCIADA
    herbrand_block_iff       : HerbrandExtractionBlock → (⊢₀ exBlock n φ ↔ ∃ tss E, cert)

📏 `[propext, Quot.sound]`. **Ni un `Classical.choice`** — como toda la via H.
⭐ Y la ⟸ es **incondicional y sin el Hauptsatz**: es `intro_ex` n veces bajo `elim_or`.

### 1 · ⭐ Por que se paga la mitad barata PRIMERO, y no es pereza

Es el metodo que el propio proyecto tiene fichado y que ADR-043 ya siguio con n = 1: *primero el
consumidor, despues el molde*. La guarda del certificado —`∀ ts ∈ tss, ts.length = n`— **sale del
consumidor**, no se inventa; escribir antes el `abbrev` habria producido una deuda demasiado
guardada, que es el fallo que `feedback-enunciar-una-deuda` documenta.

⬜ Y `HerbrandExtractionBlock` se **enuncia** como `Prop`, nunca se postula.

### 2 · ⭐ La pieza de riesgo, y una leccion de ENUNCIADO que vale para todo el repo

Todo el modulo cuelga de poder sustituir **a traves** del bloque:

    substFormula k t (exBlock n φ) = exBlock n (substFormula (n + k) (liftN n t) φ)

⚠️ Escrito `k + n`, el caso `k = 0` obliga a reescribir con `Nat.zero_add` **en cada uso**, porque
`0 + n` NO es `n` por definicion (`Nat.add` recurre en el segundo argumento). Escrito `n + k`,
`n + 0` **si** reduce y el consumidor no paga nada.

🔑 *El orden de una suma en un enunciado no es cosmetico: decide si el consumidor reescribe o no.*
Es el primo del §14 de las trampas de notacion («el INDICE de nivel no es cosmetico»).
⚠️ MEDIDO: fue el unico error de compilacion del modulo, y con el orden bueno desaparecio.

### 3 · ⬜ La mitad ⟹: por que NO sale por composicion, y cuanto cuesta

⛔ **No sale de `herbrand` (n = 1)**: el cuerpo de un bloque de altura ≥ 2 **no es** una formula sin
cuantificadores, luego la hipotesis `QuantFree` de `herbrand` no se cumple. No es que sea dificil:
no aplica.

⚠️ Lo que haria falta, MEDIDO leyendo `FOL.Sequent0.lk0_herbrand`: **rehacer su induccion de 14
casos con un invariante mas rico**. Hoy el invariante es «todo `d ∈ Δ` es sin cuantificadores **o**
es exactamente `Formula.ex φ`» (`Sequent0.lean:203`) y la salida lleva `ts : List Term`.
⭐ La buena noticia, y esta comprobada: el caso `exR` baja de `exBlock (m+1) ψ` a `exBlock m ψ'` con
`ψ'` sin cuantificadores (`quantFree_instB`), luego **el invariante SI se cierra**. La mala: hay que
llevar ademas la **tupla parcial** acumulada y la salida pasa a `List (List Term)`.
⇒ **~350-450 l., riesgo alto**. No es la envoltura que la estimacion inicial (~250 l.) sugeria.

### 4 · ⚠️ Y de paso, lo MEDIDO sobre Loewenheim-Skolem ASCENDENTE y Lindstroem

Un barrido de 8 agentes los midio, pero **sus ocho refutadores murieron por limite de gasto** ⇒ sus
informes NO son medicion. Lo que sigue lo he verificado yo, y solo esto:

| afirmacion | veredicto |
|---|---|
| los simbolos son `String` (`FOL/FOL.lean:10-24`) | ✅ **medido** |
| `natToTerm_surj` (`Enumeration.lean:268`) **refuta** que haya κ terminos distintos para κ no numerable | ✅ **medido** — no es una limitacion pendiente de comprobar: hay un TEOREMA compilado |
| toda la maquinaria de Henkin es una ω-cadena: `cst : Nat → String` (`Fresh0.lean:91`), `LindenbaumStep : Nat → …` (`Lindenbaum0.lean:130`), `hen`/`hidx` (`HenkinLimit0.lean:221`/`:193`) | ✅ **medido** |
| `Model D` **no tiene signatura**: `func : String → List D → D`, `rel : String → List D → Prop` (`Semantics.lean:23-25`) | ✅ **medido** |
| `pullback` renombra **solo** simbolos de funcion (`Canonical0.lean:472`) — un informe decia «todos» | ✅ **medido**, el informe era falso |
| en el nucleo NO hay `Zorn`, `zorn_le`, `Cardinal`, `Ultrafilter`, `Filter`, `WellOrderingTheorem`, `Set`, `Finset` | ✅ **medido POR EL COMPILADOR** (`#check` ⇒ unknown identifier) |
| SI hay `Classical.choice`, `Classical.em`, `Classical.propDecidable`, `WellFounded.fix`, `Quotient.exists_rep`, **`Function.Injective`** y **`Function.Surjective`** | ✅ **medido POR EL COMPILADOR** |

⇒ **Consecuencias, y la primera cambia el ORDEN del plan:**

1. ⛔⛔ **`List Char` NO sirve para LS ascendente**, ni `Nat`: los dos son numerables. Y el requisito
   que el plan escribe en §7.2 es literalmente «**infinito numerable**» (linea 1007) — que es
   **incompatible** con LS ascendente para κ arbitrario. ⇒ si LS ascendente entra en la hoja de
   ruta, la migracion tiene que ir a un **parametro** `S`, no a un tipo numerable concreto, o se
   hace **dos veces**. 🔑 *Una decision de firma tomada sin mirar al consumidor de mas adelante se
   paga dos veces* — es «primero el consumidor, despues el molde», a escala de repo.
   📐 Tamano de parametrizar: **163 modulos / 3 902 declaraciones** (FOL 42/545, RPP 121/3 357),
   MEDIDO. Comparable al enhebrado de `AnclaEq` (~440 firmas), pero un orden mayor.
2. ⭐ **El ENUNCIADO de LS ascendente si es expresable**: `Model D` toma un `Type` arbitrario y
   `Function.Injective` existe ⇒ «modelo de cardinalidad ≥ |I|» se dice sin Mathlib. Lo bloqueado
   es la **ruta de prueba**, no el enunciado. (Esto corrige la lectura pesimista habitual.)
3. ⛔ La ruta estandar (κ constantes nuevas + compacidad) exige **Lindenbaum transfinito** ⇒ Zorn,
   que **no esta** y habria que construirlo desde `Classical.choice`. La alternativa por
   ultraproductos exige el **lema del ultrafiltro**, que tambien es Zorn.
   ⚠️ Y hay que decir lo que eso le hace a la narrativa: hoy el proyecto publica que la no-finitud
   esta **localizada en una linea Π⁰₁ que es el WKL** (plan §6.3). Zorn es MUCHISIMO mas fuerte.
   No cambia el footprint de Lean —`Classical.choice` ya esta—, cambia la **lectura de reversa
   matematica**, y esa frase del plan habria que reescribirla. Es justo la distincion de
   «el FOOTPRINT no es CONSTRUCTIVIDAD».

⬜ **Nada de esto decide**. Queda escrito para que la decision se tome con cifras.

**Controles:** RPP **145 jobs** · FOL **45 jobs** · `check-footprints` **107** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

**Vease tambien:** `FOL/HerbrandBlock0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.13 y §7.5,
ADR-052, ADR-043, ADR-054.

---

## ADR-056: H sobre F — y el axioma de Skolem/Henkin es CONSERVATIVO

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: del catalogo de metateoremas quedaban dos, **F** (interpolacion de Craig por Maehara)
y **H** (Skolem), ~850-1400 l. cada una. Se elige **H**. `FOL/Skolem0.lean`, 110 l. de codigo.

    evalFormula_updateFunc : ¬ occursFormula c f → (eval (updateFunc M c F) v f ↔ eval M v f)
    henkin_conservative    : c fresco para Γ, A, φ → (henkinAx c A :: Γ) ⊢₀ φ → Γ ⊢₀ φ

📏 El lema de coincidencia y sus dos auxiliares, **sin ningun axioma**. `henkin_conservative`,
`[propext, Classical.choice, Quot.sound]` — el WKL de `completeness₀` mas la eleccion del testigo.

### 1 · Por que H y no F, con las razones MEDIDAS

| | F (interpolacion) | H (Skolem) |
|---|---|---|
| obstruccion | ⛔ **CONFIRMADA**: `eqAx` no se deja repartir por signatura ⇒ lo unico entregable seria interpolacion para un calculo **distinto** (`LK₀` sin `eqAx`), que **no es el que el proyecto usa** | ⛔ falta el puente `occursFormula`↔`evalFormula` — **cierto, y son 70 lineas net-0** |
| reutilizacion | ⛔ la unica «gratis» era FALSA: `occursFormula` **descarta el nombre del predicado** (`Eigenvariable.lean:368`, `\| .atom _ ts =>`) ⇒ `SubLang` hay que construirlo entero | ⭐ ese mismo hecho la FAVORECE: Skolem anade un simbolo de **funcion**, y para funciones `occursFormula` es exactamente la nocion correcta |
| pieza cara | `SubLang` + Maehara desde cero | ⭐ la capa prenexa es un **PORT**: `Derives₀` tiene *verbatim* los constructores que usan las pruebas de `Theorems/Quantifiers.lean` |
| menciones en el proyecto | **cero** (grep Craig/Maehara/Beth: 1 hit, y es ruido) | cero tambien |

🔑 *Entre dos frentes que no descargan nada, gana el que se apoya en lo que el arbol ya tiene.*
⚠️ Y F queda **abierta**, no descartada: su Nivel 1 (fragmento puro, `LKp`) sigue siendo hacible.

### 2 · ⭐⭐ El bloqueo medido eran 70 lineas, y son net-0

La medicion externa acerto: **no habia ningun lema que conectara `occursFormula` (sintactico,
`Eigenvariable.lean:366`) con `evalFormula` (semantico, `Semantics.lean:54`)**. Sin el, «`c` no
aparece en `f`» no permite concluir que reinterpretar `c` no cambia el valor de `f` — la frescura
no decia NADA semanticamente.

⭐ `evalFormula_updateFunc` **no depende de ningun axioma**, y es reutilizable por cualquier
argumento de frescura, no solo por Skolem. ⚠️ Y el `if f = c` usa `String.decEq`, que **no** trae
`Classical.choice`: lo que lo trae es DESCOMPONER un `String`, no compararlo (plan §7).

### 3 · ⭐ El axioma de Skolem YA ESTABA ESCRITO

`henkinAx c A = (∃A) ⇒ A[c]` (`FOL/Henkin0.lean:90`) **es** el axioma de Skolem para un existencial
cuyo cuerpo no tiene mas variables libres. No hubo que definir nada. *Antes de construir, buscar* —
y van siete.

⚠️ Lo que el proyecto tenia sobre el era `henkin_step_consistent` (ADR-037): que el paso **preserva
la CONSISTENCIA**. La conservatividad es **estrictamente mas fuerte**: preservar consistencia no
impide inventar teoremas nuevos en el lenguaje viejo; la conservatividad si.

### 4 · ⭐ Donde paga la frescura, que son tres sitios y cada uno hace algo distinto

    (henkinAx c A :: Γ) ⊢₀ φ
      --[ derives0_soundness ]->  vale en todo modelo del contexto ampliado
      --[ se EXPANDE M en `c` con un testigo ]->  ese modelo existe
      --[ coincidencia, DOS veces ]->  Γ ⊨ φ
      --[ completeness₀ ]->  Γ ⊢₀ φ

* en **Γ**: para transportar el contexto al modelo expandido;
* en **A**: para elegir el testigo (y, en la rama sin testigo, para que el axioma valga **vacuamente**);
* en **φ**: para traer la conclusion de vuelta.

🔑 *Una hipotesis de frescura que se usa tres veces no es una: hay que comprobar los tres usos por
separado.*

### 5 · ⬜ Lo que H **NO** incluye, dicho sin adornos

* ⬜ La **capa prenexa** sobre `Derives₀` (el port de `Theorems/Quantifiers.lean:80-171`, hoy sobre
  `Derives` y por tanto prohibido por M-11). ~250-350 l., riesgo bajo por ser port.
* ⬜ La **skolemizacion de una formula arbitraria** (simbolos de funcion de aridad > 0): la
  maquinaria de frescura del arbol (`Fresh0.lean`) es de **constantes**, y el lema de coincidencia
  de aqui ya cubre aridad arbitraria, pero falta el suministro de simbolos frescos n-arios.
* ⇒ lo entregado es el **nucleo**: la conservatividad del axioma, con el puente que faltaba.

**Controles:** RPP **145 jobs** · FOL **46 jobs** · `check-footprints` **109** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

**Vease tambien:** `FOL/Skolem0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.6,
ADR-037, ADR-054, ADR-055.

---

## ADR-057: La CAPA PRENEXA sobre `Derives₀` — las ocho equivalencias, y la clásica no la pone Lean

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: primera mitad de lo que le faltaba a **H** (ADR-056 §5). `FOL/Prenex0.lean`, 260 l.
de codigo: las **ocho** formas de sacar un cuantificador de debajo de una conectiva.

| | equivalencia | ¿clasica? |
|---|---|---|
| 1 | `(∀A) ∧ B ↔ ∀(A ∧ B↑)` | no |
| 2 | `(∃A) ∧ B ↔ ∃(A ∧ B↑)` | no |
| 3 | `(∀A) ∨ B ↔ ∀(A ∨ B↑)` | ⚠️ la vuelta |
| 4 | `(∃A) ∨ B ↔ ∃(A ∨ B↑)` | no |
| 5 | `(∀A) → B ↔ ∃(A → B↑)` | ⚠️ la ida |
| 6 | `(∃A) → B ↔ ∀(A → B↑)` | no |
| 7 | `B → (∀A) ↔ ∀(B↑ → A)` | no |
| 8 | `B → (∃A) ↔ ∃(B↑ → A)` | ⚠️ la ida |

📏 Las ocho, `[propext, Quot.sound]`. **Ni un `Classical.choice`.**

### 1 · ⭐ La condicion lateral no se comprueba: se CONSTRUYE

La formulacion de libro lleva una condicion lateral —*x no libre en B*— que hay que comprobar en
cada aplicacion. En De Bruijn no hay nombres, y aqui `B↑` es `liftFormula 0 B`: **una formula
levantada no puede mencionar la variable recien ligada**.
🔑 *Una condicion lateral codificada en el TIPO no hay que comprobarla* — desaparece del enunciado
y de todas sus aplicaciones futuras.

### 2 · ⭐⭐ Y la logica clasica NO entra por Lean

Tres de las ocho tienen una direccion que no es intuicionista (la «paradoja del bebedor» y sus
primas). Salen de `derives0_em_ctx` (`FOL.Propositional0`, **footprint `-`, sin ningun axioma**) y
del **constructor** `Derives₀.forall_not_ex_not`.

🔑 **La fuerza clasica de este calculo esta en sus CONSTRUCTORES, no en el metanivel.** Por eso se
puede usar sin encarecer el footprint, y por eso las ocho salen `[propext, Quot.sound]` igual que
las cinco intuicionistas. ⚠️ Es exactamente la distincion que el proyecto lleva midiendo desde
ADR-041: *el footprint habla del nucleo de Lean, no de la matematica*.

### 3 · ⭐ El truco que hace las ocho pruebas, y es uno solo

`intro_forall` **levanta el contexto** (es la regla de la eigenvariable), asi que bajo el binder la
hipotesis `∀A` llega como `∀(A↑¹)`. Se instancia en `Term.var 0` y vuelve intacta:

    inst_var0 : substFormula 0 (Term.var 0) (liftFormula 1 A) = A      -- = substFormula_lift_var

Aparece en siete de las ocho. La octava usa `substFormula_liftFormula`, para devolver el `B` de
fuera. ⇒ **el coste real por equivalencia es ~24 lineas**, medido con las dos primeras antes de
escribir las seis restantes.

⚠️ Y los unicos cuatro errores de compilacion de todo el modulo fueron **contextos mal escritos a
mano** (poner `A ::` donde iba el cuerpo del `∃`, o mapear `lift` sobre una lista ya levantada) y
dos `have` sin anotar que no infieren el contexto. Ninguno fue matematico.
🔑 *Cuando la regla levanta el contexto, el error no esta en la logica: esta en la contabilidad.*

### 4 · ⬜ Lo que falta para la forma NORMAL

Estas ocho son el **motor**, no la forma normal. Falta `prenex : Formula → Formula` con su
terminacion y su correccion (`Γ ⊢₀ φ ↔ Γ ⊢₀ prenex φ`).
⬜ ~200 l., riesgo **medio**: lo caro no son las equivalencias —estan aqui— sino la **medida de
terminacion** del algoritmo de prenexacion.

⚠️ Y hay que decirlo porque cambia la cifra de ADR-056 §5: alli se estimo la capa prenexa en
«~250-350 l., riesgo bajo **por ser un port**». **El port era falso**: `Theorems/Quantifiers.lean`
tiene SEIS teoremas sobre `⊢` y **ninguno es una regla de desplazamiento** (son `forall_dni`, las
dos dualidades ∃/¬ y la distribucion ∀/∧). Las ocho se han escrito **desde cero**.
🔑 *«Es un port» es una estimacion, y hay que medirla como cualquier otra.*

**Controles:** RPP **145 jobs** · FOL **47 jobs** · `check-footprints` **113** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry** · ✅ CI.

**Vease tambien:** `FOL/Prenex0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.7, ADR-056.

---

## ADR-058: La FORMA NORMAL prenexa — y la «medida de terminación» que no hacia falta

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: segunda mitad de la capa prenexa (ADR-057 §4). `FOL/PrenexNF0.lean`, 240 l.

    prenex              : Formula → Formula
    derives0_prenex_iff : (Γ ⊢₀ φ) ↔ (Γ ⊢₀ prenex φ)

📏 `[propext, Quot.sound]`. **Ni un `Classical.choice`** (`iffAll_trans`, sin ningun axioma).

### 1 · ⭐⭐ La TERMINACION no hacia falta, y era lo que se daba por caro

ADR-057 §4 estimo esta pieza en «~200 l., riesgo **medio**: lo caro es la **medida de
terminacion**». **Refutado por el compilador**: las seis definiciones las acepta Lean por
**recursion estructural**, sin `termination_by` ni `decreasing_by`.

🔑 La razon es una y vale para toda la familia: **se recurre sobre UN argumento y se LEVANTA el
otro**.

    mergeAnd (∀A') B = ∀ (mergeAnd A' (liftFormula 0 B))

decrece en el primero, y que el segundo cambie da igual: **no es el argumento de la recursion**.
*Cuando la recursion y la transformacion van por argumentos distintos, no hay nada que medir.*

⚠️ Y es la **tercera estimacion mia refutada en dos dias**: ADR-052 §1 (el dividendo de `struct`),
ADR-057 §4 (el «port» de la capa prenexa) y esta. Las tres en la misma direccion — **estimar el
coste por la forma del enunciado y no por la del ARBOL**.

### 2 · ⭐ Dos fases por conectiva, y por eso son estructurales

Sacar los cuantificadores de `A ∧ B` son dos pasadas: primero los de `A` (recurriendo en `A`), y
cuando `A` ya no tiene prefijo, los de `B` (recurriendo en `B`). De ahi el par
`mergeAnd`/`mergeAndR`, y sus gemelos para `∨` y `→`.
⚠️ **A la izquierda de `→` el cuantificador SE DA LA VUELTA**: `mergeImpl (∀A') B = ∃(…)`. Es la
unica asimetria de las seis, y viene de la equivalencia 5 de ADR-057.

### 3 · ⭐ Las congruencias no se escribieron: se ENVOLVIERON

`FOL.Derives1` ya tenia las ocho congruencias — y con la hipotesis **esquematica en el contexto**
(`∀ Δ, Δ ⊢₁ …`), que es justo lo que hace falta para meterlas bajo un binder, donde el contexto
llega levantado. ⇒ **dos lineas de envoltorio cada una** via `derives0_iff_derives1`, en vez de
noventa de reescritura.
🔑 *Antes de construir, buscar* — van **ocho**. Y esta vez lo que se encontro no fue solo el lema:
fue que **estaba enunciado en la forma que hacia falta**, que es lo que de verdad ahorro el trabajo.

⚠️ Las cuatro versiones «por la derecha» (`and_forall_r`, …) tampoco se escribieron: salen de las
de ADR-057 mas conmutatividad, en seis lineas cada una.

### 4 · 🏁 El puente a la skolemizacion — HECHO el mismo dia

`prenex_isPrenex : ∀ f, Prenex (prenex f)`, footprint `[propext]`; `quantFree_lift`, **sin ningun
axioma**. El teorema de correccion no lo necesita, pero **la skolemizacion si**: sin el no se sabe
donde poner los simbolos de Skolem.

⚠️ **Estimado ~70 l.; medido 95.** Se deja la cifra vieja a la vista: es la primera estimacion mia
del dia que se queda CORTA en vez de larga, y las dos cifras juntas valen mas que la buena sola.
🔑 La causa es identificable: conte «dos inducciones sobre las fusiones» y son **seis** —
`mergeX`/`mergeXR` por tres conectivas—. *Contar las piezas por la definicion, no por la idea.*

⭐ Y sale por el mismo patron que todo lo demas: `Prenex X` y `QuantFree X` son **definicionalmente
iguales** cuando `X` no es un cuantificador, asi que los seis casos base de cada induccion son
`⟨hA, hB⟩` sin mas.

**Controles:** RPP **145 jobs** · FOL **48 jobs** · `check-footprints` **116** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

**Vease tambien:** `FOL/PrenexNF0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.8, ADR-057.

---

## ADR-059: SKOLEMIZACION — el axioma con termino de argumentos fijos, y el bloqueo n-ario que NO existia

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: ADR-056 entrego la conservatividad del axioma de Skolem con una CONSTANTE. Aqui se
generaliza a un **termino de Skolem** con argumentos cualesquiera. `FOL/Skolem0.lean`, +45 l.

    skolemAxT c t̄ A    := (∃A) ⇒ A[c(t̄)]
    skolem_conservative : c fresco para Γ, A, φ → (skolemAxT c t̄ A :: Γ) ⊢₀ φ → Γ ⊢₀ φ
    henkin_conservative : el caso t̄ = [], ahora un COROLARIO de una linea

### 1 · ⛔ Un bloqueo que YO declare y que NO existe

ADR-056 §5 dijo que faltaba «suministro de simbolos frescos **n-arios**». **Falso, y medido**:

* `Term.func : String → List Term → Term` (`FOL/FOL.lean:12`) toma una lista de **cualquier**
  longitud ⇒ **la aridad no esta en el tipo**.
* `occursFormula c f` (`FOL/Eigenvariable.lean:366`) mira el **NOMBRE**, no la aridad.

⇒ `cst : Nat → String` (`FOL/Fresh0.lean:91`) ya da infinitos simbolos de Skolem de cualquier
aridad, y `exists_fresh` (`:281`) ya entrega frescura frente a **teoria + lista + formula**, que es
exactamente la forma que una conservatividad necesita. **No habia nada que construir.**

⚠️ Van **CUATRO** obstrucciones mias declaradas y luego refutadas en dos dias (ADR-052 §1,
ADR-057 §4, ADR-058 §1 y esta). 🔑 *Declarar un bloqueo es una MEDICION, y hay que hacerla con el
arbol delante — no con la intuicion de como suele ser el problema.*

### 2 · ⭐ Y `t̄` no necesita ser fresco — lo que abarata el paso

Con argumentos **fijos**, la interpretacion del simbolo nuevo puede ser **constante**
(`updateFunc M c (fun _ => w)`). Entonces `c(t̄)` vale lo mismo **sean cuales sean los argumentos**,
incluso si mencionan `c`. ⇒ **no hace falta ninguna correspondencia entre la lista de argumentos y
el entorno De Bruijn**, que es justo lo caro del caso general.

🔑 *Cuando la interpretacion que se construye es constante, los argumentos dejan de ser un
problema.* ⇒ el paso costo **45 l.** y ADR-056 se queda como corolario de una linea.

### 3 · ⬜ Lo que falta, MEDIDO pieza a pieza

El axioma bajo un **prefijo de universales**:

    ∀y₁…∀y_k ( (∃x A) → A[x := c(y₁,…,y_k)] )

Ahi el testigo **depende de la tupla**, luego `F : List D → D` ya no puede ser constante.

| pieza | estado |
|---|---|
| prefijo `∀ⁿ` (`forallN`, `vars`, `skolemAx`) | ⬜ ~40 l. — **copia** de `exBlock`/`subst_exBlock` (`FOL/HerbrandBlock0.lean`, ADR-055) |
| frescura | ✅ **lista**: `exists_fresh`, `cst_bound_list` |
| coincidencia semantica para aridad arbitraria | ✅ **ya pagada**: `evalFormula_updateFunc` vale para `F : List D → D` sin restriccion |
| **entorno ↔ lista de valores** | ⛔ **MEDIDO que no existe nada**: `FOL/Semantics.lean` tiene `shiftEnv`/`updateEnv` y sus conmutaciones, pero **nada iterado `k` veces** ni que reconstruya un entorno desde una lista |

⇒ **~200 l., riesgo medio, y el riesgo esta ENTERO en la ultima fila.** ⚠️ ESTIMADO.

**Controles:** RPP **145 jobs** · FOL **48 jobs** · `check-footprints` **119** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry** · **0 warnings**.

**Vease tambien:** `FOL/Skolem0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.9, ADR-056, ADR-055.

---

## ADR-060: SKOLEM bajo un PREFIJO de universales — el entorno no se RECONSTRUYE, se CONSTRUYE

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: ADR-059 §3 dejo una tabla de cuatro filas con **el riesgo entero en la ultima**:
«entorno ↔ lista de valores, MEDIDO que no existe nada». Esta ADR paga esa fila.
`FOL/SkolemN0.lean`, modulo nuevo, **113 l. de codigo** (240 con documentacion).

    skolemAxN c n A        := ∀x₀…∀x_{n-1} ( (∃y. A) → A[y := c(x₀,…,x_{n-1})] )
    skolem_conservative_n  : c fresco para Γ, A, φ → (skolemAxN c n A :: Γ) ⊢₀ φ → Γ ⊢₀ φ
    skolemAxN c 0 A = skolemAxT c [] A                                         -- por `rfl`

### 1 · ⭐⭐ La decision de diseno, y es lo unico que hace falta entender

Bajo el prefijo el testigo **depende de la tupla ligada**, asi que `F : List D → D` ya no puede ser
constante (que es lo que abarataba ADR-059). Hace falta un entorno acumulado. La eleccion:

    envPush v []              = v                          -- ⭐ las dos, por `rfl`
    shiftEnv (envPush v ds) d = envPush v (d :: ds)

`envPush` se define **POR `shiftEnv`** y recurriendo **solo sobre la lista**. ⇒ el paso inductivo de
`eval_allBlock_envPush`, que es el que atraviesa el binder, **no lleva ni un `rw`**: el `show` cae
por definicion y la llamada recursiva es directa.

🔑 *Cuando una induccion tiene que atravesar un binder, lo que la abarata es definir el dato
acumulado CON el constructor que el binder va a producir.* El entorno no se **reconstruye** desde la
lista: se **construye** con la misma operacion que la semantica del `∀` ya usa.

### 2 · ⭐ Y la fila «no existe nada» era CIERTA — lo que fallo fue la conclusion

La medicion de ADR-059 era correcta: en `FOL/Semantics.lean` no habia nada iterado `k` veces ni nada
que reconstruyera un entorno desde una lista. Pero de ahi NO se sigue que hubiera que construirlo
todo. `vars` se escribe

    vars 0       = []
    vars (n + 1) = Term.var 0 :: liftTerms 0 (vars n)        -- y NO `(vars n).map (liftTerm 0)`

y con esa forma la conmutacion semantica que hace falta **ya existe**: `eval_liftTerms_ext`
(`FOL/Semantics.lean:94`). ⇒ `evalTerms_vars` va de **lista a lista**, sin un solo `funext`, y el
unico puente que se paga —`updateEnv 0 v d = shiftEnv v d`— se paga **una vez**, en un lema de tres
lineas.

🔑 *Cuando para el dato que necesitas no existe nada, elige la DEFINICION del dato de modo que se le
aplique lo que si existe.* La estimacion de ~200 l. se quedo en **113**: casi la mitad del ahorro
viene de esa unica eleccion de `vars`.

### 3 · ⚠️ Tres detalles que NO son cosmeticos

* **El orden del contador**: la guarda va `n + ds.length = k`, no `ds.length + n = k`. `Nat.add`
  recurre sobre el **segundo** argumento ⇒ con `ds = []` la primera forma reduce sola y la segunda
  no. Es la misma trampa que ADR-055 §`subst_exBlock` (`n + k`, no `k + n`). Van **dos**.
* **La guarda `ds.length = n` es NECESARIA**, no decorativa: sin ella el enunciado del bloque es
  falso ya para `n = 1`, porque `c(x₀,…,x_{n-1})` tiene `n` argumentos y el entorno acumulado
  tendria otra longitud.
* **`Classical.propDecidable` va EXPLICITO** en `skF`: el modulo no abre `Classical` (a proposito),
  y con la instancia implicita el binder de `dite` **no llega a tipar**. La alternativa —quedarse
  en `by_cases` + `Exists.choose`, como `skolem_conservative`— no sirve aqui: el testigo depende de
  `ds`, luego hace falta una **funcion**, no una eleccion puntual.

### 4 · ⚠️ La trampa que costo la unica correccion de compilacion

En `evalTerms_vars`, terminar con `rw [...]` **no cierra**: el `rfl` final que `rw` intenta es
`with_reducible rfl`, y ni `evalTerm` ni `shiftEnv` estan marcados `@[reducible]`. El objetivo que
queda es literalmente `evalTerm M (shiftEnv w d) #0 :: ds = d :: ds`, cierto por definicion pero no
por reducibilidad. Hay que escribir el `rfl` **a mano** en la linea siguiente.

⭐ Este fallo estaba **predicho**: el refutador del diseno lo senalo como «el unico defecto real de
compilacion», y fue exactamente uno de los dos errores del primer `lake env lean`. 🔑 *Un refutador
que compila mentalmente el termino vale mas que uno que juzga el enunciado.*

### 5 · ⬜ Lo que esto NO es, dicho antes de que nadie lo suponga

Esto es **el paso de Skolem**, no la **forma normal de Skolem**. Da la conservatividad de **un**
axioma `∀ⁿ(∃ → ·)`. Iterar sobre una formula prenexa entera —eliminar todos los `∃` de
`prenex f` (ADR-058) reutilizando este paso— **no esta hecho**, y es la pieza que cerraria
«skolemizacion de formulas arbitrarias». ⬜ **No medida.**

Tampoco cambia nada del frente godeliano: `skolem_conservative_n` pasa por `completeness₀`, luego
arrastra el `Classical.choice` que es el **WKL** (ADR-041 §2), como `skolem_conservative`.

### 6 · ⛔ Y una cifra MIA que era FALSA, corregida aqui

ADR-057, ADR-058 y ADR-059 cerraron con **«0 warnings»**. **Falso.** Medido hoy: **7 warnings en
RPP** (`Meta/CodeWitnessPrf.lean` x4, `Meta/SubstfcWitnessPrf.lean`, `Meta/ChainNegPrf.lean` x2 —
del 2026-09-09) y **4 en FOL** (`TheoryFramework/Relations.lean`). Lo que era cierto es que la
`lean_lib FOL` sola sale a cero; la cifra se **generalizo** al arbol entero sin volver a medirla.

🔑 *Una cifra de control se copia de una pasada a la siguiente sin volver a ejecutarla, y ahi
deja de ser una medicion.* Los once son cosmeticos (`simp` sin usar, binder sin referenciar), pero
la deuda que importa es la otra: **`0 warnings` no lo vigila ningun control** — no hay un
`check-warnings.bash`. ⬜ Deuda escrita; mientras no exista, la cifra va **con su alcance al lado**.

**Controles:** RPP **145 jobs** · FOL **49 jobs** · `check-footprints` **124** ·
`check-estratos` **10** · `check-doc-sync` ✅ · `check-axioms` ✅ · `check-sorry` ✅ · **0 sorry** ·
warnings: **7 (RPP) + 4 (FOL)**, todos cosmeticos y todos anteriores a esta ADR.

**Vease tambien:** `FOL/SkolemN0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.10, ADR-059,
ADR-056, ADR-055.

---

## ADR-061: FOL adopta `check-doc-sync` -- y en su PRIMERA ejecucion encuentra NUEVE cosas

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: la decision (2) del informe de PeanoRF («no tienes check-doc-sync.bash»), mas la
deuda escrita en ADR-053 sobre `lk0_not_empty`. Se cierran las dos, y la segunda la destapo la
primera. `../FOL/check-doc-sync.bash` (nuevo, 431 l. portadas), `../FOL/FOL/Finitary0.lean` (+24),
`../FOL/FOL/SequentSound0.lean` (doc), `../FOL/REFERENCE.md` §6.15.

### 1 · ⛔ La premisa del informe de PeanoRF es FALSA, y el fallo real es el contrario

El informe decia: *«adoptarlo exige que `CURRENT-STATUS-PROJECT.md` lleve la linea de cifras
canonicas, porque el control compara contra ella y falla si no existe»*.

**Medido, leyendo el script**: `check-doc-sync.bash` **no lee** ninguna cifra de los documentos.
Las **calcula del arbol** (`ls`, `grep -c`, `check-sorry.bash`) y despues las **contrasta** contra
las cabeceras. Si la frase no aparece en ningun doc, `check_num` hace `return 0` y el script
**sale con 0** imprimiendo «⚠️ control VACIO».

⇒ No falla: **da VERDE sin haber comprobado nada**, que es estrictamente peor. La linea de cifras
hay que ponerla igual, pero por la razon opuesta a la que el informe daba.
🔑 *Un control sin nada que contrastar no aprueba: se ABSTIENE, y la abstencion se lee como
aprobado.* Es la misma forma que el arreglo `255e007` del propio informe (`SIN MEDIR` tenia que
ser rojo), una capa mas abajo.

### 2 · ⭐⭐ Lo que encontro en la PRIMERA ejecucion, y por eso se adopta

Antes de adoptarlo se hizo un **simulacro**: portar el script al scratchpad, adaptarle las rutas y
ejecutarlo. Salio en rojo, y ninguno de los hallazgos era ruido:

| hallazgo | desde | lo veia alguien |
|---|---|---|
| `README.md` — «⚠️ 1 sorry (eq/Henkin)» en el arbol de directorios | mayo 2026 | no |
| `CURRENT-STATUS-PROJECT.md` — idem | mayo 2026 | no |
| `CURRENT-STATUS-PROJECT.md` — «\| 6 \| FOL con Igualdad \| ✅ Complete (1 sorry pendiente) \|» | mayo 2026 | no |
| los **SEIS** modulos de `TheoryFramework/` sin proyectar en `REFERENCE.md` | siempre | no |
| 3 controles [A] en «VACIO» por no haber contra que contrastar | — | no |

⇒ **el arbol lleva a CERO `sorry` desde el 2026-09-13** y tres documentos autoritativos seguian
publicando «1 sorry» cuatro meses despues.

⛔⛔ **Y la novena causa, otra vez**: de los seis modulos de `TheoryFramework`, **CUATRO quedaban
ABSUELTOS POR SUBCADENA** con el matcher que traia RPP (casaba por `basename`, y `Logic`, `Theory`,
`Properties` y `FOL` aparecen sueltos por todo `REFERENCE.md`). Solo saltaban dos.
🔑 *Casar por subcadena no comprueba: absuelve.* Van **dos veces la misma causa en un dia** — el
2026-09-17 por la manana ya se habia endurecido ese mismo matcher para `FOL/Theorems/Eq.lean`.
⇒ en la copia de FOL, `TheoryFramework` va con la **misma vara** que `FOL/`: contra §6 y por
**RUTA con frontera de palabra**.

### 3 · Las cuatro adaptaciones, y la que importa es la primera

* ⛔ **No ejecuta `lake build`**, y no es un olvido: es **M-3**. FOL no se construye desde FOL. La
  cifra de jobs la mide y la publica RPP (`lake build FOL TheoryFramework` = **49**). En esta copia
  **no hay control [A] de jobs**, y se dice en la cabecera.
* **[B] necesita el hermano.** Los docs de FOL citan con razon simbolos de RPP (sus tres `axiom` de
  Lean). Sin `../ROBINSON_PlusPlus` en el alcance, el control los da por MUERTOS.
  🔑 *Un control con el alcance equivocado no comprueba: INVENTA.* En la CI se clona en `_rpp` y se
  pasa por `RPP_DIR`, porque `actions/checkout` **no admite un `path:` fuera del workspace**. Si
  falta, el control lo **anuncia** como «alcance REDUCIDO» en vez de callarse.
* **[A]: una cifra entre «comillas latinas» es una CITA.** Los avisos de estado de FOL usan el
  formato «lo que decia \| lo medido», y sin esa exclusion los CUATRO daban falso positivo citando
  **textualmente el error que la propia fila esta corrigiendo**.
* **[C]** contra §6 (Exports), no contra la tabla de modulos.

✅ Probado **con el fallo puesto** (48 → 47 modulos, y un modulo de `TheoryFramework` renombrado en
el catalogo): rojo con exit 1, verde al restaurar.

### 4 · 🏁 Y la deuda de `lk0_not_empty`, saldada -- pero NO como estaba escrita

La deuda decia «re-enunciar `lk0_not_empty` sobre `lk0_empty`/`lkc_empty`». Medido:

* `FOL.SequentSound0.lk0_not_empty` mide `[propext, Classical.choice, Quot.sound]` porque pasa por
  `lk0_to_derives0`, que **es** `completeness₀`.
* Pero `lkc_sound` **ya mide lo mismo por su cuenta** (`evalFormula` va a `Prop`) ⇒ reprobarlo alli
  desde `lk0_sound` **no gana nada**.
* No hay ciclo de imports entre `SequentSound0` y `Finitary0` (son hermanos), asi que el alias
  seria posible. ⛔ **Y se rechaza**: meteria `FOL.NDtoLK0` —la traduccion ND→LK— en un modulo
  sobre solidez semantica, y sobre todo seria **blanquear el footprint**. El contenido de
  `SequentSound0` es caro, y su corolario debe decirlo.
  🔑 *El footprint de un corolario debe decir la verdad sobre el modulo en el que vive; lo que se
  arregla es a DONDE SE MANDA AL LECTOR.*

Lo entregado, en `FOL/Finitary0.lean`:

    lk0_empty_of_no_bot : ¬ LK₀ [] [⊥] → ¬ LK₀ [] []        -- net-0 PURO, por `struct`
    lkc_empty_of_no_bot : idem para LKc                      -- net-0 PURO
    lk0_not_empty_fin   : ¬ LK₀ [] []      [propext, Quot.sound]
    lkc_not_empty_fin   : idem

⭐ Y el dividendo no estaba previsto: la **relacion de fuerza** —«`¬ LK₀ [] [⊥]` implica
`¬ LK₀ [] []` por `struct`, y no al reves»— llevaba desde ADR-053 **en el docstring del modulo,
sin demostrar**. Ahora es un teorema, y `lk0_not_empty_fin` se deriva **del fuerte**.
⚠️ *Un docstring que afirma una relacion de fuerza y no la demuestra afirma mas que el modulo.*

### 5 · ⬜ Lo que esto deja abierto

* ⬜ **No hay `check-warnings.bash`** en ningun repo (ADR-060 §6). Warnings medidos hoy:
  **7 en RPP** + **4 en FOL**.
* ⬜ El `CHANGELOG.md` de FOL sigue fechado en **2026-05-16**: el control [E] compara los titulares
  CONTRA el, asi que hoy no puede detectar nada. Control **vivo pero desarmado**.
* ⬜ Los otros tres repos del informe (Peano, AczelSetTheory, ZfcSetTheory) siguen sin esto.

**Controles:** RPP **145 jobs** · FOL **49 jobs** · `check-footprints` **126** ·
`check-estratos` **10** · `check-doc-sync` ✅ **en los DOS repos** · `check-axioms` ✅ ·
`check-sorry` ✅ · **0 sorry** · warnings **7 (RPP) + 4 (FOL)**.

**Vease tambien:** `../FOL/check-doc-sync.bash`, `../FOL/REFERENCE.md` §6.15,
`../FOL/FOL/Finitary0.lean`, ADR-060, ADR-053, ADR-046.

---

## ADR-062: 🏁 LA FORMA NORMAL DE SKOLEM -- y la recursion se pasa, no se mide

**Fecha**: 2026-09-17
**Estado**: ✅ ACEPTADA
**Contexto**: cerrar «skolemizacion de formulas arbitrarias», lo unico que ADR-060 §5 dejaba
abierto de ese frente. `../FOL/FOL/SkolemNF0.lean`, modulo nuevo, **350 l. de codigo** (536 con
documentacion).

    skolemize k f     : Formula          -- ∀ᵐ ψ, con ψ SIN cuantificadores
    skolemAxioms k f  : List Formula     -- los axiomas de Skolem que consume

    skolemize_shape        : Prenex f → ∃ m ψ, skolemize k f = allBlock m ψ ∧ QuantFree ψ
    skolemizeF_impAll      : la forma normal IMPLICA el original  -- ⭐ NET-0, sin axiomas
    skolem_conservative_nf : el BLOQUE ENTERO de axiomas de Skolem no inventa teoremas
    derives0_of_skolemNF   : 🏁 lo que se demuestra desde la forma normal se demuestra sin ella

### 1 · ⭐⭐ El unico riesgo que habia, y se mata con una decision de definicion

Tres disenos independientes (uno recursivo, uno de paso unico, uno semantico), cada uno con dos
refutadores adversariales, dieron el MISMO veredicto: **ningun enunciado es falso** —los seis
buscaron activamente un contraejemplo, desarrollaron a mano `n = 0, 1, 2` y prefijos mixtos
`∀∃∀∃`, y no hay captura de variables— y **todo el riesgo esta en un solo sitio**:

> `skolemize` recurre sobre `substFormula 0 t A`, que **no es subtermino** de `.ex A` ⇒ Lean la
> compila por recursion **bien fundada**, y una definicion WF **no reduce definicionalmente**:
> solo se abre por sus lemas de ecuacion.

⇒ la decision: **el prefijo se recorre con un COMBUSTIBLE**, y entonces la recursion es
**estructural sobre el primer `Nat`**. El combustible no es una cota arbitraria: es
**exactamente** la longitud del prefijo (`qdepth`), y sustituir no la cambia (`qdepth_subst`).

🔑 *Cuando una recursion no es estructural, antes de pagar la recursion bien fundada hay que
mirar si el argumento que decrece se puede PASAR, en vez de MEDIR.*

**Dividendo, y es el que hace la diferencia**: las tres ecuaciones de `skolemizeF` son **`rfl`**,
asi que la normalizacion de una formula concreta se comprueba **por COMPUTO**, no por prueba:

    skolemize 0 (∀∃∀∃ Q(x,y,z,w)) = ∀∀ Q(x₁, c₀(x₁), x₀, c₁(x₀,x₁))          -- `by rfl`
    skolemize 0 (∃y ∀x P(x,y))    = ∀x P(x, c₀)                               -- `by rfl`

⭐ El segundo ejemplo no es decorativo: con el existencial por FUERA el simbolo de Skolem es una
CONSTANTE, y eso lo decide `vars 0 = []` sin ningun caso especial.

### 2 · 🏁 Lo entregado, y las dos columnas de footprint

| pieza | footprint |
|---|---|
| `occursFormula_lift` | **sin ningun axioma** |
| `qdepth_subst`, `occurs_prenex` | `[propext]` |
| `skolemizeF_shape`, `skolemizeF_impAll`, `skolemNF_shape` | `[propext, Quot.sound]` |
| `skolem_conservative_nf`, `derives0_of_skolemNF` | `[propext, Classical.choice, Quot.sound]` |

⭐ **La direccion que vale sale NET-0**: `skolemizeF_impAll` —la forma normal implica el
original— es `intro_ex` bajo el prefijo, y no consume **ni un axioma de Skolem**. El
`Classical.choice` entra solo por `skolem_conservative_n`, que cruza por `completeness₀`: es el
**WKL**, y no es nuevo.

### 3 · ⚠️ Un puente que faltaba, y sin el el teorema NO ES APLICABLE

`occursFormula_lift` **no existia**: el arbol tenia `occursTerm_lift` y `occursTerms_lift`
(`FOL/HenkinLimit0.lean:92,101`) y **nada** para formulas. Sin el no se puede transportar la
frescura a traves de `prenex`, y sin eso `derives0_of_skolemNF` pide una hipotesis que ningun
consumidor puede descargar.

🔑 *Una conservatividad cuyas hipotesis nadie puede descargar no es un teorema utilizable.* Costo
el puente (12 l.) mas las seis conmutaciones `occurs_merge*` (60 l.) mas `occurs_prenex` (12).

### 4 · ⬜ Lo que este modulo NO entrega, dicho antes de que nadie lo suponga

⬜ **La direccion `φ → skolemize φ` CON los axiomas.** Exige empujar el axioma de Skolem **bajo el
prefijo `∀ⁿ`** (la regla K iterada sobre `allBlock`), y **no esta medida**. Sin ella no hay
`iff`: hay una implicacion y una conservatividad, que juntas son lo que la skolemizacion se usa
PARA (refutar), pero no la equivalencia.

⬜ **El enchufe con Herbrand no esta escrito.** `skolemNF_shape` entrega `∀ᵐ ψ` con `QuantFree ψ`,
que es exactamente la hipotesis de `FOL.Hauptsatz0.herbrand`, pero el puente
`allBlock m ψ` ↔ lo que `herbrand` consume (`Formula.ex`) **va en la direccion contraria**:
Herbrand habla de EXISTENCIALES y Skolem los quita. El ensamblaje real es
*refutar `∀ᵐ ψ`* = *derivar `∃ᵐ ¬ψ`*, y esa negacion **no esta escrita**.

### 5 · Nota de metodo sobre el diseno

Los tres disenos y sus seis refutadores costaron 2,7 M de tokens y 39 min. Lo que compraron **no
fue el diseno ganador** —ninguno de los tres se implemento tal cual— sino **la coincidencia**: los
seis senalaron el mismo punto de riesgo, y eso convirtio «hay que elegir entre tres rutas» en «hay
que resolver un problema de reduccion». ⚠️ Y los refutadores volvieron a acertar donde ya
acertaron en ADR-060: el fallo que predijeron es de **reduccion**, no de matematica.
🔑 *Cuando varios analisis independientes convergen en el mismo punto de riesgo, el punto de
riesgo es el problema; las rutas eran la misma ruta.*

**Controles:** RPP **145 jobs** · FOL **50 jobs** · `check-footprints` **132** ·
`check-estratos` **10** · `check-doc-sync` ✅ en los DOS repos · `check-axioms` ✅ ·
`check-sorry` ✅ · **0 sorry** · warnings **7 (RPP) + 4 (FOL)**, todos anteriores.

**Vease tambien:** `../FOL/FOL/SkolemNF0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.11,
ADR-060, ADR-058, ADR-059.

---

## ADR-063: 🏁 MAEHARA y la INTERPOLACION DE CRAIG para `LKp` -- y la condicion correcta no es la que uno escribe primero

**Fecha**: 2026-09-18
**Estado**: ✅ ACEPTADA
**Contexto**: **F**, el ultimo frente del catalogo de metateoremas. ADR-056 §1 lo dejo ABIERTO con
su obstruccion CONFIRMADA («lo unico entregable seria interpolacion para un calculo **distinto**»)
y estimado en **~850 l., riesgo alto**. `../FOL/FOL/Craig0.lean`, modulo nuevo, **665 l. de
codigo** (784 con documentacion).

    LKp     -- el fragmento PURO: `LK₀` sin `eqAx`. **13 constructores**, no 14.
    maehara : LKp Γ Δ → ∀ particiones, ∃ C interpolante con su condicion de lenguaje
    craig   : LKp [A] [B] → ∃ C, LKp [A] [C] ∧ LKp [C] [B] ∧ PredSub C [A] ∧ PredSub C [B]
    craig_impl : la forma reconocible -- de `A ⊢ B` salen `⊢ A ⇒ C` y `⊢ C ⇒ B`

📏 **`[propext, Quot.sound]` en todo el modulo: ni un `Classical.choice`, ni un axioma del
proyecto.** `lkp_to_lk0`, `predF_lift` y `predF_subst`, **sin ningun axioma**.

### 1 · ⛔⛔ La condicion sobre simbolos de FUNCION hace FALSO el paso `allL`

Al desarrollar a mano el caso `allL` aparece este contraejemplo, que es minimo:

    ∀x P(x)  ⊢  P(f(c))          -- por `allL` con t = f(c), y arriba `ax`

La premisa es `P(f(c)), ∀xP(x) ⊢ P(f(c))`, cuyo interpolante (caso `ax`, izquierda-derecha) es
`P(f(c))`. Pero tras la regla el lado 1 solo tiene `∀xP(x)`, cuyos simbolos son `{P}`. El
interpolante mete `f` y `c` ⇒ **la condicion se rompe**.

⭐ Y el TEOREMA no es falso: el interpolante correcto es `∀xP(x)`. Lo falso es el **paso ingenuo**.
La salida clasica --y es como Craig se enuncia en la mayoria de los textos-- es pedir la condicion
**solo sobre los simbolos de RELACION**.

🔑 *La condicion que hace demostrable un teorema no siempre es la que uno escribiria primero: aqui
la correcta se descubre desarrollando el caso que falla, no leyendo el enunciado.*

⇒ Y el dividendo es desproporcionado: con `predF` (solo predicados) los DOS lemas que los cuatro
casos de cuantificador necesitan --`predF_lift` y `predF_subst`-- son **triviales y sin ningun
axioma**, porque levantar y sustituir solo tocan **terminos**. Con simbolos de funcion dentro, esos
mismos dos lemas son **falsos**.

⭐ **Convergencia**: dos refutadores adversariales independientes (lentes «tipado» y
«alternativas») señalaron **el mismo punto**, con el mismo contraejemplo, y los dos propusieron la
misma correccion. Ninguno de los dos vio el modulo: solo el enunciado. Segunda vez en dos dias que
la convergencia del panel vale mas que cualquiera de sus propuestas (ADR-062 §5).

### 2 · ⭐⭐ La particion va por PERTENENCIA, y es lo que hace posible el analisis de casos

    def Split (Γ Γ₁ Γ₂ : List Formula) : Prop := ∀ x, x ∈ Γ → Or (x ∈ Γ₁) (x ∈ Γ₂)

Con `Γ = Γ₁ ++ Γ₂` el analisis de casos es **imposible**: cada regla pone la formula principal en
la CABEZA, y de `Γ₁ ++ Γ₂ = A :: Γ'` no se sigue en cual de los dos cayo `A`. Por pertenencia basta
preguntarle a la hipotesis donde fue la formula principal ⇒ **dos casos por regla**.

⭐ Lo que lo autoriza es `struct`: reordena, contrae y debilita **por pertenencia**, asi que el
secuente se comporta como un CONJUNTO. Y es tambien lo que **absorbe** la formula principal al
final de cada caso (`sub_drop`) -- el paso que cierra los 26.
⭐ Y `struct` como CASO de la induccion sale gratis: la particion de la premisa es la misma de la
conclusion compuesta con la inclusion. Una linea.

### 3 · ⭐⭐⭐ Los cuatro casos de eigenvariable NO des-levantan nada

Era el coste que dominaba la estimacion. En `allR`/`exL` el interpolante de la hipotesis de
induccion vive en el mundo LEVANTADO (`Γ.map (liftFormula 0)`), y la ruta obvia pide **des-levantar
una derivacion** -- que en `LK₀` solo se tiene via `lk0_subst`, y ese pasa por `LKh` y por
`lkh_subst`, **la pieza cara de ADR-051**: para `LKp` habria que reprobarla entera.

No hace falta. El interpolante se **cuantifica con el mismo binder que la regla introduce**:

| regla | lado 1 | interpolante | como sale |
|---|---|---|---|
| `allR` | `∀A ∈ Δ₁` | `∃C` | `exR` con `t = x₀`, reordenar, `allR` |
| `allR` | `∀A ∈ Δ₂` | `∀C` | `allR` directo / `allL` con `t = x₀` + `allR` |
| `exL` | `∃A ∈ Γ₁` | `∃C` | `exR` con `t = x₀` + `exL` |
| `exL` | `∃A ∈ Γ₂` | `∀C` | `allL` con `t = x₀`, reordenar, `exL` |

Los seis movimientos se midieron **antes** de escribir nada: compilaron a la primera, usando solo
CONSTRUCTORES mas `FOL.Lift0.substFormula_lift_var`.
🔑 *La condicion de eigenvariable es GRATIS en De Bruijn: el contexto llega literalmente como
`Γ.map lift`, y eso ES la frescura.*

### 4 · Las cifras, y donde estaba el riesgo de verdad

| | ADR-056 (estimado) | medido |
|---|---|---|
| lineas | ~850 | **665** |
| riesgo | alto | **medio**, y en otro sitio |
| «pieza cara» declarada | `SubLang` + Maehara desde cero | ⛔ **falso**: `predF`+`PredSub`+`Cov` son **30 l.** |
| donde estaba de verdad | -- | ⭐ en **elegir que simbolos se cuentan**, que es una decision de ENUNCIADO |

⚠️ Y una cifra del propio encargo que era falsa: `LK₀` tiene **14** constructores, no 15, luego
`LKp` son **13**, no 14. Lo cazo la medicion del panel leyendo el inductivo uno a uno; el docstring
de `Sequent0.lean:25` ya decia «14 ctors» y era el que acertaba. Van dos ADR seguidas con una cifra
mia corregida por una medicion (ADR-060 §6, y esta).

⭐ La prueba entera --722 l. en el sondeo-- compilo con **SEIS errores**, todos triviales: dos
rotaciones de lista al reves y cuatro veces el namespace de `substFormula_lift_var`. Ninguno
matematico. *Cuando el enunciado es el correcto, los 26 casos son mecanica.*

### 5 · ⬜ Lo que este modulo NO da, dicho antes de que nadie lo suponga

* ⛔ **No hay puente HACIA `LKp`.** `ndToLK` produce `LK₀` y usa `eqAx`; para consumir `craig` hay
  que exhibir una derivacion de `LKp` a mano. ⬜ **No medido.** ⭐ Por eso el modulo lleva
  `lkp_example` y `craig_example`: controles de NO VACUIDAD, para que el teorema no pueda ser
  cierto y no decir nada.
* ⛔ **No es interpolacion para FOL⁼.** `LKp` no tiene los axiomas de la igualdad, y esa es
  exactamente la obstruccion que ADR-056 §1 dejo CONFIRMADA. Este modulo es su «Nivel 1».
* ⚠️ **No incluye la condicion sobre VARIABLES LIBRES** de la interpolacion de Craig clasica, solo
  la de simbolos de relacion. Para **sentencias** esa condicion es vacua y el enunciado de aqui es
  el completo; para formulas abiertas es estrictamente mas debil, y se dice.
* ⚠️ `Formula.eq` se cuenta como simbolo **logico**. En `LKp` no hay `eqAx`, asi que `=` no tiene
  axiomas; contarlo fuera **debilita** el enunciado, no lo falsea.

**Controles:** RPP **145 jobs** · FOL **51 jobs** · `check-footprints` **138** ·
`check-estratos` **10** · `check-doc-sync` ✅ en los DOS repos · `check-axioms` ✅ ·
`check-sorry` ✅ · **0 sorry** · warnings **7 (RPP) + 4 (FOL)**, todos anteriores.

**Vease tambien:** `../FOL/FOL/Craig0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.12,
ADR-056 (donde F quedo abierta), ADR-062, ADR-051 (`lkh_subst`, la pieza que NO hizo falta).

---

## ADR-064: 🏁 La mitad ⟹ de HERBRAND DE BLOQUE -- y la funcion que ya llevaba el dato

**Fecha**: 2026-09-18
**Estado**: ✅ ACEPTADA
**Contexto**: **E**, la ultima deuda enunciada del catalogo. ADR-055 la dejo como `Prop` con su
consumidor delante y midio la obstruccion. `../FOL/FOL/BlockExtraction0.lean`, modulo nuevo,
**≈400 l. de codigo** (518 con documentacion).

    lk0_herbrand_block        : la induccion de 14 casos sobre `LK₀`, con el invariante de bloque
    herbrand_extraction_block : HerbrandExtractionBlock            -- ⬜ era una deuda
    herbrand_block            : ([] ⊢₀ exBlock n φ) ↔ ∃ tss E, HerbrandCertBlock n φ tss E

📏 `[propext, Quot.sound]` en todo el modulo: **ni un `Classical.choice`** — como toda la via H.
`instB_nil`, **sin ningun axioma**.

### 1 · ⭐⭐ `instB` YA ERA la funcion de resto parcial

ADR-055 midio asi la obstruccion: *«hay que llevar ademas la TUPLA PARCIAL acumulada ⇒ es un
redisenio del enunciado, no una envoltura»*. Correcto en el QUE. Pero el dato no habia que
construirlo: el caso que parecia basura de `instB` **no lo es**.

    instB (n+1) [] φ = exBlock (n+1) φ          -- el bloque que queda PENDIENTE
    instB 2 [t] φ    = exBlock 1 (φ[1 := t])    -- resto tras consumir UNA componente

⇒ `instB n us φ` con `us` **mas corta que `n`** ES el resto parcial, y la tupla parcial **es** `us`.
El invariante del consecuente cabe en una linea:

    BlockInv n φ d := QuantFree d  ∨  ∃ us, us.length ≤ n ∧ d = instB n us φ

🔑 *Antes de construir el dato que falta, mirar si una funcion que ya existe lo devuelve en su caso
degenerado.* Van **ocho** de «antes de construir, buscar».

### 2 · ⭐ La pieza de riesgo era UNA, y es la que casa con `exR`

`instB_snoc`: alargar la tupla parcial por la derecha es **exactamente** lo que hace el
constructor `exR` — pelar un `∃` y sustituir.

    us.length < n  →  ∃ A, instB n us φ = ∃A  ∧  instB n (us ++ [t]) φ = A[0 := t]

Se sondeo **antes** de escribir nada y compilo con dos correcciones, las dos conocidas: `instB n []`
no reduce con `n` variable (hace falta `instB_nil`, dos lineas), y el `rfl` final de `rw` es
`with_reducible` — **tercera vez** que aparece esa trampa (ADR-060 §4, ADR-062, esta).

Con ella, los otros trece casos son el **calco** de `FOL.Sequent0.lk0_herbrand`, y la induccion
entera compilo **a la primera, sin un solo error**.

### 3 · ⭐ Un invariante MAS FUERTE salio MAS BARATO

`lk0_herbrand` pide del testigo `Not (d = Formula.ex φ)`. Aqui se pide **`QuantFree d`**, que es
estrictamente mas fuerte — y hace el trabajo solo en el subcaso de `exR` en que **queda bloque**:
el testigo no puede ser la cabeza porque la cabeza sigue siendo un `∃`, y eso se lee del invariante
sin ningun razonamiento adicional.

🔑 *Un invariante mas fuerte puede salir MAS BARATO: descarta casos en vez de obligar a tratarlos.*

### 4 · ⚠️ El caso `n = 0` no es decorativo, y sin el el teorema NO sale

`exBlock 0 φ = φ` **si** es sin cuantificadores. Luego para `n = 0` el testigo de la induccion es
legitimo y no hay contradiccion que explotar. El ensamblaje distingue: para `n = 0` mete la **tupla
vacia** en el certificado, y entonces «todas las instancias falsas» contradice al testigo.
⚠️ Y ahi aparecio la otra trampa conocida: `instB 0 [] φ` y `exBlock 0 φ` son **ambos** `φ`, pero
`rw` casa por SINTAXIS — hubo que pedir la forma comun con dos `have` tipados.

### 5 · ✅ Y la estimacion de ADR-055 ACERTO

| | ADR-055 (estimado) | medido |
|---|---|---|
| lineas | ~350-450 | **≈400** ✅ dentro del rango |
| riesgo | alto | medio |
| «hay que llevar la tupla parcial» | ⚠️ cierto | ✅ **cierto** — pero ya la llevaba `instB` |

⭐ Es la **primera** estimacion de esta serie que cae dentro de su propio rango. Lo que se abarato
fue la PIEZA conceptual, no el total: no hubo `peelB` que escribir, pero los 14 casos se escriben
igual.

⛔ **Y una cifra mia que casi se publica sin medir**: al redactar la cabecera escribi «310 l.» y la
compare con el rango para concluir que la estimacion se habia quedado larga. **No la habia medido.**
Medida: ≈400, y la conclusion era la contraria. Corregida antes de commitear. Es exactamente lo que
**M-13** dice, aplicado a mi mismo dos ADR despues de escribirla.

### 6 · ⬜ Lo que queda

* ⬜ `HerbrandBlock0.HerbrandExtractionBlock` sigue siendo un `def ... : Prop` (el molde). El
  teorema que lo habita vive en el modulo nuevo. No se fusionan: `HerbrandBlock0` no puede importar
  `Hauptsatz0` sin invertir la dependencia que ADR-055 eligio a proposito.
* ⬜ Nada mas de E. **El catalogo de metateoremas queda sin deudas enunciadas.**

**Controles:** RPP **145 jobs** · FOL **52 jobs** · `check-footprints` **142** ·
`check-estratos` **10** · `check-doc-sync` ✅ en los DOS repos · `check-axioms` ✅ ·
`check-sorry` ✅ · **0 sorry** · warnings **7 (RPP) + 4 (FOL)**, todos anteriores.

**Vease tambien:** `../FOL/FOL/BlockExtraction0.lean`, `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.13,
ADR-055 (donde E quedo enunciada), ADR-052 (el Hauptsatz, que esto consume), ADR-063.

---

## ADR-065: La direccion ⟹ de Skolem, `check-warnings.bash`, y el informe de PeanoRF MEDIDO

**Fecha**: 2026-09-18
**Estado**: ✅ ACEPTADA
**Contexto**: tres frentes de un tiron. `../FOL/FOL/SkolemNF0.lean` §8 (+70 l.),
`check-warnings.bash` (nuevo, 110 l.), y la medicion del informe de PeanoRF.

### 1 · 🏁 La direccion ⟹ de la skolemizacion -- y sale SIN `Classical.choice`

    derives0_skolemize_iff : (∀ g ∈ skolemAxioms k f, g ∈ Γ) → (Γ ⊢₀ f ↔ Γ ⊢₀ skolemize k f)

ADR-062 §4 la dejo abierta: *«exige empujar el axioma de Skolem bajo el prefijo `∀ⁿ` (la regla K
iterada), y no esta medida»*. Medida: **un solo lema**, y por una identidad que estaba delante:

    allBlock n (Formula.forall A) = allBlock (n + 1) A

⇒ `n` universales seguidos de `∀A` **son** `n+1` universales seguidos de `A`. Con eso, el caso
`.forall` de la induccion es la hipotesis de induccion **tal cual, sin tocar un binder**, y todo el
manejo de eigenvariables se concentra en `derives0_allBlock_mp` (la regla K iterada), que baja con
`derives0_lift` + `elim_forall (var 0)` y vuelve con `intro_forall`.

📏 **Y las dos mitades salen `[propext, Quot.sound]`**: el WKL entra **solo al RETIRAR** los
axiomas (`skolem_conservative_nf`, que pasa por `completeness₀`), no al usarlos.
🔑 *Usar un axioma es finitario; retirarlo es lo que cuesta.*

⭐ Compilo **a la primera**. Van dos ADR seguidas en que la pieza «no medida» resulto ser un lema.

### 2 · ⭐⭐ `check-warnings.bash` -- el control que faltaba, y nace de un fallo mio

ADR-060 §6 midio que «0 warnings» era FALSO en ADR-057/058/059, y dejo escrito que **no habia
ningun control detras**. Ahora lo hay: declara los warnings por **fichero + clase + cuenta** (no
por numero de linea, que se mueve al editar) y rompe en **los dos sentidos**.

    ✅ LOS 11 WARNINGS CUADRAN.   (7 en ROBINSON_PlusPlus + 4 en FOL)

✅ Probado **con el fallo puesto** en los tres caminos: cifra de mas (`dice 5, real 4`), fila
borrada (`NO DECLARADO`), y verde al restaurar. Cableado en la CI y en `make warnings`.

🔑 *La diferencia entre una cifra de control y una costumbre es que algo la reejecute.* Es M-13
convertida en script.

### 3 · El informe de PeanoRF, medido punto por punto

**(1) El `Classical.choice` de `Minimal.Axioms.axioms`.** ⛔ Su diagnostico (`HA.ctx`) describe SU
puerta: **`HA.ctx` no existe en ROBINSON_PlusPlus**. La nuestra, medida:

| medicion | resultado |
|---|---|
| constituyentes de `axioms` | **109** |
| de ellos, con `Classical.choice` | **5**: `ax_vpf_ind`, `ax_vpf_listInd`, `ax_tc_zero`, `ax_tc_succ`, `ax_lineWF_listInd` |
| `coreAxioms` | ⭐ **sin ningun axioma** (net-0 puro) |
| causa raiz | `charsCodeM` (sobre `List Char`) **net-0**; `strCodeM s := charsCodeM s.toList` **con choice** ⇒ la puerta es **`String.toList`** |

⇒ **no es una deuda matematica**, es la deuda de implementacion del nucleo que el plan §7 ya tenia
medida. ⭐ Y la respuesta de calendario es concreta: sanearlo **es** el «paso 4: `String →
List Char`», que esta en la mesa hoy — pero ⛔ el plan §7.5 advierte que `List Char` es numerable y
que si LS ascendente entra en la hoja de ruta la migracion habria que hacerla **dos veces**. La
decision es del propietario.
⭐ **Lo que si pueden hacer hoy sin esperarnos**: si les basta `coreAxioms`, es **net-0** y rodea el
problema entero sin tocar nada.

**(2) «todo termino cerrado = numeral».** ⛔ **No esta, ni a medias.** `Full/Numerals.lean` tiene
`numeral` y su aritmetica (`numeral_add`, `_mul`, `_pow`, `_lt`, `_ne`) — **no** el teorema de
representacion. ⚠️ Y `natToTerm_surj` (`FOL/Enumeration.lean`) **no sirve**: enumera *todos* los
terminos, no dice que los cerrados sean numerales. ⚠️ Aviso de M-10: si lo enuncian sobre
`axioms ⊢`, ese calculo es **sintacticamente completo** y el enunciado saldria cierto por la razon
equivocada.

**(3) Su oferta (clasificar por TIPO).** ✅ Aceptada, y **no duplica**: nuestro
`check-estratos.bash` ya clasifica por el tipo, pero mide otra cosa — cuantos `axiom` **HABITAN**
cada inductivo (M-11). El suyo mira los **constructores**, que es un eje nuevo.
⭐ Aplicado a nuestro arbol: `PrfH.p3` es nuestro (`Meta/HilbertDeduction.lean:35`) y es literalmente
`((A ⇒ ⊥) ⇒ ⊥) ⇒ A` ⇒ **`PrfH` es clasico**. Y `Prf₀` **no** tiene `p3` (tiene `efq`) ⇒
intuicionista ✅, como el libro dice. La unica imprecision: el libro clasifica `Prf₀` y `Prf` pero
deja `PrfH` como «variante contextual» **sin decir que es clasico** ⇒ va por
`doc/FEEDBACK-PARA-EL-LIBRO.md`, que es su canal.

### 4 · ⬜ Lo medido y NO hecho

* ⬜ **El enchufe Skolem↔Herbrand** (~90-130 l., riesgo bajo-medio ⚠️ ESTIMADO). La pieza existe:
  `Derives₀.forall_not_ex_not` (`Derives0.lean:141`) es `¬∀A ⇒ ∃¬A`, **un constructor**. Falta
  iterarla sobre el bloque (`¬ allBlock m ψ ⇒ exBlock m (¬ψ)`) con `ex_congr`.
* ⛔ **El puente hacia `LKp`** — y la medicion dice que **el camino barato no existe**. `ndToLK` usa
  `eqAx` solo en los cuatro constructores de igualdad de `Derives₂`, asi que un calculo fuente sin
  ellos traduciria a `LKp` + `cut`. **Pero `cut_elimination` esta probado para `LKc → LK₀`**, y que
  la eliminacion preserve la ausencia de `eqAx` **no esta enunciado**. Lo correcto es
  **parametrizar `Hauptsatz0` por el conjunto de axiomas de teoria** — un refactor de un modulo de
  1 256 l. ⚠️ ESTIMADO alto. Merece decision propia; **no se improvisa**.

**Controles:** RPP **145 jobs** · FOL **52 jobs** · `check-footprints` **145** ·
`check-estratos` **10** · `check-warnings` ⭐ **11** (nuevo) · `check-doc-sync` ✅ en los DOS repos ·
`check-axioms` ✅ · `check-sorry` ✅ · **0 sorry**.

**Vease tambien:** `../FOL/FOL/SkolemNF0.lean` §8, `check-warnings.bash`, ADR-062 (donde la
direccion ⟹ quedo abierta), ADR-060 §6 (donde nacio M-13), ADR-055, ADR-063.

---

## ADR-066: El enchufe Skolem<->Herbrand, y la MEDICION del paso 4 (`String -> S`)

**Fecha**: 2026-09-18
**Estado**: ✅ ACEPTADA (§1) · 🔶 DECISION TOMADA, EJECUCION NO EMPEZADA (§3)
**Contexto**: [[2.]], [[3.]] y [[5.]] de la lista del propietario.
`../FOL/FOL/SkolemHerbrand0.lean` (nuevo, ~55 l. de codigo).

### 1 · 🏁 [[2.]] El enchufe -- y las dos piezas NO componian

    derives0_neg_allBlock_iff : (Γ ⊢₀ ¬∀ᵐψ) ↔ (Γ ⊢₀ ∃ᵐ¬ψ)
    herbrand_of_skolemNF      : ∃ m ψ, QuantFree ψ ∧
                                 ([] ⊢₀ ¬(skolemize k (prenex φ)) ↔ ∃ tss E, HerbrandCertBlock m (¬ψ) tss E)

📏 `[propext, Quot.sound]`: **ni un `Classical.choice`**.

ADR-062 §4 midio bien la juntura: `skolemNF_shape` entrega **exactamente** `∀ᵐψ` con `QuantFree ψ`,
que es la hipotesis de `herbrand_block`… pero **Herbrand habla de EXISTENCIALES y Skolem los
quita**. No es que faltara un lema: es que las dos piezas se encuentran **al otro lado de una
negacion**.

🔑 *Dos teoremas que «encajan por el tipo» pueden no componer: hay que mirar si uno habla del DUAL
del otro.*

⭐ Y la mitad cara **ya era un constructor**: `Derives₀.forall_not_ex_not` (`Derives0.lean:141`).
Iterarla sobre el bloque son tres lineas por direccion. La reciproca es intuicionista y se
construye con `elim_ex` + `elim_forall` — con las dos trampas de siempre: bajo `elim_ex` el
contexto llega **levantado** (hace falta `inst_var0` a mano) y el paso hay que **generalizarlo en
el contexto**, porque un `have` con `_` no lo infiere.

### 2 · ⛔ [[3.]] El puente hacia `LKp` -- y hay una ruta MEJOR que la que se descarto

ADR-065 §4 midio que el camino barato no existe: `cut_elimination` esta probado para `LKc → LK₀` y
que **preserve la ausencia de `eqAx` no esta enunciado**.

⛔⛔ **RECTIFICADA por ADR-067**: la ruta que sigue era **VACUA**, y hay contraejemplo
compilado (`sondeos/CraigEqVacuo.lean`). Se conserva el texto porque el error es el hallazgo.

⭐ Pero al mirarlo de nuevo aparece una tercera ruta, y es **mejor que las dos anteriores**:
**relativizar la condicion de lenguaje a las instancias de igualdad usadas**, exactamente como
`lk0_herbrand` hace con su `E`:

    maehara_eq : LK₀ Γ Δ → ∀ particiones, ∃ C E, (∀ g ∈ E, EqInstance g) ∧ … ∧
                 PredSub C (Γ₁ ++ Δ₁ ++ E) ∧ PredSub C (Γ₂ ++ Δ₂ ++ E)

El caso `eqAx` cierra: se mete `g` en `E` y la condicion lo admite. ⚠️ **RAZONADO, NO COMPILADO.**

⛔ ~~Y lo que eso entregaria es interpolacion para `LK₀` ⇒ refutaria la obstruccion de
ADR-056 §1~~ — **RETIRADO** (ADR-067 §4): aun con la correccion, lo entregado seria Craig
**modulo las instancias usadas**, mas debil que Craig clasico. La obstruccion sigue confirmada («lo unico
entregable seria interpolacion para un calculo distinto»). Seria la **sexta** obstruccion mia
refutada.

⚠️ Coste: reescribir `Craig0` entero con el parametro `E` (los 26 casos, ~700 l. mecanicas).
⬜ No empezado: es una sesion completa, y no se improvisa un refactor de ese tamaño.

### 3 · 📐 [[5.]] El paso 4 -- MEDIDO, y la cota del plan sobreestimaba por un orden

**Decision del propietario: parametro `S` generico.** Antes de tocar nada, dos mediciones.

**(a) El alcance real.** El plan §7 citaba «163 modulos / 3 902 declaraciones». Eso es el tamaño
del **arbol**, no el del **cambio**:

| | modulos que mencionan `String` | lineas |
|---|---|---|
| FOL | **19** de 46 | 144 |
| ROBINSON_PlusPlus | **15** | 75 |
| **total** | **34** | **219** |

⚠️ Matiz honesto: al parametrizar el INDUCTIVO, todo lo que menciona `Term`/`Formula` cambia de
tipo aunque no mencione `String` ⇒ la cota de 163 modulos vale para *eso*. El trabajo **no
mecanico** son las 219 lineas.

**(b) La viabilidad tecnica — sondeada y COMPILADA** (`sondeos/SymbolParam.lean`):

* ✅ `inductive Term (S : Type)` con recursion **anidada** compila, y `deriving Repr, BEq`
  **sobrevive** al parametro.
* ✅ `occursTerm {S} (c : S)` compila **sin `DecidableEq`** — compara con `=` en `Prop`.
* ✅ `updateFunc` compila con `[DecidableEq S]`.
* ✅ Y la variante ligera (`abbrev Sym : Type := List Char`, inductivo SIN parametro) tambien
  compila, y `symCode` sobre `List Char` sale **net-0** ⇒ confirma que la puerta del
  `Classical.choice` (`String.toList`) **desaparece**.

⚠️⚠️ **Y una consecuencia que hay que decidir antes de empezar**: con `S` **arbitrario**,
`FOL.Metamath.Enumeration.natToTerm_surj` **deja de ser demostrable** (enumera los terminos, y eso
exige que los simbolos sean numerables). De el cuelgan `Canonical0` (completitud) y `Compacity0`
(compacidad y LS descendente). ⇒ el parametro generico obliga a **añadir una hipotesis de
numerabilidad** a esa rama. ⬜ No medido cuanto cuesta.

⭐ La variante ligera no tiene ese problema y cumple el objetivo declarado —«que no haya que
migrar dos veces»— porque cambiar el tipo de simbolos pasa a ser **una linea**. Lo que NO da es
genericidad real: ni dos signaturas a la vez, ni teoremas cuantificados sobre `S`.

🔑 *Antes de ejecutar una migracion de firma, medir el alcance REAL: la cota que circulaba
sobreestimaba por un orden de magnitud, y eso cambia que variante conviene.*

**Controles:** RPP **145 jobs** · FOL **53 jobs** · `check-footprints` **147** ·
`check-estratos` **10** · `check-warnings` **11** · `check-doc-sync` ✅ en los DOS repos ·
`check-axioms` ✅ · `check-sorry` ✅ · **0 sorry**.

**Vease tambien:** `../FOL/FOL/SkolemHerbrand0.lean`, `sondeos/SymbolParam.lean`, ADR-065,
ADR-063 (Craig), ADR-056 §1 (la obstruccion que §2 pondria en duda).

---

## ADR-067: ⛔⛔ `maehara_eq` relativizado a `E` es VACUO -- y lo prueba un lema que yo escribi a favor

**Fecha**: 2026-09-18
**Estado**: ⛔ RUTA DESCARTADA (con contraejemplo COMPILADO) · 🔶 la corregida, MEDIDA y no empezada
**Contexto**: ADR-066 §2 anuncio una «tercera ruta, mejor que las dos anteriores» para la
interpolacion sobre `LK₀`, y dijo que **refutaria la obstruccion que ADR-056 §1 declaro
CONFIRMADA**. `sondeos/CraigEqVacuo.lean` (compilado).

### 1 · ⛔ El enunciado que publique es VACUO, y hay contraejemplo

Lo publicado en ADR-066 §2:

    maehara_eq : LK₀ Γ Δ → ∀ particiones, ∃ C E, (∀ g ∈ E, EqInstance g) ∧ … ∧
                 PredSub C (Γ₁ ++ Δ₁ ++ E) ∧ PredSub C (Γ₂ ++ Δ₂ ++ E)

⛔ **`E` es una salida existencial SIN COTA**, y `FOL.Herbrand0.EqInstance.atom`
(`Herbrand0.lean:207`) toma `p : String` **completamente libre** — sin frescura, sin pertenencia
al secuente, sin relacion con el resto de sus argumentos. Y `eqAtomAx p …` **menciona `p`**.

⇒ para CUALQUIER interpolante se fabrica un `E` que satisface **las dos** condiciones a la vez
**sin mirar el secuente**. Contraejemplo, compilado en `sondeos/CraigEqVacuo.lean`:

    secuente : LK₀ [] [t ≐ t]          (por `eqAx` con `eqReflAx t`, y `ax`)
    reparto  : Γ₁ = [], Γ₂ = [], Δ₁ = [], Δ₂ = [t ≐ t]
    C := P ⇒ P                         con P := atom "P" []
    E := [eqAtomAx "P" [] [] t t]

Las cinco condiciones se cumplen (`vac_eqInstance`, `vac_der1`, `vac_der2`, `vac_cond1`,
`vac_cond2`) **con un interpolante cuyo predicado `P` no aparece en ninguno de los dos lados**.
Eso es exactamente lo que Craig PROHIBE. El teorema seria cierto y no diria nada.

### 2 · ⛔⛔ Y la prueba de la vacuidad es un lema que YO escribi COMO CONTROL A FAVOR

Al medir las cinco instancias de igualdad anote, con razon:

| instancia | predicados que menciona |
|---|---|
| `eqReflAx`, `eqSymmAx`, `eqTransAx`, `eqFuncAx` | **ninguno** |
| `eqAtomAx q pre post a b` | ⛔ **`q`, y `q` es ARBITRARIO** |

y escribi `predF_eqAtomAx : predF p (eqAtomAx q …) ↔ q = p` presentandolo como **«lo que impide
que la relativizacion vuelva vacua la condicion»**. Es literalmente lo contrario: ese lema, leido
de derecha a izquierda, **construye** el `E` que la vuelve vacua
(`eqInstance_aporta_cualquier_predicado`, tres lineas).

🔑 *Una medicion correcta con la conclusion invertida es peor que no medir: viene con la prueba de
lo contrario adjunta y con una etiqueta de «control» encima.* Es el mismo patron que ADR-060 §6
(la cifra falsa que arrastraba su propio juicio), una capa mas arriba: aqui lo falso no era el
dato sino **la direccion en que se leyo**.

⚠️ Van **dos** anuncios mios corregidos por el panel adversarial en dos dias, y los dos en la
direccion de anunciar valor antes de tiempo.

### 3 · ✅ La correccion, MEDIDA — hay que ATAR `E` a la derivacion

`LK₀` es `Prop`-valued (`Sequent0.lean:109`) ⇒ **no existe** funcion `LK₀ Γ Δ → List Formula` que
extraiga las instancias usadas. La correccion es declarar el calculo **indexado por ellas**:

    inductive LKe : List Formula → List Formula → List Formula → Prop
      -- los 13 constructores enhebrando E; solo cambian los binarios (E₁ ++ E₂) y
      | eqAx : ∀ Γ Δ g E, EqInstance g → LKe (g :: Γ) Δ E → LKe Γ Δ (g :: E)

    lk0_of_lke : LKe Γ Δ E → LK₀ Γ Δ
    lke_of_lk0 : LK₀ Γ Δ → ∃ E, LKe Γ Δ E

    maehara_eq : LKe Γ Δ Eu → ∀ particiones, ∃ C E, (∀ g ∈ E, g ∈ Eu) ∧ …

⇒ `E` deja de ser libre: queda **acotado por las instancias que la derivacion DADA usa**.
⚠️ ESTIMADO: `LKe` + los dos puentes ~120 l.; el port de los 26 casos ~800-900 l. (los binarios
dejan de ser copia literal: dos hipotesis con `E₁` y `E₂`).

### 4 · ⚠️ Y esto NO refuta ADR-056 §1 — retiro ese anuncio

ADR-066 §2 dijo que la ruta «refutaria la obstruccion que ADR-056 §1 declaro CONFIRMADA».
**Se retira.** Aun con la correccion, lo que se entrega es Craig para `LK₀` **modulo las
instancias de igualdad efectivamente usadas**, que es **mas debil** que Craig clasico (donde la
igualdad es logica y no aporta predicados). Que `Eu` se pueda purgar de sus `eqAtomAx` con
predicados ajenos al secuente es un teorema **aparte y NO MEDIDO**.

⇒ la obstruccion de ADR-056 §1 sigue **CONFIRMADA** mientras eso no se mida.

### 5 · ⭐ Lo que el panel compro esta vez

Tres lentes; la de **vacuidad** dio `NO_SIRVE` con el contraejemplo entero escrito en la sintaxis
del proyecto, y acerto. Las otras dos no lo vieron.
🔑 *Un refutador que pregunta «¿y si el teorema es cierto y no dice nada?» caza lo que ninguno que
pregunte «¿es cierto?» va a cazar.* La lente de VACUIDAD entra en el repertorio fijo.

⭐ Y el coste evitado: la implementacion iba por **3 errores de compilacion restantes** de 51.
Estaba a punto de aterrizar un teorema vacuo **con todos los controles en verde** — `check-axioms`,
`check-footprints` y `check-doc-sync` no miran si un enunciado dice algo.

**Controles:** RPP **145 jobs** · FOL **53 jobs** · `check-footprints` **147** ·
`check-estratos` **10** · `check-warnings` **11** · `check-doc-sync` ✅ · `check-axioms` ✅ ·
`check-sorry` ✅ · **0 sorry**.

**Vease tambien:** `sondeos/CraigEqVacuo.lean`, ADR-066 §2 (rectificada aqui), ADR-063,
ADR-056 §1 (que sigue confirmada).

---

## ADR-068: 🏁 el TIPO DE LOS SÍMBOLOS es un PARÁMETRO — y costó **3 ficheros**, no 163

**Fecha**: 2026-09-18
**Estado**: ✅ ATERRIZADO · árbol verde en los dos repos, **147 footprints idénticos**
**Contexto**: paso 4 del propietario (`String → S`), plan §7.3/§7.4/§7.5. Decisión del
propietario: **parámetro `S` genérico** (no `abbrev Sym := List Char`), porque `List Char` sirve
para Gödel pero **no** para Löwenheim-Skolem **ascendente**, y habría que migrar dos veces.

### 1 · Lo hecho, y su medida

`FOL/FOL.lean` declara ahora `TermG (S : Type)` y `FormulaG (S : Type)`, y

    abbrev Term := TermG String
    abbrev Formula := FormulaG String

⇒ **el árbol entero sigue diciendo `Term`/`Formula` y no cambió ni una línea.**

| fichero | qué | líneas |
|---|---|---|
| `FOL/FOL.lean` | los dos inductivos + 2 `abbrev` + 2 bloques `export` + 3 shims | ~40 |
| `FOL/DecEq.lean` | 3 firmas generificadas + 2 `abbrev` de compatibilidad | ~6 |
| `ROBINSON_PlusPlus/Meta/HilbertSeq.lean` | 3 firmas (tiene su PROPIO `decEqTerm`) | ~3 |

**Total: TRES ficheros.** RPP **145 jobs**, FOL **53 jobs**, `check-footprints` **147** — y los
147 footprints salen **exactamente iguales** que antes de tocar nada.

### 2 · ⛔⛔ Y la estimación que había escrita era falsa **por un factor de ~50**

`NEXT-STEPS.md` decía «📐 163 módulos / 3 902 declaraciones». Esa cifra medía el **ALCANCE** del
tipo (cuántos módulos lo mencionan), no el **TRABAJO**. Un `abbrev` más un `export` absorbe el
alcance entero.

🔑 *Medir el ALCANCE de un tipo no es medir el TRABAJO de cambiarlo; lo que los separa es
**cuánto puede absorber una capa de compatibilidad**, y eso sólo lo dice el compilador.*

⚠️ Es la tercera vez que una estimación sin etiqueta viaja por los documentos
([[feedback-estimacion-sin-etiqueta]]) — pero la primera **en la dirección contraria**: la
estimación no exageraba el premio, exageraba el precio, y por eso el paso llevaba **dos meses
aplazado**. ⇒ una estimación inflada no sólo desinforma: **bloquea**.

### 3 · ⚠️ Lo que el compilador encontró y NINGÚN sondeo previo había visto

Para un inductivo **CON parámetro**, Lean 4.31 genera cosas distintas:

| | sin parámetro | con parámetro |
|---|---|---|
| `noConfusion` | homogéneo: `t = t' → …` | ⛔ **heterogéneo**: `S = S' → t ≍ t' → …` |
| `Ctor.inj` | ✅ se genera | ⛔ **no se genera** (sólo `.injEq`) |

⇒ 13 usos de `Formula.noConfusion` y 2 de `Formula.ex.inj` se rompen. Se arreglan con **tres
shims de tres líneas** en `FOL/FOL.lean`, y el árbol no se entera. ⭐ El `noConfusion` shim va
con `{P : Prop}`: con `{P : Sort u}` Lean lo rechaza como `theorem` y como `def` rompe el
generador de código.

⭐ `sondeos/SymbolParam.lean` (viabilidad, hecho antes) **no** cazó nada de esto, porque no
instanció el núcleo genérico como el tipo que el árbol ya usa. 🔑 *Un sondeo que reconstruye el
núcleo en vez de sustituirlo mide si la idea tipa, no si el árbol sobrevive.*

### 4 · ⛔ Lo que esto **NO** hace — y es la mitad del valor

**Nada del árbol es genérico todavía.** `S` no puede instanciarse en otro tipo, porque dos
módulos son `String` por dentro:

1. `FOL/Fresh0.lean` fabrica símbolos frescos (`shift`, `cst`) ⇒ clase **`FreshSym`**, tres
   propiedades (`shift_inj`, `cst_inj`, `cst_ne_shift`) y ninguna más.
2. ⛔ `FOL/Enumeration.lean` necesita `natToString_surj` ⇒ clase **`EnumSym`**, y de ella cuelgan
   `Lindenbaum0` → `HenkinLimit0` → `Canonical0` → `completeness₀`. **Ésta es la cara.**

📐 `sondeos/SymbolParamCoste.lean` (compilado) mide que **las dos clases son mínimas y
instanciables por `List Char` sin pasar por `String`**. Y da el dato que decide §7.5:

    #print axioms ProbeCoste.instEnumSymString    → [propext, Classical.choice, Quot.sound]
    #print axioms ProbeCoste.instEnumSymListChar  → [propext, Quot.sound]

⭐⭐ **La enumeración de `List Char` NO lleva `Classical.choice`; la de `String` SÍ** — y sale de
la capa 1 de `Enumeration.lean` (`natToList_surj`, sobre `List Nat`), que ya estaba escrita. Es
la confirmación *compilada* de [[feedback-footprint-no-es-constructividad]]: la raíz es
**descomponer un `String`**. ⇒ el paso 4 tiene un dividendo medible, no sólo arquitectónico.

### 5 · ⚠️ Por qué NO se generifica el resto ahora

Porque generificar un módulo mueve el footprint de teoremas **ya publicados y medidos** (ADR-041,
052, 053…). La ruta es **módulo a módulo, cada uno con su verde y su tabla de footprints**, no un
big-bang. El parámetro estando dentro, cada paso es independiente — que es justamente lo que esta
entrega compra.

**Controles (re-ejecutados, M-13):** RPP **145 jobs** · FOL **53 jobs** · `check-footprints` **147
idénticos** · `check-estratos` **10** · `check-warnings` **11** · `check-doc-sync` ✅ en los dos
repos · `check-axioms` ✅ · **0 sorry**.

**Véase también:** `sondeos/SymbolParamCoste.lean`, `sondeos/SymbolParam.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §7.5, ADR-067.

---

## ADR-069: 🏁 la CAPA DE OPERACIONES, genérica — y el orden que el panel corrigió

**Fecha**: 2026-09-18
**Estado**: ✅ ATERRIZADO · verde en los dos repos · **147 footprints intactos + 14 nuevos = 161**
**Contexto**: ADR-068 metió el parámetro `Sym` en los dos inductivos. Esto generifica lo que va
encima, que es lo que de verdad bloqueaba instanciar nada.

### 1 · ⛔⛔ El orden pedido era imposible, y el panel lo refutó entero

El encargo era «Fresh0 → Enumeration → Lindenbaum/Henkin». **Medido, el DAG lo impide**:

    Fresh0 ← Henkin0 ← Lift0 ← Eigenvariable ← Derives0 ← FOL.lean
    Fresh0 ← Rename ← Derives0          Enumeration ← FOL.lean  (INDEPENDIENTE de Fresh0)

Se lanzó un panel de 18 agentes (4 planes de capa + 4 refutadores, 5 auditorías + 5 refutadores).
⛔ **Los CUATRO planes fueron refutados**, y convergieron en lo mismo:

* ⭐⭐ **La capa 0 real no es `Enumeration` ni `Fresh0`: es la capa de OPERACIONES de
  `FOL/FOL.lean`** (`neg/top/iff`, `lift*`, `subst*`, `getAt?`/`replaceAt`). Empezar por
  `Enumeration` habría sido **cierto y VACUO**: un `FormulaG (List Char)` que ninguna operación
  del núcleo acepta. 🔑 *Ordenar por baratura y llamarlo dependencia es el error que ADR-068 ya
  pagó a ×50.*
* ⛔ **El parámetro NO puede llamarse `S`**: `S` está ocupado por la TEORÍA (`Formula → Prop`) en
  `Henkin0`, `Fresh0`, `HenkinLimit0`, `Lindenbaum0` y `Canonical0`, y es además el binder de la
  `local notation … ⊢₀* …`. Se llama **`Sym`**. Ese choque se habría visto **en el quinto módulo**.
* ⛔ **`Fresh0` no puede retirar sus seis declaraciones de `String`**: `HenkinLimit0`,
  `Lindenbaum0` y `Canonical0` usan `cst`, `shift` y `shiftTheory` **desnudos** en ~12 sitios.
  La instancia se añade **al lado**.
* ⚠️ Y una medición mía que el refutador tumbó: «`top` no se usa como fórmula en ningún sitio».
  **Falso** — `Craig0.lean:344` y `:353`, y en posición de testigo dentro de un `refine ⟨top, …⟩`,
  que es el peor sitio para un implícito. Yo había grepeado la **notación** y no el identificador:
  es [[feedback-controles-que-no-comprueban]] otra vez, «casar por subcadena que ABSUELVE».

### 2 · Lo hecho, y lo que costó — MEDIDO, paso a paso y con su verde

| paso | qué | coste MEDIDO |
|---|---|---|
| **0‑a** | `neg`, `top`, `iff` | 3 firmas · **0 errores** |
| **0‑b** | `liftTerm/Terms/Formula`, `substTerm/Terms/Formula` | 6 firmas · **8 anotaciones de tipo** |
| **0‑c** | `getAt?`, `replaceAt` | 2 firmas · **0 errores** |
| **1** | `occurs*`, `abs*` (`Eigenvariable`), `rename*` (`Rename`) | 9 firmas · **0 errores** |
| **2** | `FOL/SymClasses.lean` + las **cuatro** instancias | 1 módulo nuevo |

⭐ La capa 0‑b es la que «expone el árbol»: **32 ficheros de `FOL/` la tocan, 29 bloqueados**, y
107 de RPP. Costó **8 anotaciones**, todas de la misma forma: un `have h : liftTerm c (.var n) =
.var n` cuyo enunciado usa **sólo constructores anónimos**, con lo que nada fija `Sym`.
🔑 *Al generificar, lo que se rompe no son los tipos: son los ENUNCIADOS que no mencionaban
ninguno.* Se encuentran todos de golpe con un grep, no de uno en uno.

### 3 · ⛔ Dónde se CORTA la generificación, y por qué

`LocalRule` y `Derives` **se quedan en `String`**, y es decisión, no olvido:

1. `Derives` es el cálculo **contaminado** (`raa`/`imp_intro` toman funciones de Lean ⇒
   sintácticamente completo), y ADR-029 prohíbe inducir sobre él de forma **PERMANENTE** (M-11).
2. 📐 **MEDIDO: RPP lo cita 192 veces y no cita `Derives₀` ni una.** Parametrizarlo tocaría esas
   192 citas y reabriría el coste de ADR-068 (`noConfusion` heterogéneo, ausencia de `.inj`) con
   22 constructores, **a cambio de nada**: la metateoría de FOL⁼ va sobre `Derives₀`.

⇒ `derives0_to_derives` queda como especialización sólo-`String`. Es la misma razón por la que
`Derives₀` existe: *cuando un tipo está contaminado, se declara al lado el que sí sirve.*

### 4 · ⭐⭐ El dividendo, ahora MEDIDO EN EL ÁRBOL y no en un sondeo

    FOL.instFreshSymListChar                        → [propext]
    FOL.Fresh0.instFreshSymString                   → [propext, Classical.choice, Quot.sound]
    FOL.Metamath.Enumeration.instEnumSymListChar    → [propext, Quot.sound]
    FOL.Metamath.Enumeration.instEnumSymString      → [propext, Classical.choice, Quot.sound]

**En las dos clases, la instancia de `List Char` es estrictamente más barata que la de `String`.**
Y las cuatro resuelven por `inferInstance` en el árbol compilado ⇒ la capa **no es vacua**: el
parámetro tiene dos habitantes de verdad, no uno.
⚠️ Lo que esto **no** dice: `completeness₀` seguirá llevando `Classical.choice` pase lo que pase,
porque el suyo es el **WKL** (ADR-041), no el `String`. Generificar la cadena de Henkin comprará
**Löwenheim-Skolem ascendente**, no un footprint menor. Hay que decirlo así.

### 5 · ⭐ Y el control que faltaba: **14 titulares nuevos declarados**

El panel midió (encargo A2) que el verde de `check-footprints` dice que las filas declaradas
cuadran, **no cuántas faltan** — y que hay **223 nombres impresos fuera de la tabla**. De ahí las
14 filas nuevas: **147 → 161**. 🔑 *Un titular que no se declara no lo vigila nadie*, y ésta es la
segunda vez que el mismo control se queda corto por la misma razón (la otra fue el 09‑17, 85→88).
⬜ Queda adjudicar el resto de los 223; ⚠️ la partición «41 titulares / 182 andamio» que el panel
propuso es **JUICIO, no medición**, porque «titular» no tiene definición operativa en el repo.

**Controles (re-ejecutados, M-13):** RPP **145 jobs** · FOL **54 jobs** · `check-footprints`
**161** · `check-estratos` **10** · `check-warnings` **11** · `check-axioms` ✅ · **0 sorry**.
⚠️ Y un aviso de operativa: una pasada de `lake build` de RPP murió con `exit 3221226505`
(`STATUS_STACK_BUFFER_OVERRUN`) y la siguiente, **sin tocar nada**, salió verde. Es la firma de
memoria agotada, no del código — hermana de «failed to read file …olean.private».

**Véase también:** ADR-068, `FOL/SymClasses.lean`, `sondeos/SymbolParamCoste.lean`,
`doc/PLAN-COMPLETITUD-FINITISTA.md` §7.5 (cuya cifra «163 módulos» se retira aquí).

---

## ADR-070: ⛔⛔ M-10 **NO** puede entrar en la firma — y la clase resultó ser otra cosa

**Fecha**: 2026-09-18
**Estado**: ⛔ IDEA DESCARTADA, con **caracterización exacta compilada** · `sondeos/MDiezEnLaFirma.lean`
**Contexto**: `Sugerencias.md` ⬜1. La tesis era que **M-10 puede salir del script y entrar en la
firma**: declarar `EsREnumerable P` (verificador · decidible · adecuado), enunciar Gödel I sobre
`[EsREnumerable P]`, y que el TIPO impidiera enunciarlo sobre `⊢` — porque `axioms ⊢` es
sintácticamente completo (ADR-024) y por tanto **no r.e.**
El propietario pidió el control adversarial en estos términos: *«que la instancia para `⊢` no
compile, y por qué. Si compila, la idea está muerta.»*

### 1 · 🏁 Compila. La idea está muerta.

`sondeos/MDiezEnLaFirma.lean` (compilado, cero `sorry`) construye
`instanciaParaDerives : EsREnumerable (fun f => Derives axioms f) code`.

⛔ **La raíz**: el campo `verifier : Nat → Nat → Bool` es **DATO**, y Lean permite construir dato
**clásicamente** (`Classical.propDecidable` + `noncomputable`). El sistema de tipos **no puede
expresar «esta función `Bool`-valuada es COMPUTABLE»**. Y `noncomputable` es una marca sintáctica,
es decir… **otro control de script**. La idea se muerde la cola.

### 2 · ⭐⭐ Y el hallazgo de verdad: la clase caracteriza EXACTAMENTE otra cosa

    theorem caracterizacion_exacta (P : Formula → Nat → …) :
      Nonempty (EsREnumerable P code) ↔ (∀ f g, code f = code g → P g → P f)

**`EsREnumerable P code` es equivalente a que `P` FACTORICE por la codificación.** Ni una palabra
sobre computabilidad ni sobre enumerabilidad: es una propiedad **de la CODIFICACIÓN**, no del
CÁLCULO. ⭐ Y la dirección que lo demuestra, `factoriza_de_instancia`, es **net-0 pura**: el
verificador sólo recibe `code f`, luego no puede distinguir dos fórmulas con el mismo código.

⇒ `[EsREnumerable P]` en la firma de Gödel I **no excluye ningún `P`** que el proyecto quisiera
excluir. La hipótesis es **decorativa**.

🔑 *Una clase que se diseña para PROHIBIR hay que medirla por lo que ADMITE, no por lo que su
nombre promete.* Y el modo de medirlo es construir el habitante que no debería existir.

### 3 · ⚠️ Es la LENTE DE VACUIDAD otra vez, y van DOS EN UN DÍA

ADR-067 mató un **teorema** cierto y vacuo; éste mata una **clase** cierta y vacua. La misma
pregunta las caza: *¿y si es cierto y no dice nada?* ⇒ la lente entra en el repertorio fijo para
**enunciados y para clases**, no sólo para teoremas — [[feedback-lente-de-vacuidad]].

⭐ Y aquí la lente se aplicó **antes** de escribir una línea de producción: coste total **un
sondeo de 110 l.**, frente a los 51 errores de compilación que ADR-067 costó llegar a tener.

### 4 · Qué queda de `Sugerencias.md`

| | encargo | estado |
|---|---|---|
| ⬜1 | ¿bloquea de verdad? | ⛔ **NO. Medido y descartado** (este ADR) |
| ⬜2 | coste de `adecuado` para `Prf` | ⛔ **decae con ⬜1**: si la clase no discrimina, enhebrarla no compra nada |
| ⬜3 | propagación real, con el compilador | ⛔ **decae con ⬜1** |
| ⬜4 | ¿hay API de linter en v4.31 sin Mathlib? | ✅ **SIGUE VIVO y es independiente**: va de adelantar el censo de `axiom`, no de M-10 |

⇒ **M-10 se queda donde está**: obligación de revisión y de script, no de tipo. ⚠️ Y eso **no**
es un fracaso del diseño: M-10 cuantifica sobre *cómo se enuncia* un teorema, y ningún juicio de
tipos coge eso — exactamente el mismo argumento que `Sugerencias.md` daba para M-11.
🔑 *Si la razón por la que M-11 no cabe en la firma vale también para M-10, la tesis estaba
refutada en su propio enunciado.*

**Controles:** RPP **145 jobs** · FOL **54** · `check-footprints` **161** · `check-estratos` **10**
· `check-warnings` **11** · `check-doc-sync` ✅ · `check-axioms` ✅ · **0 sorry**.

**Véase también:** `sondeos/MDiezEnLaFirma.lean`, `Sugerencias.md`, ADR-024 (M-10),
ADR-067 (la lente de vacuidad), ADR-069.

---

## ADR-071: 🏁 `Derives₀` genérico — **dos firmas** — y la obligación que yo inventé, REFUTADA

**Fecha**: 2026-09-18
**Estado**: ✅ ATERRIZADO · verde en los dos repos · **161 footprints intactos**
**Contexto**: el panel (ADR-069 §1) dio `Derives₀` por el paso caro: inductivo, 21 constructores,
21 ficheros consumidores, y las dos asimetrías de ADR-068 reabiertas.

### 1 · 🏁 Costó **DOS firmas** y **cero errores**

    inductive Derives₀ {Sym : Type} : List (FormulaG Sym) → FormulaG Sym → Prop
    inductive LocalRule {Sym : Type} : FormulaG Sym → FormulaG Sym → Prop

Y ya está. Los 22 ficheros que citan `Derives₀` compilaron **sin tocar ni una línea**, RPP
tampoco, y `check-footprints` sigue en **161**.

⭐ **Por qué salió gratis, y son tres razones medidas, no suerte:**

1. ⭐⭐ **El parámetro va IMPLÍCITO** (`{Sym : Type}`, no `(Sym : Type)`) ⇒ la notación
   `infix:50 " ⊢₀ " => Derives₀` **sigue valiendo tal cual**. Con parámetro explícito habría
   habido que reescribirla y con ella los 22 ficheros. 🔑 *En un inductivo cuyo parámetro se
   infiere siempre del índice, implícito no es cosmético: es lo que salva la notación.*
2. ⭐ **Las dos asimetrías de ADR-068 NO muerden aquí**, y es medible de antemano:
   `grep 'Derives₀.noConfusion\|Derives₀.*.inj'` en los dos repos da **cero**. Sobre una
   derivación se hace `induction` y `cases`, nunca `injection`. 🔑 *Las asimetrías de ADR-068
   pesan en los inductivos de DATOS, no en los de `Prop`.*
3. Todo lo que los 21 constructores mencionan (`liftFormula`, `substFormula`, `neg`, `getAt?`,
   `replaceAt`, `⊥`) ya era genérico desde ADR-069.

📏 `Derives₀.rec` sigue en `[propext]` y `LocalRule.rec` es **net-0** ⇒ el **criterio de
aceptación del Paso 0** (`PLAN-COMPLETITUD-FINITISTA.md` §9) se mantiene.
✅ Y la no-vacuidad, compilada: `@Derives₀ (List Char) [A] A := Derives₀.hyp _ _ (.head _)`.

### 2 · ⛔ Y una RECTIFICACIÓN de ADR-069, en el punto exacto

ADR-069 §3 escribió que `LocalRule` se quedaba en `String` porque «es su premisa y le sigue»
—refiriéndose a `Derives`—. **Falso.** `LocalRule` es premisa de `rewrite_at`, que está **también**
en `Derives₀`. Al generificar `Derives₀`, `LocalRule` era el único bloqueante.

🔑 *Una premisa compartida sigue al consumidor **MÁS GENÉRICO**, no al primero que uno mire.*
⚠️ Es la tercera vez en el proyecto que un dividendo o una dependencia se atribuye a la pieza
equivocada, y las tres sobrevivieron hasta que **esa pieza cambió** (ADR-050 §`struct`,
ADR-053 §4, y ésta). Aquí el coste fue nulo porque salió el mismo día.

### 3 · ⛔⛔ La «obligación que nadie ha enunciado» era **MÍA**, y está REFUTADA

`NEXT-STEPS.md` publicó, atribuyéndolo al panel, que antes de `HenkinLimit0` había que decidir
«que el lenguaje ampliado con las constantes de Henkin siga siendo enumerable».

⚠️ **Eso no lo dijo el panel: lo puse yo en el prompt del agente G3 como sospecha, y su informe
NO la confirmó.** Publicarlo como hallazgo ajeno es la misma clase de error que
[[feedback-estimacion-sin-etiqueta]] denuncia, con el agravante de que **inventa una procedencia**.

Y medido, **la obligación no existe**:

* 📐 `grep 'structure Language\|structure Signature'` en `FOL/` → **cero**. Este proyecto **no
  tiene noción de lenguaje ni de signatura**: una fórmula es `FormulaG Sym` y *cualquier* símbolo
  de `Sym` puede aparecer en ella.
* ⇒ **no hay «lenguaje ampliado»**: las constantes de Henkin `cst n : Sym` están en el tipo desde
  el principio.
* Y `natToFormula_surj : ∀ f : Formula, ∃ n, …` es sobreyectiva sobre **TODAS** las fórmulas, no
  sobre un fragmento; igual que `EnumSym.enum_surj` lo es sobre **todo** `Sym`.

🔑 *La obligación es real en la Henkin de libro —donde se extiende la signatura L ⊆ L∪{cₙ} y hay
que argumentar que la extensión sigue siendo numerable— y **desaparece en esta formalización
porque no hay signatura**.* ⭐ Un teorema no hereda las obligaciones de su demostración de libro:
hereda las de **su** formalización.

### 4 · ⛔⛔ Lo que SÍ encontró el panel, y es el muro de verdad: **`Model`**

`FOL/Semantics.lean:24` —

    structure Model (D : Type) where
      func : String → List D → D
      rel  : String → List D → Prop

**Hasta que `Model` no sea `Model Sym D`, `Canonical0` no se puede generificar, punto.** Y `Model`
se usa en **9 ficheros MEDIDOS**: `Canonical0`, `Compacity0`, `Finitary0`, `Rename`, `Semantics`,
`SequentSound0`, `Skolem0`, `SkolemN0`, `Soundness0`.

⭐ Y el dato de orden que no estaba en ningún sitio: **`Canonical0` es el punto de unión de DOS
ramas del DAG que no se tocan hasta él** — la sintáctica (`FOL → Derives0 → Eigenvariable → Lift0
→ Henkin0 → Fresh0 → HenkinLimit0 → Lindenbaum0`) y la **SEMÁNTICA** (`FOL → Semantics →
Soundness0`), que nadie había planificado. ⇒ son **DOS entregas con verde propio**, no una.

### 5 · ⚠️ Y dos avisos que hay que pagar ANTES de tocar `Enumeration`

1. ⛔ **La fila que se va a mover hacia ABAJO**: `FOL.Metamath.Enumeration.natToFormula_surj`.
   Su `Classical.choice` entra **sólo** por la capa 2 (`natToString`, `String.ofList_toList`,
   `map_ofNat_toNat`); al generificar, `natToString_surj` se sustituye por `EnumSym.enum_surj`
   —una proyección sin axiomas— y el fichero **deja de tocar `String`**. `check-footprints`
   compara **conjuntos exactos** ⇒ **rompe también hacia abajo**.
   🔧 **La medición barata y no invasiva, antes de tocar nada**: añadir a
   `sondeos/SymbolParamCoste.lean` (fuera del build) un `natToFormulaG {Sym} [EnumSym Sym]` con su
   sobreyectividad y su `#print axioms`. Mide la caída **sin mover ninguna fila publicada**.
2. ⚠️ **La decisión de ENUNCIADO que decide si hay que reabrir ADR-041**: si a `completeness₀` se
   le añaden `{Sym} [FreshSym Sym] [EnumSym Sym]`, `#print axioms` pasa a medir el teorema
   **genérico**, que ya no arrastra las instancias y **puede bajar**. Si en cambio se hace
   `completeness₀G` genérico **más** `theorem completeness₀ := completeness₀G` en `String`, el
   footprint **no se mueve** y no hace falta ADR.
3. ✅ Y un riesgo que **no** existe: `[DecidableEq Sym]` **no hace falta** en `HenkinLimit0`,
   `Lindenbaum0` ni `Canonical0` — lo clásico va por `open Classical`, y `occursTerm` es
   `Prop`-valued.

**Controles (re-ejecutados, M-13):** RPP **145 jobs** · FOL **54 jobs** · `check-footprints`
**161** · `check-estratos` **10** · `check-warnings` **11** · `check-axioms` ✅ · **0 sorry**.

**Véase también:** ADR-068, ADR-069 (rectificada en §2), `doc/AUDITORIA-2026-09-18.md` (G3),
`PLAN-COMPLETITUD-FINITISTA.md` §9.

---

## ADR-072: 🔧 **A3 y A1** — dos controles que aprobaban siempre, rearmados y **probados rompiendo**

**Fecha**: 2026-09-18
**Estado**: ✅ ATERRIZADO · verde en los dos repos
**Contexto**: encargos A3 y A1 de `doc/AUDITORIA-2026-09-18.md`.

### 1 · A3 · `[E]` estaba desarmado por **TRES** vías, no por una

| # | el defecto | medido |
|---|---|---|
| 1 | su **referencia** era la entrada más reciente de `CHANGELOG.md`, que un HUMANO mantiene | congelado en **2026‑05‑16** con **115 commits** detrás ⇒ `NEWEST` viejo ⇒ ningún doc podía estar «por detrás» ⇒ **aprobaba siempre** |
| 2 | `E_HITS` **no tocaba `FAIL`** en ninguna rama, ni en la de «control VACÍO» | los `FAIL=1` están en las líneas 126/178/378/389/426; el bloque `[E]` va de la 230 a la 263 |
| 3 | leía la fecha con `head -12`, y `**Last updated:**` vive en la **línea 22‑38** | medía la fecha del **aviso histórico** de la cabecera, no la marca |

🔑 *Un control cuya **REFERENCIA** es un documento que alguien tiene que mantener se pudre con él.
La referencia tiene que **CALCULARSE**.* Ahora se calcula, y **por documento**: la fecha del
último commit que tocó **ese** documento (`git log -1 -- "$d"`), que no se puede quedar vieja.

⭐ **La tabla de deuda, y por qué**: al rearmarlo, la medición dio **21 defectos en 24 documentos**
(11 desfases + 10 sin marca). Ponerlo en rojo de golpe habría dejado el repo en rojo
indefinidamente; callarlo habría sido volver al verde falso. Se **declara**, como
`check-warnings.bash` (ADR‑065), y **rompe en los dos sentidos** ⇒ la cifra sólo puede **BAJAR**.
📐 Hoy: **7 declarados en FOL, 11 en RPP**.

✅ **PROBADO rompiendo, no afirmado** (`scratchpad/probar_E.ps1`): un doc declarado que ya está
bien → rojo («la deuda ESTÁ SALDADA, quítalo de la tabla»); un doc que falla y no está declarado
→ rojo; restaurado → verde.

⭐ Y lo que el control destapó al mirar de verdad: `FOL/REFERENCE.md` tenía marca **2026‑05‑08**
y **`**Lean version**: v4.28.0`** — las dos falsas, y el árbol lleva en **v4.31.0** desde julio.
🔑 *Una marca de tiempo falsa no viene sola: viene con lo que hay a su lado.*

⬜ `CHANGELOG.md` de FOL, reconstruido de 2026‑05‑28 a 2026‑09‑18 desde `git log` y las ADR.
⚠️ **No** desde el borrador del panel: su propio refutador marcó sus cifras como no verificadas.

### 2 · A1 · `[G.1]` — lo que **ningún** control miraba

`[E]` mira la **FECHA** del titular; nadie miraba lo que un docstring **AFIRMA QUE FALTA**.
📐 Medido: de **24** líneas con ⬜ en **16** módulos, **19 anuncian una deuda ya pagada**, más
**≥7** afirmaciones falsas sin ⬜ ⇒ **≥26 sitios** (cota inferior).

⭐⭐ **Y esto se puede comprobar A MÁQUINA porque el idioma del proyecto es exacto**: *una deuda
se **ENUNCIA** como `Prop`, nunca se postula*, y se paga con `theorem X : ESA_PROP := …`. No hay
que leer prosa: se compara un nombre con otro.
🔑 *Una convención de escritura estricta es lo que convierte una revisión de prosa en un grep.*

`[G.1]` encuentra **exactamente las tres previstas y cero falsos positivos**:
`Herbrand0:275` (`HerbrandExtraction`), `HerbrandBlock0:183` (`HerbrandExtractionBlock`),
`Sequent0:504` (`CutElim`). ✅ **Probado rompiendo**: al revertir una cabecera a ⬜ vuelve a rojo.

⚠️ **Afinado**: dispara si la cabecera marca DEUDA **y NO** la marca PAGADA. No lo debilita —
`[G.1]` sólo mira deudas **cuyo testigo ya existe**, luego escribir «PAGADA» ahí es escribir la
verdad; lo que caza es *«dice ABIERTA y está CERRADA»*.

⛔ **`[G.2]` NO entra**: acierta **2 de 11** (`Skolem0` cita `shiftEnv`/`exBlock` justo para decir
«esto SÍ está, lo otro no»). 🔑 *Un control que grita lobo se deja de mirar.*

### 3 · ⛔⛔ Y la mitad de A1 que el REFUTADOR cazó, no el informe

`TheoryFramework` decía que «`completeness` se apoya en **cinco `axiom`** de
`FOL/Completeness.lean`». **Doblemente falso**: ese fichero **no existe**, y
`cuarentena/Completeness.lean` tiene **UNO**. Era su **TERCERA** aparición en el repo.

⚠️ Pero el informe lo clasificó entre las 19 obsoletas, y **la deuda sigue VIGENTE**. Su razón de
verdad es otra, y nadie la había escrito: `folSystem` declara `derives := fun Γ f => Derives Γ f`
—el cálculo **contaminado**— mientras `completeness₀` se prueba sobre **`Derives₀`** ⇒
**`completeness₀` NO paga `CompleteLogic Formula`**.

🔑 *Una deuda puede sobrevivir a la desaparición de su motivo. Comprobar que el motivo sigue en
pie es parte de comprobar la deuda* — y es justo lo que un barrido por patrones **no** hace.
⬜ Las dos salidas quedan escritas en el fichero; elegir exige ADR.

**Controles (re-ejecutados, M-13):** RPP **145 jobs** · FOL **54 jobs** · `check-footprints`
**161** · `check-estratos` **10** · `check-warnings` **11** · `check-doc-sync` ✅ con `[E]`
rearmado y `[G.1]` nuevo · `check-axioms` ✅ · **0 sorry**.

### 4 · ⛔⛔ Y la CI tumbó mi propio control en su primera ejecución

`[E]` lee la **historia de git**, y el checkout por defecto de Actions es **SHALLOW**
(profundidad 1). En un clon superficial `git log -1 -- <fichero>` devuelve **HEAD para TODOS los
ficheros** ⇒ el control **medía una cosa en local y otra en CI**, y la puso roja con dos falsos
positivos (`doc/REFERENCE-Godelization.md`, `sondeos/README.md`).

📐 Medido en un clon superficial de verdad (`git clone --depth 1`): `REFERENCE.md`, `AXIOMS.md` y
`AI-GUIDE.md` devuelven **los tres** la fecha de HEAD, cuando en local dan 2026‑09‑18, 2026‑09‑13
y 2026‑07‑12.

🔑 *Un control que depende de la historia de `git` mide **OTRA COSA** bajo un clon superficial, y
la diferencia **no se ve en local**.* ⇒ dos arreglos, y hacen falta **los dos**:

1. `fetch-depth: 0` en el checkout del job `build`, en los dos repos.
2. ⭐ Una **guarda** en `[E]`: `git rev-parse --is-shallow-repository` ⇒ si es `true`, **rompe
   diciendo qué hacer**, en vez de medir basura en silencio. Sin esto, revertir (1) devolvería el
   control a mentir sin que nadie lo notara.

⚠️⚠️ Y lo que más escuece: **el job `libro` del MISMO fichero ya llevaba `fetch-depth: 0`, con un
comentario de once líneas explicando exactamente esta clase de bug** («el checkout por defecto es
SHALLOW … la puerta daba SIEMPRE `run=false` … este job terminó EN VERDE sin ejecutar ninguno de
sus pasos»). La lección estaba aprendida, escrita y a la vista, **en el mismo fichero**, y no se
aplicó al job de al lado.
🔑 *Una lección escrita en el punto de uso protege ESE punto de uso y ninguno más; lo que
generaliza no es el comentario, es el control.*

**Véase también:** `doc/AUDITORIA-2026-09-18.md` (A1, A3), ADR-065 (el patrón de la tabla de
deuda), ADR-041 (`completeness₀`), ADR-071.

---

## ADR-073: 🔧 **A4 y A2** — certificar el par, y la definición de «TITULAR» que faltaba

**Fecha**: 2026-09-18
**Estado**: ✅ ATERRIZADO · `check-footprints` **161 → 383**, cobertura **356/356**
**Contexto**: encargos A4 y A2 de `doc/AUDITORIA-2026-09-18.md`.

### 1 · A4 · el verde certificaba «contra ALGÚN FOL», no contra cuál

`build.yml` clona FOL con `ref: master` y no dejaba constancia de **qué** master. ⇒ el par
(RPP@sha, FOL@sha) no quedaba escrito, y pasada la retención de 90 días de los logs dejaba de ser
**certificable** (inferible de la historia sí; certificado, no).

⛔ **No se fija el `ref`, y es deliberado**: el objetivo de esa CI es cazar el día que FOL rompe a
RPP, y con un SHA fijo **dejaría de cazarlo**. 🔑 *Lo que faltaba no era fijar el dato: era
dejarlo ESCRITO.* Se añade un paso que vuelca el par al `$GITHUB_STEP_SUMMARY`, en los dos repos.
⚠️ En FOL va con `continue-on-error`, porque su checkout hermano ya lo lleva: un alcance
**REDUCIDO** no debe convertirse en un fallo.

### 2 · A2 · lo primero que faltaba no era adjudicar: era **DEFINIR**

El informe proponía repartir los 223 nombres en «41 titulares / 182 andamio», y su propio
refutador lo marcó como **JUICIO, no medición**, porque «titular» **no tiene definición operativa
en el repo**. Sin definición, adjudicar es opinar.

⭐⭐ **La definición**: *un **TITULAR** es toda declaración cuyo `#print axioms` **EL ÁRBOL
IMPRIME**.*

🔑 Por qué ésta: **(a)** es **objetiva** —la decide un grep sobre la salida de construcción—;
**(b)** está **alineada con el propósito** —si el proyecto se molesta en imprimir un footprint es
que lo **publica**, y una cifra publicada hay que vigilarla—; **(c)** es **auto-mantenida**
—poner un `#print axioms` obliga a poner la fila, y quitarlo obliga a quitarla—.
⇒ con ella **no hay nada que adjudicar**, y el reparto 41/182 sobra.

📐 Medido: **356** nombres impresos contra **161** filas ⇒ **222 sin declarar**. Tabla nueva:
**383 filas** (356 impresos + 27 que se vigilan sin ensuciar el módulo con un `#print axioms`,
que es legítimo). Y ⭐ **cero discrepancias** en los 161 que ya estaban: la tabla sólo crece.

⭐ **`[COBERTURA]`**, el bloque nuevo: compara los nombres que el árbol imprime contra los
declarados y **rompe si falta alguno**. Es lo que A2 pedía: *el verde decía que las filas
declaradas cuadran, no cuántas faltan*.

### 3 · ⛔⛔ Y el hallazgo técnico que casi arruina la tabla

**`#print axioms` da respuestas distintas según DÓNDE se pregunte.** Medido:

| dónde | `derives0_raa` |
|---|---|
| elaborando `FOL/Derives0.lean` | `[propext]` |
| tras `import FOL`, en otro fichero | **`does not depend on any axioms`** |

Y los **nombres de los axiomas se abrevian por el contexto**: `raa` dentro del módulo,
`FOL.MetaRules.raa` fuera. Copiar los valores de la salida de construcción a la tabla produjo
**5 falsos fallos** de 222.

🔑 *El valor declarado hay que medirlo en el **MISMO CONTEXTO** en que el control lo verifica.*
⇒ los **NOMBRES** salen de la salida de construcción (ésa es la definición de titular), pero los
**VALORES** se miden en el fichero que el propio script genera. Es hermano de
[[feedback-footprint-no-es-constructividad]] («el footprint de una táctica depende del entorno de
imports»), una capa más abajo: aquí depende del entorno **incluso sin táctica**.

### 4 · ⛔ Y mi control nuevo nació con el bug que este repo lleva DOCE veces documentando

`[COBERTURA]` contaba con `printf '%s' "$X" | wc -l`. `printf '%s'` **no añade salto final**, así
que con **exactamente un** titular sin declarar `wc -l` devolvía **0** y el control **aprobaba**.

Lo cazó **su propia prueba de rotura**, a la primera: quité la fila de `completeness₀` y dijo
«✅ LOS 382 FOOTPRINTS CUADRAN». Arreglado (`printf '%s\n'`) y re-probado: ahora dice
«❌ 1 titular impreso y SIN declarar: `FOL.Canonical0.completeness₀`».

🔑 *Un control que no se ha visto romper no es un control — y el que lo escribe no está exento:
éste nació con la misma clase de fallo que el repo lleva doce veces midiendo.*

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **383** (cobertura
356/356) · `check-doc-sync` · `check-estratos` **10** · `check-warnings` **11** · `check-sorry` ·
`check-axioms` ✅ · RPP **145 jobs** · FOL **54 jobs**.

**Véase también:** `doc/AUDITORIA-2026-09-18.md` (A2, A4), ADR-072, ADR-065.

---

## ADR-074: ✅ **⬜4** — sí hay linter en v4.31 sin Mathlib, y su punto ciego está MEDIDO

**Fecha**: 2026-09-18
**Estado**: ✅ MEDIDO con evidencia compilada (`sondeos/lintlab/`) · ⬜ despliegue NO decidido
**Contexto**: el último ⬜ de `Sugerencias.md`, y el único que sobrevivió a ADR-070. No iba de
M-10: va de **adelantar el censo de `axiom`**, de un barrido posterior a un aviso **en el punto
de declaración**.

### 1 · ✅ La respuesta es SÍ, a las dos preguntas

`Lean.Elab.Command.Linter` + `addLinter` + `register_option` están en **core**, sin Mathlib.
📐 Evidencia compilada (`sondeos/lintlab/`, dos ficheros):

    linters: 19 — incluye axiomCensus: true
    Uso.lean:29:0: warning: axiom declarado -- necesita ADR y fila en AXIOMS.md
    Uso.lean:31:0: warning: axiom declarado -- necesita ADR y fila en AXIOMS.md

⭐ **Dos avisos, en las dos líneas `axiom`, y ninguno** en el `def` ni en el `theorem`: no grita
lobo, que era la calibración que tumbó a `[G.2]` en ADR-072.

### 2 · ⚠️ La trampa que costó TRES intentos, y es genérica

El linter recibe **el comando ENTERO**, que para una declaración es
`Lean.Parser.Command.declaration`; el `axiom` es un nodo **HIJO**. `stx.isOfKind
``Lean.Parser.Command.axiom` **no casa nunca** — y el linter entonces **no falla: CALLA**.

🔑 *Un linter que no casa no da error: se queda mudo. Y un control mudo se lee como «no hay
nada».* Es la misma forma que las doce causas de [[feedback-controles-que-no-comprueban]], pero
en una herramienta que se escribe precisamente para vigilar.

⚠️ Antes de dar con eso descarté dos hipótesis, las dos **falsas** y las dos medidas: no era que
la API no existiera (existe), ni que estuviera gateada por opción (`lintersRef` traía las 19 con
la mía dentro, en el fichero que importa). *Medir dónde NO está el fallo también es medir.*

### 3 · ⛔ El punto ciego, MEDIDO y no supuesto

1. Un linter registrado con `initialize addLinter` **no se aplica al fichero que lo registra**:
   sus propios `axiom` posteriores pasan sin aviso.
2. Sí se aplica a los que **importan** ese módulo.
3. ⇒ **un `axiom` en un módulo que no importe el linter no lo mira nadie.**

⇒ **tienen que ser LOS DOS**, como el propietario anticipó: el linter como aviso **TEMPRANO** y
`check-axioms.bash` como **CENSO**, con la misma tabla y siempre **igualdad exacta**, nunca cota.
Es la doctrina de `check-warnings.bash`, de `[E]` y de `[COBERTURA]`.

### 4 · ⬜ Lo que NO está decidido

Dónde colgarlo para que lo importe todo el árbol. El candidato es el barril, pero eso lo
convierte en dependencia de todo y **no está medido** qué le hace al tiempo de construcción.
⚠️ Y ojo con el orden: los cuatro `axiom` de FOL viven en `FOL/MetaRules.lean`, que el barril
importa — habría que comprobar que el linter llega **antes** que ellos, no después.

**Controles (todos `exit 0`):** `check-footprints` **383** (cobertura 356/356) · `check-doc-sync`
· `check-estratos` **10** · `check-warnings` **11** · `check-sorry` · `check-axioms` ✅.

**Véase también:** `sondeos/lintlab/`, `Sugerencias.md` ⬜4, ADR-070 (que mató ⬜1‑⬜3),
ADR-072 (`[G.2]` fuera por gritar lobo).

---

## ADR-075: 🏁 la ESTRUCTURA del caso (e) — y **dos afirmaciones falsas** en la cabecera que la describía

**Fecha**: 2026-09-21
**Estado**: ✅ ATERRIZADO (§1bis de `ChainNegPrf`) · ⬜ el alimentador, MEDIDO y no escrito
**Contexto**: primer paso de la vía A — `DEUDA_chainNeg` caso (e) → `NegVerifier` → `⊬¬G`.

### 1 · 🏁 El gemelo estaba a UNA PALABRA, y el docstring lo decía

`lineOkB c p i := land (lineWF (nthc p i)) (boundedPremsIn c p i (premsOf (nthc p i)))` es un
`land` de **dos** conjuntos, y `prf_lineWF_of_chainOk` (`Meta/D3BodyPrf.lean:78`) deriva
`lineOkB nil q i` **entero** y termina en `PrfH_and_elim_left`.

⇒ el caso (e) es **la misma derivación con `and_elim_right`**. Aterrizados en `§1bis`:

| | footprint (medido en el contexto del control) |
|---|---|
| `prf_boundedPremsIn_of_chainOk` | `[propext, Classical.choice, Quot.sound]` — **net-0 de axiomas del proyecto** |
| `derives_chainOk_neg_of_prems` | idéntico a `derives_chainOk_neg_of_line`, su gemelo |

🔑 Y el docstring de la pieza original **ya lo anunciaba**: *«lo consumen **las dos** mitades de
`hbody`»*. La maquinaria que la cabecera daba por inexistente llevaba meses escrita.
⇒ van **SIETE** de «antes de construir, buscar».

### 2 · ⛔⛔ Las DOS afirmaciones falsas de la cabecera de `ChainNegPrf`

| lo que decía | lo medido |
|---|---|
| «las causas son **CINCO**» | ⛔ son **SEIS**: falta el **desajuste de TIPO** de argumento (no de aridad). `decodeTerm`/`decodeForm` tienen rangos de tag **disjuntos** y `StdArgs` sólo exige `formCode _` **o** `termCode _`, **sin decir cuál** |
| «**(a)–(d) componen con §1 y cierran**» | ⛔⛔ **FALSO**. El puente exige `k` y `x` **concretas**, y no existe nada que vaya de `decodeChainAux … = none` a esa `k` (`grep` de `firstBad\|badIdx\|failIdx\|takeWhile` : **vacío**). Ese **front-end** les falta a **las SEIS** |

⭐ Pero la sexta causa **no es un muro**, y ahí el panel se equivocó y su refutador lo cazó: los
tags 9/10 llevan las guardas `hasWitF`/`hasWit` **dentro** desde **ADR-020**, y
`crit_isTC1_junk_refuted_open` (`Meta/CodeWitnessPrf.lean:1168`) las refuta.
🔑 *Un `lineWF` más fuerte es más fácil de refutar* — escrito en `Meta/LineWFCases.lean:99`.

⚠️ Y el patrón: **una afirmación de estado viaja a una cabecera sin que nadie la compile**, y de
ahí a la cotización de la tanda. Quien cotizara esto como «sólo (e)» pagaba además el front-end.

### 3 · ⭐⭐ La decisión de ruta, y por qué se DISUELVE

`chainOk` tiene **dos** descomposiciones, y no cuestan lo mismo:

* **con acumulador** — `lineOk c line := lineWF line ∧ allIn c (premsOf line)`. Tiene el corazón
  listo (`prf_not_In_listFormCodeM`, la pieza que ya saldó `DEUDA_inNeg`), pero para llegar a la
  línea `k` hay que **pelar `prf_chainOk_cons` `k` veces** — y `k` es **simbólica**, así que no es
  pelar: es una inducción nueva más una distributividad `⟦a++b⟧ ≐ concat ⟦a⟧ ⟦b⟧` **que no existe**.
* **Δ₀** — `chainOkB c p := ∀ i < lenc p. lineOkB c p i`. La línea `k` sale por **instanciación**.
  Es la ruta de §1bis, y está compilada.

⭐ Y **convergen**: `boundedCarcIn y p` es **definicionalmente** `boundedCarcLt y p (lenc p)`
(`Meta/ChainOkBoundedPrf.lean:102`), y **los DOS sentidos** de
`boundedCarcIn y p ⇔ In y (runFn nil p)` existen (`Meta/RunFnBoundedPrf.lean:225` y `:246`).
Encadenando con `prf_runFn_objList` + `decode_heads` se llega a `In _ (listFormCodeM fs)` —
**exactamente la composición que cierra `DEUDA_inNeg`** (`Meta/ChainNegPrf.lean:255-261`).

⇒ la ruta Δ₀ **alcanza el corazón de la otra**. La decisión no es entre dos caminos: es pagar
**(i) un cambio de cota** (`boundedCarcLt y ⟦l⟧ k̄ → boundedCarcIn y ⟦l.take k⟧`, molde
`prf_ex_elim_imp`) en vez de **(ii) el pelado**. (i) es estrictamente menor.
🔑 *La forma Δ₀ se construyó para que el acumulador desapareciera; la negación de (e) es donde
eso paga.*

### 4 · ⭐ Y el control de ayer cazó el trabajo de hoy

Al aterrizar las dos piezas, `[COBERTURA]` (ADR-073) se puso **rojo** con los dos nombres nuevos
sin declarar, y obligó a medirlos y ponerlos en la tabla: **383 → 385**, cobertura **358/358**.
Es la primera vez que el control muerde a quien lo escribió, y funcionó.

### 5 · ⬜ Lo que queda, y el orden

1. **(i) el cambio de cota** — ~20 l. ESTIMADO. Va **antes** que el front-end: *primero lo que
   puede matar la idea*. Si no sale, cae la ruta Δ₀ y **cambia la forma del front-end**.
2. **El front-end** `decodeChainAux_none_first` — molde `decode_heads` (**32 l. medidas**),
   ESTIMADO 70–100, y sirve a **las SEIS** causas.
3. Los cierres de (a), (b), (c'), (d), (e), (f). ⭐ (e) está **escrita en positivo** en
   `Meta/Representability2Prf.lean:307-337`.

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **385** (cobertura
358/358) · `check-doc-sync` · `check-estratos` **10** · `check-warnings` **11** · `check-sorry` ·
RPP **145 jobs** · FOL **54 jobs**.

**Véase también:** ADR-073 (`[COBERTURA]` y la definición de titular), ADR-020 (las guardas
dentro), ADR-022 (`StdChain` estrechada), `Meta/ChainNegPrf.lean` §1bis.

---

## ADR-076: 🏁 la causa **(d)**, CERRADA de punta a punta — y la ✅ que la daba por cerrada era **falsa**

**Fecha**: 2026-09-21
**Estado**: ✅ ATERRIZADO (4 ficheros) · **la primera de las seis causas cerrada entera**
**Contexto**: vía A — los cierres de `DEUDA_chainNeg`, después del front-end (ADR-075).

### 1 · ⛔⛔ La ✅ de (d) era falsa, y sobre una instancia **ALCANZABLE**

La tabla de causas de `Meta/ChainNegPrf.lean` marcaba (d) con **✅
`derives_lineWF_neg_thy_of_not_prf`**. Ese lema pide **`¬ Prf φ`**. Lo que el decodificador
entrega es otra cosa:

    | 15, _ => (findIdx f axioms).map Rule.thy        -- Meta/ChainDecode.lean:164

es decir, **`φ ∉ axioms`** y nada más. Y `prf_ax : f ∈ axioms → Prf f` va en **un solo sentido**:
de `φ ∉ axioms` **no** se sigue `¬ Prf φ`. Como `axioms` son **141** fórmulas mientras `Prf` es
infinito, **existen** `f` con `Prf f` y `f ∉ axioms` — y sobre ésas el lema citado **no se podía
aplicar**. No es un tecnicismo de dirección de implicación: es la clase mayoritaria.

⭐ Es exactamente la lente de **ADR-067** aplicada a una ✅ en vez de a un teorema: *un lema
CIERTO cuya hipótesis no es la que le va a llegar*.
🔑 **Una ✅ que nombra un lema no dice que ese lema ACEPTE la hipótesis que le llegará.**
La ✅ se pone mirando la **conclusión**; el fallo estaba en la **hipótesis**.

### 2 · ⭐⭐ El arreglo no fue clonar: fue **generalizar en su sitio**

El reflejo barato era escribir un gemelo `…_of_not_mem` al lado. No hizo falta, porque
`neg_In_axiomsCodeT` (`Meta/AxiomListCode.lean`) **ya hacía todo el trabajo** y lo único que
sobraba era **su primer paso**:

    rw [key]; exact neg_In_axiomsList_of_not_prf φ hnp     -- ANTES
    rw [key]; exact prf_not_In_listFormCodeM φ axioms hnm  -- AHORA

Se renombró el teorema a `neg_In_axiomsCodeT_of_not_mem`, se cambió esa línea, y el antiguo quedó
como **corolario de una línea**. Idéntico en `Meta/LineWFCases.lean` con
`derives_lineWF_neg_thy_of_not_prf`. **Cero pruebas nuevas en los dos escalones.**

🔑 *Generalizar sale más barato que clonar — y además **retira** el defecto en vez de dejarlo
vivo al lado del arreglo.* Un clon habría dejado dos lemas y la ✅ vieja seguiría siendo cierta
para uno de ellos.

### 3 · 🏁 (d), de punta a punta — **la primera de las SEIS**

`derives_lineWF_neg_thy_of_decode` (`ChainNegPrf` §2ter) va del `= none` del verificador a un
`axioms ⊢ neg (lineWF …)`. Son **tres eslabones**, y ninguno costó una prueba de verdad:

| eslabón | pieza | de dónde salió |
|---|---|---|
| `decodeRuleTag … 15 … = none` ⇒ `findIdx f axioms = none` | `rfl` | `ChainDecode.lean:164` |
| ⇒ `f ∉ axioms` | `not_mem_of_findIdx_none` | contrarrecíproco, **13 l.**, `[propext]` |
| ⇒ la refutación | `derives_lineWF_neg_thy_of_not_mem` | §2, generalizar en su sitio |

⭐ `not_mem_of_findIdx_none` se colocó en `Meta/ChainDecode.lean`, **junto a sus dos gemelos**
`findIdx_sound` y `findIdx_isSome_of_getElem` — que es donde alguien lo buscaría, no donde se usa.

### 4 · ⚠️ M-13 en una frase que **todavía era cierta**

La cabecera de `ChainNegPrf` decía, sin etiqueta de ámbito:

> ⚠️ **Nada de esto usa el ancla de codificación**: el footprint no cita `AnclaEq` ni
> `ax_axiomsCodeT_eq`.

Valía para `deuda_inNeg`, y **sigue valiendo** para `deuda_inNeg`. Pero estaba escrita en la
cabecera del **MÓDULO**, y el cierre de (d) **sí** entra por `axiomsCodeT` ⇒ su footprint cita
`ax_axiomsCodeT_eq`. Sin la etiqueta, la frase se habría vuelto falsa **sola**, sin que nadie la
tocara. Se le puso el ámbito **antes** de aterrizar (d), no después.

🔑 *Una cifra sin ámbito se lee como global, y caduca en cuanto el módulo crece.*

⚠️ Y un dato de la tabla de footprints: **`ax_axiomsCodeT_eq` no aparecía en NINGUNA de las 393
filas anteriores**. (d) es el primer sitio de la cadena de `NegVerifier` por donde entra el ancla
de codificación. No es un problema — `axiomsCodeT` es justo lo que el ancla fija — pero conviene
que esté **declarado**, porque es la clase de dependencia que uno quiere ver moverse.

### 5 · ⬜ Lo que queda de los cierres

* **(e)** — todas las piezas existen (§1bis + front-end + `Representability2Prf.lean:307-337`);
  es **el ensamblaje**.
* **(c′)** — nombrar las 19 ecuaciones `prf_tagConcl_code`, que hoy sólo viven como subtérminos
  anónimos dentro de un `cases` de 169 l. (`Meta/Representability2Prf.lean:180-346`), + 2 lemas
  de inalcanzabilidad (tags 15/16) + transporte de 3 líneas.
* **(b)** — las 19 ramas `prf_lenc_*` que faltan, una línea cada una.
* **(f)** — no es una causa, **son tres cierres**.

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **398** (cobertura
**368/368**, +5 filas y +2 titulares) · `check-estratos` **10** · `check-warnings` **11** ·
`check-sorry` · RPP **145 jobs**, 0 errores. ⚠️ **ÁMBITO**: FOL **no se tocó** en esta entrada;
sus cifras son las de ADR-074.

**Véase también:** ADR-067 (la lente de vacuidad, que es la misma lente), ADR-075 (el front-end),
ADR-073 (`[COBERTURA]`), `Meta/ChainNegPrf.lean` §2ter.

---

## ADR-077: 🏁 la causa **(e)**, CERRADA — y la que iba a ser cara salió de **refutar por instanciación**

**Fecha**: 2026-09-21
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §2quater, 5 lemas) · ⬜ el **transporte** a `mp`/`gen`
**Contexto**: vía A — los cierres de `DEUDA_chainNeg`, tras ADR-075 (front-end) y ADR-076 ((d)).

### 1 · 🔑 El hallazgo: **refutar un acotado es exhibir un testigo**

La cabecera llamaba a (e) «la única sin maquinaria», y la ruta obvia era recorrer la lista de
premisas con `prf_boundedPremsIn_cons_succ_iff` (`Meta/ChainOkBoundedPrf.lean:637`), que existe
precisamente para eso. **No hacía falta.** `boundedPremsIn` **es** un `Formula.forall`:

    boundedPremsIn c p i L := ∀ j < lenc L. (In (nthc L j) c ∨ boundedCarcLt (nthc L j) p i)

y para **refutarlo** basta **un** índice malo: `spec` da la instancia, y el resto es un *modus
ponens* contra la cota. Son **16 líneas** (`derives_not_boundedPremsIn_of_index`), y la inducción
sobre `L` desaparece entera.

🔑 **Refutar un acotado es exhibir un testigo; sólo PROBARLO obliga a recorrerlo entero.**
⚠️ Y el aviso: la existencia de `prf_boundedPremsIn_cons_succ_iff` **empujaba** hacia la ruta cara.
*Que exista la herramienta para recorrer no es una razón para recorrer.*

### 2 · ⭐ El lado `In _ nil` sale **gratis**, y eso es la forma Δ₀ pagando

El `lor` de `boundedPremsIn` tiene dos lados. El primero, `In (nthc L m̄) c`, con `c = nil` lo
refuta `prf_not_in_nil_D`, que lleva en `Meta/AxiomListCode.lean` desde el nivel D.

Eso **no es suerte**: es exactamente lo que la forma Δ₀ prometía. La descomposición con
acumulador (`Minimal/Axioms.lean:803`) llega a la línea `k` con un `c` que ha ido creciendo;
`chainOkB` la alcanza por **instanciación** con `c = nil` intacto. El acumulador ha desaparecido,
y por eso ese lado del `lor` es trivial en vez de ser la mitad del trabajo.

### 3 · Las cinco piezas, y sus footprints (medidos en el contexto del control)

| pieza | qué hace | footprint |
|---|---|---|
| `derives_neg_lor` | refutar un `lor` por sus dos lados | net-0 + `or_elim`, `raa` |
| `derives_not_boundedCarcLt_congr` | transporte por el **término buscado** | **net-0 puro** |
| `derives_not_boundedCarcLt_of_not_mem` | ⭐⭐ **el motor**: `φ ∉ acc` ⟹ ninguna de las `k` primeras líneas concluye `⌜φ⌝` | + `ex_elim`, `imp_intro`, los dos `ax_*induction*` |
| `derives_not_boundedPremsIn_of_index` | ⭐⭐ refutar el ∀ acotado **instanciando** | net-0 + `raa` |
| `derives_chainOk_neg_of_prem` | ⭐⭐⭐ **el cierre**: la cadena entera queda refutada | + `imp_intro`, `or_elim`, `raa`, los dos `ax_*induction*` |

⚠️ **(e) NO cita `ax_axiomsCodeT_eq`**, a diferencia de (d) (ADR-076). El ancla de codificación
entra por `axiomsCodeT`, y (e) no pasa por ahí: va por `runFn`/`carc`. Los dos cierres tienen
footprints **distintos**, y eso es información, no ruido.

⭐ El motor salió de encajar dos cosas escritas: `decodeChainAux_carc_mem` (ADR-075, §2bis) dice
**qué** fórmula del acumulador es el `carc` de cada línea del prefijo, y `formCode_ne` separa los
códigos de dos fórmulas distintas. El paso de `φ ∉ L` a «distinta de cada una» es un `▸`.
⇒ van **NUEVE** de «antes de construir, buscar».

### 4 · ⚠️ Dos tropiezos de forma, los dos del mismo tipo

1. **El bloque se colocó antes de su dependencia.** `derives_not_boundedCarcLt_of_not_mem` usa
   `decodeChainAux_carc_mem`, que vive en §2bis; el bloque entró como «§1quater» y el compilador
   lo rechazó con `Unknown identifier`. Pasó a **§2quater**. **En Lean el orden del fichero ES
   una dependencia**, y una numeración de sección que sugiere lo contrario es una trampa.
   ⚠️ Es la **segunda vez en dos días** — la primera fue §1ter contra `decodeLine_stepConcl`.
2. **`formCodeM_eq` no estaba en el `open` del módulo.** El sondeo abría
   `Meta.Representability`; `ChainNegPrf` no. Se cualificó entero en vez de añadir un `open`
   nuevo a un fichero de 750 líneas, donde un `open` de más es una ambigüedad futura.

🔑 *Un sondeo compila en SU contexto de `open`s, no en el del fichero destino.*

### 5 · ⬜ Lo que queda de (e), y no es lógica

El cierre pide dos hipótesis sobre la línea `k`, y las dos son **transporte**, no razonamiento:

* `⊢ lt m̄ (lenc (premsOf (nthc ⟦l⟧ k̄)))`
* `⊢ neg (boundedCarcLt (nthc (premsOf (nthc ⟦l⟧ k̄)) m̄) ⟦l⟧ k̄)`

y las piezas que las alimentan existen: `SinWTs.prf_nthc_objList` (`nthc ⟦l⟧ k̄ ≐ x`),
`prf_premsOf_mp`/`prf_premsOf_gen` (escritas **en positivo** en `Meta/PremsOfTagPrf.lean`), y el
`derives_not_boundedCarcLt_congr` de esta misma entrada. Falta la congruencia de `premsOf`/`lenc`
bajo `≐` y encadenarlo.

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **403** (cobertura
**372/372**) · `check-estratos` **10** · `check-warnings` **11** · `check-sorry` ·
`check-doc-sync` · RPP **145 jobs**, 0 errores. ⚠️ **ÁMBITO**: FOL **no se tocó**.

**Véase también:** ADR-075 (el front-end y §1bis), ADR-076 ((d)), `Meta/ChainNegPrf.lean` §2quater.

---

## ADR-078: 🏁 el **DESPACHADOR**, aterrizado — y el riesgo declarado de la vía **se cae al medirlo**

**Fecha**: 2026-09-21
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §4, `dispatcher`, **net-0 puro**) · 2 sondeos
**Contexto**: vía A, tras ADR-075 (front-end), ADR-076 ((d)) y ADR-077 ((e)).

### 1 · ⛔⛔ El riesgo estaba cotizado sobre una vía ABANDONADA

Repartir entre las seis causas exige un split de 21 tags, y la cabecera de
`Meta/ChainDecode.lean:44` avisa:

> Un `match` sobre `Term` con las 21 formas anidadas revienta el `whnf` (`String.decEq` en el
> discriminante). Se **pela** el justif a `List Term` (`peelArgs`) y se matchea `(tag, args)` —
> superficial y barato.

El aviso es **cierto**. Y su segunda frase dice que esa vía **ya se abandonó**. Aun así, la parte
que viajó a la cotización del despachador fue la primera. **Medido**
(`sondeos/DespachadorCoste.lean`): el split de 21 ramas sobre `Nat`, con la hipótesis
`decodeRuleTag … = none` abierta en cada rama, elabora en **4,5 s** y sale **net-0 puro**; y cada
ecuación por tag sale por **`rfl`**, sin táctica (muestra: aridades 1/2/3 más 15, 16 y 17).

🔑 **Una nota de riesgo sobrevive al rediseño que la deja sin objeto, y se sigue cotizando.**
⭐ Es el patrón de ADR-075/076 con el signo cambiado: allí viajaba un **logro inexistente**
(la ✅ falsa de (d)); aquí viajaba un **coste que ya no existía**.

### 2 · 🏁 `dispatcher`: doce líneas, y no prueba nada por su cuenta

`ChainNegPrf` §4 va de `chainOkDec l = false` a la tabla de causas: la **primera** línea que el
verificador rechaza, ya partida en `⟨⌜f⌝, tag, as⟩` con `StdArgs as`, más el prefijo decodificado
`rs`, el acumulador `L` en ese punto, y el corte regla-vs-conclusión hecho.

Compone cuatro piezas que ya existían y no añade ninguna:
`chainOkDec`/`decodeChain` (definiciones) → `decodeChainAux_none_first` (ADR-075) →
`StdChain`/`StdLine` (ADR-022) → `decodeLine_none_cases` (ADR-075).

⭐ Y deja a las seis causas **con la misma entrada**: el `Or.inr` **es** (c′), el `Or.inl` reparte
(a), (b), (d), (e) y (f), y `L` es justo el acumulador que pide
`derives_not_boundedCarcLt_of_not_mem` (ADR-077). Footprint: `[propext, Classical.choice,
Quot.sound]`.

### 3 · ⚠️ Un precio nuevo, medido: `Nat.le` explícito ciega a `omega`

La rama `k ≥ 21` se descarga de `hk : Nat.le k 20`, y **`omega` no la ve**: *«No usable
constraints found»*. `Nat.le a b` es defeq a `a ≤ b` pero no lo mismo sintácticamente, y las
tácticas aritméticas trabajan sobre la clase `LE`. Se cierra con
`Nat.le_trans (Nat.le_add_left 21 n) hk` y un `decide` sobre `21 ≤ 20`.

🔑 *Escribir `Nat.le` para esquivar la trampa del símbolo OBJETO `le` tiene su propio precio.*
⇒ entrada nueva para `feedback_lean_notation_traps`: el esquive de una trampa de notación puede
ser, él mismo, una trampa.

### 4 · 📐 El inventario, ya sin estimaciones sueltas

| pieza | estado |
|---|---|
| despachador | 🏁 **`dispatcher`**, net-0 puro |
| (a) tag ≥ 21 | ✅ `derives_lineWF_neg_of_tag_big` |
| (b) aridad | 🔶 motor + **2 de 21** ramas `prf_lenc_*` — 19 de una línea (ESTIMADO) |
| (c′) conclusión | ⬜ 21 ecuaciones: **12 por `rfl`** (medido 6/6), **7 en 3 líneas** (medido 3/3 sobre 9/10/11), ⬜ 13/18/19/20 sin medir — ADR-077bis (`sondeos/TagConclCoste.lean`) |
| (d) `thy` | 🏁 de punta a punta |
| (e) `mp`/`gen` | 🏁 cerrada; ⬜ la forma de `premsOf x` por regla |
| (f) tipo de argumento | ⬜ **tres cierres, nada escrito** (ESTIMADO) |

⭐ **Lo que este ADR cambia en el plan**: el despachador ya no es el desconocido de la vía, así que
el orden deja de ser «medir el reparto antes que los cierres». Ahora lo único sin medir es **(f)**,
y ése pasa a ser el siguiente, por la regla de siempre: *primero lo que puede matar la idea*.

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **406** (cobertura
**375/375**) · `check-estratos` **10** · `check-warnings` **11** · `check-sorry` ·
`check-doc-sync` · RPP **145 jobs**, 0 errores. ⚠️ **ÁMBITO**: FOL **no se tocó**.

**Véase también:** ADR-075 (el front-end), ADR-076 ((d)), ADR-077 ((e)),
`sondeos/DespachadorCoste.lean`, `sondeos/TagConclCoste.lean`, `Meta/ChainNegPrf.lean` §4.

---

## ADR-079: 🏁 la causa **(b)**, CERRADA — una tanda mecánica se ESCRIBE, no se cotiza

**Fecha**: 2026-09-21
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §1ter: 19 ramas + `derives_lineWF_neg_of_arity`)
**Contexto**: vía A, tras ADR-078 (el despachador).

### 1 · ⚠️ La cotización costó más que el trabajo

Las diecinueve ramas que le faltaban a (b) viajaron por **tres mensajes** como «19 líneas de una
línea cada una, ESTIMADO». Escribirlas costó **un `awk` y un `while read`**: la tabla (tag, lenc)
de los veintiún esquemas está en el propio `Minimal/Axioms.lean`, que es el único sitio donde
podía haber un error, y el generador la lee de ahí en vez de de la memoria. Las diecinueve
compilan a la primera, **4,7 s**, y las diecinueve usan el envoltorio `_and` — ninguna el `plain`,
que sigue siendo exclusivo de `mp`.

🔑 **Una tanda mecánica se ESCRIBE, no se cotiza.** Y el corolario operativo: cuando la variación
entre los casos es una tabla que ya existe en el árbol, el generador la lee del árbol.

### 2 · 🏁 `derives_lineWF_neg_of_arity`: uno solo para los veintiún tags

La línea mide `args.length + 2` (`SinWTs.prf_lenc_objList`), el tag exige `n` (los veintiún
`prf_lenc_*`), y si no coinciden la teoría refuta `lineWF`. El motor era
`derives_lineWF_neg_of_lenc_imp`, ya escrito.

⭐ `himp` se toma como **hipótesis** en vez de despacharse por tag dentro: así el lema es **uno**
para los veintiún tags y el despachador (§4, ADR-078) le pasa el `prf_lenc_*` que toque. Es la
misma decisión que en `derives_chainOk_neg_of_prem_line`: *el reparto vive en el despachador, no
dentro de cada cierre*.

### 3 · 📐 El inventario tras esta entrada

| pieza | estado |
|---|---|
| despachador | 🏁 `dispatcher` (ADR-078) |
| (a) tag ≥ 21 | ✅ `derives_lineWF_neg_of_tag_big` |
| (b) aridad | 🏁 **CERRADA aquí** |
| (c′) conclusión | ⬜ 21 ecuaciones: 12 por `rfl` y 7 en 3 líneas, **medidas**; ⬜ 13/18/19/20 |
| (d) `thy` | 🏁 punta a punta (ADR-076) |
| (e) `mp`/`gen` | 🏁 cerrada (ADR-077); ⬜ la forma de `premsOf x` por regla |
| (f) tipo de argumento | ⬜ **tres cierres, nada escrito, nada medido** |

⇒ quedan **(c′)**, **(f)** y el resto de **(e)**. (f) sigue siendo el único **sin medir**, y por
tanto el siguiente: *primero lo que puede matar la idea*.

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **409** (cobertura
**378/378**) · `check-estratos` **10** · `check-warnings` **11** · `check-sorry` ·
`check-doc-sync` · RPP **145 jobs**, 0 errores. ⚠️ **ÁMBITO**: FOL **no se tocó**.

**Véase también:** ADR-078 (el despachador), ADR-077 ((e)), ADR-076 ((d)),
`Meta/ChainNegPrf.lean` §1ter.

---

## ADR-080: 🏁 la causa **(c′)**, CERRADA — y **cinco de los siete lemas duros ya estaban escritos**

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §1quater: `TagCode` + cierre + los **19** `tc_*`)
**Contexto**: vía A, tras ADR-079 ((b)). Orden pedido: (c′) → (e) → (f).

### 1 · ⭐⭐ La forma que hace UNO el cierre de diecinueve tags

El cierre de (c′) es `derives_lineWF_neg_of_tag k concl args e (h : tagConcl k args = some e)
(hne : ⊢ ¬ concl ≐ e)`, y `hne` sale de `formCode_ne` **sólo si `e` se identifica como el código
de una fórmula**. La igualdad de Lean `tagConcl k args = some ⌜c⌝` sirve para **doce** de los
diecinueve; para los otros siete **no existe**, porque `substfc` y `liftfc` son símbolos OBJETO y
no reducen.

La pieza que unifica los dos grupos es

    def TagCode (k : Nat) (args : List Term) (c : Formula) : Prop :=
      ∃ e, And (tagConcl k args = some e) (Prf (e =eq formCode c))

—la ecuación **literal** de `tagConcl` más una igualdad **demostrable** hasta el código. Los doce
fáciles ponen `prf_refl`; los siete duros ponen su reconstrucción aritmética. El cierre
`derives_lineWF_neg_of_concl` es entonces **uno solo** para los diecinueve.

🔑 *Cuando una igualdad de Lean sólo vale para parte de los casos, el enunciado que los une no es
el débil: es el que lleva la igualdad DEMOSTRABLE al lado de la definicional.*

### 2 · ⛔⛔ Y el hallazgo caro: cinco de los siete **ya estaban**

`prf_q1_concl_code`, `prf_q2_concl_code`, `prf_leibniz_concl_code`, `prf_ind_concl_code` y
`prf_listInd_concl_code` viven en `Meta/ArithPrf.lean:470-540`, **exportados a la raíz**. Entre
ellos los **dos que yo había marcado como los más gnarly** (`ind` y `listInd`, los que anidan
`substfc` dentro de `liftfc`). Los re-derivé antes de encontrarlos, y las re-derivaciones salieron
**línea por línea idénticas** a las que ya estaban.

🔑 **Cuando la re-derivación sale idéntica a la original, no es que el problema fuera fácil: es
que ya estaba resuelto y no se buscó.** Ésa es la señal barata que tenía a mano y no usé.
⇒ van **ONCE** de «antes de construir, buscar», y es la más cara de las once en líneas evitables.

⚠️ El sondeo `sondeos/TagConclCoste.lean` (ADR-079, del día anterior) **midió bien y buscó mal**:
dijo «`prf_substFormula_arith` es la ecuación que falta» —cierto— y no miró **dos declaraciones
más abajo**, donde estaban ya compuestas para los cinco tags. *Encontrar el ingrediente no es
haber buscado el plato.*

⭐ Lo que de verdad faltaba eran **dos**: `q3` (11) y `qconf` (19), los del `liftfc`. Difieren sólo
en si el `liftfc` va en el antecedente o en el consecuente del `∀`, y por eso ninguna de las dos
se habría heredado de la otra. Dos líneas cada una.

### 3 · 📐 El inventario

| pieza | estado |
|---|---|
| despachador | 🏁 `dispatcher` (ADR-078) |
| (a), (b), (c′), (d) | 🏁 **CERRADAS** |
| (e) `mp`/`gen` | 🏁 cerrada (ADR-077); ⬜ la forma de `premsOf x` por regla |
| (f) tipo de argumento | ⬜ tres cierres, nada escrito, **nada medido** |

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **414** (cobertura
**383/383**) · RPP **145 jobs**, 0 errores. ⚠️ **ÁMBITO**: FOL **no se tocó**; el resto de
controles se re-ejecuta en la entrada de cierre de la tanda.

**Véase también:** ADR-079 ((b)), ADR-078 (el despachador), `sondeos/TagConclCoste.lean`,
`Meta/ArithPrf.lean:470-540`, `Meta/ChainNegPrf.lean` §1quater.

---

## ADR-081: 🏁 la causa **(f)**, MEDIDA y con sus refutadores cerrados — y no era un muro

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`Meta/CodeDistinct.lean` + `ChainNegPrf` §1quinquies) · ⬜ el reparto
**Contexto**: vía A, último de los cierres pedidos ((c′) → (e) → (f)). (f) era **la única sin medir**.

### 1 · 📏 La medición, que es lo que se pedía

(f) es el **desajuste de TIPO** de argumento: `StdArgs` (`Meta/OmegaReflect.lean:148`) sólo exige
que cada argumento sea `formCode _` **o** `termCode _`, **sin decir cuál**, así que una línea
estándar puede llevar un código de término donde el tag espera uno de fórmula. Es la **sexta**
causa, la que la enumeración original de la cabecera no tenía (ADR-075).

**Medido: no es un muro, y el hecho de fondo cabe en una línea.** Los tags de cabeza son
**disjuntos** — `termCode` usa 0/1 y `formCode` usa 2…9 — así que

    theorem formCode_ne_termCode (A : Formula) (t : Term) :
        axioms ⊢ neg (formCode A =eq termCode t) := by
      cases A <;> cases t <;> exact cons_ne_head (gnum_ne (by decide))

⭐ Y la mitad que parecía cara —«¿y si el tag **sí** coincide?»— resulta ser **un solo
constructor por lema**: allí se desciende una capa y se vuelve al mismo hecho de una línea. Las
siete ranuras (`implc` ×2, `andc`, `orc`, `forallc`, `exc`, `eqc`) salen a cuatro líneas cada una,
sobre un `formCode_ne_cons_of_tag` uniforme que despacha todos los tags que **no** coinciden.

⚠️ Lo que yo había dicho —«las guardas `hasWitF`/`hasWit` de ADR-020 la cierran»— **no era la
ruta**: esas guardas cierran los tags 9/10, pero la vía barata no las necesita, porque el
desajuste ya se ve en la **conclusión reconstruida**, no en los testigos.
🔑 *Tener identificada una pieza que serviría no es haber medido por dónde sale.*

### 2 · 🏁 Dónde vive cada cosa, y por qué sólo DOS cierres

El álgebra de códigos entera va a `Meta/CodeDistinct.lean`, **al lado de `formCode_ne`**, que es
donde alguien la buscaría. En `ChainNegPrf` §1quinquies van **dos** cierres, no diecinueve, y es
deliberado: cada tag necesita saber **qué ranura** lleva el argumento del tipo equivocado, y eso
es un análisis de `StdArgs` que pertenece al **reparto** (§4), no al cierre. Los dos aterrizados
fijan el patrón de las **dos direcciones** del desajuste: `p1` (un `termCode` donde va fórmula) y
`eqrefl` (un `formCode` donde va término).

### 3 · ⭐ El control `[E]` mordió, y era verdad

Al cerrar esta tanda, `check-doc-sync [E]` rompió: *«DECISIONS.md: la marca dice 2026-09-21 y el
último commit que lo tocó es 2026-09-22»*. Correcto — la cabecera decía «hasta ADR-075» con cinco
ADR nuevas dentro. Es la primera vez que el `[E]` rearmado en ADR-072 caza una desincronización
**real** y no un autotest.

### 4 · 📐 El estado de `DEUDA_chainNeg`

| pieza | estado |
|---|---|
| despachador | 🏁 `dispatcher` (ADR-078) |
| (a) tag ≥ 21 | ✅ |
| (b) aridad | 🏁 (ADR-079) |
| (c′) conclusión | 🏁 (ADR-080) |
| (d) `thy` | 🏁 (ADR-076) |
| (e) `mp`/`gen` | 🏁 (ADR-077 + instancias) |
| (f) tipo de argumento | 🏁 **refutadores**; ⬜ el reparto |

⬜ **Lo único que queda de `DEUDA_chainNeg` es el REPARTO**: enchufar los seis cierres a las ramas
del `dispatcher`, con el análisis de `StdArgs` por tag. Ya no hay nada sin medir.

**Controles (re-ejecutados, M-13, todos `exit 0`):** `check-footprints` **424** (cobertura
**389/389**) · `check-estratos` **10** · `check-warnings` **11** · `check-sorry` ·
`check-doc-sync` · RPP **145 jobs**, 0 errores. ⚠️ **ÁMBITO**: FOL **no se tocó**.

**Véase también:** ADR-075 (la sexta causa), ADR-078 (el despachador), ADR-072 (`[E]`),
`Meta/CodeDistinct.lean`, `Meta/ChainNegPrf.lean` §1quinquies.

---

## ADR-082: ⭐⭐⭐ la INVERSIÓN de `StdArgs` — un cambio de **SOPORTE**, no un lema

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §1ter) · es el arranque del **reparto**
**Contexto**: cerradas las seis causas (ADR-076…081), lo único que le queda a `DEUDA_chainNeg`
es enchufarlas a las ramas del `dispatcher` (ADR-078).

### 1 · El problema no era probar nada: era el soporte

`StdArgs` (`Meta/OmegaReflect.lean:148`) vive sobre `Term` y **ahí se invierte mal** — para
destruirlo hay que casar contra `cons (formCode A) t`, con `cons` un `Term.func`. El reparto
trabaja sobre la **lista pelada** `peelArgs as`, donde el mismo inductivo se destruye con `cases`.

⇒ `StdArgList : List Term → Prop`, los mismos tres constructores, más `stdArgs_peel` (ida) y
`stdArgList_objList` (vuelta, que es la que reconstruye el término que piden los cierres).

🔑 **Un inductivo sobre `Term` se invierte mal; el mismo inductivo sobre `List Term` se destruye
con `cases`. La inversión no es un lema: es un cambio de soporte.**

⭐ Y `stdArgList_cons` (destructor de **un** paso) evita la familia «un lema por aridad»:
iterándolo se llega a cualquiera.

### 2 · ⭐⭐ Por qué no es fontanería

Con la aridad correcta **y los tipos correctos**, `decodeRuleTag` **decodifica**
(`decodeRuleTag_p1_some`, `decodeRuleTag_q1_some`). Ergo, para un tag estructural,
`decodeRuleTag … = none` **implica** aridad equivocada (b) **o** tipo equivocado (f), y **no hay
tercera opción**. `tag0_none_dichotomy` es esa implicación: **16 líneas, net-0 puro**, y es la
**plantilla de las diecinueve ramas**.

⇒ el reparto **no tiene que razonar: sólo destruir**. Eso es lo que la inversión compra.

⚠️ Trampa nueva, para `feedback_lean_notation_traps`: el caso `[_]` va con `simp` y **no** con
`decide` — con una variable libre dentro, `decide` se niega («Expected type must not contain free
variables») aunque la longitud sea computable. Es la gemela de la de ADR-078 (`omega` y `Nat.le`).

**Controles:** `check-footprints` **427** (cobertura **392/392**) · RPP **145 jobs**, 0 errores.

---

## ADR-083: 🏁 el MURO de `Model` — alcance **9 ficheros**, trabajo **1**

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`FOL/FOL/Semantics.lean`, commit `2d5b7c8`) · ⬜ segunda entrega
**Contexto**: `Model (D : Type)` con `func : String → List D → D` era **el muro declarado** de la
migración del símbolo a parámetro (ADR-068/069/071): en el banner del proyecto, «**9 ficheros**».

### 1 · 📏 Medido por SUSTITUCIÓN, y el muro no estaba

`Model` se citaba en **9 ficheros, 68 veces**. La migración fue:

    structure ModelG (S D : Type) where
      func : S → List D → D
      rel  : S → List D → Prop
    abbrev Model (D : Type) := ModelG String D

más `evalTerm`/`evalTerms`/`evalFormula`/`contextSatisfies` a `{S D}` sobre `TermG S`/`FormulaG S`.
**Cinco ediciones, un fichero.** Los **ocho** restantes **no se tocaron**: el `abbrev` los deja
intactos, igual que `abbrev Term := TermG String` hizo con el núcleo. FOL **54 jobs** y RPP
**145 jobs**, verdes **a la primera**.

🔑 **Medir el ALCANCE de un tipo no es medir el TRABAJO** — van **dos** veces en esta misma
migración (ADR-068 cotizó 163 módulos y eran 3 ficheros).
⭐ Y la regla de método que lo hizo barato: *un sondeo que RECONSTRUYE mide si la idea tipa; sólo
uno que SUSTITUYE mide si el árbol sobrevive* (ADR-068 §2). Aquí se fue directo a sustituir.

### 2 · ⬜ La segunda entrega, que sí es trabajo

`Canonical0` (el modelo canónico, 22 de las 68 citas) sigue en `String`, y es **la que une la
rama sintáctica con la SEMÁNTICA** del DAG. Necesitará `FreshSym` — la clase que
`sondeos/SymbolParamCoste.lean` ya midió como una de las **dos y sólo dos** que hacen falta.
⚠️ No la cotizo: el historial de esta migración dice que cualquier número que ponga aquí sería
una estimación sin etiqueta.

### 3 · ⚠️ Lo que este ADR **no** arregla

`ModelG` es condición necesaria para un **modelo de los 141 axiomas**, que es lo que retiraría la
vacuidad de Gödel I/II (nada prueba `ConsistentH`). Pero **no es ese modelo**: aquí sólo se ha
generificado la estructura. La solidez de `Prf` respecto de un modelo **sigue sin existir** en
RPP — medido: FOL tiene `lk0_sound` (secuentes) y nada más.

**Controles:** FOL `check-sorry` · `check-axioms` · `check-doc-sync` · **54 jobs**;
RPP **145 jobs**. ⛔ **M-12 respetada**: FOL commiteado **antes** que RPP.

**Véase también:** ADR-068/069/071 (la migración del símbolo), `sondeos/SymbolParamCoste.lean`,
`FOL/CHANGELOG.md` 2026-09-22.

---

## ADR-084: 🔧 la DEUDA DE CONTROL, adjudicada — y **las tres cifras publicadas estaban bajas**

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`check-doc-sync.bash`: `[H]` nuevo, `[E]` ampliado, `[B]` con trinquete)
· ⬜ dos deudas de LECTURA, declaradas
**Contexto**: frente C. Cuatro puntos, y **tres de los cuatro** eran una cifra que resultó ser
más alta de lo publicado — siempre por la misma razón.

### 1 · 🔑 El patrón: cada cifra se había tomado con una red más estrecha que la realidad

| punto | cifra publicada | cifra MEDIDA hoy | por qué difería |
|---|---|---|---|
| sondeos sin proyectar | **13 de 74** | **19 de 76** | se contaba como proyectado cualquier fichero **mencionado en la prosa** de otra fila |
| marcas `Last updated` | **11 de 18** | **35 de 40** | `[E]` sólo recorría los **15 AUTHORITATIVE**; los otros 25 `.md` no los miraba nadie |
| símbolos muertos | **223 nombres** | **44** | 223 era el conteo de CANDIDATOS **antes** de aplicar los `DEAD_MARKER` |

🔑 **Una cifra de deuda sin decir en qué punto del filtro se tomó no es comparable consigo
misma** — y las tres se habían publicado como si lo fueran.
⚠️ Dos de las tres se movieron **hacia arriba**; la tercera, hacia abajo. El sesgo no es
optimismo: es que **nadie volvió a medir con la red ancha**.

### 2 · 🏁 `[H]`: el catálogo de `sondeos/`, cerrado

`sondeos/` está **fuera del build** por diseño ⇒ `[C]` (que proyecta las `lean_lib`) no lo mira.
`[H]` compara `ls sondeos/*.lean` contra las **cabeceras de fila** del README y **rompe en los
dos sentidos**: un fichero sin fila es trabajo que se repetirá, y una fila sin fichero es una
referencia falsa (el daño de ADR-072). **Probado rompiendo las dos veces**, y la prueba A con
**exactamente uno**, que es donde el bug de `printf '%s'` habría absuelto.

⭐ Para que naciera **verde y honesto** se añadió al README la tabla **⬜ SIN REDACTAR** con los
19, cada uno con su **primera línea útil copiada literalmente** del fichero. ⛔ No se les
inventó un «resultado»: redactarlos exige leer ≈ **4 000 líneas**, y una fila de resultado
escrita sin leer el fichero es exactamente la documentación que este repo lleva un año
retirando. La deuda queda **enunciada**, no escondida.

⚠️ Bug propio, cazado al primer arranque: los backticks dentro de un `echo "…"` se ejecutaron
como **sustitución de comando** y el título salió mutilado. *Un control también es código.*

### 3 · 🏁 `[E]`: mismo control, universo de 15 → 40

`[E]` **ya era** el control de frescura con tabla de deuda y trinquete (ADR-072). Lo que fallaba
era **a qué miraba**. Se amplió su universo a todos los `.md` salvo `doc/book/**`, y se declaró
la deuda medida. ⭐ **Y el propio control cazó TRES que mi medición a mano no vio** (`comm` con
locales distintos se las comió): `doc/PLAN-COMPLETITUD-FINITISTA.md`, `ESCALANDO_EL_PROYECTO.md`,
`NAMING-CONVENTIONS.md`. 🔑 *Esta vez la red estrecha era la mía.* Total declarado: **35**.

⛔ Lo que **no** se hizo: poner la fecha de hoy en los 35. Eso es actualizar el **banner** sin
tocar el **cuerpo** — el defecto exacto que este control existe para cazar.

### 4 · 🏁 `[B]`: de AVISO a CONTROL, y un agujero en mi propio trinquete

`[B]` no rompía («requiere juicio»), y un aviso que nadie adjudica es una lista que crece sola.
Ahora declara los **44** y rompe en los dos sentidos.

⛔⛔ **Y la prueba de rotura encontró un agujero que yo había metido**: el bucle recorre los
símbolos **CITADOS**, así que una entrada de la tabla cuyo documento se arregle **deja de entrar
en el bucle** y la tabla guardaría fantasmas para siempre. La comprobación de «deuda saldada»
tuvo que salir **fuera** del bucle.
🔑 *Un trinquete que sólo mira lo que entra en el bucle no es un trinquete: es media cuenta.*
La versión de `[E]` no tenía el agujero porque recorre **documentos**, que siempre existen; ésta
recorre **citas**, que desaparecen. ⭐ Van tres controles nuevos este mes y **los tres** tenían un
defecto que sólo salió al probarlos rompiendo.

### 5 · ⛔ El linter de ADR-074: **medido, y la respuesta es NO desplegarlo**

⬜4 dejaba abierto «dónde colgarlo y qué le hace al tiempo de construcción». Medido:

* **`import Lean` cuesta +3,2 s por módulo** (`Minimal/Axioms.lean`: 5,4 s → 8,6 s).
* El candidato que ADR-074 nombraba —**el barril**— es **inservible**: medido, **CERO** módulos
  del árbol importan `ROBINSON_PlusPlus`. Colgarlo ahí no vigilaría nada.
* Los tres `axiom` viven en `Minimal/Axioms.lean` (la **raíz** del DAG), `Full/Induction.lean` y
  `Full/Lists.lean`. Y —por el punto ciego que el propio sondeo midió— **un linter sólo ve el
  fichero que lo IMPORTA**. Para vigilar el de la raíz hay que colgarlo en la raíz, y entonces
  los **131** módulos pagan el import.

⇒ **No se despliega.** `check-axioms.bash` ya hace el censo con **igualdad exacta**, en
milisegundos, y sobre el árbol entero. 🔑 *Un aviso más temprano no vale un build 131 veces más
caro cuando el censo tardío es exacto.* ⬜ Si algún día hay muchos más `axiom`, se reabre.

### 6 · ⬜ Lo que queda, y es de LECTURA

1. Redactar el resultado de los **19** sondeos de la tabla nueva.
2. Adjudicar los **44** de `B_DEUDA`: por cada uno, mirar su línea y decidir si es historia
   (⇒ marcarla) o una afirmación de estado caducada (⇒ arreglar el doc).
3. Las **35** marcas `Last updated`: leer el cuerpo y entonces bumpear.

Las tres están **declaradas y con trinquete**: no pueden crecer.

**Controles (re-ejecutados, M-13):** `check-doc-sync` con `[H]` **76/76**, `[E]` **35
declaradas / 0 sin declarar / 0 sin saldar**, `[B]` **44 de 44** · `check-footprints` **427**
(cobertura **392/392**) · RPP **145 jobs**. ⚠️ **ÁMBITO**: FOL no se tocó en esta entrada.

**Véase también:** ADR-072 (`[E]` rearmado), ADR-073 (`[COBERTURA]`), ADR-074 (el linter),
`sondeos/lintlab/`.

---

## ADR-085: 📏 **M1–M4**: el modelo de los 141 es alcanzable — y el censo de agujeros sale **limpio**

**Fecha**: 2026-09-22
**Estado**: ✅ MEDIDO (`sondeos/ModeloDiscriminador.lean`) · ✅ censo aterrizado en `check-sorry.bash`
**Contexto**: las cuatro mediciones que decidían el frente del modelo, más el censo que sustituye
al linter de ADR-074 (cerrado en NO por ADR-084 §5).

### 1 · Las cuatro mediciones, y **las cuatro salen a favor**

| | qué | resultado |
|---|---|---|
| **M1** | ¿de qué depende `ConsistentH ↔ ¬ Prf ⊥`? | ✅ **net-0** ⇒ un modelo lo descarga **entero**, sin residuo de los 3 `axiom` de Lean |
| **M2** | ¿es tratable `evalFormula` sobre un axioma real? | ✅ `intro v d; simp […]`, y **`[propext]`** — el mejor footprint posible |
| **M3** | ¿se puede montar la capa de LISTAS sobre ℕ? | ✅ la inyectividad de Cantor es **net-0 pura**; `carc` existe como inversa clásica |
| **M4** | ¿cuánto de la solidez de `Prf` está? | ✅ **el aparato semántico entero**: 13 lemas en `FOL/Semantics.lean`, probados en uso por `lkc_sound` (14 reglas) |

⭐ **M4 es el que cambia la cotización**: la parte cara de toda solidez —la semántica de
sustitución y lifting— **ya está escrita**. La solidez de `Prf` es inducción sobre `Prf`
reusándola, y **M-11 no la bloquea** porque `Prf` está en la lista blanca.
⇒ el frente pasa de «¿es posible?» a «¿en qué orden?».

### 2 · ⛔ Lo que M3 encontró EN CONTRA, y no es matemática

1. **`Nat.sqrt` no está en el core de Lean.** `coreAxioms` tiene `ax14_sqrt_le` y
   `ax15_lt_succ_sqrt`, así que el modelo tendrá que **definir** una raíz entera y probar esas
   dos. Acotado, pero no gratis.
2. **Sin Mathlib no hay `ring` ni `by_contra`**, y **`omega` no ve** un producto como
   `s*(s+1)/2`: el número triangular hay que definirlo **por recursión** para que lo trate
   linealmente.

🔑 **El obstáculo del frente no era la matemática: era qué trae el core de Lean sin Mathlib.**

### 3 · ⚠️⚠️ Una trampa de notación NUEVA: **las dos se muerden**

Con `Minimal.Axioms` abierto, **`≤` resuelve al símbolo OBJETO `le`** (trampa vieja). Esquivarla
escribiendo `Nat.le` explícito **ciega a `omega`** (ADR-078). En M3 saltaron **las dos, en el
mismo lema**, y sólo al **promover** el sondeo — en el scratchpad no estaba ese `open`.

🔑 *Cuando dos trampas de notación se muerden, la salida no es elegir una: es **acotar el
`open`** para que no coincidan.* M3 vive fuera del `open`; M1/M2, dentro de una `section`.
⇒ entrada nueva para `feedback_lean_notation_traps`.

### 4 · 🏁 El censo de agujeros de confianza — **limpio, y ahora vigilado**

ADR-084 §5 cerró el linter en NO y propuso medir **los otros** agujeros. Medido en los dos repos:

| | RPP | FOL | |
|---|---|---|---|
| `native_decide` | 0 | 0 | ⭐ el peor de todos, y **no está** |
| `unsafe` · `opaque` · `@[implemented_by]` · `@[extern]` | 0 | 0 | ⭐ ninguna implementación nativa sin verificar |
| `sorry` | **0** | 0 | los 12 *hits* del grep son **comentarios**; `check-sorry` tenía razón |
| `partial def` | 1 | 3 | ⚠️ los cuatro **inocuos**: `termToString` y tres ayudantes en `MetaM` — no entran en ningún término de prueba |

⇒ el censo se aterriza en `check-sorry.bash`, con **igualdad exacta** y **probado rompiendo**
(un `native_decide` de juguete lo pone rojo).
🔑 *Un agujero que hoy vale cero y que nadie vigila es un agujero abierto, no uno cerrado.*
⚠️ `partial def` se deja **fuera** del control y se dice por qué: hoy la cifra no discrimina
entre inocuo y peligroso, y un control que no discrimina se acaba ignorando.

⚠️ Y por segunda vez en el mismo día, **backticks dentro de un `echo "…"` ejecutados como
sustitución de comando**. *Un control también es código, y el mío falló igual dos veces.*

### 5 · ⬜ El orden que esto deja para el frente del modelo

1. Raíz entera sobre ℕ + `ax14`/`ax15`.
2. Los **34 core** (molde: M2).
3. La capa de listas (molde: M3) y de ahí los **107 coding**, interpretando por
   **decodificar → función de Lean → recodificar**.
4. **Solidez de `Prf`** por inducción, reusando los 13 lemas de M4.
5. ⇒ `¬ Prf ⊥` = `ConsistentH`.

**Controles:** `check-doc-sync` (`[H]` **77/77**) · `check-sorry` + censo · RPP **145 jobs**.
⚠️ **ÁMBITO**: FOL no se tocó en esta entrada.

**Véase también:** ADR-083 (`ModelG`), ADR-084 §5 (el linter, cerrado en NO),
`sondeos/ModeloDiscriminador.lean`.

---

## ADR-086: 🏗️ el MODELO ESTÁNDAR arranca — **8 de los 34 core**, y la raíz entera era lo único que faltaba

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`sondeos/ModeloNat.lean`) · ⬜ 26 core + los 107
**Contexto**: pasos ① y ② del orden que fijó ADR-085 §5.

### 1 · ⛔⛔ Y van DOCE — pero esta vez lo cazó la instrucción de buscar

`triN` (`Meta/CodeNumeralPrf.lean:46`), `consN`, `two_mul_consN` y **`consN_inj`**
(`Meta/CodeNatInjPrf.lean:85`) estaban **en producción**: el emparejamiento de Cantor sobre `Nat`
y **su inyectividad**, que es exactamente el crux que M3 midió ayer… re-derivándolo.

⭐ La diferencia con las once anteriores: aquí no lo cacé yo, lo cazó **la instrucción explícita
de mirar antes**. 🔑 *La señal «la re-derivación sale idéntica» funciona a posteriori; mirar
primero funciona antes.*

### 2 · 📏 `Nat.sqrt`: no está, y el transporte de Peano NO compensa **para esto**

**`Nat.sqrt` no existe en el core de Lean**, y `ax14_sqrt_le`/`ax15_lt_succ_sqrt` lo piden.
Se miró `Peano/PeanoNat/Sqrt.lean`: tiene desarrollo **completo** —`sqrtMod`, `sqrtRem`,
`sqrtMod_spec`, `sqrt_upper_bound`, `csqrt`— pero sobre **`ℕ₀`**, el natural propio de Peano.

ℕ₀ es isomorfo a `Nat`, así que transportar es posible. Medido: aquí sólo hacen falta **dos
desigualdades**, y escribirlas directamente son **30 líneas net-0 puras**; el transporte pide el
iso más la preservación de `*` y `≤`. **No compensa.**

🔑 **Un desarrollo ajeno se reutiliza por lo que hay que TRANSPORTAR, no por lo que contiene.**
⬜ Donde el transporte **sí** puede pagar es más adelante: `div`/`mod`, `pow`, y sobre todo
`Peano/PeanoNat/Foundation/GodelBeta.lean` — la **β de Gödel**, que la capa de listas necesitará.

### 3 · 🏁 Lo validado, y con qué footprint

**8 de los 34 `coreAxioms`**, todos **net-0**: `ax2`, `ax3`, `ax4`, `ax14`, `ax15`, `ax18`,
`ax25`, `ax26`. La forma es siempre la misma — `intro v d; simp […]` — y los dos de la raíz
rematan con `omega` contra `sqrtN_le` / `lt_sq_succ_sqrtN`.

⇒ el molde de M2 (ADR-085) **escala**: no hubo que inventar nada por axioma.

### 4 · ⚠️ Dos trampas, y una es reincidente

1. **Nueva**: el sucesor de un cuadrado va como `k+1+1` y **no** como `k+2`. Para `omega` el
   producto es un **ÁTOMO**, y `(k+2)*(k+2)` y `(k+1+1)*(k+1+1)` son átomos **distintos**: con
   `k+2` el lema no cierra aunque sea la misma desigualdad.
2. **Reincidente, y es la segunda vez en esta sesión**: el linter marcó `ax25_pred_zero` como
   argumento `simp` «no usado», se quitó, y **rompió** — `ax25` es el único de los ocho que no
   es un `forall_`, así que sin su nombre no hay nada que abrir.
   🔑 *Un aviso de «no usado» no es una medición de que sobre.*

### 5 · ⬜ Lo que queda, por capas

| capa | qué falta |
|---|---|
| aritmética | `ax5`–`ax12`, `ax16`, `ax17`, `ax21`, `ax24`, `ax29`, `pow` — mecánicos, molde fijado |
| orden | `ax13_lt_def` (define `<` por un `∃`) y `ax19_lt_trichotomy` |
| **listas** | `ax_L0`–`ax_L3`, `ax_C1`–`ax_C3`, `prodp` — ⭐ **es la que comparte maquinaria con los 107**, y ya tiene `consN`/`consN_inj` |
| **los 107** | interpretando por **decodificar → función de Lean → recodificar** |
| solidez de `Prf` | inducción sobre `Prf` reusando los 13 lemas de M4 |

⚠️ Vive en `sondeos/` **a propósito**: es un frente de varias sesiones y no debe mover el
contador de jobs ni los controles de proyección hasta estar completo.

**Controles:** `check-doc-sync` (`[H]` **78/78**) · RPP **145 jobs**, 0 errores.
⚠️ **ÁMBITO**: FOL no se tocó.

**Véase también:** ADR-085 (M1–M4 y el orden), ADR-083 (`ModelG`),
`Meta/CodeNatInjPrf.lean`, `Peano/PeanoNat/Sqrt.lean`.

---

## ADR-087: 🏁 la capa ARITMÉTICA del modelo, COMPLETA — **25 de los 34**, y el molde no falló ni una vez

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`sondeos/ModeloNat.lean`) · ⬜ los 9 de listas + los 107
**Contexto**: continuación directa de ADR-086.

### 1 · 🏁 El molde de M2 **escaló sin excepciones**

**25 de los 34 `coreAxioms` validados**, todos **net-0** (`[propext]` o `+ Quot.sound`). Los
veinticinco tienen la **misma forma**: `intro` de los binders, un `simp` que abre la evaluación,
y un `Nat.*` del core o un `omega` para rematar.

⭐ **Ni un solo axioma pidió una idea nueva.** Eso es lo que M2 (ADR-085) predijo sobre una
muestra de uno; aquí queda confirmado sobre veinticinco, incluyendo los que parecían distintos:
la conmutatividad y la asociatividad (`Nat.mul_comm`/`Nat.mul_assoc`), la paridad (`omega`
conoce `/2` y `%2` **por literales**), el monus, la potencia y el **orden**.

⚠️ `ax13_lt_def` merece nota aparte: **define `<` por un `∃`**, así que validarlo no es rutina —
es comprobar que la relación que el modelo eligió (`a < b` de `Nat`) es **la que el axioma
exige**, y no una cualquiera que case con los demás.

### 2 · ⚠️ Las dos únicas piedras, y las dos fueron de FORMA

1. **`⇔` es `FOL.iff`, un `def`, y `simp` NO lo atraviesa** si no se le nombra. Y no vive en el
   namespace `FOL`: va como **`_root_.iff`**. Fallaron **exactamente** los dos axiomas que
   **definen** algo —`ax16` (paridad) y `ax13` (orden)—, que son justo los que usan `⇔`.
   🔑 *El conectivo que no se reduce es el que aparece en los axiomas que DEFINEN, no en los que
   calculan.*
2. En `ax13`, `simp` convierte el `∃k` del **antecedente** de una implicación en un `∀k`. Se
   introduce **como tal** (`intro k hk`), no con `⟨k, hk⟩`.

### 3 · ⚠️ Y la reincidente, por tercera vez: el linter de `simp`

Quitar los argumentos que el linter marca «no usado» **rompió** `v_ax25` (el único de los
veinticinco que no es un `forall_`, así que sin el nombre del axioma no hay nada que abrir). El
fichero lleva ahora `set_option linter.unusedSimpArgs false` **con la razón escrita al lado**, y
precedente en `Meta/AxiomListCode.lean:15`.

🔑 **Un aviso de «no usado» es una hipótesis, no una medición.** Van tres veces en esta sesión.

### 4 · 📐 Lo que queda del modelo, y ya no es aritmética

Los **9** que faltan de los 34 son **exactamente la capa de listas**: `ax_L0_cons_def`,
`ax_L1_in_nil`, `ax_L2_in_cons`, `ax_C1`–`ax_C3` (concat), `ax_L3_in_concat`, `ax_prodp_nil` y
`ax_prodp_cons`.

⭐ Y esa capa **es la que abre los 107**: necesita `concatN`, `InN` y `prodpN` sobre `Nat`,
definidos por recursión sobre la lista **decodificada** — que es la misma técnica
(*decodificar → función de Lean → recodificar*) con la que se interpretarán los axiomas de
codificación. `consN` y **`consN_inj`** ya están (ADR-086).

⬜ Y ahí es donde el transporte desde Peano puede pagar de verdad:
`Peano/PeanoNat/Foundation/GodelBeta.lean`.

**Controles:** `check-doc-sync` (`[H]` **78/78**) · RPP **145 jobs**. ⚠️ **ÁMBITO**: FOL intacto;
el sondeo está fuera del build a propósito.

**Véase también:** ADR-086 (la capa aritmética arranca), ADR-085 §5 (el orden del frente).

---

## ADR-088: ⛔⛔ **ℕ no es modelo de `Prf`** — la capa de listas se para antes de empezar

**Fecha**: 2026-09-22
**Estado**: 📏 MEDIDO Y COMPILADO (`sondeos/ModeloBasura.lean`) · ⛔ **decisión del propietario**
**Contexto**: cerrada la capa aritmética (ADR-087), tocaba la de listas. Se midió **antes** de
escribirla si el dominio ℕ era el correcto. No lo es.

### 1 · El dato, compilado

`ax_L0_cons_def` **obliga** a interpretar `cons a b` como `pair a (σb) = cantor_func a (b+1)`, y
`nil` es `zero = 0`. Con `+`, `*` y `div2` estándar —que los demás core fuerzan— eso es
exactamente `consN` de `Meta/CodeNumeralPrf.lean:65`.

La imagen de `cons` es `{cantor(x,y) : y ≥ 1}`, que **deja fuera los números triangulares**.
⇒ **el 1 no es ni `nil` ni un `cons`**, y está probado abajo, no argumentado.

### 2 · ⛔⛔ La consecuencia

`Prf` tiene `listInd (A) : Prf (listInductionFormula A)`, y con **Φ := «es `nil` o es un `cons`»**
—una fórmula del lenguaje— el esquema tiene **base verdadera, paso verdadero y conclusión FALSA**
en ℕ (falla en `1`).

⇒ **`Prf` no es sólido respecto del modelo estándar de la aritmética**, y la ruta
«modelo en ℕ ⇒ `¬ Prf ⊥` ⇒ `ConsistentH`» **no funciona tal cual**.

🔑 **Un esquema de inducción sobre una clase que el lenguaje no sabe separar cuantifica sobre
TODO el dominio — y entonces habla de lo que no debería.**

### 3 · ⚠️ Lo que esto **NO** dice, y hay que decirlo con cuidado

* **No dice que `Prf` sea inconsistente.** Dice que **ℕ no está entre sus modelos**. Un cálculo
  puede ser consistente y no tener a ℕ por modelo.
* **No es un error en ninguna prueba del árbol.** Todo lo que RPP demuestra sigue siendo teorema
  de `Prf`; lo que cambia es qué estructuras lo satisfacen.
* **No es un fallo de la aritmetización**: `listInd` está para razonar sobre **códigos**, y sobre
  códigos la inducción es legítima. Lo que falla es que el lenguaje no separa los códigos del
  resto del dominio.

⚠️ Y sí conviene subrayar una cosa: `ax_list_induction` es **uno de los 3 `axiom` de Lean** del
proyecto — un **postulado**. Esta medición dice que ese postulado es **falso en ℕ**. No lo
invalida (el propietario puede querer justamente esa fuerza), pero **deja de ser inocuo**, y
`AXIOMS.md` debería decirlo.

### 4 · 📏 El coste de la salida que parece buena

De las cuatro salidas posibles —dominio distinto, relativizar `listInd`, renunciar al modelo
estándar, o comprobar que las instancias ya llevan guarda— la única que conserva **a la vez** la
aritmética y la codificación es **relativizar `listInd`** con una guarda de buena formación.

**Medido: `prf_list_induction` se consume en 42 sitios** del árbol. Ése es el tamaño de esa
salida. ⬜ Lo que **no** está medido es cuántos de los 42 ya tienen la guarda por otra vía, y ésa
es la medición que decide — no la cotizo.

### 5 · ⭐ Por qué esto es un buen resultado, y no un revés

Se midió **antes** de escribir los 9 axiomas de la capa de listas. Si se hubieran escrito
primero, habrían compilado igual —son ciertos en ℕ, uno a uno— y el problema habría aparecido
**al intentar la solidez de `Prf`**, con la capa entera ya construida sobre un dominio
equivocado.

🔑 *La pregunta «¿es éste el dominio correcto?» no se contesta validando axiomas uno a uno: se
contesta buscando un elemento que sobre.*

**Controles:** `check-doc-sync` (`[H]` **79/79**) · RPP **145 jobs**. ⚠️ **ÁMBITO**: FOL intacto.

**Véase también:** ADR-087 (la capa aritmética), ADR-085 §5 (el orden del frente, que esto
reordena), `Meta/CodeNumeralPrf.lean:65`, `Meta/ChainPrf.lean:29`.

---

## ADR-089: 🏁 EL REPARTO — **son SEIS ramas, no veintiuna**

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §5) · ⬜ el `match` que las enhebra
**Contexto**: lo único que le quedaba a `DEUDA_chainNeg` tras ADR-076…082.

### 1 · ⭐⭐ La sorpresa: el reparto casi no depende del tag

El `dispatcher` (ADR-078) entrega **siempre la misma tupla**, y cada causa la consume de **una**
forma. Lo que cambia de un tag a otro no es la estructura de la rama: es **qué entrada de la
tabla se le pasa**.

| rama | qué le queda por tag |
|---|---|
| (a) `rama_tag_grande` | ⭐ **nada** — ni menciona el tag |
| (b) `rama_aridad` | el `prf_lenc_*` — los **21** están |
| (c′) `rama_concl` | el `TagCode` — los **19** están |
| (d) `rama_thy` | ⭐ **nada** |
| (e) `mp`/`gen` | ⭐ **nada**: `derives_chainOk_neg_mp_major`/`_minor`/`_gen` **ya son** la rama |
| (f) `rama_tipo_*` | el refutador de `Meta/CodeDistinct.lean` |

🔑 **El reparto no es un `case` de veintiuna ramas: es un `case` de seis, con una TABLA dentro.**
Y eso es exactamente lo que compró la **inversión de `StdArgs`** (ADR-082): el análisis por tag se
hace **destruyendo**, no razonando. El `rw [stdArgs_objList hargs]` de `rama_concl` es el punto
donde se ve.

⬜ Queda el `match` sobre `tag` que elige rama y pasa la entrada. **Sin incógnitas**: las seis
ramas compilan y el split de 21 está medido en 4,5 s.

**Controles:** `check-footprints` **431** (cobertura **396/396**) · RPP **145 jobs**.

---

## ADR-090: ⛔⛔ relativizar `listInd` **NO es barato** — toca los activos del núcleo

**Fecha**: 2026-09-22
**Estado**: 📏 MEDIDO (censo con 8 agentes, **lectura**, no compilación) · ⛔ decisión del propietario
**Contexto**: ADR-088 dejó cuatro salidas y dijo que la medición que decide es «¿cuántas
instancias de `listInd` ya llevan guarda?». Ésta es esa medición.

### 1 · ⚠️ Primero, la cifra se movió — **otra vez**

Mi `grep` había dicho **42**. Contando sólo **usos reales** (no menciones en docstring ni
apariciones del tipo `listInductionFormula`): **21**. Es la **tercera** cifra que se corrige hoy
al medirla bien (ADR-084 tenía las otras dos).
🔑 *Un `grep` cuenta apariciones; un censo cuenta usos.*

### 2 · 📏 El reparto de los 21

| | nº |
|---|---|
| con guarda de buena formación (vacuas sobre basura) | **7** |
| **SIN guarda** | **13** |
| dudoso | 1 |

⛔⛔ **Y los 13 sin guarda incluyen los activos**:

* **`prf_chainOk_iff_chainOkB`** — *el* asset reutilizable de toda la vía (e)/Δ₀. Es un
  bicondicional incondicional, y ⭐ sobre basura el lado Δ₀ (`∀ i < lenc p …`) es **vacuamente
  cierto**, así que la Φ **obliga** a `chainOk c basura`.
* **`prf_nil_or_cons_all`** — literalmente la Φ del contraejemplo de ADR-088, confirmada por una
  lectura independiente que no sabía que la buscaba.
* `prf_concat_assoc`, `prf_concat_nil_right`, `prf_runFn_concat`, `prf_runFn_weaken`,
  `prf_chainOk_concat`, `prf_lenc_runFn`, `prf_allIn_of_boundedAllIn`, `prf_lenc_liftsc_all`,
  `prf_eval_lenc_all`, `prf_In_mono_imp`, y el propio envoltorio `prf_list_induction`.

### 3 · ⇒ La salida (2) de ADR-088 **se encarece**

Relativizar `listInd` con una guarda obliga a **re-enunciar 13 teoremas**, y entre ellos el que
sostiene la forma Δ₀ entera. No es una tanda mecánica: es rediseñar la capa de cadenas.

⚠️ **ÁMBITO de esta medición**: es una **lectura** de ocho agentes, no una compilación. La
clasificación «¿tiene antecedente que la haga vacua sobre basura?» es una pregunta de lectura y
está dentro de su competencia, pero **ninguna de las 13 está verificada por el compilador**.
🔑 *Los agentes miden bien y estiman mal porque no compilan; esto es medición, pero de LECTURA.*

⬜ **Queda abierto** —y es del propietario— cuál de las cuatro salidas de ADR-088 se toma. Lo que
esta entrada aporta es que **(2) ya no es la barata**.

**Véase también:** ADR-088 (ℕ no es modelo de `Prf`), `sondeos/ModeloBasura.lean`.

---

## ADR-091: ⭐⭐ los 21 tags sólo tienen **SEIS FORMAS** de argumentos

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §5, cuatro de las seis) · ⬜ `[F,F,F]` y `[F,T,T]`
**Contexto**: el `match` que enhebra las seis ramas de ADR-089.

`decodeRuleTag` distingue veintiún tags, pero sus **listas de argumentos** sólo tienen seis
formas: `[F]` (6 tags), `[T]` (1), `[F,F]` (**8**), `[F,F,F]` (2), `[F,T]` (2), `[F,T,T]` (1), más
`thy` (15) que **no mira los argumentos**.

⭐ Y cada dicotomía toma **como hipótesis** el hecho «con esta forma, el tag decodifica» —que por
tag es un `rfl`—, así que son **seis lemas y veintiuna instancias de una línea**, no veintiún
lemas. Las cuatro más pobladas (17 de los 21 tags) están aterrizadas y son **net-0**.

🔑 **Cuando un `case` de N ramas se repite, mira si las ramas no serán M FORMAS con N instancias.**
Es la misma jugada que ADR-089 («seis ramas, no veintiuna»), un nivel más abajo.

**Controles:** `check-footprints` **433** (cobertura **398/398**) · RPP **145 jobs**.

---

## ADR-092: ⛔ el modelo de TÉRMINOS es **CIRCULAR** — y aparece una salida que no había

**Fecha**: 2026-09-22
**Estado**: 📏 MEDIDO · ⛔ decisión del propietario
**Contexto**: ADR-090 dejó la salida (2) cara. Yo había recomendado la (3), «buscar la
consistencia por un modelo de términos». **Esta entrada me corrige.**

### 1 · ⛔ La (3) no vale, y es estructural

Medido en `FOL/Canonical0.lean`: **toda** la construcción del modelo canónico toma
`IsMaximalConsistent₀ S` como hipótesis — empezando por `termSetoid`, que lo necesita ya sólo
**para que `termEqv` sea una relación de equivalencia** (`termEqv_refl/_symm/_trans`, l. 162-176).

⇒ El modelo de términos es la dirección **«consistente ⇒ tiene modelo»** de la completitud.
Usarlo para **probar** la consistencia es **circular**.
🔑 *Un modelo canónico no da consistencia: la consume.*
⚠️ Y la recomendación que yo di sin medirla era ésa. Van las que van.

### 2 · ⭐⭐ La salida que no había considerado: **cambiar UN axioma**

La basura de ADR-088 existe porque `ax_L0_cons_def` dice `cons a b = pair a (σb)`, y
`λ a b. cantor(a, b+1)` **se deja fuera los triangulares**. Pero el `σ` sólo está ahí para que
`cons h t ≠ nil`. Póngase **fuera**:

    cons a b = σ (pair a b)

`pair` es una **biyección** ℕ²→ℕ, luego `σ ∘ pair` es una biyección **ℕ² → ℕ≥1**, y `nil = 0` no
está en la imagen. ⇒ **todo número es `nil` o un `cons`, y la basura desaparece.** La inducción de
listas pasa a ser **verdadera en ℕ**, y `carc`/`cdrc` a ser inversas **totales**.

⚠️ Y la monotonía que sostiene la recursión sobre códigos **sobrevive**: `σ(pair h t) ≥ t+1 > t`
igual que antes.

### 3 · 📏 El radio, medido

| | |
|---|---|
| `ax_L0_cons_def` | **18 menciones**, ~**5 consumidores reales** (`prf_cons_def`, la instancia codificada de `DotConsPrf`, dos usos en `Block6`, las listas de axiomas) |
| `consN` (el espejo numérico) | **5 ficheros, 86 ocurrencias** |

⇒ Comparado con la salida (2) —**13 teoremas de carga**, entre ellos `prf_chainOk_iff_chainOkB`,
que sostiene la forma Δ₀ entera— esto es **más pequeño y más localizado**.

### 4 · ⛔ Pero es un cambio en el SISTEMA DE AXIOMAS, y eso no lo decido yo

Cambiar `ax_L0_cons_def` **cambia la codificación**, y con ella **`G`**. Los puentes que hoy
cierran por `rfl` sobre la forma numérica habría que **re-verificarlos uno a uno** — el mismo
aviso que ya está escrito para la migración de `String`.

⬜ **Decisión del propietario.** Lo que esta entrada aporta es que la baraja ya no es
«(2) caro vs (3) imposible»: hay una **(5)** medida y más barata que la (2).

**Véase también:** ADR-088 (la basura), ADR-090 (el coste de (2)), `FOL/Canonical0.lean:162`.

---

## ADR-093: ⭐⭐ **CÓMO se corrige la basura** — sacando el `σ` fuera, y está MEDIDO

**Fecha**: 2026-09-22
**Estado**: 📏 MEDIDO Y COMPILADO (`sondeos/CantorSobreyectivo.lean`) · ⛔ decisión del propietario
**Contexto**: ADR-092 §2 apuntó la salida (5) pero no la verificó. Ésta la verifica.

### 1 · La corrección, y por qué funciona

`ax_L0_cons_def` dice `cons a b = pair a (σb)`. El `σ` sólo está para que `cons h t ≠ nil`.
**Sáquese fuera**: `cons a b = σ (pair a b)`.

| | probado |
|---|---|
| El Cantor **pelado** es **sobreyectivo** sobre ℕ | `cantorN_surj`, **net-0 puro** |
| ⇒ `σ ∘ pair` es **biyección ℕ² → ℕ≥1**, con `nil = 0` fuera de la imagen | |
| ⇒ **todo número es `nil` o un `cons`** | `sin_basura`, net-0 |
| ⇒ la **inducción de listas es verdadera en ℕ**, y `carc`/`cdrc` son inversas **totales** | |

⚠️ **Y el riesgo obvio no se materializa**: mover el `σ` podía romper la monotonía que hace
terminar toda recursión sobre códigos. Medido (`cola_decrece`): la cola sigue siendo
**estrictamente menor** que el `cons`. 🔑 *El riesgo evidente de un cambio se mide, no se teme.*

### 2 · 📏 Comparado con la otra salida

| salida | coste medido |
|---|---|
| (2) relativizar `listInd` | **13 teoremas de carga**, incluido `prf_chainOk_iff_chainOkB`, que sostiene la forma Δ₀ entera (ADR-090) |
| (3) modelo de términos | ⛔ **circular** (ADR-092 §1) |
| **(5) sacar el `σ`** | `ax_L0_cons_def`: 18 menciones / ~**5 consumidores**; `consN`: **5 ficheros, 86 ocurrencias** |

⇒ (5) es **la más pequeña y la más localizada** de las tres.

### 3 · ⛔ Lo que esto **no** decide

Cambiar `ax_L0_cons_def` **cambia la codificación**, y con ella **`G`**. Los puentes que hoy
cierran por `rfl` sobre la forma numérica habría que **re-verificarlos uno a uno** — el mismo
aviso que ya está escrito para la migración de `String`. **Es una decisión sobre el sistema de
axiomas, y es del propietario.**

🔑 *Lo que un sondeo puede hacer es quitarle a la decisión la parte de adivinar: el «funciona» ya
no es una opinión.*

**Véase también:** ADR-088 (la basura), ADR-090 (el coste de (2)), ADR-092 (la circularidad
de (3)), `sondeos/CantorSobreyectivo.lean`.

---

## ADR-094: 🏁 **el cierre de UN tag, de punta a punta** — y el coste por tag queda MEDIDO

**Fecha**: 2026-09-22
**Estado**: ✅ ATERRIZADO (`ChainNegPrf` §5, `cierra_tag0`) · ⬜ 17 tags estructurales + 15/16/17
**Contexto**: el ensamblado del `match`, tras ADR-089 (seis ramas) y ADR-091 (seis formas).

### 1 · 🏁 Qué es `cierra_tag0`

Va de la **tupla que entrega `dispatcher`** hasta `axioms ⊢ neg (chainOk nil ⟦l⟧)`, cubriendo
**las tres causas que un tag estructural puede disparar**: (b) aridad, (f) tipo y (c′) conclusión.
Es el único sitio donde la máquina entera funciona junta, y por eso **mide** el coste por tag.

**~40 líneas** para el tag, más lo que hizo falta de nuevo:

| pieza nueva | alcance |
|---|---|
| `decodeForm_termCode` / `decodeTerm_formCode` | ⭐ **compartidas por los dieciocho** |
| `neg_p1_slot2` | propia del tag — es lo único que se repite |

### 2 · ⭐ El descubrimiento: los refutadores de (f) se COMPONEN

La ranura 2 de `p1` reconstruye `implc a (implc (termCode u) a)`. No hizo falta un lema base
nuevo: `neg_p1_slot2` es **`formCode_ne_implc_tc_1` bajo dos `cons_ne_tail`**.

🔑 **El refutador de una ranura profunda se compone del de la ranura de fuera, un nivel más
adentro.** ⇒ (f) no necesita un lema base por ranura: necesita un **ensamblaje** por tag, y la
base (`Meta/CodeDistinct.lean`, ADR-081) ya está completa.

### 3 · ⚠️ Y una pieza que faltaba y nadie había echado en falta

`decodeForm` mira los tags **2..9** y `termCode` usa **0/1** — disjuntos. Que
`decodeForm (termCode t) = none` es **evidente y no estaba probado** en ningún sitio. Es el
gemelo, del lado del **decodificador**, de `formCode_ne_termCode` (ADR-081), que sí estaba.

🔑 *Una simetría a medio construir no se nota hasta que se necesita el otro lado.*

### 4 · 📐 Lo que queda del ensamblado, ya con números

| | |
|---|---|
| tags estructurales cerrados | **1 de 18** (`cierra_tag0`) |
| tags estructurales pendientes | **17**, misma plantilla, cambiando `decodes_*`, `prf_lenc_*`, `TagCode` y el ensamblaje de (f) |
| tags de contexto | **3** (15 `thy`, 16 `mp`, 17 `gen`) → rutas (d) y (e), **ya cerradas** (ADR-076/077) |
| el `match` final | ⬜ 21 llamadas de una línea, una vez estén los 21 cierres |

⚠️ **No cotizo las 17.** Lo que sí está medido es que la plantilla **funciona entera** y que lo
único que se repite por tag es el ensamblaje de (f).

**Controles:** `check-footprints` **438** (cobertura **403/403**) · `check-doc-sync` ·
`check-sorry` + censo · `check-estratos` **10** · `check-warnings` **11** · RPP **145 jobs**.
⚠️ **ÁMBITO**: FOL intacto.

**Véase también:** ADR-089 (las seis ramas), ADR-091 (las seis formas), ADR-081 (los refutadores
de (f)).

---

## ADR-095: 🏁 la forma `[F,F]` COMPLETA — un refutador para ~32 ranuras y un cierre por FORMA

**Fecha:** 2026-09-22 · **Estado:** ACEPTADO · **Ámbito:** RPP (`Meta/CodeDistinct.lean`,
`Meta/ChainNegPrf.lean`). FOL intacto.

### Contexto

ADR-094 cerró **un** tag de punta a punta (`cierra_tag0`, ~40 líneas) y dejó **17** con la misma
plantilla. La cotización honesta de entonces fue *«no cotizo las 17»*. Esta entrada las ataca en
tanda y mide **qué parte de esas 40 líneas era realmente por tag**.

### 1 · ⭐⭐⭐ `NotFC` — UN refutador donde había ~32

El caso (f) —tipo de argumento equivocado— pide, por cada ranura de cada tag, un
`axioms ⊢ neg (formCode f =eq <reconstrucción con un termCode dentro>)`. Con 18 tags
estructurales y 1–3 ranuras cada uno son **~32 obligaciones**, cada una con su ensamblaje de
`cons_ne_tail`/`cons_ne_head` a la profundidad que toque (ADR-094, §2).

⇒ Se sustituyen por **un inductivo y un teorema**, en `Meta/CodeDistinct.lean`:

```lean
inductive NotFC : Term → Prop
  | tc (u : Term) : NotFC (termCode u)
  | implcL {a} (b) : NotFC a → NotFC (implc a b)     -- y implcR, andcL/R, orcL/R
  | forallcI {a} : NotFC a → NotFC (forallc a)       -- y excI

theorem formCode_ne_notFC : ∀ {e}, NotFC e → ∀ f, axioms ⊢ neg (formCode f =eq e)
```

`NotFC e` = «`e` **no es el código de ninguna fórmula**, y se ve por su sintaxis». La inducción
es sobre `NotFC`, y cada constructor descarga con los refutadores base de ADR-081.

🔑 **Un ensamblaje que se repite con la misma FORMA a profundidades distintas es un
INDUCTIVO, no 32 lemas.** El refutador de la ranura profunda ya no se «compone a mano» (ADR-094):
se **deriva**, y la derivación es de una línea (`NotFC.implcR _ (NotFC.implcL _ (NotFC.tc u))`).

⚠️ **Límite MEDIDO, no estimado**: de las ~32 ranuras, **tres** caen dentro de `substfc` —el
argumento de término de los tags 9 (`q1`) y 10 (`q2`), y el de fórmula del 13 (`leibniz`)— y ésas
**no se refutan por la sintaxis**, porque `substfc` es un símbolo OBJETO que no reduce
([[feedback-simbolos-objeto-no-reducen]]). Ésas necesitan las guardas de ADR-020.

### 2 · ⭐⭐ `cierra_FF` — el cierre por FORMA, no por tag

De las ~40 líneas de `cierra_tag0`, **casi todas eran las mismas** para los ocho tags de forma
`[F,F]`. `cierra_FF` las toma como **ocho hipótesis de una línea** (`hdec`, `hlenc`, `hbadlen`,
`hbadty`, `hbadty2`, `hrecon`, `hnf1`/`hnf2`, `htc`, `hstep`) y hace el resto. Cada tag pasa a
ser **una instancia de ~15 líneas**, de las cuales las que razonan son **cero**.

🔑 *Primero se cierra UNO a mano para ver la máquina; luego se factoriza lo que no cambiaba.*
El orden inverso —factorizar antes de haber cerrado ninguno— produce abstracciones que no encajan
con ningún caso. `cierra_tag0` **se queda desplegado a propósito**: es el ejemplo que enseña qué
hay dentro, y **no se duplica** como instancia.

⚠️ `hbadlen` existe porque con el tag como **variable** `decodeRuleTag` **no reduce**. Por tag es
un `match` de cuatro ramas con tres `rfl`.

⭐ Y un dividendo que no se esperaba: los dos tags con `liftfc` (`q3`, `qconf`) **sí** salen por
`NotFC`, porque el argumento malo aparece **también** en una posición transparente.
🔑 *Un argumento que el esquema usa DOS veces sólo necesita UNA de las dos apariciones para ser
refutable.*

### 3 · ⚠️ La trampa: `export` trae el TIPO pero no sus CONSTRUCTORES

`export ... (NotFC formCode_ne_notFC)` compila, y luego `NotFC.implcL` es **constante
desconocida** en el consumidor. Hay que listar los **nueve** constructores uno a uno.

🔑 *Un `export` de un inductivo que no nombra los constructores exporta algo con lo que no se
puede construir nada.*

### 4 · 📐 Estado del ensamblado

| | |
|---|---|
| forma `[F,F]` | 🏁 **8 de 8** (tag 0 desplegado + 7 instancias) |
| formas pendientes | `[F]` (5 tags), `[F,F,F]` (2), `[T]` (1), `[F,T]` (2), `[F,T,T]` (1) |
| de ésas, refutables por `NotFC` | **todas menos tres ranuras** (§1) |
| tags de contexto | **3** (15/16/17) → (d) y (e), cerradas (ADR-076/077) |
| el `match` final | ⬜ |

**Coste medido de la tanda:** 7 tags = 7 `badlen_*` + 7 instancias, **ninguna con razonamiento
nuevo**. La forma `[F,F]` es la más poblada de las seis.

**Controles:** `check-footprints` **442** (cobertura **406/406**) · `check-doc-sync` ·
`check-sorry` + censo · `check-estratos` **10** · `check-warnings` **11** · RPP **145 jobs**.
⚠️ **ÁMBITO**: FOL intacto.

**Véase también:** ADR-094 (el tag desplegado), ADR-091 (las seis formas), ADR-081 (los
refutadores base), ADR-020 (las guardas de `substfc`).

---

## ADR-096: 🏁 los DIECIOCHO tags estructurales, cerrados — y `NotTC`, la mitad que faltaba

**Fecha:** 2026-09-22 · **Estado:** ACEPTADO · **Ámbito:** RPP (`Meta/CodeDistinct.lean`,
`Meta/ReprPrf.lean`, `Meta/ChainNegPrf.lean`). FOL intacto.

### Contexto

ADR-095 cerró la forma `[F,F]` (8 tags) y dejó **diez**: `[F]` (4), `[F,F,F]` (2), `[T]` (1),
`[F,T]` (2), `[F,T,T]` (1). Los tres últimos tenían el límite **medido** de `NotFC`: tres ranuras
caen dentro de `substfc` y no se refutan por la sintaxis.

### 1 · ⭐ Las formas `[F]`, `[F,F,F]` y `[T]` — sin sorpresa, con un dividendo

`cierra_F` (4 instancias: 8 `efq`, 14 `p3`, 18 `ind`, 20 `listInd`) y `cierra_FFF` (2: 1 `p2`,
7 `j3`), mismo molde que `cierra_FF`. El tag 12 (`eqrefl`, forma `[T]`) **no se factoriza**: un
cierre genérico con una sola instancia no es abstracción, es indirección.

⭐⭐ Y el dividendo: los tags **18 y 20** meten su único argumento dentro de un `substfc` en la
primera aparición… y **salen igual por `NotFC`**, porque el esquema lo usa **también** en el
`forallc` final. 🔑 *Un argumento que el esquema usa dos veces sólo necesita UNA aparición
transparente.* Lo que en `q3`/`qconf` parecía un accidente de dos tags resulta ser **la mitad de
la forma `[F]`**.

### 2 · ⭐⭐ `NotTC` — (f) tiene DOS direcciones, y sólo había una

`NotFC` dice «no es código de fórmula». Los tags 12 y 13 necesitan la contraria: un `formCode`
donde va un código de TÉRMINO. ⇒ `NotTC` (un constructor, `fc`) más dos constructoras de `NotFC`:

```lean
| eqcL {a} (b) : NotTC a → NotFC (eqc a b)
| eqcR (a) {b} : NotTC b → NotFC (eqc a b)
```

`eqc` es la **única** constructora transparente que abre un hueco de término. Con eso, las dos
ranuras de término del tag 13 (`eqc t₁ t₂`) salen por sintaxis y **no** piden guarda.

⚠️ `NotTC` tiene **una sola** constructora y eso es deliberado: es lo que hace falta, **medido**.

### 3 · ⭐⭐⭐ Las tres ranuras OPACAS — las cierra la GUARDA de ADR-020

Ranuras: argumento de TÉRMINO de los tags 9 (`q1`) y 10 (`q2`), y de FÓRMULA del 13 (`leibniz`).

🔑 **La ranura que no se puede refutar por la forma es, por construcción, la que el esquema tuvo
que guardar.** No es coincidencia: `substfc` no se evalúa sin buena formación, así que la
opacidad y la guarda **tienen la misma causa**. ADR-020 metió `hasWitF`/`hasWit` dentro de
`lineWF` por la fidelidad de la reconstrucción; sirven aquí sin tocar nada.

Y los dos refutadores de la guarda salen **baratos**, porque los reconocedores son ecuacionales:

| refutador | el reconocedor es | coste |
|---|---|---|
| `neg_hasWit_formCode` | `isTermCodeE1` = **2** formas, cabezas 0 y 1 | 2 `formCode_ne_cons_of_tag` |
| `neg_hasWitF_termCode` | `isFormCodeE2` = **8** formas, cabezas 2…9 | 8 `termCode_ne_cons_of_tag` |

⭐ Las piezas de enganche **ya estaban**: `prf_isTermCodeE1_of_In`, `prf_isFormCodeE2_of_In`,
`substF_isTC1`, `substF_isFC1`. Lo nuevo son tres **proyecciones** de la guarda en `ReprPrf.lean`
(`prf_lineWF_q1_hasWit`, `_q2_hasWit`, `_leibniz_hasWitF`), gemelas de los `prf_lineWF_*_imp` y
con el mismo cuerpo salvo **qué conjunto se proyecta**; y `termTag`/`termCode_ne_cons_of_tag`, el
espejo exacto de `formTag`/`formCode_ne_cons_of_tag`.

Van **trece** de «antes de construir, buscar» — [[feedback-antes-de-construir-buscar]].

### 4 · ⚠️ Dos trampas

* **`decide` exige un objetivo CERRADO**: `by cases B <;> decide` falla con
  *«Expected type must not contain free variables»* en los constructores con argumentos
  (`formTag (.atom p ts) ≠ 0` conserva `p`, `ts`). Sale con `simp [formTag]`, que **reduce
  antes**.
* **Un lema puede existir y no estar en el ámbito**: `liftTerm_termCode` está en
  `Meta/DerivCondPrf.lean`, sin `export`, y ese módulo no llega. La salida es el puente
  `termCodeM_eq` + `liftTerm_termCodeM`, dos líneas.

**Controles:** `check-footprints` **457** (cobertura **421/421**) · el resto verde · 145 jobs.

---

## ADR-097: 🏁🏁🏁🏁 `DEUDA_chainNeg` SALDADA y **`NegVerifier` PROBADO**

**Fecha:** 2026-09-22 · **Estado:** ACEPTADO · **Ámbito:** RPP (`Meta/ChainNegPrf.lean` §6).
FOL intacto.

### El resultado

```lean
theorem deuda_chainNeg_proved : DEUDA_chainNeg
theorem negVerifier_proved : NegVerifier
```

`Meta/VerifierSound.lean` (2026-09-10h) dejó `NegVerifier` reducido a **dos obligaciones con
nombre y firma**. `deuda_inNeg` se pagó el 2026-09-21; `deuda_chainNeg_proved` la cierra hoy, y
`negVerifier_of_deudas` las junta. ⇒ **`NegVerifier` deja de ser hipótesis.**

⚠️ **ÁMBITO (M-13)**: lo que cae es `NegVerifier`, **no** la ω-consistencia. `reflects_of_omega`
tomaba **dos** hipótesis y ahora toma **una** (`OmegaConsistent`). Y `StdChain` sigue estrechada
(ADR-022), escrito en el enunciado.

**Footprint de `negVerifier_proved`** (medido, no estimado): `propext, Classical.choice,
Quot.sound, ex_elim, imp_intro, or_elim, raa, ax_induction_prim, ax_list_induction,
ax_axiomsCodeT_eq`. **Ningún axioma nuevo**: los tres de RPP son los sancionados.

### 1 · ⭐⭐ Los tres tags de CONTEXTO no tenían cierre, sólo piezas

Los dieciocho estructurales estaban (ADR-094/095/096); 15/16/17 tenían las rutas (d) y (e)
**sueltas**. Lo que faltaba era repartir su propio `hcase`:

| tag | lo que tenía | lo que faltaba |
|---|---|---|
| 15 `thy` | `rama_thy`, que pide la línea con `nil` EXPLÍCITO | el caso `args ≠ []` ⇒ (b) aridad, y cerrar el `Or.inr` |
| 16 `mp` | las dos instancias de (e), con la premisa YA identificada | leer `findIdx` para saber CUÁL falta, y el caso de tipo |
| 17 `gen` | la instancia de (e) | ídem, más **(c′)** |

⭐ **`thy` y `mp` no pueden fallar por (c′)**, y eso lo dice `findIdx_sound`: si el decodificador
devuelve índice, ahí está lo que buscaba, luego `stepConcl = some f`. `gen` **sí** puede: `∀g` no
tiene por qué ser `f`. 🔑 *Qué causas puede disparar un tag no se elige: lo dicta el decodificador.*

### 2 · ⭐⭐⭐ El dividendo que no estaba previsto: `NotFC` sirve a DOS vías

`ax_lineWF_mp` **no dice nada de la forma del argumento** (sólo `lenc = 3`), así que una línea
`mp` con un `termCode` donde va una fórmula es **bien formada**. Parecía un agujero. No lo es:
su premisa mayor es `↑u ⇒ ⌜f⌝`, que **no es el código de ninguna fórmula**, luego ninguna línea
anterior la concluye ⇒ cae por la vía de las **PREMISAS**.

🔑 *El mismo refutador sirve a dos vías distintas porque lo que refuta es un HECHO SOBRE CÓDIGOS,
no sobre `lineWF`.* Costó dos lemas: `derives_not_boundedCarcLt_of_notFC` (gemelo de
`_of_not_mem`, con `NotFC` en vez de `φ ∉ L`) y `derives_chainOk_neg_of_prem_at` — que es
`derives_chainOk_neg_of_prem_code` **generalizado en el sitio**: la premisa mala no tiene por qué
ser un `formCode`.

### 3 · 🏁 El `match`: veintiún tags, veintiuna líneas

`cierra_por_tag` es un `match` sobre `tag` por el compilador de ecuaciones; **cada rama es una
línea**, y `n+21` no menciona ningún tag. 🔑 *Un `match` de 21 ramas cuyas ramas son todas de una
línea no es un `match` de 21 ramas: es una TABLA.* El coste del split estaba medido en 4,5 s
(ADR-078) y no dio sorpresas.

### 4 · ⚠️ La trampa de la tanda

`Option.noConfusion` **no ve a través de `Option.map`/`bind`**: `(none).map f = some r` no es
sintácticamente `none = some r`, así que hay que dejar que `simp` reduzca primero. Cinco veces en
el mismo bloque. ⭐ En cambio **sí** vale `have h2 : some (Rule.thy i) = some r := hr'`:
`Option.map` sobre `some` reduce por `rfl`, y ahí `injection` entra. 🔑 *Lo que `noConfusion` no
acepta por sintaxis, la ASCRIPCIÓN de tipo lo acepta por defeq.*

### 5 · 📐 El estado de la vía

| | |
|---|---|
| `DEUDA_inNeg` | 🏁 saldada (2026-09-21) |
| `DEUDA_chainNeg` | 🏁 **saldada** |
| `NegVerifier` | 🏁 **teorema** |
| `OmegaConsistent` | ⬜ sigue siendo **hipótesis** — es la única que queda en `reflects_of_omega` |

**Controles:** `check-footprints` **457** (**421/421**) · `check-doc-sync` · `check-sorry` +
censo · `check-estratos` **10** · `check-warnings` **11** (los 6 nuevos se **retiraron**, no se
declararon: el build siguió verde sin ellos) · RPP **145 jobs**.
⚠️ **ÁMBITO**: FOL intacto.

**Véase también:** ADR-022 (`StdChain` estrechada), ADR-076…081 (las seis causas), ADR-089 (las
seis ramas), ADR-091 (las seis formas), ADR-094/095/096 (los 18 tags).

---

## ADR-098: ⛔⛔ la propiedad de disyunción para `Derives₀` es **FALSA** — y la que se quería **ya estaba probada**

**Fecha:** 2026-09-23 · **Estado:** 📏 MEDIDO Y COMPILADO · **Ámbito:** FOL (medición) + PeanoRF (lectura).

### Contexto

El propietario decidió ir a por la **propiedad de disyunción** como último resultado antes de
congelar FOL. Antes de construir nada se verificó el objetivo. No sobrevivió.

### 1 · ⛔⛔ El objetivo, como estaba enunciado, es FALSO

`Derives₀` es deducción natural **CLÁSICA** — su cabecera lo dice (`FOL/Derives0.lean:95`) y
tiene `dne_rule`, `dne_schema` y `forall_not_ex_not` como **constructores**. La propiedad de
disyunción es la marca de lo **intuicionista**.

El contraejemplo estaba **partido en dos mitades del propio árbol**, a dos módulos de distancia:

| pieza | dónde | qué da |
|---|---|---|
| `derives0_em_ctx` | `FOL/Propositional0.lean:78` | `Δ ⊢₀ A ∨ ¬A`, finitario, por `dne_rule` |
| `derives0_not_complete` | `FOL/Soundness0.lean:235` | `∃A, ⊬₀ A ∧ ⊬₀ ¬A`, dos modelos sobre `Unit` |

Juntas: `[] ⊢₀ A ∨ ¬A` con **ninguno de los dos disyuntos derivable**. Compilado, **net‑0**,
cinco líneas de prueba.

🔑 Van **CATORCE** de «antes de construir, buscar», y ésta en su forma más cara: no es un lema
que se habría re‑derivado, es **la refutación del objetivo**, que se habría encontrado *después*
de abrir el frente.

### 2 · ⭐⭐⭐ Y la propiedad que SÍ se quería ya estaba probada — en PeanoRF

`PeanoRF/Calculus/DerivesI.lean` define `Derivesᵢ` = **literalmente `Derives₀` menos los tres
constructores clásicos**, sobre nuestra `FOL.Formula`, importando nuestro `FOL.Derives0`, **con
`refl`, `subst` y `rewrite_at`**. Y `Slash.lean:899` prueba `disjunction_property` por la **barra
de Kleene**; `:930` la de existencia; `:964` la separación `⊢ᵢ ≠ ⊢₀` — **cuyo testigo es nuestro
`derives0_em_ctx`**. Cero `sorry`, cero `axiom` en los ocho ficheros (2 667 l.).

⇒ **QUINCE.** El trabajo estaba en el repositorio de al lado.

### 3 · ⛔⛔ Las dos rutas de construcción, medidas y cerradas

* **Ruta A (secuentes).** Restringir `LK₀` a succedente único **no se hereda** en `orR` (su
  premisa lleva **dos** fórmulas a la derecha; en LJ eso se parte en `orR1`/`orR2`, reglas
  *distintas*), `implL` y `struct` (contracción a la derecha, justo lo que lo hace clásico). Y
  mata **`LeftPrin`**, el dato que reduce el Hauptsatz de 5×14 casos a dos pasadas de 14.
  ⇒ `LJ₀` sería un inductivo nuevo con eliminación de corte nueva, del orden de las **1 256
  líneas** de `Hauptsatz0.lean`, **con cero reutilización**.
* **Ruta B (importar la de PeanoRF).** ⛔ **Imposible**: la cadena baja a `PeanoRF.Prelim`, que
  importa `ROBINSON_PlusPlus.Minimal.Axioms` y `Peano.PeanoNat.Axioms`. **La DP existe,
  compilada, y es inalcanzable desde FOL.**

### 4 · ⚠️ Una medida NUESTRA, rectificada

Se iba a decir a PeanoRF que `Subst.lean` «no es adoptable tal cual» porque `Prelim` importa RPP
y Peano. **La premisa sobre `Prelim` es cierta y la conclusión sobre `Subst.lean` es falsa**:
medido, su cuerpo (l. 54‑346) **no menciona ni un identificador de RPP ni de Peano**; todo lo
externo son 8 nombres del nivel raíz de `FOL/FOL.lean` más core de Lean 4.31, y el acoplamiento
con `Prelim` es **un `open FOL` vestigial**. Son **4 líneas**.

🔑 *Medir el acoplamiento de un módulo por el de su import no es medirlo.*

### 5 · ⇒ La propuesta (C), sancionada por el propietario

Que **`Subst.lean`, `DerivesI.lean` y `Slash.lean` bajen a FOL**: son sobre `FOL.Formula` y
`FOL.Derives0`, no sobre HA. ⭐ Y es barato por un dato medido: **el acoplamiento de toda esa
cadena con RPP y Peano es UNA SOLA LÍNEA** (`Collapse.lean:72`, `zero`).

⬜ Enviada como propuesta en `../FOL/RESPUESTA-PEANORF-2026-09-23.md`. **FOL no se sella hasta
que contesten.**

### 6 · ⚠️ Lo que NO se sigue, y lo escribe PeanoRF

`Slash.lean:845‑867`: son las propiedades de la **lógica `⊢ᵢ`**, **no las de HA** — barrar el
esquema de inducción es el caso difícil y no está hecho. Y el testigo de `existence_property` en
el caso `[]` **puede llevar variables libres**: es más débil que la propiedad de existencia de HA.

**Véase también:** ADR-050/052 (el Hauptsatz), `sondeos/` no aplica (esto se midió en solo lectura).

---

## ADR-099: 🏁 el CIERRE de FOL — (D)(B)(C), el encargo §3, la cuarentena vaciada y `folSystem` retirada

**Fecha:** 2026-09-23 · **Estado:** ✅ EJECUTADO · **Ámbito:** FOL. RPP sin cambios de código.

### 1 · (D) El rojo vivo

`REFERENCE.md` marcaba 2026‑09‑18 con su último commit el 2026‑09‑22 (ADR‑083, `ModelG`). El
**cuerpo sí estaba al día**; lo que faltaba era la marca. Lo cazó `[E]`.

### 2 · (B) NUEVE cabeceras que anunciaban ABIERTO lo probado al lado

| decía ⬜ | lo paga |
|---|---|
| `Herbrand0` (×3) | `Hauptsatz0.herbrand_extraction` / `BlockExtraction0` |
| `Derives1`, `Derives2`, `Propositional0`, `Sequent0` | `Hauptsatz0.cut_elimination` |
| `Prenex0` | `PrenexNF0` — que **refuta su propia estimación** de ~200 l. |
| `Skolem0` | `SkolemN0.skolem_conservative_n` (decía «**MEDIDO** que no existe nada de eso») |
| `Lindenbaum0` | `Canonical0` — era una **predicción cumplida** |
| `Rename` | `Eigenvariable.derives0_gen_fresh` |
| `Derives0` | los **tres** puntos de su hoja de ruta, hechos |

Todas corregidas **nombrando quién las paga**, y dejando el párrafo original como historial.

### 3 · (C) ⭐⭐ `[G.2]`, y el hueco MEDIDO de `[G.1]`

`[G.1]` (ADR‑072) sólo lee el docstring **pegado a un `def X : Prop`** y sólo acepta como pago un
`theorem X : X :=`. ⇒ no ve **(a)** la marca de deuda que vive en la cabecera `/-! … -/` del
módulo, ni **(b)** la deuda que paga **otro módulo entero**. Las dos clases estaban pobladas y
`[G.1]` estaba en **VERDE**.

`[G.2]` es el **censo** de marcadores con trinquete en los dos sentidos: cada uno se clasifica
como `ABIERTA` / `DIFERIDA` / `OFERTA` / `HISTORIAL`. **Probado rompiendo** en las tres
direcciones (marcador sin declarar · fila que ya no casa · ancla ambigua) y verde al restaurar.

🔑 *`[G.1]` comprueba que la deuda tiene TESTIGO; `[G.2]`, que ha sido MIRADA.*
⚠️ Y el recuento es el mismo que ADR‑072 midió al crear `[G.1]` (19 de 24): **sin trinquete, el
problema vuelve a crecer**.

### 4 · 🏁 El encargo §3 de PeanoRF

`FOL/Complexity.lean`: `formulaComplexity` y `complexity_substFormula` bajan de `Canonical0` §5 —
estaban detrás de toda la cadena clásica de completitud sin necesitarla. Footprint **`[propext]`**.

⛔ **Y un fallo de método, con nombre**: se verificó con `lake build` desde RPP y dio **VERDE sin
haber compilado el módulo** — RPP no importa `FOL.Canonical0`, así que su build no alcanza la capa
₀. El build de FOL es `lake build "@FOL/FOL" "@FOL/TheoryFramework"` desde la raíz de RPP.
🔑 *Un verde puede no ser haber comprobado* — [[feedback-build-cache]].

### 5 · (E) La cuarentena, VACIADA

| fichero | qué | por qué |
|---|---|---|
| `Soundness.lean`, `Compacity.lean`, `Theorems_Soundness.lean` | **BORRADOS** | teoremas FALSOS; sujetos reparados en `Soundness0`/`Compacity0` |
| `Completeness.lean` | **BORRADO** | superado por `Canonical0.completeness₀` |
| `Inconsistencia.lean` | ⭐ **SUBE AL BUILD** → `FOL/Inconsistencia.lean` | era la EVIDENCIA |

⚠️ **E2 no revierte ADR‑032**, que decidió que `henkin_extension_lemma` se quedaba: desaparece el
**módulo** que lo alojaba, superado por un teorema que no lo necesita. La decisión queda **sin
objeto**, no revocada. ⇒ el repositorio pasa a **4 `axiom` y ni uno más en ninguna parte**.

⭐⭐ **E3 es el que importa.** `Inconsistencia.lean` prueba que la solidez de `Derives` es falsa, y
vivía en un directorio que **no se compila** — que es lo que `cuarentena/README.md` §7 identifica
como la causa de que un `axiom` falso sobreviviera **ochenta días**. Footprint medido:
`[propext, FOL.MetaRules.raa]`. Seguro en la librería principal porque el teorema es
**CONDICIONAL**: `(solidez : …) → False`, no afirma `False`.

🔑 **Congelar un repositorio con su pieza de evidencia sin compilar es congelar una afirmación,
no un hecho.**

### 6 · (1) `folSystem`, RETIRADA

**Medido**: se declaraba **una vez** (`TheoryFramework/Instances/FOL.lean:77`) y **no la consumía
nadie en código** — las otras tres apariciones del nombre eran prosa. Declaraba
`derives := Derives`, el cálculo contaminado, y por eso `SoundLogic Formula` era **inhabitable** y
`CompleteLogic Formula` **no** la pagaba `completeness₀`.

⚠️ **El módulo se queda**, y a propósito: lo que vale de él es la cabecera que explica **por qué
no hay instancia** y la vía para reabrirlo (declararla sobre `Derives₀`, con lo que `SoundLogic`
la pagaría `derives0_soundness` y `CompleteLogic` la pagaría `completeness₀`).
🔑 *Borrar la explicación de una deuda es cómo la deuda sobrevive a su propio motivo.*

⬜ **Y queda una pregunta abierta que el propietario no ha contestado**: con `folSystem` retirada,
`TheoryFramework` (6 módulos, 456 l.) queda **sin ningún habitante y sin ningún consumidor**. Es
exactamente la forma que mandó `FOLPure`/`PropLogic`/`FOL_poli` a cuarentena. **No se ha tocado.**

### 7 · ⚠️ Hallazgo de proceso

`FOL/DECISIONS.md` lleva **dormido desde ADR‑010** mientras todas las decisiones de FOL van a
este fichero. Avisado en su cabecera. 🔑 *Un log de decisiones que nadie escribe no es un log
vacío: es un puntero falso* — la misma causa que congeló el `CHANGELOG` y con él el control `[E]`
(ADR‑072). Y con PeanoRF hay **colisión de numeración**: prefijos `RPP‑` / `PRF‑` desde hoy.

**Controles:** FOL `check-doc-sync` · `check-axioms` · `check-sorry` en verde. **FOL 56 jobs**
(54 → 55 módulos activos, 0 en cuarentena). RPP 145 jobs, sin cambios.

## ADR-100: 🏁 el CIERRE de FOL, la tarde — seis teoremas, cuatro decisiones y una política de congelación POR FICHERO

**Fecha:** decisiones 2026-09-23 (tarde) · ejecución 2026-09-23 y 2026-09-26 · **Estado:** ✅ EJECUTADO
salvo lo marcado ⬜ · **Ámbito:** FOL. RPP: las 14 filas de `check-footprints.bash` del 2026‑09‑23 y
las 14 del 2026‑09‑26, y el arreglo de `git-lock.bash`.

### 1 · Las decisiones del propietario (2026-09-23, tarde)

1. **La vía de la 2ª entrega de `ModelG` queda CERRADA.** Su única justificación escrita
   (`FOL/FOL.lean`: LS ascendente) era FALSA: a LS↑ lo bloquea la indexación por `Nat` de la cadena de
   completitud (`LindenbaumStep : Nat → …`, `FreshSym.cst : Nat → Sym`), y `EnumSym` es falsa para los
   tipos no numerables que LS↑ necesita (`SymClasses.lean`). El parámetro de `ModelG` se queda. La receta
   para reabrir la vía queda DIFERIDA en `[G.2]`.
2. **Entran los cinco resultados «a un paso»** del sondeo de candidatos (journal `wf_749c5bbe-663`).
3. **Entra el modelo infinito por compacidad** ⇒ FOL tiene teoría de modelos.
4. **Se borran los duplicados literales**: `FOL/Theorems/Deduction.lean` y `FOL/Classical.lean`.
   ⬜ `Tactics2.lean` se dejó sin decidir.
5. (Contesta ADR‑099 §6) **`TheoryFramework` se queda**, sin habitantes, con la vía **cerrada y
   documentada** y su mapa de vuelta escrito (`538d5f8`).
6. **Política de congelación**: nada se congela hasta estar terminado; `lock` por fichero; `freeze`
   sólo de lo MEDIDO como intocable. «Congelar FOL» deja de ser un acto: es una **lista**. Criba de
   cinco criterios: sin deuda propia · fuera del cono de una decisión pendiente · no base de la
   cadena entrante · footprint vigilado por módulo y compilado · no hogar de un resultado pendiente.
7. **PeanoRF, propuesta (C)**: bajan a FOL **siete** módulos, no tres (su corrección, PRF‑049):
   `Subst`, `DerivesI`, `SubstDerives`, `Consistency`, `Eq`, `Collapse`, `Slash`. `Slash` entra con
   `lock`, no con `freeze`. El acoplamiento que NO puede viajar es `Collapse.lean:61` (`open
   ROBINSON_PlusPlus.Minimal.Axioms`, que dentro de FOL sería un ciclo) — corrige ADR‑098 §5, que lo
   situaba en «una sola línea» de la `:72`. PeanoRF parametriza `collapseT` antes de entregar.

### 2 · El catálogo: los seis, y lo que NO entra

| | teorema | módulo | footprint MEDIDO |
|---|---|---|---|
| T1 | `model_existence_iff : IsConsistent₀ S ↔ IsSatisfiable S` | `Compacity0` | `[propext, Classical.choice, Quot.sound]` |
| T2 | `max_cons_neg`, `IsSyntacticallyComplete₀`, `max_cons_complete` | `Canonical0` | ídem |
| T3 | `pcheck_complete`, `ptautCheck_iff`, `instDecidablePTaut` | `Herbrand0` | `[propext]` (los dos teoremas; la instancia no se imprime) |
| T4 | `EqPropCert`, `derives0_qf_iff` (§9) | `Hauptsatz0` | `[propext, Quot.sound]` |
| T5 | once inversiones: las nueve proposicionales, `inv_allR`, `inv_exL` | `Inversion0` | `[propext, Quot.sound]` |
| T6 | `infinite_model_of_large` y cía. (§3) | `Compacity0` | `[propext, Classical.choice, Quot.sound]`; `evalFormula_updateCsts` `[propext]` |

⭐ **T4 resuelve la duda de vacuidad** que dejó abierta el 2026‑09‑23 (el precedente es el Maehara
relativizado de ADR‑067): la `E` sin cota **no** trivializa el lado derecho, porque la valuación
constante `true` satisface toda `EqInstance`; dos `example` lo compilan. ⚠️ **Caracteriza, NO
decide**: la versión ACOTADA queda como OFERTA en `[G.2]`, sin medir. Y ⚠️ **va en `Hauptsatz0`**,
que `d961bb2` había evitado reabrir creando `Inversion0` aparte: es el módulo MÁS BAJO que tiene
las cuatro piezas, y nada está congelado todavía.

⭐ **T6 NO es LS↑**: sube de «finitos arbitrariamente grandes» a «numerable e infinito», nunca de un
infinito a un cardinal mayor. Sin hipótesis de frescura (`shiftTheory` + `pullback`). Cuatro
controles de no vacuidad.

🔑 **`inv_allR`/`inv_exL` (2026‑09‑26)**: la DIFERIDA de `Inversion0` decía que la identidad
`substFormula 0 (var 0) (liftFormula 1 A) = A` «no se ha medido». **Existía dos veces**
(`Lift0.substFormula_lift_var`, `Theorems/Quantifiers.subst_lift_cancel_formula`) y el diseño de las
dos inversiones estaba en el journal del 2026‑09‑23 con `planCierra = True`. Compilaron a la primera.
*Antes de construir, buscar — y antes de DIFERIR, también.*

⛔ **Falsos en este marco** (no abrir): la propiedad de subfórmula tal cual (`eqAx` y las
instancias de `allL`/`exR`; ya estaba medido en ADR‑054 §4); «el fragmento QF es decidible por
tabla de verdad»; Herbrand para φ y Γ componiendo lo que hay. **Lejos**: Beth y Robinson (piden un
puente `LK₀`→`LKp`), LS↑ a cardinal arbitrario, la noción de **sentencia** (bloqueo transversal),
la independencia de axiomas vía `IsAxiomRedundant`.

### 3 · La auditoría de cierre (2026‑09‑26, 8 agentes, con refutación)

* ⚠️ **T1‑T3 estaban sin proyectar** en `REFERENCE.md` desde `f9efd94`, y el `CHANGELOG` no recogía
  T1‑T3 ni T5: `[C]` casa por MÓDULO en §6, no por declaración. Proyectados.
* ⚠️ **Tres docstrings míos afirmaban más que lo medido** (la séptima clase): la cabecera de footprint
  de `Hauptsatz0` (`lk0_to_lkh` mide `[propext]`), el «(hasta ℵ₀)» y la procedencia del
  `Classical.choice` de `Compacity0` §3 (en `infTheory_finSat`/`evalTerm_updateCsts` es el de
  `Fresh0`, no el WKL), y el de `Herbrand0.instDecidablePTaut`, que se leía como «la versión relativa
  DECIDE». Corregidos antes del commit.
* ⛔ **`git-lock.bash` borraba por SUBCADENA** (`grep -Fv` sin `-x`) en `unlock` y `thaw`: el `unlock
  FOL.lean` de `d961bb2` se llevó también `FOL/FOL.lean`, que quedó read‑only en disco pero fuera de
  `locked_files.txt` — y el hook ya no lo guardaba. Es la causa «casar por SUBCADENA» de
  `feedback_controles_que_no_comprueban`, otra vez. Arreglado en los dos repos (`-Fxv`).
* `[G.2]` no reconocía «no está medido/a»: ampliado. Hoy **19** marcadores (2 ABIERTA, 4 DIFERIDA,
  1 OFERTA, 12 HISTORIAL).
* **La criba de congelación**, re‑corrida (`FOL/criba-congelacion.py`, traída del scratchpad): 16
  módulos pasan los criterios medibles; **la refutación objeta 13**. Sólo resisten `Prenex0`,
  `PrenexNF0` y `SkolemN0`. ⇒ **no se congela nada todavía**.

### 4 · ⬜ Lo que queda — en `FOL/NEXT-STEPS.md`

Siete decisiones del propietario (D1 `Tactics2`, que resulta idéntico a la copia de
`librerias-retiradas/FOL_poli`; D2 la definición de T2, por pertenencia y no sobre sentencias; D3 las
dos ABIERTA; D4 `ModelG` a CERRADA; D5 el refactor de `Lift0`; D6 el `₀` de T1; D7 la migración
`String`→`List Char`), la entrega de PeanoRF — ⚠️ con una condición que nuestra respuesta (2) omitió:
`Subst`/`DerivesI` importan `PeanoRF.Prelim`, que importa RPP y Peano —, y una pasada de higiene de
docstrings antes de cualquier `freeze`.

🔑 **Lecciones**: *contar una cadena por los módulos que nombras no es contarla* (y su cierre
TRANSITIVO toca 14 módulos de FOL, no 4); *medir un cono por la palabra que lo nombra no es medirlo*;
*un censo que comprueba que un marcador está CLASIFICADO no comprueba que lo que nombra EXISTA*
(`73476af`); ⛔ *el commit se condiciona al verde* (`6bdf8bc` subió con `[G.2]` en rojo).

**Controles:** FOL 57 jobs · 54 módulos activos · 4 `axiom` · 0 `sorry` · `[G.2]` 19/19.
RPP `check-footprints` con las 14 filas de hoy.

## ADR-101: las decisiones D1-D7 del propietario sobre el cierre de FOL, y la condición para PeanoRF

**Fecha:** 2026-09-26 · **Estado:** 🔄 EN EJECUCIÓN (D1 hecho) · **Ámbito:** FOL. Detalle vivo en
`FOL/NEXT-STEPS.md` («Lo que queda para CERRAR FOL»).

| # | decisión del propietario | estado |
|---|---|---|
| D1 | borrar `FOL/Tactics2.lean` | ✅ borrado: era idéntico, salvo el `import`, a `librerias-retiradas/FOL_poli/Tactics2.lean`. El 2026‑09‑23 se había comparado con el fichero equivocado (`Tactics.lean`). FOL: **53 módulos** |
| D2 | renombrar `IsSyntacticallyComplete₀` antes de congelar `Canonical0` | ⬜ nombre medido: `IsMemComplete₀` |
| D3 | las dos ABIERTA de `[G.2]` | ⏸ «lo hablamos al final» |
| D4 | cerrar la vía de `ModelG` «si está terminada» | ✅ medido TERMINADA ⇒ ⬜ se cierra |
| D5 | hacer el refactor de `Lift0` | ⬜ los dos diseños convergen en el genérico (`absTermP`); juez en curso |
| D6 | ¿qué marca `₀`? (con el FOL intuicionista a la vista) | medido: ninguna regla; nació como ordinal de plan (ADR‑033). ⚠️ En RPP, `Prf₀` es la capa **intuicionista**: la misma marca dice lo contrario en los dos repos. ⬜ decisión sobre la regla |
| D7 | cerrar la migración `String`→`List Char` «si está terminada» | ⛔ NO lo está (los `abbrev` siguen en `String`) ⇒ no se cierra; recomendación medida: abandonarla en FOL |

⛔ **Condición nueva, no negociable, para la propuesta (C)** (ADR‑100 §1.7): **FOL no puede depender
de nada más allá de sí mismo.** Medido: los siete módulos de PeanoRF la incumplen hoy (todos importan
`PeanoRF.Prelim`, que trae RPP y Peano; `Collapse` y `Eq` usan `zero`/`succ` de RPP; y `Eq` usa
`FOL.substTerm_liftTerm`, que le llega **a través de RPP**, dependencia que ninguna carta había visto).

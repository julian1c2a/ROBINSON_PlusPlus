# Decisiones de Diseño — ROBINSON_PlusPlus

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
| **M-11** | ⛔⛔ **Antes de demostrar algo por INDUCCIÓN sobre un tipo inductivo, comprobar que NINGÚN `axiom` lo habita.** Un `axiom` cuyo tipo es una aplicación de un `inductive` produce habitantes que **no son aplicaciones de constructor**; la inducción cubre los constructores, pero el teorema cuantifica sobre **todos** los habitantes ⇒ el teorema es **FALSO**. ⚠️ Es *eliminar* lo peligroso (`induction`/`cases`/`rec`), **no** *introducir*: usar los constructores para construir es seguro. ⭐ **EL CRITERIO QUE DE VERDAD SEPARA NO ES «META‑REGLA» SINO *PREMISA‑FUNCIÓN*** (2026‑09‑12,
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

### 🏁 Lo ejecutado con la ratificación: **9 de 11**

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

⬜ Queda **ax24** por certificar sobre los primitivos — su derivación ya es honesta (pasa por la
alternancia **demostrada**); falta migrar `Full/Mod2.lean`, que arrastra `teo_1_3`/`teo_2_9` de
`Block1`. **Medible, no pedido.**

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

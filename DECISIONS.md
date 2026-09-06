# Decisiones de Diseño — ROBINSON_PlusPlus

> ## ESTADO REAL — 2026-09-05 · rama A cerrada · PROMOCIÓN: B0–B2 hechas · **B3 EN CURSO** (SubstfcPlanos cerrado; EvalSubsttc medido)
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 124 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **112 módulos activos** (Minimal 11 + Meta 90 + Full 11) **+ 0 en `cuarentena/` + 60 en `sondeos/`.**
> **7 `axiom` de Lean · 141 axiomas objeto** en `axioms`.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia
>   **numeral** `godelCN`.
> * **0 módulos en `cuarentena/`** (D3 y Gödel II aún fuera de la cadena activa). NO borrados.
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

**Última actualización:** 2026-09-05 — **ADR-019 confirmado en vivo por B3**: el general mal colocado dejaba un corolario inalcanzable, y la duplicación por INSTANCIA que ningún censo ve. ADR-018 en producción.
**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> Este fichero adopta el esqueleto unificado de `lean4-project-template` (ADR-001–009,
> traducidos al español) y **preserva íntegros** los dos ADR reales y sustanciosos que
> ya existían aquí (renumerados a ADR-010/011) — son, junto con los de Peano, los ADR
> de mejor calidad entre los proyectos hermanos: documentan contraejemplos matemáticos
> concretos, no solo preferencias de estilo.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto)

**Sin MANDATORIES explícitas más allá de la disciplina documentada en ADR-010/011**:
este proyecto no prohíbe `Classical.*` (2 usos verificados en 2026-07-12), pero sí
mantiene una disciplina activa de **cero axiomas espurios**: cualquier `axiom`
declarado debe justificarse con un ADR propio (ver ADR-010/011 como ejemplo) o
eliminarse. El episodio histórico "F7a" (retirada de 7 postulados legacy, documentado
en `CHANGELOG.md`) es la aplicación práctica de esta disciplina.

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
**Estado**: Aceptado

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

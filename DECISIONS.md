# Decisiones de Diseño — ROBINSON_PlusPlus

**Última actualización:** 2026-07-12
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

**Fecha**: 2026-04-20
**Estado**: Propuesto (no implementado)

**Decisión**: `REFERENCE.md` debería ser solo el índice raíz, con el detalle de cada
bloque temático en nodos bajo `doc/REFERENCE-{tema}.md`.

**Justificación**: `REFERENCE.md` actual (103 KB, 1531+ líneas) ya es demasiado
grande para navegarse como fichero único — exactamente el síntoma que `AI-GUIDE.md`
§0.5 describe como señal de que hace falta partirlo.

**Consecuencias**: **pendiente de implementar** — no existe todavía directorio `doc/`
en este proyecto. Candidato más urgente de los 4 proyectos de la cola de propagación
para beneficiarse de este ADR, dado el tamaño ya alcanzado.

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

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]

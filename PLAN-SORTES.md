# PLAN — Separación de tipos: reparar la inconsistencia de `tcFn`

**Creado:** 2026‑07‑27 · **Estado:** diseño, pendiente de decisión sobre el NIVEL de tipado
**Contexto:** ver memoria `project-inconsistencia-tcfn-cons` y `AXIOMS.md`.

---

## 1 · Qué hay que reparar, exactamente

`tcFn` intenta ser **`termCode`** — una operación sobre la **sintaxis** — declarada como símbolo de
función objeto, que sólo puede depender de **valores**. Sus dos ecuaciones recurren sobre
estructuras distintas:

| ecuación | recursión sobre |
|---|---|
| `ax_tc_zero`, `ax_tc_succ` | estructura **NUMERAL** (`zero`/`succ`) |
| `ax_tc_cons` | estructura de **CÓDIGO** (`cons`) |

Y `cons 0 nil = pair 0 (σ0) = 2 = σσ0` — **mismo valor, dos sintaxis** ⟹ contradicción.

**Cada una por separado es legítima.** La contradicción nace **de la fusión en un símbolo**.

---

## 2 · Hechos verificados que acotan el diseño

| hecho | verificación |
|---|---|
| Sólo `tc` está infectada; ninguna otra familia | auditoría completa de axiomas (2026‑07‑27) |
| **Opción B (tipos por axiomas en el lenguaje mono‑sortido) es IMPOSIBLE** | `OptionBProbe3` compila: `ax13 + ax19 + ax6 + ax4` prueban `∀x. x=0 ∨ ∃k. x=σk` **sin inducción** ⟹ no hay sitio para un `cons` que no sea 0‑ni‑sucesor |
| La separación en dos símbolos es bien‑formada | `Probe/Sortes.lean` compila; `tcNumFn ≠ tcCodeFn` demostrable |
| Alcance: **1175 usos de `tcFn` en 32 módulos** | `grep` |
| Kernel FOL: **8.323 líneas**, `Term` mono‑sortido | `find` + lectura de `FOL/FOL.lean:10‑24` |

---

## 3 · La reparación mínima (necesaria en TODOS los escenarios)

**Partir `tcFn` en dos símbolos objeto:**

```lean
def tcNumFn  (t : Term) : Term := Term.func "tcNum"  [t]   -- código del NUMERAL de un número
def tcCodeFn (t : Term) : Term := Term.func "tcCode" [t]   -- código de un CÓDIGO (cons-árbol)

ax_tcNum_zero  : tcNum 0       = ⟨1,⌜"0"⌝,[]⟩
ax_tcNum_succ  : tcNum (σx)    = ⟨1,⌜"σ"⌝,[tcNum x]⟩
ax_tcCode_cons : tcCode (a::b) = ⟨1,⌜"::"⌝,[tcCode a, tcCode b]⟩
```

**Modelo explícito (⟹ consistencia):** en ℕ,
- `tcNum(n)` := código del término `σⁿ0` — función total ℕ→ℕ, recursión sobre ℕ. ✔
- `tcCode(c)` := código de `c` leído como `cons`‑árbol. `cons` es **inyectiva** (Cantor), así que
  está bien definida sobre su imagen; fuera de ella queda **subdeterminada, no contradictoria**. ✔
- La recursión de `tcCode` **termina**: `prf_cantor_mono` (ya probado) da sub‑código < código.

El paso que producía `⊥` **deja de conectar**: `tcNum(σ(pred C))` y `tcCode(cons 0 nil)` son
términos con **símbolos distintos**, y ningún axioma los relaciona.

---

## 4 · ⚠️ DECISIÓN PENDIENTE: en qué NIVEL van los tipos

Hay dos formas de «separar tipos», con consecuencias **muy** distintas:

### A1 — Tipos en LEAN (meta), kernel intacto

Envolver `Term` en tipos Lean según el papel (`NumTm` / `CodeTm`), de modo que
**`tcNum` sobre un código no compile**. La teoría objeto sigue siendo **mono‑sortida**.

* **Coste:** capa nueva en Lean + retipar los 1175 sitios. Grande pero acotado. **Kernel intacto.**
* **Teorema:** sigue siendo la incompletitud **de la aritmética**. ✔
* **Previene la recaída:** sí, en el momento de *construir* los axiomas — que es donde ocurrió el error.

### A2 — Sortes en el KERNEL FOL (multi‑sortido real)

Añadir sortes a `Term`/`Formula`/`Derives`.

* **Coste:** 8.323 líneas de FOL + los 99 módulos de RPP. Enorme.
* **Teorema:** ⚠️ **cambia**. La teoría pasa a ser aritmética **+ un sorte de códigos**; el
  resultado ya no es la incompletitud de la aritmética sino la de una teoría bi‑sortida. Es un
  teorema legítimo, pero **no el mismo**.
* **Previene la recaída:** sí, y además a nivel semántico.

> **Recomendación:** **A1**. Es más barato **y** preserva el teorema. A2 sólo compensa si el
> objetivo pasa a ser explícitamente «incompletitud de una teoría de sintaxis + aritmética»
> (la vía Paulson/Świerczkowski con conjuntos hereditariamente finitos).
>
> Nota: la reparación **§3 es la misma en ambos casos**. A1/A2 sólo deciden *qué impide repetirlo*.

---

## 5 · Plan por fases (independiente de A1/A2)

| fase | entregable | verificación |
|---|---|---|
| **0** | `Probe/` con los dos símbolos + sus axiomas; confirmar que el `boom` no reconecta | ✅ hecho |
| **1** | Clasificar los **1175 sitios**: cuáles son numeral‑`tcFn` y cuáles código‑`tcFn`. **Script + revisión**, no a ojo | informe con los 32 módulos y su reparto |
| **2** | Sustituir `ax_tc_*` por los tres nuevos en `Minimal/Axioms.lean`; reconstruir `TcArithPrf` | `lake build` verde hasta `TcArithPrf` |
| **3** | Propagar por la capa punteada (`EvalListPrf`, `CodeCtorKit`, `Sigma1TrackedPrf`, `D3InDotPrf`, los 14 tags) | `lake build` verde |
| **4** | **Re‑auditar**: `#print axioms` de D1, D2, Gödel I; y **reintentar el `boom`** para confirmar que ya no compila | el `boom` debe FALLAR |
| **5** | (A1) capa de tipos Lean que impida la reconflación | los 1175 sitios tipados |

⚠️ **Riesgo principal, honesto:** la fase 1 es la que decide la viabilidad. Si hay sitios donde
`tcFn` se aplica a algo cuyo papel **no está determinado estáticamente** (p. ej. `tcFn (nthc t i)`
con `t` abstracto — 13 ocurrencias), ahí **no se puede elegir símbolo**, y esos casos necesitarán
rediseño, no sustitución mecánica. **Eso hay que medirlo antes de prometer plazos.**

---

## 6 · Qué se pierde mientras tanto

Los resultados de la capa punteada (14 tags, `hI_dot`, D3 en curso) **se apoyan en `ax_tc_cons`**
y habrá que rehacerlos sobre `tcCode`. `prf_tc_form` (28 usos) y `prf_tc_numeral` (56 usos) se
desdoblan. **D1, D2 y Gödel I no dependen de la parte rota** y deberían sobrevivir sin cambios —
verificar en la fase 4.

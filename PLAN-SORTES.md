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

## 4bis · ⛔ RESULTADO DE LA FASE 1 (2026‑07‑27) — **§3 es INSUFICIENTE**

Decisión tomada: **A1**. Ejecutada la clasificación. El resultado **invalida la reparación de §3**
y hay que corregirla. Lo que sigue sustituye a §3.

### Los números reales

`grep` daba 1175, pero eso contaba identificadores que *contienen* `tcFn` (`prf_congr_tcFn`, …).
Extrayendo el argumento con paréntesis balanceados (`scripts/clasifica_tcfn.py`):

| | sitios | % |
|---|---:|---:|
| **aplicaciones reales `tcFn <arg>`** | **899** | 100 |
| argumento = **variable abstracta** | 683 | 76 % |
| argumento aritmético (`succ`,`add`,`zero`,`lenc`…) | 77 | 9 % |
| argumento proyección (`carc`,`nthc`) | 48 | 5 % |
| argumento constructor de código (`cons`,`formCode`…) | 34 | 4 % |

**El 76 % no se clasifica por sintaxis.** El papel lo fija la **intención del módulo**, no el
argumento. Y ahí está el hallazgo.

### Las dos lecturas — ambas VIVAS y ambas cargando peso

| lectura | qué es `tcFn a` | recursión | dónde |
|---|---|---|---|
| **NUMERAL** | código del numeral `σᵃ0` | `zero`/`succ` | `NumCodeClosedPrf.lean:31` lo dice **literalmente**; toda la capa punteada (683 sitios) |
| **SINTÁCTICA** | código del **término** `a` leído como árbol | `cons` | `prf_tc_form`/`prf_tc_term`/`prf_tc_str` (`TcArithPrf.lean:102‑128`) |

Son **incompatibles**: `formCode φ` es un **árbol `cons` de numerales** (`Provability.lean:55‑61`),
cuyo *valor* es un número N; la lectura numeral daría `⌜σᴺ0⌝` y la sintáctica el código del árbol.
Números distintos. **No hay función Nat‑valuada de codificación en el proyecto** (verificado): los
códigos son **siempre** árboles.

### ⛔ Por qué partir el símbolo NO basta

`tcCode` necesitaría **las dos recursiones**, no sólo la de `cons`:

```lean
-- TcArithPrf.lean:103
prf_tc_term (.var n) = prf_tc_of_cons (prf_tc_numeral 0) (prf_tc_of_cons (prf_tc_numeral n) prf_tc_zero)
--                                     ^^^^^^^^^^^^^^^^ recursión SUCC, dentro de un nodo cons
```

Las **hojas** de un árbol de código son numerales ⟹ `tcCode` debe computar sobre numerales ⟹
necesita `succ`. Y `succ` + `cons` **en un mismo símbolo es exactamente el `boom` ya verificado**
(la demostración es la misma con el constante renombrada). Con sólo `cons`, `tcCode (numeral 2)`
daría `⟨1,⌜::⌝,…⟩` porque `2 = cons 0 nil`, mientras `termCode (numeral 2)` tiene cabeza `⌜σ⌝` ⟹
`prf_tc_numeral` sería **falso** para `tcCode` ⟹ `prf_tc_form` no se recupera.

> **⚠️ Corrección a §3: partir `tcFn` en dos símbolos salva la capa punteada (`tcNum`) pero NO
> salva `prf_tc_form`.** La lectura sintáctica no es reparable por renombrado.

### La raíz, en una frase

`tcFn` pide a la teoría objeto ver **información intensional que los números no llevan**: qué
término *escribimos* para denotar N. Con los códigos representados como **árboles `cons`** esa
información se pierde en el valor. Con los códigos representados como **numerales** no se pierde,
porque el numeral **es** canónico.

### Reparación revisada

**`tcFn` := sólo la lectura NUMERAL. Se ELIMINA `ax_tc_cons`.**

* **Coste en axiomas: −1. Ninguno nuevo.** (Contra los «< 12 axiomas» de la otra vía.)
* **Consistente**, con modelo: `n ↦ ⌜σⁿ0⌝`, total sobre ℕ.
* **Salva** los 683 sitios variable y toda la capa punteada sin tocarlos.
* **Rompe** `prf_tc_of_cons`/`_term`/`_terms`/`_str`/`_chars`/`_form` y sus consumidores:
  **20 sitios en 4 módulos** (`D3InDotPrf` 6, `InAxiomsCodePrf` 7, `Sigma1CorePrf` 6,
  `TrackedCorePrf` 1) — no 899.
* **Exige** representar `⌜φ⌝` como **numeral** donde se le aplique `tcFn`: construir
  `codeNat : Formula → Nat` y `formCode φ =eq numeralM (codeNat φ)` (mismo valor, vía
  `ax_L0_cons_def`). Entonces `prf_tc_form` **se vuelve** `prf_tc_numeral` — que sólo usa
  `zero`/`succ`.

⚠️ **Lo que NO está verificado y decide la fase 2:** que esos 20 sitios se re‑prueben con la
representación numeral. La evaluación provable del emparejamiento de Cantor sobre `codeNat` es
finita y mecánica, pero **no está compilada**. Antes de tocar `Minimal/Axioms.lean` hay que cerrar
un piloto: **un** solo sitio de `InAxiomsCodePrf` re‑probado por la vía numeral.

---

## 4ter · PILOTO DE LA FASE 2 (2026‑07‑27) — ✅ cierra, y **parte los sitios en dos familias**

Piloto en `Probe/PilotoAislado.lean` (no es módulo de producción). Compila, **0 errores, 0 avisos**,
footprint `[propext, Classical.choice, Quot.sound]` — **sin `sorryAx`**.

### Cómo se verificó la independencia (el crawler de dependencias NO sirve)

Un auditor de constantes transitivas da **falsos negativos**: Lean 4.31 devuelve `value? = NONE`
para teoremas importados (medido), así que sólo recorre **tipos**, no pruebas. Se descartó.

En su lugar, **aislamiento por importaciones**, que sí es concluyente:

* `SubstCodeOpenPrf` (27 módulos) y `DerivCondPrf` (32) **no alcanzan** `TcArithPrf`; `InAxiomsCodePrf`
  (61) sí — verificado con cierre transitivo del grafo de imports.
* El piloto importa **sólo** esos dos ⟹ `prf_tc_form`/`_of_cons`/`_cons`/`_term` **no existen en su
  entorno** ⟹ no puede usarlos. Comprobado por máquina con `#noExiste` (falla si alguien los mete).

### Lo que el piloto cierra

`substtc_inv_termCode_listFormCodeM` con **tipo idéntico** al de producción, por la vía estructural:
`prf_substtc_arith_open` (sólo ecuaciones de variable de `substtc`) + `substCodeT_closed`
(`listFormCodeM L` es cerrado). Más el caso general

```lean
substtc_inv_termCode_closed (a) (ha : ∀ c, liftTerm c a = a) (W) :
    Prf (substtc zero W (termCode a) =eq termCode a)
```

que **sustituye a `substtc_inv_termCode_of_tc` eliminando su hipótesis `tcFn a =eq termCode a`** —
justo la que obligaba a la lectura sintáctica.

### ⚠️ Lo que el piloto DESTAPA: los 20 sitios son de dos clases, y sólo una está cerrada

| familia | enunciado | ¿resuelta? |
|---|---|---|
| **invariancia** | `substtc W (termCode a) =eq termCode a` | ✅ **sí, net‑0, compilado** |
| **puente** | `tcFn a =eq termCode a` | ❌ **no** |

Sitios de la familia **puente** (los duros): `InAxiomsCodePrf:185` (`haform` de `pcc_in_head_swap`),
`D3InDotPrf:340`, `Sigma1CorePrf:114`, `:204`, `:213`.

El puente dice **«el código RASTREADO (`tcFn a`, que produce la maquinaria punteada) es el código
ESTÁTICO (`termCode a`, que produce el meta)»**. Es exactamente el punto donde las dos lecturas
tienen que coincidir — y por §4bis no pueden, mientras `⌜φ⌝` sea un **árbol**.

### La salida, y su precio

Con `⌜φ⌝` representado como **numeral**, el puente pasa a ser
`tcFn (numeralM N) =eq termCode (numeralM N)`, que es **`prf_tc_numeral`: ya demostrado, y sólo usa
`zero`/`succ`**. El puente se recupera *gratis* — pero exige:

1. `codeNat : Formula → Nat` — **no existe**;
2. `formCode φ =eq numeralM (codeNat φ)` — exige **evaluación provable del emparejamiento de
   Cantor** sobre numerales concretos. **Verificado que NO existe** ningún lema
   `cons (numeral a) (numeral b) =eq numeral k` en el repo. Es el grueso real de la fase 2.
   (El instrumental aritmético para hacerlo sí está: `NatMulPrf`, `div2`/`mod2` vía `ax17`/`ax21`.)

⚠️ **A vigilar, no verificado:** `N` crece como el emparejamiento de Cantor iterado, así que la
prueba objeto que denota `prf_tc_numeral (codeNat φ)` tiene longitud astronómica. En Lean todo queda
**simbólico** (nunca se normaliza `numeral (codeNat φ)`), luego la formalización no se rompe; pero
antes de comprometerse hay que comprobar que las **cotas** de la capa acotada (`boundedCarcIn`)
toleran ese tamaño.

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

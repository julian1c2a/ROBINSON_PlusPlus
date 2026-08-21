# PLAN — Reparar la inconsistencia de `tcFn`

**Creado:** 2026‑08‑19 · **Última medición:** 2026‑08‑19 (sondeos S1–S5 + piloto diagonal)
**Contexto:** memoria `project-inconsistencia-tcfn-cons`, `AXIOMS.md`, `sondeos/README.md`.

---

## 🟢 LEER ESTO PRIMERO — estado vigente y qué secciones están SUPERADAS

Este documento se escribió por capas y **las secciones posteriores invalidan a las anteriores**.
Orden de autoridad: **§4septies > §4sexies > §4quater > §4bis > §3**.

### Lo que está VERIFICADO EN EL COMPILADOR

| hecho | dónde |
|---|---|
| La teoría objeto es **inconsistente**: `axioms ⊢ ⊥`, footprint sancionado, sin `sorryAx` | sesión previa |
| El daño entra a Gödel I **por un solo sitio**: el **lema diagonal** (`godelC'_fixedpoint` cita exactamente `[propext, choice, Quot.sound, imp_intro, tc_cons]`) | §4sexies (S1) |
| **D1 (`repr_pos'_prf`) está LIMPIO**, y el argumento de Gödel (`goedel_first_unprovable_real'`, `_unrefutable_real'`) también: son **modulares** | §4sexies (S1) |
| La familia **INVARIANCIA** se re‑prueba sin la lectura sintáctica | §4ter |
| `codeNat φ` **se mantiene simbólico**: Lean nunca lo reduce | §4sexies (S3) |
| ✅ **El punto fijo SOBREVIVE con códigos numerales**, footprint del original **menos `tc_cons`** | **§4septies** |
| ✅ Las dos representaciones son intercambiables **en un paso de Leibniz** ⟹ D1 y la cadena existente se transfieren | **§4septies** |

### ⛔ Lo que está DESCARTADO (no re‑litigar)

* **§3 «partir `tcFn` en dos símbolos» — INSUFICIENTE.** `tcCode` necesitaría las dos recursiones
  (las hojas de un árbol de código son numerales) ⟹ reproduce el mismo `⊥`. Ver §4bis.
* **§4bis «eliminar `ax_tc_cons`» — NO ES OPCIÓN.** Decapita el lema diagonal: el «código del
  código» **es** lo que la diagonalización exige. Ver §4sexies (S1).
* **§4quater «Gödel I está estructuralmente limpio» — FALSO.** Fue un falso negativo de la
  heurística de `import`s. Ver §4sexies (S1) y la trampa nº1 de `sondeos/README.md`.
* **Un paquete de buena‑formación NO repara `tc`** (S2, 17 agentes, 4/4 ángulos). `substfc` pide un
  reconocedor **extensional**; `tc` pide una distinción **intensional**. Ver §4sexies.
* **Opción B (tipos por axiomas en el lenguaje mono‑sortido)** — imposible, §2.
* **Puerta (a) del muro `substfc`** — imposibilidad estructural, ver `project-substfc-wall`.

### ▶ LA VÍA VIVA, y lo único que falta

**Representar `⌜φ⌝` como NUMERAL en lugar de como árbol `cons`.** Con eso `tcFn` se queda **sólo**
con la lectura numeral (`ax_tc_zero`/`ax_tc_succ`), que es consistente y tiene modelo en ℕ.

Todo el diseño está pilotado **salvo una pieza**:

```lean
prf_div2_numeral   -- div2 (numeral (2*m)) =eq numeral m   ← LO ÚNICO QUE FALTA
```

de la que cuelgan `prf_cons_eval` → `prf_formCode_numeral` (= `hFN`, ya asumida y pilotada).

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
| Sólo `tc` está infectada; ninguna otra familia | auditoría completa de axiomas (2026‑08‑19) |
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

## 4bis · ⛔ RESULTADO DE LA FASE 1 (2026‑08‑19) — **§3 es INSUFICIENTE**

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

## 4ter · PILOTO DE LA FASE 2 (2026‑08‑19) — ✅ cierra, y **parte los sitios en dos familias**

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

## 4quater · MEDICIÓN (2026‑08‑19): la cota, las magnitudes, y el radio real del daño

### Respuesta a «¿a cuánto habría que elevar `boundedCarcIn`?» → **a nada**

```lean
-- RunFnBoundedPrf.lean:214
def boundedCarcIn (y p : Term) : Formula :=
  Formula.ex (land (lt (.var 0) (liftTerm 0 (lenc p))) …)
--                                            ^^^^^^ la cota es `lenc p`
```

La cota es **`lenc p`** — el **número de líneas** de la lista, no la magnitud de los códigos. Es
**paramétrica**: se adapta sola. Barrido de todas las cotas del proyecto (`boundedIn`,
`boundedCarcLt`, `boundedAllIn`, `boundedPremsIn`, `bdExCode`, `bdAllCode`): **ninguna es un numeral
concreto**. No hay nada que elevar.

### Las magnitudes sí son brutales (medidas, `Probe/Magnitud.lean`)

Con `cons h t = ((h+σt)(h+σt+1) + 2σt)/2`, cada `cons` **eleva al cuadrado**:

| fórmula | prof. `cons` | nodos | log₂(N) |
|---|---:|---:|---:|
| `⊥` | 1 | 1 | 3,6 |
| `0 = 0` | 6 | 11 | 300 |
| `0=0 ⇒ 0=0` | 9 | 25 | 2 395 |
| `ax_L0_cons_def` | 35 | 98 | **3,85 × 10¹⁰** |
| `ax_tc_cons` | 260 | 704 | **8,66 × 10⁷⁸** |
| `ax_tc_succ` | **3 873** | 4 905 | **desborda un `double`** |

**Causa diagnosticada, y es corregible:** el estallido lo dominan los **numerales unarios de los
puntos de código Unicode**, no la estructura de la fórmula. `σ` es U+03C3 = **963**, así que
`strCodeM "σ"` mete un `numeralM 963`, y su `termCode` anida 963×3 ≈ 2 889 niveles de `cons`.
Eso explica que `ax_tc_succ` (prof. 3 873) desborde mientras `ax_L0_cons_def` (prof. 35) no.
**Codificar los símbolos por índice de tabla (0…40) en vez de por Unicode recortaría la profundidad
unas 100×** — barato e independiente de todo lo demás.

### ⚠️ El riesgo real NO es la cota

Es si **`codeNat φ` se mantiene SIMBÓLICO** en los términos de prueba de Lean. `numeral (codeNat φ)`
y `prf_tc_numeral (codeNat φ)` son aplicaciones bien formadas mientras Lean **no** intente reducir
`codeNat φ`. Si algún paso fuerza su evaluación a literal, nada de eso tipa. **Eso es lo que hay que
sondear, no la cota.**

### ✅ La mejor noticia: **Gödel I está estructuralmente limpio**

Alcanzabilidad transitiva de `TcArithPrf` sobre los 100 módulos:

* **33 contaminados** (pueden alcanzarlo) — toda la capa `Eval*`/`LineWF*`/`Sigma1*`/`D3*`.
* **66 libres** — y ahí están **`DiagonalTwo` (`goedel_first_real'`), `GodelTwo`,
  `Representability2Prf` (D1) y `ReflectionPrf`**.

⟹ **La prueba de Gödel I no puede estar usando la familia `tc`.** Reparados los axiomas,
**sobrevive sin re‑demostrar nada**. Hoy es **vacua** (su hipótesis `ConsistentOmega` es refutable
en la teoría inconsistente), pero eso lo cura la reparación, no trabajo de prueba.
El daño está **confinado a la capa rastreada**.

---

## 4quinquies · SONDEOS PROPUESTOS (por prioridad)

### S1 · Quitar `ax_tc_cons` y reconstruir — **el más informativo, hacer PRIMERO**
En rama aparte, eliminar `ax_tc_cons` de `coreAxioms` y `lake build`. Da la lista **exacta** de lo
que rompe, en vez de la cota superior de 33 módulos que da la alcanzabilidad. Es reversible
(`git checkout`) y no sanciona nada. **Sin esto, cualquier plan de reparación va a ciegas.**

### S2 · ¿`isFormCode` resuelve LOS DOS muros? — **el que puede cambiar la estrategia**
El muro de `substfc` pedía un predicado de buena‑formación (`isFormCode`, < 12 axiomas); el puente
`tc` pide distinguir **árbol** de **numeral**. **Son la misma carencia.** Si un solo paquete de
axiomas cierra ambos, la economía cambia por completo: dejaría de ser «−1 axioma pero pierdo la capa
rastreada» y pasaría a ser «+N axiomas que desbloquean B.3c **y** reparan `tc`».
Ver [[project-substfc-wall]] — **hay que evaluarlo antes de comprometerse con la vía numeral.**

### S3 · ¿Se mantiene simbólico `codeNat φ`? — decide si la vía numeral existe
Escribir `codeNat : Formula → Nat`, elaborar `prf_tc_numeral (codeNat φ)` y comprobar que Lean **no**
reduce. Medir tiempo de elaboración y `maxRecDepth`. Barato, y si falla **mata la vía numeral**.

### S4 · Evaluación provable de Cantor sobre numerales — el grueso técnico
`prf_cons_eval (a b : Nat) : Prf (cons (numeral a) (numeral b) =eq numeral (consN a b))`.
Pregunta clave: ¿sale por inducción **objeto** (net‑0, `a`/`b` abstractos) o sólo por inducción
**meta** (término de profundidad `a`)? Sólo lo primero sirve.

### S5 · Recodificar símbolos por índice — ganancia independiente
Sustituir el punto Unicode por un índice de tabla en `strCode`/`strCodeM`. Recorte ~100× en
profundidad. No depende de ninguna decisión anterior y **beneficia a todas las vías**.

**Orden recomendado: S1 → S2 → (según S2) S3 → S4. S5 en cualquier momento.**

---

## 4sexies · RESULTADOS DE LOS SONDEOS (2026‑08‑19)

### ⛔ S1 — el radio exacto, y **invalida «quitar `ax_tc_cons`»**

Experimento en rama `sondeo/s1-sin-ax-tc-cons` (commit `4b3492f`, **NO MERGEAR**): `ax_tc_cons`
fuera de `axioms`, y los dos puentes que lo consumen (`TcArithPrf.prf_tc_cons`, `Diagonal.tc_cons`)
convertidos en **axiomas de Lean**, para que el árbol compile y `#print axioms` delate
mecánicamente a sus consumidores **sin falsos negativos**.

*Sólo **2 fallos directos*** (`TcArithPrf:54`, `Diagonal:61`); con los dos como axioma el árbol
entero compila (113 jobs). Auditoría:

| | resultado |
|---|---|
| **limpio** | `repr_pos'_prf` (**D1**), `goedel_first_unprovable_real'`, `goedel_first_unrefutable_real'`, `goedel_second'` (cita `d3`), `d3_prf_of_dotted_atoms` |
| **sucio** | **`godelC'_fixedpoint`**, `goedel_first_real'`, `goedel_first_undecidable_real'`, los 14 tags `pcc_lineWF_tracked_*`, `hI_dot`, `d3_prf_of_chainOkDot`, `prf_tc_form`, `prf_tc_listFormCodeM`, `prf_tc_objList` |

`godelC'_fixedpoint` cita **exactamente** `[propext, choice, Quot.sound, imp_intro, tc_cons]`.
⟹ **la única puerta de entrada del daño a Gödel I es el LEMA DIAGONAL.** El argumento de Gödel y
D1 son **modulares** y sobreviven intactos: `goedel_first_real'` sólo se ensucia al *descargar* el
punto fijo.

> **⛔ CONCLUSIÓN QUE INVALIDA §4bis: «quitar `ax_tc_cons`» NO ES UNA OPCIÓN.**
> `godelC'_fixedpoint` usa `diag_arith` → `tc_form` = **el código del código**
> (`Diagonal.lean:124‑145`). Eso **es** la diagonalización: para construir `G = β(⌜β⌝)` la teoría
> tiene que computar el código de un término que ya es un código. La lectura **sintáctica** no es un
> accidente de la capa rastreada — **es lo que Gödel exige**. El puente hay que **REPARARLO**.

> ⚠️ **Corrige también §4quater:** allí dije que Gödel I estaba estructuralmente limpio, por
> alcanzabilidad de importaciones. Sólo miré `TcArithPrf` y se me escapó `Diagonal`, que tiene el
> mismo puente en la capa ω. **La heurística de imports da falsos negativos; sólo `#print axioms`
> es concluyente.**

### ✅ S3 — `codeNat φ` SÍ se mantiene simbólico

`codeNat` escrito **total y estructural** (si fuera `partial` sería opaca y el sondeo no probaría
nada). Los 6 teoremas elaboran **al instante**, footprint `[propext, choice, Quot.sound]`:
`φ` abstracta, `φ` concreta (`ax_tc_zero`), **el peor caso** (`ax_tc_succ`), y encadenado por
congruencia con argumento concreto. **Lean nunca reduce `codeNat φ`.** La vía numeral es viable
del lado de Lean.

### 🔬 S4 — cadena identificada; falta **una** pieza

| paso | estado |
|---|---|
| (1) `cons h t =eq div2 (cpOf h t)` | ✅ existe (`prf_cons_div2`) |
| (2) `cpOf ā b̄ =eq numeral P` | ✅ existen (`prf_numeral_add`/`_mul`) |
| (3) **`div2 (numeral P) =eq numeral (P/2)`** | ❌ **NO existe** |

(3) es un argumento de **paridad** vía `ax17_div_mod_eq` + `ax21_mod2_range` + cancelación.
Instrumental completo y disponible (`prf_lt_trichotomy`, `prf_lt_of_mul_lt_mul_right`,
`prf_div_mod_eq`, `prf_mod2_range`). **Primer eslabón ya COMPILADO** (net‑0,
`[propext, choice, Quot.sound]`):

```lean
prf_add_eq_zero_right (a b) : Prf ((add a b =eq zero) ⇒ (b =eq zero))
```

⟹ vía **abierta**, ~20 líneas por lema, en forma **objeto** (`x` abstracto ⟹ vale para todo `a,b`).

### 📏 S5 — el recorte por índice de símbolo: **424×**

| | valor |
|---|---|
| suma de puntos Unicode de los 10 símbolos | **19 068** |
| con índices `0…9` | **45** |
| profundidad `cons` de `formCode`: `ax_tc_succ` / `ax_tc_cons` / `ax_tc_zero` / `ax_L0_cons_def` | 3 873 / 260 / 211 / 35 |

Independiente de toda decisión anterior y beneficia a **todas** las vías.

### ⛔ S2 — **NO.** Un solo paquete NO cierra los dos frentes (17 agentes; 4/4 ángulos, 3 sobreviven refutación)

**Razón de fondo:** las dos carencias tienen **forma lógica distinta**. `substfc` pide un
**reconocedor extensional** (un subconjunto de ℕ sobre el que hacer análisis de casos); `tc` pide que
**una función tome dos valores en un mismo punto** (distinción **intensional**: qué sintaxis
escribimos para el número 9). Un predicado *es* un subconjunto: **no separa lo que no está separado
en los valores**.

Ningún paquete **aditivo** puede reparar `tc` (monotonía: `ax_tc_*` no mencionan predicado alguno).
Y las tres variantes de **guarda** mueren:

| variante | resultado |
|---|---|
| guardar sólo `cons` | **INCONSISTENTE**. Testigo `varc zero = cons 0 (cons 0 nil)`, valor **9**: la guarda se cumple, y `prf_cantor_mono_left` lo hace sucesor ⟹ `ax_tc_succ` sin guardar dispara ⟹ ⊥ |
| guardar sólo `succ` | **INÚTIL**: `prf_tc_numeral` es esquema meta ∀n instanciado con `n` libre; la guarda no es descargable uniformemente |
| guardar **ambas** | **consistente** (modelo en ℕ por recursión fuerte) **pero mata Gödel I**: `prf_tc_numeral` muere justo en los valores‑código 2,4,7,9,12… que son los TAGS que `prf_tc_form` consume |

#### ⚠️ R‑3 — la vía numeral **NO es un drop‑in** (corrige la lectura optimista de S3)

Con `prf_formCode_numeral φ : Prf (formCode φ =eq numeralM N)`, la congruencia `prf_congr_tcFn`
(`TcArithPrf.lean:133`) + `prf_tc_numeral N` dan `tcFn (formCode φ) =eq termCode (numeral N)`;
pero `prf_tc_form φ` da `=eq termCode (formCode φ)`. `formCode φ` es siempre `cons _ _` y
`numeral N` es `σᴺ0` ⟹ cabezas `"::"` vs `"σ"` ⟹ `termCode_ne` (`CodeDistinct.lean:97`) ⟹ **⊥**.

> **La vía numeral sólo es coherente si `prf_tc_form` MUERE** — y S1 mostró que eso **decapita el
> lema diagonal**. S3 probó que Lean aguanta `codeNat` simbólico (cierto), pero eso es condición
> **necesaria, no suficiente**: `prf_tc_form` hay que **sustituirlo**, no conservarlo, y la
> diagonalización hay que **refundarla**.

#### 🚩 R‑6 — la enmienda «obvia» de los 7 esquemas es INCORRECTA en 4 de 7

* `ind`(18) y `listInd`(20) tienen **`lenc = 3`: no existe casilla 3.** `nthc L 3` cae en `nthc nil zero`,
  sin axioma ⟹ término indeterminado ⟹ `isTermCode` de él es **independiente** ⟹ **ninguna línea de
  inducción sería certificable** (rompe además `PropCodePrf.lean:137`).
* `q3`(11) y `qconf`(19) llevan **códigos de FÓRMULA** en la casilla 3 ⟹ `isTermCode` ahí es
  **refutable** ⟹ la teoría probaría **`¬lineWF` de líneas genuinas**, y los 7 reflectores se
  cerrarían **ex falso**: B.3c en verde 21/21 con un verificador que ya no certifica ∃‑elim ni
  inducción. Es el incidente `ax_lineWF_gen` **en espejo**.

#### El paquete, si aun así se quiere (sólo para `substfc`)

**3 axiomas netos** (mejor que los «< 12» estimados): `ax_isTermCode_iff`, `ax_isTermsCode_iff`,
`ax_isFormCode_iff` (inversión por los 8 constructores) + los 7 esquemas **enmendados**, no añadidos.
Verificado que `isFormCode`/`isTermCode`/`isTermsCode` tienen **0 ocurrencias** hoy.
⚠️ La enmienda **cuesta D1**: `repr_pos'_prf` consume la dirección ⇐ de los 7 bicondicionales
(`Representability2Prf.lean:220,227,233,248,260,268,276`) ⟹ hace falta `prf_isFormCode_formCode`
(argumentado net‑0, **0 líneas escritas**).

#### ⚠️ Nota metodológica (fallo mío)

El workflow corrió **mientras yo tenía la rama S1 con `ax_tc_cons` retirado**. Dos de los cuatro
diseños leyeron el árbol mutado y afirmaron que ya estaba fuera. **La síntesis lo detectó (R‑1) y
verificó contra `master` `df55d0a`**, pero los sondeos no deben lanzarse contra un árbol que cambia.

## 4septies · ✅ PILOTO DEL LEMA DIAGONAL BAJO CÓDIGOS NUMERALES — **PASA**

*El riesgo nº1 de S2, resuelto en POSITIVO.* Orden invertido a propósito: se pilota **antes** de S4,
asumiendo su resultado como axioma de Lean, para no arriesgar ~20 lemas sin saber dónde enchufarlos.

**Lo asumido, y nada más** (`Probe/PilotoDiagonal.lean`):

```lean
axiom codeN : Formula → Nat                                    -- abstracto a propósito
axiom hFN (φ) : axioms ⊢ (numeral (codeN φ) =eq formCode φ)    -- ← LA SALIDA DE S4
```

**Resultados, con footprint verificado:**

| teorema | footprint | ¿`tc_cons`? |
|---|---|---|
| `diag_arith_num` | `[propext, choice, codeN, hFN, Quot.sound]` | **NO** |
| `godelCN_fixedpoint` | `[…, imp_intro]` | **NO** |
| `provCode_transfer` | `[…, imp_intro]` | **NO** |

Compárese con el original: `godelC'_fixedpoint` = `[propext, choice, Quot.sound, imp_intro, tc_cons]`.
**Footprint idéntico menos `tc_cons`**, más las dos hipótesis.

**Por qué funciona — y por qué el temor de S2 era infundado.** S2 avisaba de que
`substFormula_arith` «no aplicaría» sobre códigos numerales. Es falso: su firma es

```lean
substFormula_arith (v : Nat) (s : Term) (f : Formula) :
    axioms ⊢ (substfc (numeral v) (termCode s) (formCode f) =eq formCode (substFormula v s f))
```

y **`s` es ARBITRARIO** ⟹ traga un numeral sin más. La cadena queda:

```
substTerm 0 ⌜ψ⌝ₙ diagTerm
  = substfc 0 (tcFn ⌜ψ⌝ₙ) ⌜ψ⌝ₙ
  ─[tc_numeral  ← SÓLO ax_tc_zero/ax_tc_succ, la lectura CONSISTENTE]→ substfc 0 (termCode ⌜ψ⌝ₙ) ⌜ψ⌝ₙ
  ─[hFN ψ, congr arg3]→ substfc 0 (termCode ⌜ψ⌝ₙ) (formCode ψ)
  ─[substFormula_arith 0 ⌜ψ⌝ₙ ψ]→ formCode (substFormula 0 ⌜ψ⌝ₙ ψ) = formCode (selfAppN ψ)
  ─[hFN⁻¹]→ ⌜selfAppN ψ⌝ₙ
```

`godelPred`, `godelBeta`, `diagTerm` y `godel_comp` **no cambian** — ninguno menciona la
representación, y `godel_comp` vale para `s` arbitrario. **No hay refundación: son ~30 líneas.**

**Y la transferencia es de UN paso:** `provCode_transfer φ : axioms ⊢ (provCodeN φ ⇔ provCodeC φ)`,
que es literalmente `subst_eq_iff provFormulaC (hFN φ)`. ⟹ **D1 (`repr_pos'`) y toda la cadena
existente se transfieren componiendo con este bicondicional, sin re‑demostrarse.**

⚠️ **Lo que NO establece:** `hFN` está **asumido**, no probado — eso es S4. Y la capa **rastreada**
(los 14 tags, `hI_dot`) no se ha pilotado: usa `tcFn` sobre códigos abstractos, no sobre `formCode φ`
concreto, y ahí la transferencia por Leibniz no es automática.

### ▶ SECUENCIA RESULTANTE (S2 la fija; el piloto la reordena)

**El frente `tc` es BLOQUEANTE y va primero** — todo lo que se cierre encima de `axioms ⊢ ⊥` es vacuo.

1. **S4 paso 3** (`prf_div2_numeral`) → `prf_cons_eval`. ~20 líneas, net‑0, instrumental completo.
2. **🚩 PILOTO DEL LEMA DIAGONAL bajo códigos numerales** — *el riesgo mayor, sin pilotar*.
   `diag_arith` (`Diagonal.lean:150‑157`) compone `congr_substfc_arg2 (tc_form ψ)` con
   `substFormula_arith 0 (formCode ψ) ψ`; con códigos numerales el primer factor aterriza en
   `termCode (numeral N)` y **`substFormula_arith` no aplica**. **Si esto no sale, la vía numeral no
   existe.** Pilotar en UN solo φ antes de tocar `Minimal/Axioms.lean`.
3. Reparación del puente → **sólo entonces** el paquete `isFormCode`.
4. **S5 en paralelo** (recorte 424×): único trabajo sin riesgo ni dependencias.

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

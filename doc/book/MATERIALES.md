# Materiales para el libro

**Abierto:** 2026-09-04 · **Autor:** Julián Calderón Almendros

## Qué es esto

La cantera. Aquí se guarda material —hallazgos, mediciones, razonamientos, discusiones— que **debe
acabar en el libro** pero que todavía no tiene su capítulo escrito. Sin esto, lo que se descubre
hablando se pierde: es exactamente el motivo por el que `PLAN-LIBRO.md` §5 pone la Parte IV antes
que las Partes I–III.

**Cada entrada lleva su destino.** Si no se sabe dónde va, se escribe «destino por decidir» y se
dice por qué, pero no se deja en blanco.

**Cada afirmación lleva su estatuto**, con la disciplina de §2.6 —un docstring es testimonio, nunca
evidencia—, y aquí se aplica también a lo que escribo yo:

| marca | significa |
|---|---|
| **[medido]** | comprobado sobre el árbol, con la orden que lo comprueba |
| **[citado]** | resultado externo, con su referencia |
| **[razonado]** | conclusión mía a partir de lo anterior; se sostiene o se cae con el argumento |
| **[conjetura]** | plausible y **no** comprobado. No entra en el libro como afirmación |

⚠️ Nada de aquí entra en un capítulo sin volver a pasar los controles de `make`: en particular, toda
cifra se vuelve a medir en el momento de escribirla. Lo de aquí es materia prima fechada, no verdad
establecida.

---

## M-1 · La fuerza de la metateoría: cuánto de Lean se usa realmente

**Destino:** capítulo 3, «Teoría objeto y metateoría», como apartado propio.
**Origen:** conversación del 2026-09-04. **Pregunta que lo abre:** *el lenguaje de Lean 4 usado como
metateoría, ¿es equivalente a Peano con inducción sobre un conjunto infinito numerable de fórmulas?*

### 1.1 · La respuesta corta

**No, y por bastante margen** — pero lo que el proyecto *usa* de Lean es muchísimo más débil que
Lean, y eso sí es medible.

### 1.2 · Por qué Lean no es equivalente a PA

* **La inducción de Lean no es un esquema.** La de PA es un esquema: un axioma por fórmula del
  lenguaje aritmético de primer orden —infinitas numerables, todas con cuantificación sólo sobre
  números—. `Formula.rec` es **un solo enunciado** que cuantifica sobre un motivo
  `C : Formula → Sort u`, o sea sobre todos los predicados. Es inducción de segundo orden, no un
  esquema numerable. **[razonado]**
  En el proyecto se usa así de verdad: `prf_formCode_numeral` va por meta-recursión sobre `Formula`
  con motivo `fun φ => Prf (formCode φ =eq numeral (codeNat φ))`, y `Prf` es a su vez un `Prop`
  inductivo — motivo que en PA no se puede ni enunciar sin aritmetizar antes `Prf`. **[medido]**
* **Los universos.** Lean tiene ω universos con `Prop` impredicativo; su teoría de tipos se
  interpreta en ZFC + numerables inaccesibles, y dentro de Lean se construye un modelo de ZFC, luego
  Lean ⊢ Con(ZFC) ⊢ Con(PA), mientras que PA ⊬ Con(PA). **[citado]** — M. Carneiro, *The Type Theory
  of Lean*, MSc thesis, CMU, 2019. ⚠️ Verificar la cita y el enunciado exacto antes de publicarla.
* **Los axiomas.** `propext`, `Classical.choice` y `Quot.sound` están en el footprint de casi todo.
  **[medido]**

### 1.3 · Cuántos niveles se usan de verdad — **dos, y ninguno más**

`grep` sobre `ROBINSON_PlusPlus/` y sobre los módulos de `FOL` que la cadena importa: **cero
`Sort u`, cero `Type 1`, cero declaraciones `universe`**. El único `Type u` del árbol está en
`FOL/Completeness.lean`, que ningún módulo de RPP importa. **[medido]**

| | tipo | nivel |
|---|---|---|
| `Term`, `Formula`, `Pos` | `Type` | `Sort 1` |
| `Derives`, `Prf₀`, `Prf`, `PrfH` | `Prop` | `Sort 0` |

Aunque `Formula.rec` sea polimórfico en universos, **el proyecto sólo lo instancia en dos sitios**:
motivo en `Prop` al demostrar por inducción, motivo en `Type 0` al *definir* por recursión
(`codeNat`, `formCode`, `liftTerm`, `substFormula`). Ninguna inducción individual necesita
polimorfismo: cada una vive en un nivel fijo. **[medido]**

Y más fuerte: **no se cuantifica sobre `Prop` en ninguna parte** —ni `∀ (P : Prop)` ni
`{P : Prop}`—, luego **la impredicatividad de `Prop`, que es de donde sale buena parte de la fuerza
de Lean, no se usa.** **[medido]** ⚠️ El grep no ve usos implícitos; confirmar con el entorno
compilado.

### 1.4 · La traducción a una metateoría aritmética

Los dos niveles pasan sin residuo:

* motivo en `Type 0` (definir una función recursiva) → **recursión de curso de valores**: la función
  β de Gödel, o —en este proyecto— la capa `lenc`/`nthc` que ya se construye para 12‑A;
* motivo en `Prop` (probar por inducción) → **el esquema de inducción** de la metateoría.

Fuerza necesaria: del orden de **IΣ₁**. **[razonado]**

**Y aquí hay un cierre que el libro debe contar:** `AXIOMS.md` §1.1 argumenta que la *teoría objeto*
necesita inducción de perfil IΣ₁ para D2/D3. La metateoría necesaria sale en el mismo sitio. **La
metateoría no tiene que ser más fuerte que la teoría de la que habla** — sólo tiene que poder hablar
de sintaxis finita. **[razonado]**

### 1.5 · `Classical`: dos usos, y no son de la misma clase

Sólo hay **dos** usos explícitos en RPP. **[medido]**

**(a) `Full/PrimeFactor.lean:49` — ELIMINABLE.** Saca `∃ a, a ∣ n ∧ a ≠ 1 ∧ a ≠ n` por contradicción
desde `¬IsPrimeNat n`. Todos los divisores están acotados por `n`, y `∣`, `=` e `IsPrimeNat` son
decidibles sobre `Nat`: es una **búsqueda acotada**, constructiva de manual.
`Decidable.byContradiction` la sustituye. **[razonado]**

**(b) `Meta/OmegaReflect.lean:160` — NO ELIMINABLE, y está identificado.** Tras el `intro`, el
objetivo es `Prf φ` con `hnp : ¬ Prf φ` — o sea `¬¬ Prf φ → Prf φ`. Y `Prf φ` es **Σ₁**: existe una
derivación finita, y verificarla es decidible (`validProofFn` es ese decisor). Eliminación de doble
negación sobre un Σ₁ de matriz decidible es **el principio de Markov**. **[razonado]**

> Recordar el contexto exacto: `Reflects G := (axioms ⊢ provCodeC' G) → Prf G`
> (`Meta/DiagonalTwo.lean:113`). **[medido]**

No es «lógica clásica» a secas: es el principio **más débil** que separa el constructivismo
intuicionista del recursivo ruso. Poder decir «un solo uso esencial, y es Markov» es un resultado
del proyecto, no una nota de limpieza.

El `Classical.choice` de los footprints es otra cosa: entra casi todo por instancias `Decidable` y
por tácticas. `Meta/ChainDecode.lean:81-82` construye a mano `DecidableEq Term` y `DecidableEq
Formula` —el handler de `deriving` no cubre el anidamiento `func : String → List Term`—, así que hay
decidibilidad real disponible y ese uso es en principio prescindible. **[medido]** + **[razonado]**

Dato relacionado: **un solo `termination_by`** en todo el árbol (`Meta/CodeDecode.lean`). Todo lo
demás es recursión estructural. **[medido]**

### 1.6 · Sustituir la maquinaria meta por el proyecto Peano

Objetivo declarado por el autor: usar su proyecto Peano (con alguna extensión) como metateoría, en
lugar de la de Lean.

**Las piezas ya se están fabricando, y para otra cosa.** `ENGARCE-ROBINSON-FOL.md` §2 es literalmente
ese programa escrito: inyectividad y disyunción de constructores desde Cantor, inducción estructural
derivada de la inducción sobre la longitud, funciones recursivas vía el lema β. Y el plan 12‑A
—capa Δ₀ del verificador, `lenc`/`nthc`, `In` acotado, `chainOk` sin acumulador— es exactamente el
instrumental que una aritmética débil necesita para hablar de sintaxis. Hasta los `String` de la
signatura tienen contrapartida numérica: `strCode`, `codeNatChars`, `codeNatStr`. **[medido]**

**Lo que transfiere: todo `Prf`.** Finitario, r.e., recursión estructural sobre objetos finitos. Una
metateoría de fuerza IΣ₁ lo hospeda entero: D1, D2, el punto fijo y Gödel II *sobre* Q++.
**[razonado]**

**Lo que no transfiere: `⊢` con `gen`.** La ω‑regla tiene premisas infinitas; ninguna aritmética de
primer orden puede hospedarla. Una metateoría‑Peano reproduciría la mitad `Prf` y **no** la mitad
`⊢`. No es un defecto —es la misma razón por la que ya hay dos cálculos—, pero la sustitución habría
que enunciarla como parcial, y decir cuál mitad. **[razonado]**

### 1.6bis · El proyecto Peano ya ha hecho el experimento — y funciona

**Hallazgo del 2026-09-04**, al conectar `E:\Dropbox\GitHub\lean4\Peano`. Lo que §1.7 propone
como experimento **ya está hecho allí**, y eso cambia el estatuto de la propuesta: de idea a
técnica probada en el propio ecosistema del autor. **[medido]**

* `Peano/ConstructiveCheck.lean` es una **guarda de compilación**: comprueba, en cada `lake build`,
  que los teoremas vigilados **no dependen de `Classical.choice`**. Si alguien introduce lógica
  clásica por accidente, la compilación falla. Usa `Lean.Util.CollectAxioms` y un comando
  `#assert_constructive`.
* `DECISIONS.md` de Peano tiene una **MANDATORY-1** (desde ADR-017, 2026-07-13): *prohibido
  `Classical.*` en código nuevo*; el proyecto se re-desarrolla como completamente intuicionista.
  La deuda clásica restante está **enumerada por fichero** (`Prelim/Classical.lean`,
  `Foundation/GodelBeta.lean`, tres de teoría de grupos) y marcada como deuda, no como precedente.
* Peano está **`FEATURE-FROZEN`** desde 2026-07-14 (ADR-018), con 72 módulos y el desarrollo activo
  trasladado a `AczelSetTheory`.

**Consecuencias para el libro y para el plan de sustitución:**

1. La técnica es **portable a RPP tal cual**: `ConstructiveCheck.lean` es un fichero, no una
   metodología por inventar. Aplicarlo a RPP daría la separación que §1.5 pide —Markov esencial
   frente a `Decidable` incidental— **como control de compilación**, no como auditoría manual. Es
   exactamente la doctrina de este libro: convertir un principio en una máquina.
2. Que `Foundation/GodelBeta.lean` esté en la lista de deuda clásica de Peano es **notable**: la
   función β de Gödel es justo la pieza que §1.4 identifica como necesaria para que una metateoría
   aritmética hospede la recursión de curso de valores. Si esa pieza aún no es constructiva en
   Peano, el plan de sustitución tiene ahí su primer trabajo concreto. **[razonado]**

⚠️ No he leído `ConstructiveCheck.lean` entero ni ADR-017 completo: sólo la cabecera y la
MANDATORY. Antes de escribirlo en un capítulo, leer los dos.

### 1.7 · Experimento propuesto (barato, y con resultado publicable)

Los footprints son ya la moneda del proyecto, pero `Classical.choice` en un `#print axioms` **no
distingue el Markov esencial del `Decidable` incidental**, y ésa es justo la distinción que el plan
de sustitución necesita. Sustituir `Classical.byContradiction` por `Decidable.byContradiction` donde
se pueda y ver qué sobrevive es trabajo de una sesión.

⚠️ Todo §1.5 y §1.3 están medidos sobre el **texto** del árbol, no sobre el entorno compilado: aquí
no hay `lake` ni `lean`. Un `#print axioms` real puede destapar usos implícitos que el `grep` no ve.

---

## M-2 · El reparto de los 141 axiomas objeto: 34 de aritmética, 107 de codificación

**Destino:** capítulo 4 («La teoría objeto: Robinson Q++») y capítulo 7 («El verificador»).
**Origen:** medición del 2026-09-03 al detallar la entrada «teoría objeto» del glosario.

Parseando `Minimal/Axioms.lean` —ignorando comentarios y contando comas a profundidad cero—:
**[medido]**

```
coreAxioms    34
codingAxioms 107
axioms       141        axioms == coreAxioms ++ codingAxioms  ✓ (entrada a entrada)
```

Las cifras de los documentos de estado eran correctas. **Lo que no está destacado en ningún
documento del proyecto es el reparto**: la teoría objeto sobre la que se hace la aritmetización
tiene **tres veces más axiomas de maquinaria de codificación que de aritmética**. Eso es,
literalmente, lo que cuesta que una teoría pueda hablar de su propia sintaxis, y es un dato con
contenido expositivo.

Conecta con **ADR-015** (capítulo 22): sancionar `isFormCode` «no es más caro, es otro teorema»,
porque `axioms` crecería y `provCodeC'` cambiaría. Con el reparto delante se ve por qué esa frontera
está donde está.

⚠️ Método: mis dos primeros conteos dieron 149 y 92 y se contradecían — el que fallaba era el
parser, no los documentos. **Volver a medir con `#eval axioms.length` antes de imprimir la cifra.**

---

## M-3 · Tres funciones `numeral` distintas

**Destino:** capítulo 6 («Códigos de términos y fórmulas»), como nota; o apéndice C (trampas).

El proyecto tiene tres funciones `numeral : Nat → Term`: `Meta.Godel.numeral`
(`Meta/Godel.lean:77`), `Full.numeral` (`Full/Numerals.lean:49`) y `Minimal.Axioms.numeralM`
(`Minimal/Axioms.lean:550`), esta última con un docstring que dice que «coincide con
`Godel.numeral`». **[medido]**

Interesa por dos razones: como aviso al lector —al citar código hay que decir cuál—, y porque el
docstring afirma una coincidencia que **el compilador no verifica** (§2.6). Si esa igualdad importa
en algún punto de la cadena, debería ser un teorema, no una frase.

⚠️ Fuera del ámbito de la tarea del libro (§0): se reporta, no se arregla.


---

## M-4 · «Q tiene 7 axiomas y nosotros 34»: por qué la comparación engaña, y cuánto se puede bajar

**Destino:** capítulo 4 («La teoría objeto: Robinson Q++»), como apartado propio — *el porqué de los
axiomas*. Con reenvío desde el capítulo 22 (ADR-015).
**Origen:** pregunta del 2026-09-04. **Fuente principal:** `MINIMAL-AXIOMS.md`, que ya hace el
análisis de minimalidad; esto lo resume y añade lo que allí no está.

### 4.1 · La comparación plana es engañosa

Q tiene 7 axiomas sobre el vocabulario `{0, σ, +, ·}`. `Minimal` tiene 34 — pero **sobre un
vocabulario mucho mayor**: añade `√`, `/₂`, `%₂`, `τ` (pred), `−` (monus), listas (`[]`, `::`, `##`),
`^` y `Π_p`. **Cada símbolo de función nuevo cuesta axiomas que lo caractericen**, porque sin ellos
el símbolo no está fijado: cualquier función lo satisface. Así que el 34 no mide «más aritmética»,
mide **más vocabulario**. **[razonado]**

El desglose real (`MINIMAL-AXIOMS.md` §4): **[citado]**

| categoría | nº | ¿reducible? |
|---|---:|---|
| núcleo Q | 6 | no — base de la aritmética |
| estructura PA⁻ (comm, assoc, distrib, orden) | 8 | no *sin inducción* |
| caracterización de `√` | 2 | no — la definen por cotas |
| caracterización de `div2`/`mod2` | 2 | no — las definen |
| caracterización de `pred` | 2 | no |
| caracterización de `sub` (monus) | 1 | no — por testigo |
| testigos inductivos (`ax21`, `ax24`) | 2 | no sin inducción |
| listas (`ax_L0-3`, `ax_C1-3`) | 7 | no sin inducción |
| `pow` | 2 | no — recursión primitiva |
| `prod_pairs` | 2 | no — recursión sobre listas |
| **total** | **34** | |

**La comparación justa.** Restringido al vocabulario de Q, `Minimal` usa **14** axiomas donde Q usa
7: los 6 del núcleo más los 8 de PA⁻. Y esos 8 de más son exactamente lo que **Q no puede
demostrar**: Q prueba `5+7 = 7+5`, pero no `∀x,y. x+y = y+x`. Sin inducción, la conmutatividad
universal hay que postularla. **Los 7 extra son el precio de querer álgebra cuantificada sin
inducción; los otros 20 son el precio de un vocabulario más rico.** **[razonado]**

⚠️ Q3 (`y = 0 ∨ ∃x. σx = y`) **no** está en `Minimal`: se usa `pred` total con `ax25`/`ax26`. Dos
axiomas donde Q gasta uno — es una de las reducciones posibles, y `MINIMAL-AXIOMS.md` §4.3 la
propone al precio de complicar toda prueba que use `pred`. **[citado]**

### 4.2 · Ya se ha reducido cinco veces

No es hipotético: hay historial documentado (`MINIMAL-AXIOMS.md` §2.4). **[citado]**

| axioma retirado | por qué | cuándo |
|---|---|---|
| `ax20_eq_decidable` | derivable de ax18 + ax19 + sustitución | 2026-05 |
| `ax22_cantor_proj_exists` | `proj1`/`proj2` pasan a definiciones concretas | 2026-06-02 |
| `ax23_cantor_proj_uniq` | nunca usado; `cantor_uniqueness` ya lo cubría | 2026-06-02 |
| `ax27_add_left_cancel` | derivable en PA⁻ (tricotomía + monotonía + irreflexividad) | 2026-06-03 |
| `ax28_mul_two_cancel` | derivable sin inducción; hoy es el teorema `teo_2_11` | 2026-06-02 |

El método es siempre el mismo y es material del libro: **buscar el axioma que ya era teorema**. Dos
de los cinco cayeron porque un símbolo opaco pasó a ser una definición.

### 4.3 · Lo que el análisis existente NO dice, y creo que es lo más importante

`MINIMAL-AXIOMS.md` está fechado antes de que existiera la capa `Meta/`, y por eso razona sobre la
reducción como si fuera una limpieza. **Ya no lo es.** **[razonado]**

Desde que `axiomsCodeT` codifica la lista de axiomas y el verificador interno la consulta,
`provCodeC'` —y con él la sentencia $G$— **dependen de qué axiomas hay**. Es exactamente el
argumento de **ADR-015** en la dirección de añadir («sancionar `isFormCode` no es más caro: es otro
teorema»), y vale igual en la dirección de quitar:

> **Reducir el número de axiomas objeto, hoy, no simplifica el mismo teorema: cambia el teorema.**

Consecuencia práctica: la ventana para reducir era *antes* de construir la aritmetización. Ahora
toda reducción obliga a re-auditar la cadena Gödel, y el libro debería decirlo — es una lección de
diseño que no aparece en los manuales: **la elección de axiomas deja de ser reversible en cuanto la
teoría empieza a hablar de sí misma.**

### 4.4 · Rutas de reducción que siguen abiertas

De `MINIMAL-AXIOMS.md` §4, con mi lectura del coste actual: **[citado]** + **[razonado]**

1. **Añadir inducción** — `ax21`, `ax24`, `ax_C3`, `ax_L3` pasan a teoremas (ya lo son en `Full/`), y
   con inducción fuerte también `ax_p_tfa`. Pero eso deja de ser `Minimal` por definición.
2. **Cambiar de codificación** — Q3 en vez de `pred` total: −1 axioma, +complicación en todas las
   pruebas con `pred`.
3. **Restringir el vocabulario** — quitar `√`, `mod2`, `sub`, listas, `pow`, `prod_pairs`: se bajaría
   mucho, pero se pierde Cantor, listas y la factorización, o sea la aritmetización entera.
4. **Diferir la factorización** a `Full/`: −4 axiomas y −1 meta-axioma, volviendo a 30.
   `MINIMAL-AXIOMS.md` lo desaconseja porque la factorización la necesita la gödelización.

Veredicto del documento, que comparto: **mínimo local defendible**. Lo que el libro tiene que
explicar no es «por qué 34 y no 7», sino **por qué cada símbolo nuevo cuesta axiomas y por qué sin
inducción hay que postular lo que con inducción se demuestra**.

### 4.5 · Pendiente

⚠️ `MINIMAL-AXIOMS.md` tiene una incoherencia interna: el encabezado de §2 dice «Comparación con
`Minimal` (30 axiomas)» y §3.5.1 y §4 dicen 34. Es el fallo de §27 —cuerpo actualizado, encabezado
no—. Fuera del ámbito del libro (§0): se reporta, no se toca. **[medido]**

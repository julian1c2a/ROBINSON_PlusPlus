# Auditoría del proyecto — 2026-09-11 · **dos ciclos, en las dos direcciones**

**Alcance:** la **intención** declarada, la **documentación de salida**, el **plan de prueba** y el
**código** — recorridos de arriba abajo y de abajo arriba, dos veces.
**Estado del árbol al auditar:** `master`, limpio, **142 jobs · 128 módulos · 0 sorry · 5 `axiom`**.
**Método:** cada afirmación va marcada, con la orden que la sostiene.

| marca | significa |
|---|---|
| **[medido]** | verificado contra el árbol, aquí, hoy |
| **[razonado]** | conclusión a partir de lo medido; se sostiene o se cae con el argumento |
| ⬜ **[no medido]** | señalado y **no** comprobado. No se afirma |

**Resultado:** **diez hallazgos**, seis corregidos en esta pasada y cuatro abiertos. Uno de ellos
—**F‑1**— no es deriva documental: es **estructural**, y afecta a lo que el proyecto puede afirmar
sobre Gödel II.

⚠️ **Tres de los diez son míos, de ayer o de hoy.** La auditoría del 2026‑09‑10 arregló el *cuerpo*
de los documentos y no miró **ni el titular ni su propia memoria**.

---

## 0 · Cómo está organizada

El encargo pedía auditar **en las dos direcciones** y **dos veces**. Eso no es repetir: es que cada
dirección ve una clase distinta de error, y el segundo ciclo ve lo que el método del primero no
puede ver.

| | recorrido | qué clase de error encuentra |
|---|---|---|
| **Ciclo 1 ↓** | intención → documentación → plan de prueba → código | **deriva**: lo que se dijo y dejó de ser cierto |
| **Ciclo 1 ↑** | código → plan de prueba → documentación → propuesta | **omisión y desajuste**: lo construido que nadie declara, y lo declarado que no se construyó |
| **Ciclo 2** | la auditoría contra sí misma | lo que *leer y comparar* **no puede ver**: acuerdos falsos, ausencias, cifras sin control |

---

## 1 · CICLO 1 ↓ — de la intención hacia el código

### F‑3 · ⛔ La **declaración de propósito** describía otro proyecto ✅ CORREGIDO

`README.md` §Description, que es la primera cosa que lee cualquiera: **[medido]**

* **No mencionaba la incompletitud** — que hoy es `Meta/`, **106 de 128 módulos**, el **83 %** del
  árbol. Hablaba sólo de fundar los naturales, las listas y el TFA.
* Citaba una capa **`Intermediate/`** que se **eliminó el 2026‑06‑11**
  (`CURRENT-STATUS-PROJECT.md:409`).
* Decía «un sistema minimalista con **34 axiomas**» sin decir que son los **matemáticos**:
  `axioms.length = 141`.

🔑 **Por qué importa más que una errata**: es el único documento que responde *«¿qué es esto?»*, y
llevaba meses respondiendo mal. La auditoría de doc del 10h recorrió los banners y **no tocó esta
sección**, porque no contiene cifras y ningún control la mira.

### F‑2 · ⛔⛔ **Seis** documentos autoritativos con **el mismo titular falso** ✅ CORREGIDO + control

`README`, `REFERENCE`, `DECISIONS`, `AXIOMS`, `DEPENDENCIES` y `GODEL-STATUS` compartían, **carácter
por carácter**: **[medido]**

> `> ## ESTADO REAL — 2026-09-09 · rama A cerrada · A5 y B8b cerradas · C3: 5 de 7 reflectores · D3 a DOS obligaciones`

**C3 se cerró el 10e** (7/7) y **D3 se probó el 10g**. Y las **cifras** de las líneas siguientes
estaban **al día** — 142 jobs, 5 `axiom` — porque `[A]` las mira.

🔑🔑 **La lección, y es nueva**: *un banner puede estar **simultáneamente al día en sus números y
mintiendo en su frase**.* Es la forma más difícil de detectar, porque el documento **parece recién
revisado**. Y el titular estaba **duplicado**: **duplicar un titular es duplicar su caducidad**.

⇒ **Control nuevo `[E]`** en `check-doc-sync.bash` (AI‑GUIDE §27.3): compara la **fecha** del
titular con la entrada más reciente del `CHANGELOG`. Es una heurística —no lee la frase— pero
habría cazado los seis. Entra como **AVISO**.

⚠️ **Calibrado al estrenarlo**: señaló **cuatro** titulares por detrás, y **los cuatro son
legítimos** (documentos que no cambiaron ese día). ⇒ `[E]` dice «míralo», no «está mal». Un titular
por detrás es normal; **seis idénticos** por detrás no lo era.

### F‑7 · `PLAN-FRENTE-A.md`, citado como «Estado autoritativo» ✅ CORREGIDO

Los mismos seis banners enviaban a `PLAN-FRENTE-A.md` como segunda parada del estado. Ese
documento (2026‑08‑19) plantea *«¿vuelve la capa rastreada?»* — pregunta **contestada** desde el
2026‑08‑23, con la cuarentena vacía. **[medido]**

### F‑4 · ⬜ **No existe un documento de estrategia de prueba** — ABIERTO

**Cero** ficheros del repo contienen «plan de prueba», «estrategia de prueba» o «test plan».
**[medido]**

El plan existe **como práctica** y es bueno: `lake build` + `check-sorry` + `check-doc-sync` + CI +
la disciplina de `sondeos/`. Pero **no está escrito**, y eso tiene un coste concreto: la disciplina
más distintiva del proyecto —**medir en un sondeo compilado antes de tocar producción**— no está
declarada en ninguna parte como *método de verificación*, sólo se infiere de que hay 61 ficheros en
un directorio.

**Propuesta**: un `PLAN-PRUEBAS.md` corto que diga qué garantiza cada control, qué **no** garantiza
ninguno, y cuándo un frente exige sondeo previo. ⚠️ Lo que hoy no garantiza **nada** está en §4.

### F‑5 · CI no comprobaba la cifra de jobs ✅ CORREGIDO

`.github/workflows/build.yml` ejecutaba `check-doc-sync.bash --quick`. Con `--quick`, `JOBS` queda
vacío y el control `[A]` **se salta la comprobación de jobs** — el propio script lo avisa.
⇒ el «142 jobs» de siete banners **sólo lo verificaba una ejecución local**. **[medido]**

---

## 2 · CICLO 1 ↑ — del código hacia la propuesta

### F‑1 · ⛔⛔⛔ **Gödel II está montado pero NO ensamblado**, y la razón es de fondo

Éste es el hallazgo de la auditoría. Lo demás es deriva; esto no.

**Lo medido, y son cuatro hechos:** **[medido]**

```lean
goedel_second' (G) (fp_bwd) (nec1) (hgi : ¬ (axioms ⊢ G)) : ¬ (axioms ⊢ consistencyFormula')
goedel_first_numeral (hcon : ConsistentOmega)             : ¬ Prf godelCN
prf_to_derives {φ} (h : Prf φ)                            : axioms ⊢ φ
```

1. `hgi` es sobre **`axioms ⊢`**, el cálculo **ω**. Gödel I concluye sobre **`Prf`**, el
   **finitario**.
2. Por `prf_to_derives`, `¬(axioms ⊢ G) → ¬ Prf G` — **no al revés**. ⇒ `hgi` es **estrictamente
   más fuerte** que lo que Gödel I entrega.
3. **No existe** la vuelta `⊢ → Prf` en el árbol (búsqueda vacía), ni ninguna versión ω de Gödel I.
4. **Nadie consume `goedel_second'`**: es una hoja, pese a estar en su bloque `export`.

**Y hay algo peor que una hipótesis sin descargar.** `FOL/MetaRules.lean` documenta, en sus propios
docstrings: **[medido]**

> `gen` — *«Generalización universal (**ω‑regla**)… **Meta‑axioma**: no derivable de
> `Derives.intro_forall` (que es finitario)»*
> `dne` — *«…sólido para el modelo estándar ℕ (coherente con la lectura ω‑lógica **"demostrabilidad
> = verdad en ℕ"**)»*

**[razonado]** Bajo esa lectura, y con `ConsistentOmega`, `G` es **verdadera** (dice exactamente
que no tiene demostración finitaria, y no la tiene). Si `axioms ⊢` alcanza las verdades de ℕ,
entonces **`hgi` es falsa** y `goedel_second'` es **vacuo**.

⬜ **[no medido]** — y es deliberado. Decidirlo exige fijar la fuerza real de `axioms ⊢`, que
depende de si `gen` se aplica sobre **todo `Term`** (lo que la acerca a una generalización ordinaria
con variable propia) o sobre **numerales** (ω‑regla plena). **Es la pregunta abierta más importante
del proyecto**, y no se contesta leyendo: se contesta decidiendo.

### F‑1b · ⚠️ Y el docstring que lo afirmaba **lo escribí yo ayer**

El 2026‑09‑10h, en el commit `eaec1d0` —una pasada cuyo propósito era **corregir docstrings
falsos**— reforcé este docstring de `goedel_second'` hasta decir:

> *«…dos son piezas construibles y **`hgi` es la mitad demostrada de Gödel I**»*

**Es falso**, por (1)–(3). El texto anterior decía sólo «(`hgi`, mitad de Gödel I)» — sugestivo,
pero más flojo. **Lo empeoré mientras arreglaba.** ✅ Retirado, con la medición escrita en su sitio.

### ⭐ La salida existe, y es construible

**Gödel II sobre `Prf`** — `goedel_second_prf : ConsistentH → ¬ Prf Con'`, el nombre que el proyecto
lleva planeando **desde junio** y que figura en la lista de símbolos muertos. Lo que hace falta,
medido: **[medido]**

| pieza | sobre `Prf` |
|---|---|
| **D1** `repr_pos'_prf` | ✅ existe |
| **D2** `d2_prf` | ✅ existe |
| **D3** `d3_prf_real` | ✅ existe |
| punto fijo `godelCN_fixedpoint` | ⬜ sólo sobre `⊢` |
| `con_imp_godel'` | ⬜ sólo sobre `⊢` |

⇒ **las tres condiciones de derivabilidad ya están donde tienen que estar.** Faltan dos piezas, y
ninguna es una condición de derivabilidad.

### F‑8 · ⬜ Los controles del **libro** no están en CI — ABIERTO

`doc/book/scripts/{simbolos,terminos,verificar_pdf}.py` sólo se ejecutan a mano. El control §2.1 del
libro —*«el código IMPRESO en el PDF es el del repo»*— **no lo ejecuta nadie automáticamente**, y es
justo el que protege contra que el libro afirme algo que el árbol ya no cumple. **[medido]**

### F‑9 · ⬜ `Probe/` está **gitignored** — ABIERTO, y es una decisión

`.gitignore:30`. **[medido]** Las mediciones que justifican decisiones —incluidas las que sostienen
ADRs— viven ahí y **no se versionan**. `sondeos/` sí se versiona, y su `README` explica por qué:
*«contienen resultados compilados que costó obtener y que no deben re‑derivarse»*. El mismo
argumento aplica a los `Probe/` que deciden un ADR. **[razonado]** No es un error: es una frontera
que nadie ha escrito.

---

## 3 · CICLO 2 — la auditoría contra sí misma

El ciclo 1 funciona **leyendo y comparando**. Esa técnica ve **deriva** y no ve tres cosas.

### (a) Lo que documentación y código **afirman de acuerdo**, y es falso

→ **F‑1**. No se encontró leyendo prosa: se encontró mirando **los tipos** y preguntando *«¿quién
descarga esta hipótesis?»*. Ningún control de sincronía podía verlo, porque **no hay
desincronía**: el doc y el código dicen lo mismo.

🔑 **La pregunta que lo destapa, y conviene que quede**: *por cada teorema cabecera, ¿quién descarga
cada una de sus hipótesis, y con qué?* Si la respuesta es «nadie», el teorema está **montado, no
ensamblado** — y eso hay que decirlo en el mismo sitio donde se anuncia el resultado.

### (b) Las **ausencias** — invisibles a cualquier diff

→ **F‑4** (no hay documento de pruebas), **F‑8** (controles del libro fuera de CI), **F‑9**
(`Probe/` sin versionar). Un documento que no existe no contradice a nadie.

### (c) Los **números que nadie comprueba**

### F‑6 · «141 axiomas objeto = 34 + 107» ✅ CORREGIDO en el kernel

Aparece en **siete** banners. `check-doc-sync` `[A]` comprueba jobs, módulos, conteo por capa,
cuarentena, `axiom` de Lean y `sorry` — **esta cifra no**. **[medido]**

Medido con el kernel: `axioms.length = 141`, `coreAxioms.length = 34`,
`codingAxioms.length = 107`. **Es cierta.** Pero lo era **por suerte**, no por control.

⇒ **La reparación no es un grep, es el kernel** (`Full/Induction.lean`):

```lean
theorem axioms_len       : axioms.length = 141 := rfl
theorem coreAxioms_len   : coreAxioms.length = 34 := rfl
theorem codingAxioms_len : codingAxioms.length = 107 := rfl
```

Si alguna lista cambia, **rompe el build** — que es infinitamente mejor que romper un control.

### F‑10 · ⚠️⚠️ Mi propia memoria tenía **la enfermedad que acababa de documentar** ✅ CORREGIDO

`MEMORY.md`, el índice que se carga en cada sesión: **[medido]**

* **Siete líneas** contradiciendo **su propio banner**: el banner decía «5 axiom» y el cuerpo decía
  «siguen **6**», «34 = **23 + 11**», «**9 de 11**», «**2 de 11** certificados», y que `primAxioms`
  «**MUEVE LA FRONTERA DE LA TEORÍA**» — afirmación que yo mismo había corregido horas antes.
* **236 líneas sobre un límite de 200** ⇒ se cargaba **truncado**: 36 líneas del índice **no se
  leían**. Un índice demasiado largo **no se lee entero**, y las que se pierden son las del final.

⇒ reescrito: **107 líneas, cero contradicciones**. Es exactamente F‑2 —banner al día, cuerpo
atrasado— **dentro del fichero que documenta F‑2**.

---

## 4 · Lo que NINGÚN control garantiza hoy

Lo más útil de una auditoría no es la lista de fallos: es el mapa de lo que **nadie está mirando**.

| nadie comprueba | consecuencia | ¿hay reparación? |
|---|---|---|
| que **las hipótesis de un teorema cabecera sean descargables** | F‑1: un resultado se anuncia como cerrado y no lo está | ⬜ no mecanizable; la **pregunta** de §3(a) sí |
| que la **frase** de un banner siga siendo cierta | F‑2, seis veces a la vez | 🔶 `[E]` mira la **fecha**, no la frase |
| que el **README** describa el proyecto que existe | F‑3, meses | ⬜ ninguna |
| que lo **impreso en el libro** siga cuadrando con el árbol | F‑8 | ⬜ existe el script, no está en CI |
| que las **cifras de los banners** estén todas medidas | F‑6 | ✅ las tres del objeto, ya en el kernel |
| que la **memoria de sesión** no se contradiga | F‑10 | ⬜ ninguna |

---

## 5 · Balance — ¿está mal la idea?

**No.** Era la pregunta explícita del encargo y la respuesta es limpia: las tres capas
(`Minimal` → `Full` → `Meta`), la teoría objeto y la cadena de Gödel son **coherentes**, y los
resultados son **reales** — D1, D2 y D3 demostradas, Gödel I `⊬G` sin postulado gödeliano, 5
`axiom` de Lean y ninguno gödeliano.

Lo que está mal es **otra cosa, y en dos sitios**:

1. **La propuesta no se actualizó nunca** (F‑3). El proyecto creció hacia la incompletitud y su
   documento de entrada se quedó en 2026‑06. No es un error de idea: es que la idea **no está
   escrita** donde debería.
2. **Gödel II está enunciado sobre el cálculo equivocado para poder ensamblarse** (F‑1). Tampoco es
   un error de idea —el enunciado es un teorema correcto—: es que **sus hipótesis no son las que la
   cadena puede dar**, y la versión que sí encaja (`Prf`) tiene ya sus tres condiciones listas.

⚠️ **Y una advertencia sobre este documento**: es testimonio, no evidencia. Lo marcado ⬜ **no está
comprobado**, en particular la fuerza real de `axioms ⊢`, que es de donde depende si F‑1 es «una
pieza que falta» o «un teorema vacuo». **Esa medición es la siguiente.**

---

**Autor:** Julián Calderón Almendros · auditoría asistida
**Relacionado:** `doc/book/AUDITORIA-2026-09-10.md` (la del libro, que encontró la causa raíz del
control), `DECISIONS.md` (ADR‑022, ADR‑023), `AI-GUIDE.md` §27.2–§27.3.
